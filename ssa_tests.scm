;;; Unit tests for (hop pass ssa), run by run_tests.sh:
;;;   csi -R r7rs -I . -s ssa_tests.scm
;;; Whole-compiler coverage of the SSA round trip comes from running the main
;;; suite with HOP_SSA=roundtrip; these tests exercise the module directly on
;;; small hand-written CFGs, including irreducible loops, unreachable code,
;;; and parallel-copy cycles.

(load "compiler.scm")

(import (scheme base) (scheme write) (srfi 69)
        (hop pass cfg) (hop pass ssa))

(define failures 0)

(define (check name ok)
  (unless ok
    (set! failures (+ failures 1))
    (display "FAIL ") (display name) (newline)))

;;; A tiny interpreter for the TAC subset the test programs use.

(define (run-cfg cfg params args)
  (let ((env (make-hash-table))
        (blocks (list->vector cfg))
        (label->index (make-hash-table)))
    (for-each (lambda (p a) (hash-table-set! env p a)) params args)
    (let loop ((i 0))
      (let ((label (basic-block-label (vector-ref blocks i))))
        (when label (hash-table-set! label->index label i))
        (when (< (+ i 1) (vector-length blocks)) (loop (+ i 1)))))
    (define (value x)
      (if (symbol? x)
          (let ((v (hash-table-ref/default env x 'unbound)))
            (when (eq? v 'unbound) (error "unbound variable" x))
            v)
          x))
    (define (eval-rhs rhs)
      (cond
       ((not (pair? rhs)) (value rhs))
       ((eq? (car rhs) 'primop)
        (let ((a (value (caddr rhs))) (b (value (cadddr rhs))))
          (case (cadr rhs)
            ((+) (+ a b)) ((-) (- a b)) ((*) (* a b))
            ((=) (= a b)) ((<) (< a b))
            (else (error "unsupported primop" rhs)))))
       (else (error "unsupported rhs" rhs))))
    (let run-block ((i 0) (steps 0))
      (when (> steps 100000) (error "runaway program"))
      (let walk ((instrs (basic-block-instructions (vector-ref blocks i))))
        (if (null? instrs)
            (run-block (+ i 1) (+ steps 1))
            (let ((instr (car instrs)))
              (case (car instr)
                ((label) (walk (cdr instrs)))
                ((assign)
                 (hash-table-set! env (cadr instr) (eval-rhs (caddr instr)))
                 (walk (cdr instrs)))
                ((if)
                 (run-block (hash-table-ref label->index
                                            (if (value (cadr instr))
                                                (caddr instr)
                                                (cadddr instr)))
                            (+ steps 1)))
                ((goto)
                 (run-block (hash-table-ref label->index (cadr instr)) (+ steps 1)))
                ((return) (value (cadr instr)))
                (else (error "unsupported instruction" instr)))))))))

(define-syntax define-program
  (syntax-rules ()
    ((_ name params instrs) (define name (cons 'params 'instrs)))))

;; diamond: join of two assignments to one variable
(define-program diamond (c a b)
  ((label e) (if c l1 l2)
   (label l1) (assign r a) (goto j)
   (label l2) (assign r b) (goto j)
   (label j) (assign out (primop + r 1)) (return out)))

;; loop that swaps two variables through a temp each iteration
(define-program swap-loop (a b n)
  ((label h) (assign t (primop = n 0)) (if t x body)
   (label body) (assign n2 (primop - n 1)) (assign tmp a) (assign a b) (assign b tmp)
   (assign n n2) (goto h)
   (label x) (assign d (primop - a b)) (return d)))

;; loop with two entries (irreducible): entry jumps into either loop block
(define-program irreducible (c x n)
  ((label e) (if c a b)
   (label a) (assign x (primop + x 1)) (goto b)
   (label b) (assign n (primop - n 1)) (assign t (primop = n 0)) (if t done a)
   (label done) (return x)))

;; entry block falls through into a loop header; dead code after a return
(define-program fallthrough (n)
  ((assign acc 0)
   (label h) (assign t (primop < acc n)) (if t body done)
   (label body) (assign acc (primop + acc 2)) (goto h)
   (label done) (return acc)
   (label dead) (assign y 2) (return y)))

;; the loop body is the entry block itself (entry is a back-edge target)
(define-program entry-loop (n acc)
  ((label h) (assign t (primop = n 0)) (if t x b)
   (label b) (assign acc (primop + acc n)) (assign n (primop - n 1)) (goto h)
   (label x) (return acc)))

(define (params-of program) (car program))
(define (cfg-of program) (build-cfg (cdr program)))

(define (round-trip-agrees? name program inputs)
  (let* ((params (params-of program))
         (cfg (cfg-of program))
         (after (ssa-round-trip-cfg params cfg)))
    (for-each
     (lambda (args)
       (let ((expected (run-cfg cfg params args))
             (got (run-cfg after params args)))
         (check (string-append name " on " (let ((port (open-output-string))) (write args port) (get-output-string port)))
                (equal? expected got))))
     inputs)))

(round-trip-agrees? "diamond" diamond '((#t 1 2) (#f 1 2)))
(round-trip-agrees? "swap-loop" swap-loop '((1 2 0) (1 2 1) (1 2 2) (5 9 7)))
(round-trip-agrees? "irreducible" irreducible '((#t 0 1) (#f 0 1) (#t 0 4) (#f 5 3)))
(round-trip-agrees? "fallthrough" fallthrough '((0) (1) (5) (6)))
(round-trip-agrees? "entry-loop" entry-loop '((0 7) (3 0) (4 1)))

;;; Construction properties

(define (phi-count ssa)
  (let ((blocks (ssa-proc-blocks ssa)))
    (let loop ((i 0) (total 0))
      (if (= i (vector-length blocks))
          total
          (loop (+ i 1) (+ total (length (ssa-block-phis (vector-ref blocks i)))))))))

(let ((ssa (cfg->ssa (params-of diamond) (cfg-of diamond))))
  (check "diamond verifies" (null? (verify-ssa ssa)))
  (check "diamond has exactly one phi (r at the join)" (= (phi-count ssa) 1)))

(let ((ssa (cfg->ssa (params-of fallthrough) (cfg-of fallthrough))))
  (check "unreachable block is dropped"
         (= (vector-length (ssa-proc-blocks ssa)) 4)))

(let ((ssa (cfg->ssa (params-of entry-loop) (cfg-of entry-loop))))
  (check "entry-loop gets a synthetic empty entry block"
         (and (not (ssa-block-label (vector-ref (ssa-proc-blocks ssa) 0)))
              (null? (ssa-block-instrs (vector-ref (ssa-proc-blocks ssa) 0)))))
  (check "entry-loop verifies" (null? (verify-ssa ssa))))

(let ((ssa (cfg->ssa (params-of irreducible) (cfg-of irreducible))))
  (check "irreducible verifies" (null? (verify-ssa ssa))))

;;; The verifier rejects broken SSA.

(let* ((ssa (cfg->ssa (params-of diamond) (cfg-of diamond)))
       (blocks (ssa-proc-blocks ssa))
       (join (vector-ref blocks 3)))
  (set-ssa-block-instrs! join (cons '(assign junk nothing-defines-this) (ssa-block-instrs join)))
  (check "verifier flags an undefined name" (pair? (verify-ssa ssa))))

(let* ((ssa (cfg->ssa (params-of diamond) (cfg-of diamond)))
       (blocks (ssa-proc-blocks ssa))
       (then-block (vector-ref blocks 1))
       (def (car (ssa-block-instrs then-block))))
  (set-ssa-block-instrs! then-block (cons def (ssa-block-instrs then-block)))
  (check "verifier flags a duplicate definition" (pair? (verify-ssa ssa))))

(let* ((ssa (cfg->ssa (params-of swap-loop) (cfg-of swap-loop)))
       (blocks (ssa-proc-blocks ssa))
       (body (vector-ref blocks 2)))
  ;; use a name before it is defined, inside one block
  (set-ssa-block-instrs! body
                         (cons '(assign early (primop + n2~1 1)) (ssa-block-instrs body)))
  (check "verifier flags a use before its definition" (pair? (verify-ssa ssa))))

;;; Parallel copies

(define (simulate-copies code env)
  (let ((e (map (lambda (p) (cons (car p) (cdr p))) env)))
    (for-each
     (lambda (instr)
       (let* ((src (caddr instr))
              (v (if (symbol? src) (cdr (assq src e)) src))
              (cell (assq (cadr instr) e)))
         (if cell (set-cdr! cell v) (set! e (cons (cons (cadr instr) v) e)))))
     code)
    e))

(define (copies-correct? copies env)
  (let* ((counter 0)
         (code (sequentialize-copies copies
                                     (lambda () (set! counter (+ counter 1))
                                             (string->symbol (string-append "tmp" (number->string counter))))))
         (after (simulate-copies code env)))
    (all (lambda (c)
           (let ((expected (if (symbol? (cdr c)) (cdr (assq (cdr c) env)) (cdr c))))
             (eqv? (cdr (assq (car c) after)) expected)))
         copies)))

(check "swap cycle" (copies-correct? '((a . b) (b . a)) '((a . 1) (b . 2))))
(check "three-cycle" (copies-correct? '((a . b) (b . c) (c . a)) '((a . 1) (b . 2) (c . 3))))
(check "chain" (copies-correct? '((a . b) (b . c)) '((a . 1) (b . 2) (c . 3))))
(check "cycle plus literal and fan-out"
       (copies-correct? '((a . b) (b . a) (c . 7) (d . a)) '((a . 1) (b . 2) (c . 0) (d . 0))))
(check "self copy is dropped" (null? (sequentialize-copies '((a . a)) (lambda () 'tmp))))

(if (zero? failures)
    (begin (display "ssa tests passed") (newline))
    (begin (display failures) (display " ssa test(s) failed") (newline) (exit 1)))
