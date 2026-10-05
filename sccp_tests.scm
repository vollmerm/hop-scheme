;;; Unit tests for (hop pass sccp), run by run_tests.sh:
;;;   csi -R r7rs -I . -s sccp_tests.scm
;;; Each case is a hand-written CFG. Shape checks look at the optimized
;;; instructions; the agreement checks run the original and optimized CFGs.

(import (scheme base) (scheme process-context))

;; HOP_COMPILER (set by tools/scheme.sh) names the compiled compiler to load.
(load (or (get-environment-variable "HOP_COMPILER") "compiler.scm"))

(import (scheme write) (only (srfi 1) any filter-map find take) (srfi 69)
        (hop utils) (hop pass cfg) (hop pass ssa) (hop pass sccp))

(define failures 0)

(define (check name ok)
  (unless ok
    (set! failures (+ failures 1))
    (display "FAIL ") (display name) (newline)))

(define-syntax define-program
  (syntax-rules ()
    ((_ name params instrs) (define name (cons 'params 'instrs)))))

(define (optimize program . options)
  (let ((ssa (cfg->ssa (car program) (build-cfg (cdr program)))))
    (ssa->cfg (apply sccp-ssa ssa options))))

(define (all-instrs cfg)
  (append-map basic-block-instructions cfg))

(define (mentions? cfg pattern)
  (let walk ((x (all-instrs cfg)))
    (cond ((equal? x pattern) #t)
          ((pair? x) (or (walk (car x)) (walk (cdr x))))
          (else #f))))

(define (assigns-literal? cfg literal)
  (any (lambda (instr)
         (and (eq? (car instr) 'assign) (equal? (caddr instr) literal)))
       (all-instrs cfg)))

(define (has-primop? cfg op)
  (any (lambda (instr)
         (and (eq? (car instr) 'assign)
              (pair? (caddr instr))
              (eq? (car (caddr instr)) 'primop)
              (eq? (cadr (caddr instr)) op)))
       (all-instrs cfg)))

(define (labels cfg) (filter-map basic-block-label cfg))

;; both arms compute the same constant, so the join is a constant
(define-program same-constant (c)
  ((label e) (if c l1 l2)
   (label l1) (assign r 2) (goto j)
   (label l2) (assign r (primop + 1 1)) (goto j)
   (label j) (assign out (primop + r 1)) (return out)))
(let ((cfg (optimize same-constant)))
  (check "join of equal constants folds" (assigns-literal? cfg 3))
  (check "no addition left" (not (has-primop? cfg '+))))

;; different constants do not fold
(define-program different-constants (c)
  ((label e) (if c l1 l2)
   (label l1) (assign r 2) (goto j)
   (label l2) (assign r 3) (goto j)
   (label j) (assign out (primop + r 1)) (return out)))
(check "join of different constants stays" (has-primop? (optimize different-constants) '+))

;; a known cons makes the null? test false and the branch dead
(define-program dead-arm (a)
  ((label e) (assign p (primop cons a 1)) (assign t (primop null? p)) (if t l1 l2)
   (label l1) (assign x 10) (return x)
   (label l2) (assign y 20) (return y)))
(let ((cfg (optimize dead-arm)))
  (check "dead arm label dropped" (not (memq 'l1 (labels cfg))))
  (check "live arm kept" (assigns-literal? cfg 20)))

;; a dead arm's values stay out of the join
(define-program dead-join (a)
  ((label e) (assign p (primop cons a 1)) (assign t (primop pair? p)) (if t l1 l2)
   (label l1) (assign r 5) (goto j)
   (label l2) (assign r 6) (goto j)
   (label j) (assign out (primop + r 1)) (return out)))
(check "unreached arm does not spoil the join"
       (assigns-literal? (optimize dead-join) 6))

;; inside the then-arm of a pair? test, a second test and a car are known
(define-program refine-pair (x)
  ((label e) (assign t (primop pair? x)) (if t l1 l2)
   (label l1) (assign u (primop pair? x)) (if u l3 l2)
   (label l3) (assign v (primop car x)) (return v)
   (label l2) (return 0)))
(let ((cfg (optimize refine-pair)))
  (check "repeated pair? test removed"
         (= 1 (length (filter (lambda (i) (and (eq? (car i) 'assign)
                                               (pair? (caddr i))
                                               (equal? (take (caddr i) 2) '(primop pair?))))
                              (all-instrs cfg)))))
  (check "car after pair? test is unsafe" (has-primop? cfg 'unsafe-car))
  (check "no safe car left" (not (has-primop? cfg 'car))))

;; a car without a test stays safe
(define-program plain-car (x)
  ((label e) (assign v (primop car x)) (return v)))
(check "untested car stays safe" (has-primop? (optimize plain-car) 'car))

;; inside the then-arm of a null? test, a second null? test is true
(define-program refine-null (x)
  ((label e) (assign t (primop null? x)) (if t l1 l2)
   (label l1) (assign u (primop null? x)) (if u l3 l4)
   (label l3) (return 1)
   (label l4) (return 2)
   (label l2) (return 3)))
(let ((cfg (optimize refine-null)))
  (check "second null? test decided" (not (memq 'l4 (labels cfg)))))

;; loop-carried values are not constants
(define-program counting-loop (n)
  ((assign acc 0)
   (label h) (assign t (primop < acc n)) (if t body done)
   (label body) (assign acc (primop + acc 2)) (goto h)
   (label done) (return acc)))
(check "loop counter not folded" (has-primop? (optimize counting-loop) '+))

;; a loop that never changes a value keeps it constant through the phi
(define-program steady-loop (n)
  ((assign k 7)
   (label h) (assign t (primop < n 10)) (if t body done)
   (label body) (assign n (primop + n 1)) (goto h)
   (label done) (assign r (primop + k 1)) (return r)))
(check "loop invariant constant folds"
       (assigns-literal? (optimize steady-loop) 8))

;; dead allocation is removed only when asked
(define-program dead-cons (a)
  ((label e) (assign p (primop cons a a)) (return a)))
(check "dead cons kept by default" (has-primop? (optimize dead-cons) 'cons))
(check "dead cons removed on request" (not (has-primop? (optimize dead-cons #t) 'cons)))

;; the optimized CFG computes what the original did
(define-program arithmetic (c n)
  ((label e) (if c l1 l2)
   (label l1) (assign r 2) (goto j)
   (label l2) (assign r (primop + 1 1)) (goto j)
   (label j) (assign out (primop * r n)) (return out)))

(define (run program args cfg)
  (let ((env (make-hash-table))
        (blocks (list->vector cfg))
        (index (make-hash-table)))
    (for-each (lambda (p a) (hash-table-set! env p a)) (car program) args)
    (for-each-index* (lambda (i b) (when (basic-block-label b)
                                     (hash-table-set! index (basic-block-label b) i)))
                     blocks)
    (define (value x) (if (symbol? x) (hash-table-ref env x) x))
    (let run-block ((i 0) (steps 0))
      (when (> steps 10000) (error "runaway"))
      (let walk ((instrs (basic-block-instructions (vector-ref blocks i))))
        (if (null? instrs)
            (run-block (+ i 1) (+ steps 1))
            (let ((instr (car instrs)))
              (case (car instr)
                ((label) (walk (cdr instrs)))
                ((assign)
                 (let ((rhs (caddr instr)))
                   (hash-table-set!
                    env (cadr instr)
                    (if (pair? rhs)
                        (let ((a (value (caddr rhs))) (b (value (cadddr rhs))))
                          (case (cadr rhs)
                            ((+) (+ a b)) ((-) (- a b)) ((*) (* a b))
                            ((<) (< a b)) ((=) (= a b))))
                        (value rhs))))
                 (walk (cdr instrs)))
                ((if) (run-block (hash-table-ref index
                                                 (if (value (cadr instr))
                                                     (caddr instr)
                                                     (cadddr instr)))
                                 (+ steps 1)))
                ((goto) (run-block (hash-table-ref index (cadr instr)) (+ steps 1)))
                ((return) (value (cadr instr))))))))))

(define (for-each-index* proc vec)
  (do ((i 0 (+ i 1))) ((= i (vector-length vec)))
    (proc i (vector-ref vec i))))

(define (agrees? name program inputs)
  (let ((original (build-cfg (cdr program)))
        (optimized (optimize program)))
    (for-each (lambda (args)
                (check (string-append name " agrees")
                       (equal? (run program args original)
                               (run program args optimized))))
              inputs)))

(agrees? "arithmetic" arithmetic '((#t 5) (#f 5)))
(agrees? "steady-loop" steady-loop '((0) (20)))
(agrees? "counting-loop" counting-loop '((0) (5) (6)))
(agrees? "same-constant" same-constant '((#t) (#f)))

;; Scalar replacement abort path. A phi carrying a record is split into field
;; phis; if an incoming value turns out not to be a pair (it cannot with a sound
;; analysis, so the test corrupts the SSA after analyzing), the blocks must be
;; restored exactly. The CFG: p is built on two entry paths, rebuilt in a loop
;; and read after it, so the phi of p has three arguments.
(define-program record-loop (x n c0)
  ((label e) (if c0 e1 e2)
   (label e1) (assign p (primop cons 1 x)) (assign i 0) (goto h)
   (label e2) (assign p (primop cons 1 x)) (assign i 1) (goto h)
   (label h) (assign c (primop < i n)) (if c body done)
   (label body) (assign a (primop car p)) (assign p (primop cons a x))
   (assign i (primop + i 1)) (goto h)
   (label done) (assign r (primop cdr p)) (return r)))

;; Analyzes record-loop at depth 3, lets corrupt! change the argument vector of
;; the phi of p, runs scalar replacement, and returns (before . after): the phi
;; names and instructions of every block. The pass visits the arguments in
;; order, so with slots 0 and 1 corrupted the third (a cons) still feeds the phi.
(define (sroa-trial corrupt!)
  (set-shape-depth! 3)
  (let* ((ssa (cfg->ssa (car record-loop) (build-cfg (cdr record-loop))))
         (blocks (ssa-proc-blocks ssa))
         (analysis (analyze ssa))
         (header (find (lambda (b) (eq? (ssa-block-label b) 'h)) (vector->list blocks)))
         (phi (find (lambda (phi) (eq? (phi-var phi) 'p)) (ssa-block-phis header))))
    (define (snapshot)
      (map (lambda (b) (cons (map phi-dst (ssa-block-phis b)) (ssa-block-instrs b)))
           (vector->list blocks)))
    (corrupt! (phi-args phi))
    (let ((before (snapshot)))
      (scalar-replace! analysis blocks)
      (cons before (snapshot)))))

(define (mentions-tree? tree pattern)
  (let walk ((x tree))
    (cond ((equal? x pattern) #t)
          ((pair? x) (or (walk (car x)) (walk (cdr x))))
          (else #f))))

;; the first incoming value is an opaque pair: the rewrite succeeds and reads
;; its cdr with an unsafe-cdr at the end of that predecessor (the car is the
;; constant 1), so the abort case below really has something to undo
(let ((trial (sroa-trial (lambda (args) (vector-set! args 0 'x)))))
  (check "opaque incoming pair is split" (not (equal? (car trial) (cdr trial))))
  (check "opaque incoming pair is read by a load"
         (mentions-tree? (map cdr (cdr trial)) '(primop unsafe-cdr x))))

;; ... but when the second incoming value is a literal, after the load was
;; added, the pass gives up and leaves every block as it was
(let ((trial (sroa-trial (lambda (args)
                           (vector-set! args 0 'x)
                           (vector-set! args 1 0)))))
  (check "scalar replacement aborts and restores the blocks"
         (equal? (car trial) (cdr trial))))

;; the control does the cleanup but learns nothing
(define (control program)
  (ssa->cfg (control-ssa (cfg->ssa (car program) (build-cfg (cdr program))))))

(let ((cfg (control same-constant)))
  (check "control keeps the addition" (has-primop? cfg '+))
  (check "control does not fold" (not (assigns-literal? cfg 3))))
(let ((cfg (control dead-arm)))
  (check "control keeps the dead arm" (memq 'l1 (labels cfg))))
(let ((cfg (control refine-pair)))
  (check "control keeps the safe car" (has-primop? cfg 'car)))
(for-each
 (lambda (args)
   (check "control agrees"
          (equal? (run arithmetic args (build-cfg (cdr arithmetic)))
                  (run arithmetic args (control arithmetic)))))
 '((#t 5) (#f 5)))

(if (zero? failures)
    (begin (display "sccp tests passed") (newline))
    (begin (display failures) (display " sccp test(s) failed") (newline) (exit 1)))
