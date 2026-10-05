;;; Random programs over cons/car/cdr/pair?/null?/if/let/letrec for differential
;;; testing of the structural cons analysis (see tools/fuzz-shapes.sh).
;;;
;;;   csi -R r7rs -I . -s tools/fuzz-shapes.scm gen DIR COUNT SEED
;;;       (or guile --r7rs -L . -s ...; HOP_COMPILER names the compiler to load)
;;;       writes DIR/pN.scm (one expression) and DIR/pN.expected (its value,
;;;       computed by the host Scheme, which is the oracle)
;;;   csi -R r7rs -I . -s tools/fuzz-shapes.scm compile DIR
;;;       compiles every DIR/pN.scm to DIR/pN.s with the compiler as configured
;;;       by the HOP_SSA / HOP_SHAPE_K environment variables
;;;
;;; Programs are typed so that they never fail: an expression is an int, a bool,
;;; a pair (always a cons cell) or a list (a pair or '()). Lists are inspected
;;; only behind a pair?/null? test.

(import (scheme base) (scheme write) (scheme file) (scheme eval)
        (scheme process-context) (scheme read) (srfi 1))

;;; Pseudo-random numbers (a small LCG, so runs are reproducible anywhere).

(define state 1)
(define (seed! n) (set! state (+ 1 (modulo n 2147483646))))
(define (next!)
  (set! state (modulo (+ (* state 48271) 11) 2147483647))
  state)
(define (random-below n) (modulo (quotient (next!) 7) n))
(define (pick . choices) (list-ref choices (random-below (length choices))))
(define (chance? percent) (< (random-below 100) percent))

;;; Generators. env is a list of (name . type) bindings in scope.

(define counter 0)
(define (fresh prefix)
  (set! counter (+ counter 1))
  (string->symbol (string-append prefix (number->string counter))))

(define (vars-of env type)
  (map car (filter (lambda (b) (eq? (cdr b) type)) env)))

(define (one-of-vars env type)
  (let ((names (vars-of env type)))
    (and (pair? names) (list-ref names (random-below (length names))))))

;; An int that is usually a variable, so component names get exercised.
(define (gen-atom env)
  (let ((v (one-of-vars env 'int)))
    (if (and v (chance? 90)) v (random-below 10))))

(define (gen-int env depth)
  (let ((v (one-of-vars env 'int)))
    (cond
     ((or (<= depth 0) (chance? 15))
      (gen-atom env))
     (else
      (case (random-below 9)
        ((7 8) (gen-join-select env))
        ((0) `(+ ,(gen-int env (- depth 1)) ,(gen-int env (- depth 1))))
        ((1) `(car ,(gen-pair env (- depth 1))))
        ((2) `(if ,(gen-bool env (- depth 1))
                  ,(gen-int env (- depth 1))
                  ,(gen-int env (- depth 1))))
        ((3) (gen-inspect-list env (- depth 1)))
        ((4) (gen-let env depth 'int))
        ((5) (gen-call env depth 'int))
        (else (if (chance? 50) (gen-record-loop env depth) (gen-loop env depth))))))))

;; Joins two three-element lists built from variables, then reads them.
(define (gen-chain env)
  (let build ((n 3))
    (if (= n 0)
        ''()
        (if (chance? 25)
            `(quote ,(map (lambda (i) (random-below 5)) (iota n)))
            `(cons ,(gen-atom env) ,(build (- n 1)))))))

(define (gen-join-select env)
  (let ((x (fresh "j")))
    `(let ((,x (if ,(gen-bool env 1) ,(gen-chain env) ,(gen-chain env))))
       (+ (car ,x)
          (+ (car (cdr ,x))
             (car (cdr (cdr ,x))))))))

;; Looks inside a list value behind a test, in one of three styles.
(define (gen-inspect-list env depth)
  (let ((x (fresh "l")))
    (let ((env2 (cons (cons x 'list) env)))
      `(let ((,x ,(gen-list env (- depth 1))))
         ,(case (random-below 3)
            ((0) `(if (pair? ,x) (car ,x) ,(gen-int env2 (- depth 1))))
            ((1) `(if (null? ,x) ,(gen-int env2 (- depth 1)) (car ,x)))
            (else `(if (pair? ,x)
                       (if (pair? (cdr ,x)) (car (cdr ,x)) ,(gen-int env2 (- depth 1)))
                       ,(gen-int env2 (- depth 1)))))))))

(define (gen-bool env depth)
  (if (<= depth 0)
      `(= ,(gen-atom env) ,(gen-atom env))
      (case (random-below 4)
        ((0) `(pair? ,(gen-list env (- depth 1))))
        ((1) `(null? ,(gen-list env (- depth 1))))
        (else `(= ,(gen-atom env) ,(gen-atom env))))))

(define (gen-pair env depth)
  (let ((v (one-of-vars env 'pair)))
    (cond
     ((and v (chance? 40)) v)
     ((<= depth 0) `(cons ,(random-below 10) '()))
     (else
      (case (random-below 5)
        ((0 1) `(cons ,(if (chance? 60) (gen-atom env) (gen-int env (- depth 1)))
                      ,(gen-list env (- depth 1))))
        ((2) `(if ,(gen-bool env (- depth 1))
                  ,(gen-pair env (- depth 1))
                  ,(gen-pair env (- depth 1))))
        ((3) (gen-quoted-list-as-pair))
        (else (gen-let env depth 'pair)))))))

(define (gen-quoted-list-as-pair)
  `',(map (lambda (i) (random-below 5)) (iota (+ 1 (random-below 3)))))

(define (gen-list env depth)
  (let ((v (one-of-vars env 'list)))
    (cond
     ((and v (chance? 35)) v)
     ((<= depth 0) ''())
     (else
      (case (random-below 7)
        ((0) ''())
        ((1 2) (gen-pair env (- depth 1)))
        ((3) `(cdr ,(gen-pair env (- depth 1))))
        ((4) `(if ,(gen-bool env (- depth 1))
                  ,(gen-list env (- depth 1))
                  ,(gen-list env (- depth 1))))
        ((5) (gen-let env depth 'list))
        (else (gen-call env depth 'list)))))))

(define (gen-of-type env depth type)
  (case type
    ((int) (gen-int env depth))
    ((pair) (gen-pair env depth))
    (else (gen-list env depth))))

(define (gen-let env depth type)
  (let* ((bound-type (pick 'int 'pair 'list))
         (x (fresh "v"))
         (init (gen-of-type env (- depth 1) bound-type)))
    `(let ((,x ,init))
       ,(gen-of-type (cons (cons x bound-type) env) (- depth 1) type))))

;; A local procedure applied once or twice, so arguments cross a call.
(define (gen-call env depth type)
  (let* ((f (fresh "f"))
         (param-types (list (pick 'int 'list) (pick 'int 'list 'pair)))
         (params (map (lambda (t) (fresh "p")) param-types))
         (body-env (append (map cons params param-types) '()))
         (body (gen-of-type body-env (- depth 1) type))
         (call (lambda ()
                 `(,f ,@(map (lambda (t) (gen-of-type env (- depth 2) t))
                             param-types)))))
    `(let ((,f (lambda ,params ,body)))
       ,(if (chance? 50) (call) (gen-combine type (call) (call))))))

(define (gen-combine type a b)
  (case type
    ((int) `(+ ,a ,b))
    (else `(if ,(pick #t #f) ,a ,b))))

;; A counted loop that rebuilds a list each time round and reads it at the end.
(define (gen-loop env depth)
  (let* ((go (fresh "go")) (n (fresh "n")) (l (fresh "acc"))
         (env2 (list (cons n 'int) (cons l 'list))))
    `(letrec ((,go (lambda (,n ,l)
                     (if (= ,n 0)
                         ,(gen-inspect-list (list (cons l 'list)) (- depth 1))
                         (,go (- ,n 1)
                              ,(case (random-below 3)
                                 ((0) `(cons ,n ,l))
                                 ((1) `(cons 1 (if (pair? ,l) (cdr ,l) ,l)))
                                 (else (gen-list env2 (- depth 1)))))))))
       (,go ,(random-below 4) ,(gen-list env (- depth 1))))))

;; A counted loop carrying a three-field record that is rebuilt (or passed on, or
;; rebuilt sharing its tail) each time round; the end uses it as fields or as a
;; whole.
(define (gen-record-loop env depth)
  (let* ((go (fresh "go")) (n (fresh "n")) (r (fresh "rec"))
         (a `(car ,r)) (b `(car (cdr ,r))) (c `(car (cdr (cdr ,r)))))
    (define (field) (pick `(+ ,a ,n) `(- ,b 1) `(+ ,b ,c) c n 7 a))
    (define (record) `(cons ,(field) (cons ,(field) (cons ,(field) '()))))
    (define (step)
      (case (random-below 4)
        ((0) (record))
        ((1) `(if (< ,n 2) ,r ,(record)))
        ((2) `(cons ,(field) (cdr ,r)))
        (else `(if (< ,n 3) (cons ,(field) (cdr ,r)) ,(record)))))
    (define (finish)
      (case (random-below 4)
        ((0) `(+ ,a (+ ,b ,c)))
        ((1) `(let ((x ,r)) (if (eq? x x) (+ (car x) 1000) 0)))
        ((2) `(let ((both (cons ,r ,r))) (if (eq? (car both) (cdr both)) ,c 0)))
        (else `(+ ,a (car (cdr (cdr ,r)))))))
    `(letrec ((,go (lambda (,n ,r)
                     (if (= ,n 0)
                         ,(finish)
                         (,go (- ,n 1) ,(step))))))
       (,go ,(random-below 5)
            (cons ,(gen-atom env) (cons ,(gen-atom env) (cons ,(gen-atom env) '())))))))

;;; Output

(define (write-file path datum)
  (call-with-output-file path
    (lambda (port) (write datum port) (newline port))))

(define (args4) (map (lambda (i) (random-below 6)) (iota 4)))

(define host-env (environment '(scheme base)))

(define (generate dir count seed)
  (seed! seed)
  (do ((i 0 (+ i 1)))
      ((= i count))
    (let* ((program `(let ((top (lambda (a b c d)
                                     ,(gen-int '((a . int) (b . int) (c . int) (d . int))
                                               (+ 3 (random-below 3))))))
                       (+ (top ,@(args4))
                          (+ (top ,@(args4))
                             (top ,@(args4))))))
           (value (eval program host-env))
           (stem (string-append dir "/p" (number->string i))))
      (write-file (string-append stem ".scm") program)
      (call-with-output-file (string-append stem ".expected")
        (lambda (port) (write value port) (newline port))))))

(define (compile-all dir)
  (load (or (get-environment-variable "HOP_COMPILER") "compiler.scm"))
  (let loop ((i 0))
    (let ((source (string-append dir "/p" (number->string i) ".scm")))
      (when (file-exists? source)
        (write-aarch64-program-file source (string-append dir "/p" (number->string i) ".s"))
        (loop (+ i 1))))))

(let ((args (command-line)))
  (cond
   ((and (= (length args) 5) (equal? (cadr args) "gen"))
    (generate (caddr args) (string->number (cadddr args))
              (string->number (list-ref args 4))))
   ((and (= (length args) 3) (equal? (cadr args) "compile"))
    (compile-all (caddr args)))
   (else
    (display "usage: fuzz-shapes.scm gen DIR COUNT SEED | compile DIR\n")
    (exit 2))))
