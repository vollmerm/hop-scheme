(define-library (hop pass cfa)
  ;;; Pass 3.5: CFA Normalization
  ;;; Pass 3.6: 0CFA Analysis and Known-Call Rewriting
  (export normalize-for-cfa
          run-0cfa
          rewrite-known-calls)
  (import (scheme base)
          (scheme cxr)
          (srfi 69)
          (hop utils))
  (begin

(define (cfa-simple-expr? expr)
  (or (symbol? expr)
      (literal-expr? expr)
      (and (pair? expr) (memq (car expr) '(local closure global)))))

(define (wrap-let-bindings bindings body)
  (let loop ((rest (reverse bindings)) (result body))
    (if (null? rest)
        result
        `(let (,(car rest)) ,(loop (cdr rest) result)))))

(define (normalize-for-cfa expr)
  (define temp-counter 0)
  (define proc-counter 0)

  (define (fresh-cfa-temp)
    (set! temp-counter (+ temp-counter 1))
    (string->symbol (string-append "cfa.tmp." (number->string temp-counter))))

  (define (fresh-cfa-proc)
    (set! proc-counter (+ proc-counter 1))
    (string->symbol (string-append "cfa.proc." (number->string proc-counter))))

  (define (normalize-simple expr)
    (let ((normalized (normalize expr)))
      (if (cfa-simple-expr? normalized)
          (values '() normalized)
          (let ((tmp (fresh-cfa-temp)))
            (values (list (list tmp normalized)) tmp)))))

  (define (normalize-simple-list exprs)
    (let loop ((rest exprs) (bindings '()) (result '()))
      (if (null? rest)
          (values bindings (reverse result))
          (let-values (((new-bindings simple-expr)
                        (normalize-simple (car rest))))
            (loop (cdr rest)
                  (append bindings new-bindings)
                  (cons simple-expr result))))))

  (define (normalize-sequence exprs)
    (map normalize exprs))

  (define (normalize expr)
    (cond
     ((or (symbol? expr) (literal-expr? expr)) expr)
     ((pair? expr)
      (case (car expr)
        ((begin)
         `(begin ,@(normalize-sequence (cdr expr))))
        ((primop)
         `(primop ,(cadr expr)
                  ,@(normalize-sequence (cddr expr))))
        ((if)
         `(if ,(normalize (cadr expr))
              ,(normalize (caddr expr))
              ,(normalize (cadddr expr))))
        ((let)
         (let* ((bindings (map (lambda (binding)
                                 (list (car binding)
                                       (normalize (cadr binding))))
                               (cadr expr)))
                (body-exprs (normalize-sequence (cddr expr))))
           `(let ,bindings ,@body-exprs)))
        ((lambda)
         `(lambda ,(cadr expr) ,@(normalize-sequence (cddr expr))))
        ((make-closure)
         (let* ((lambda-expr (cadr expr))
                (captures (cddr expr)))
           (let-values (((capture-bindings simple-captures)
                         (normalize-simple-list captures)))
             (let ((proc-name (fresh-cfa-proc)))
               (wrap-let-bindings
                capture-bindings
                `(make-closure ,proc-name
                               ,(normalize lambda-expr)
                               ,@simple-captures))))))
        ((closure-call)
         (let-values (((op-bindings simple-op)
                       (normalize-simple (cadr expr)))
                      ((arg-bindings simple-args)
                       (normalize-simple-list (cddr expr))))
           (wrap-let-bindings
            (append op-bindings arg-bindings)
            `(closure-call ,simple-op ,@simple-args))))
        ((closure-apply)
         (let-values (((op-bindings simple-op)
                       (normalize-simple (cadr expr)))
                      ((arg-bindings simple-args)
                       (normalize-simple-list (cddr expr))))
           (wrap-let-bindings
            (append op-bindings arg-bindings)
            `(closure-apply ,simple-op ,@simple-args))))
        ((closure-callcc)
         (let-values (((op-bindings simple-op)
                       (normalize-simple (cadr expr))))
           (wrap-let-bindings op-bindings `(closure-callcc ,simple-op))))
        ((self-tail-call)
         (let-values (((arg-bindings simple-args)
                       (normalize-simple-list (cdr expr))))
           (wrap-let-bindings arg-bindings `(self-tail-call ,@simple-args))))
        ((group-tail-call)
         (let-values (((arg-bindings simple-args)
                       (normalize-simple-list (cddr expr))))
           (wrap-let-bindings
            arg-bindings
            `(group-tail-call ,(cadr expr) ,@simple-args))))
        ((group-closures)
         `(group-closures
           ,(map (lambda (member)
                   (list (car member)
                         (cadr member)
                         (caddr member)
                         (normalize (cadddr member))))
                 (cadr expr))
           ,(map (lambda (capture-spec)
                   (list (car capture-spec)
                         (normalize (cadr capture-spec))))
                 (caddr expr))))
        ((cons)
         (error "cons in normalize-for-cfa: should have been canonicalized" expr))
        ((make-vector)
         (error "make-vector in normalize-for-cfa: should have been canonicalized" expr))
        ((vector-length)
         (error "vector-length in normalize-for-cfa: should have been canonicalized" expr))
        ((vector-ref)
         (error "vector-ref in normalize-for-cfa: should have been canonicalized" expr))
        ((vector-set!)
         (error "vector-set! in normalize-for-cfa: should have been canonicalized" expr))
        ((set-box!)
         `(set-box! ,(normalize (cadr expr)) ,(normalize (caddr expr))))
        ((box unbox)
         `(,(car expr) ,(normalize (cadr expr))))
        ((set-global!)
         `(set-global! ,(cadr expr) ,(normalize (caddr expr))))
        ((local closure global)
         expr)
        (else
         (error "Unknown expression in CFA normalization" (car expr)))))
     (else
      (error "Invalid expression in CFA normalization" expr))))

  (normalize expr))

;;; ── 0CFA ─────────────────────────────────────────────────────────────────
;;;
;;; Flow sets over-approximate which closures and boxes an expression may
;;; evaluate to. Their elements are:
;;;
;;;   - a procedure name (cfa.proc.N): a closure made by that make-closure;
;;;   - a box site (%box.N): a box made by that (box ...) expression;
;;;   - unknown-value: any value the analysis cannot see into -- one read
;;;     out of a pair or vector, returned by code in another unit, handed
;;;     to a procedure by the runtime (apply, call/cc), and so on.
;;;
;;; Non-closure, non-box values are not tracked at all, so an empty set means
;;; "definitely not a closure or box" -- which is why every source of values
;;; the analysis can't follow must contribute unknown-value rather than
;;; nothing. A set containing unknown-value can never resolve to a single
;;; known procedure in rewrite-known-calls.
;;;
;;; The converse direction matters just as much: a closure that *escapes*
;;; into code the analysis can't see (stored in a pair or vector, passed to
;;; an unknown callee or through apply, stored in an exported global) can be
;;; called from there with arbitrary arguments, so escape! gives each of its
;;; parameters unknown-value -- and whatever it returns escapes too. An
;;; escaped box can likewise be filled with anything, and its contents
;;; escape.

(define unknown-value '%unknown)

;; exported-globals: the global labels another compilation unit can read (a
;; library's exports); whatever is stored in one escapes. '() for a
;; standalone program.
(define (run-0cfa expr . maybe-exported-globals)
  (define exported-globals
    (if (pair? maybe-exported-globals) (car maybe-exported-globals) '()))
  (define procedures (make-hash-table))
  (define var-flow (make-hash-table))
  (define box-contents (make-hash-table))
  (define global-flow (make-hash-table))
  (define proc-results (make-hash-table))
  (define defined-globals (make-hash-table))
  (define escaped (make-hash-table))
  ;; (box ...) expression (compared with eq?) -> its site name. The same
  ;; expression objects are re-analyzed on every iteration, so each keeps
  ;; one stable site.
  (define box-sites (make-hash-table eq?))
  (define box-site-count 0)
  (define changed #f)

  (define (flow-ref table key)
    (let ((value (hash-table-ref/default table key #f)))
      (if value value '())))

  (define (add-flow! table key values)
    (if (or (not key) (null? values))
        #f
        (let* ((current (flow-ref table key))
               (updated (dedupe-symbols (append current values))))
          (if (set-equal? current updated)
              #f
              (begin
                (hash-table-set! table key updated)
                (set! changed #t)
                #t)))))

  (define (box-site-for expr)
    (or (hash-table-ref/default box-sites expr #f)
        (begin
          (set! box-site-count (+ box-site-count 1))
          (let ((site (string->symbol
                       (string-append "%box." (number->string box-site-count)))))
            (hash-table-set! box-sites expr site)
            (hash-table-set! box-contents site '())
            site))))

  (define (box-site? value)
    (hash-table-exists? box-contents value))

  (define (take-n lst n)
    (if (= n 0) '() (cons (car lst) (take-n (cdr lst) (- n 1)))))

  (define (procedure-meta value)
    (hash-table-ref/default procedures value #f))

  ;; A procedure's own (non-capture) fixed parameters. A variadic
  ;; procedure's rest parameter is not included: it only ever holds a
  ;; freshly consed list, never a closure or box.
  (define (actual-params meta)
    (list-tail (params-fixed (cadr meta)) (car meta)))

  (define (escape! values)
    (for-each
     (lambda (value)
       (if (not (hash-table-ref/default escaped value #f))
           (cond
            ((procedure-meta value)
             => (lambda (meta)
                  (hash-table-set! escaped value #t)
                  (set! changed #t)
                  (for-each (lambda (param)
                              (add-flow! var-flow param (list unknown-value)))
                            (actual-params meta))))
            ((box-site? value)
             (hash-table-set! escaped value #t)
             (set! changed #t)
             (add-flow! box-contents value (list unknown-value))))))
     values))

  ;; Flows arg-sets into every possible target's parameters and returns the
  ;; union of what those targets may return. A target that isn't a known
  ;; procedure (unknown-value, a continuation, a letrec group member) can do
  ;; anything with its arguments, so they escape.
  (define (flow-into-call! target-set arg-sets)
    (let loop ((rest target-set) (result '()))
      (if (null? rest)
          result
          (let ((meta (procedure-meta (car rest))))
            (if meta
                (begin
                  (let zip ((params (actual-params meta)) (args arg-sets))
                    (cond
                     ((null? args) 'done)
                     ;; Extra arguments land in a variadic procedure's rest
                     ;; list -- a pair the analysis doesn't look into.
                     ((null? params) (for-each escape! args))
                     (else
                      (add-flow! var-flow (car params) (car args))
                      (zip (cdr params) (cdr args)))))
                  (loop (cdr rest)
                        (set-union result (flow-ref proc-results (car rest)))))
                (begin
                  (for-each escape! arg-sets)
                  (loop (cdr rest) (set-union result (list unknown-value)))))))))

  ;; Primops that can neither store their arguments anywhere nor produce a
  ;; closure or box.
  (define closure-free-primops
    '(pair? null? symbol? vector? eq? vector-length
      + - * = < > safe-+ safe-- safe-* safe-= safe-< safe->))

  (define (collect-procedures expr)
    (cond
     ((or (symbol? expr) (literal-expr? expr)) 'done)
     ((pair? expr)
      (case (car expr)
        ((begin)
         (for-each collect-procedures (cdr expr)))
        ((primop cons set-box!)
         (for-each collect-procedures (cdr expr)))
        ((if)
         (collect-procedures (cadr expr))
         (collect-procedures (caddr expr))
         (collect-procedures (cadddr expr)))
        ((let)
         (collect-procedures (cadr (caadr expr)))
         (for-each collect-procedures (cddr expr)))
        ((lambda)
         (for-each collect-procedures (cddr expr)))
        ((make-closure)
         (let ((proc-name (cadr expr))
               (lambda-expr (caddr expr))
               (captures (cdddr expr)))
           (hash-table-set! procedures
                            proc-name
                            (list (length captures)
                                  (cadr lambda-expr)
                                  (body->expr (cddr lambda-expr))))
           (collect-procedures (body->expr (cddr lambda-expr)))
           (for-each collect-procedures captures)))
        ((closure-call known-call self-tail-call closure-apply closure-callcc)
         (for-each collect-procedures (cdr expr)))
        ((group-tail-call)
         (for-each collect-procedures (cddr expr)))
        ((group-closures)
         (for-each (lambda (member)
                     (collect-procedures (cadddr member)))
                   (cadr expr))
         (for-each (lambda (capture-spec)
                     (collect-procedures (cadr capture-spec)))
                   (caddr expr)))
        ((box unbox)
         (collect-procedures (cadr expr)))
        ((set-global!)
         ;; A global this unit never stores to is defined by another unit,
         ;; so reading it yields unknown-value (see analyze-expr's global).
         (hash-table-set! defined-globals (cadr expr) #t)
         (collect-procedures (caddr expr)))
        ((local closure global) 'done)
        (else
         (error "Unknown expression while collecting CFA procedures" (car expr)))))
     (else
      (error "Invalid expression while collecting CFA procedures" expr))))

  (define (analyze-expr expr current-proc)
    (define (analyze e) (analyze-expr e current-proc))
    (cond
     ((literal-expr? expr) '())
     ((symbol? expr) (flow-ref var-flow expr))
     ((pair? expr)
      (case (car expr)
        ((local closure)
         (flow-ref var-flow (cadr expr)))
        ((global)
         (let ((label (cadr expr)))
           (if (not (hash-table-ref/default defined-globals label #f))
               (add-flow! global-flow label (list unknown-value)))
           (flow-ref global-flow label)))
        ((begin)
         (let loop ((rest (cdr expr)) (last '()))
           (if (null? rest)
               last
               (loop (cdr rest) (analyze (car rest))))))
        ((primop)
         (let ((op (cadr expr))
               (arg-sets (map analyze (cddr expr))))
           (cond
            ((memq op closure-free-primops) '())
            ((memq op '(car cdr unsafe-car unsafe-cdr vector-ref))
             (list unknown-value))
            ((memq op '(cons make-vector vector-set!))
             (for-each escape! arg-sets)
             '())
            (else
             (for-each escape! arg-sets)
             (list unknown-value)))))
        ((if)
         (analyze (cadr expr))
         (set-union (analyze (caddr expr))
                    (analyze (cadddr expr))))
        ((let)
         (for-each (lambda (binding)
                     (add-flow! var-flow (car binding) (analyze (cadr binding))))
                   (cadr expr))
         (analyze (body->expr (cddr expr))))
        ((make-closure)
         (let* ((proc-name (cadr expr))
                (meta (procedure-meta proc-name))
                (env-params (take-n (params-fixed (cadr meta)) (car meta))))
           (for-each (lambda (env-param capture)
                       (add-flow! var-flow env-param (analyze capture)))
                     env-params
                     (cdddr expr))
           (list proc-name)))
        ((closure-call)
         (let* ((target-set (analyze (cadr expr)))
                (arg-sets (map analyze (cddr expr))))
           (flow-into-call! target-set arg-sets)))
        ((closure-apply)
         ;; The spread argument count is only known at run time, so the
         ;; arguments can't be matched up with parameters: every argument
         ;; escapes, and every parameter of every possible target gets
         ;; unknown-value.
         (let* ((target-set (analyze (cadr expr)))
                (arg-sets (map analyze (cddr expr))))
           (for-each escape! arg-sets)
           (let loop ((rest target-set) (result '()))
             (if (null? rest)
                 result
                 (let ((meta (procedure-meta (car rest))))
                   (if meta
                       (begin
                         (for-each (lambda (param)
                                     (add-flow! var-flow param (list unknown-value)))
                                   (actual-params meta))
                         (loop (cdr rest)
                               (set-union result (flow-ref proc-results (car rest)))))
                       (loop (cdr rest) (set-union result (list unknown-value)))))))))
        ((closure-callcc)
         ;; The receiver is called with a continuation (a runtime closure:
         ;; unknown-value) and call/cc yields either what the receiver
         ;; returns or whatever any continuation is later called with --
         ;; which, being a call to unknown-value, has already escaped.
         (let ((target-set (analyze (cadr expr))))
           (set-union (flow-into-call! target-set (list (list unknown-value)))
                      (list unknown-value))))
        ((self-tail-call)
         (let ((meta (and current-proc (procedure-meta current-proc))))
           (if meta
               (flow-into-call! (list current-proc)
                                (map analyze (list-tail (cdr expr) (car meta))))
               (begin
                 (for-each (lambda (arg) (escape! (analyze arg))) (cdr expr))
                 (list unknown-value)))))
        ((group-tail-call)
         ;; letrec group members aren't tracked procedures (see
         ;; group-closures): calling one is like calling unknown-value.
         (for-each (lambda (arg) (escape! (analyze arg))) (cddr expr))
         (list unknown-value))
        ((group-closures)
         ;; (group-closures ((box-var member-name params body capture-names) ...)
         ;;                 ((capture-param value) ...))
         ;; Members become closures in a shared cluster procedure rather than
         ;; entries in the procedures table, so they're modeled as
         ;; unknown-value: their parameters can receive anything, whatever
         ;; they return escapes, and the boxes they're stored into hold
         ;; unknown-value. Their bodies are still analyzed, so flows inside
         ;; them (closures they make, calls they perform) are not lost.
         (for-each (lambda (capture-spec)
                     (add-flow! var-flow (car capture-spec) (analyze (cadr capture-spec))))
                   (caddr expr))
         (for-each
          (lambda (member)
            (let ((box-var (car member))
                  (params (caddr member))
                  (body (cadddr member)))
              (for-each (lambda (param)
                          (add-flow! var-flow param (list unknown-value)))
                        (params-names params))
              (escape! (analyze-expr body #f))
              (for-each (lambda (value)
                          (if (box-site? value)
                              (add-flow! box-contents value (list unknown-value))))
                        (flow-ref var-flow box-var))))
          (cadr expr))
         '())
        ((box)
         (let ((site (box-site-for expr)))
           (add-flow! box-contents site (analyze (cadr expr)))
           (list site)))
        ((unbox)
         (let loop ((rest (analyze (cadr expr))) (result '()))
           (cond
            ((null? rest) result)
            ((box-site? (car rest))
             (loop (cdr rest) (set-union result (flow-ref box-contents (car rest)))))
            ((eq? (car rest) unknown-value)
             (loop (cdr rest) (set-union result (list unknown-value))))
            (else (loop (cdr rest) result)))))
        ((set-box!)
         (let ((box-set (analyze (cadr expr)))
               (value-set (analyze (caddr expr))))
           (for-each (lambda (value)
                       (cond
                        ((box-site? value) (add-flow! box-contents value value-set))
                        ((eq? value unknown-value) (escape! value-set))))
                     box-set)
           value-set))
        ((set-global!)
         (let ((value-set (analyze (caddr expr))))
           (add-flow! global-flow (cadr expr) value-set)
           (if (memq (cadr expr) exported-globals)
               (escape! value-set))
           value-set))
        (else
         (error "Unknown expression in 0CFA" (car expr)))))
     (else
      (error "Invalid expression in 0CFA" expr))))

  (collect-procedures expr)

  (let loop ()
    (set! changed #f)
    (analyze-expr expr #f)
    (for-each
     (lambda (proc-name)
       (let ((body (caddr (procedure-meta proc-name))))
         (add-flow! proc-results proc-name (analyze-expr body proc-name))))
     (hash-table-keys procedures))
    ;; Whatever an escaped procedure returns, or an escaped box holds, has
    ;; escaped too -- including anything added since it first escaped.
    (for-each
     (lambda (value)
       (escape! (if (procedure-meta value)
                    (flow-ref proc-results value)
                    (flow-ref box-contents value))))
     (hash-table-keys escaped))
    (if changed
        (loop)
        (list procedures var-flow box-contents global-flow proc-results))))

(define (rewrite-known-calls expr analysis)
  (let ((procedures (car analysis))
        (var-flow (cadr analysis))
        (box-contents (caddr analysis))
        (global-flow (cadddr analysis)))
    (define (flow-ref table key)
      (let ((value (hash-table-ref/default table key #f)))
        (if value value '())))

    ;; Mirrors run-0cfa's analyze-expr for the forms a call's operator can
    ;; take. (After normalize-for-cfa it is always a simple expression, so
    ;; the compound cases are only a fallback; anything unrecognized is
    ;; unknown-value, never "no closure".)
    (define (closure-set expr)
      (cond
       ((symbol? expr) (flow-ref var-flow expr))
       ((literal-expr? expr) '())
       ((pair? expr)
        (case (car expr)
          ((local closure)
           (flow-ref var-flow (cadr expr)))
          ((global)
           (flow-ref global-flow (cadr expr)))
          ((unbox)
           (let loop ((rest (closure-set (cadr expr))) (result '()))
             (cond
              ((null? rest) result)
              ((hash-table-exists? box-contents (car rest))
               (loop (cdr rest) (set-union result (flow-ref box-contents (car rest)))))
              ((eq? (car rest) unknown-value)
               (loop (cdr rest) (set-union result (list unknown-value))))
              (else (loop (cdr rest) result)))))
          ((make-closure)
           (list (cadr expr)))
          ((let)
           (closure-set (body->expr (cddr expr))))
          ((begin)
           (if (null? (cdr expr))
               '()
               (closure-set (car (reverse (cdr expr))))))
          ((if)
           (set-union (closure-set (caddr expr))
                      (closure-set (cadddr expr))))
          (else (list unknown-value))))
       (else (list unknown-value))))

    (define (rewrite expr)
      (cond
       ((or (symbol? expr) (literal-expr? expr)) expr)
       ((pair? expr)
        (case (car expr)
          ((begin)
           `(begin ,@(map rewrite (cdr expr))))
          ((primop)
           `(primop ,(cadr expr) ,@(map rewrite (cddr expr))))
          ((if)
           `(if ,(rewrite (cadr expr))
                ,(rewrite (caddr expr))
                ,(rewrite (cadddr expr))))
          ((let)
           `(let ,(map (lambda (binding)
                         (list (car binding)
                               (rewrite (cadr binding))))
                       (cadr expr))
              ,@(map rewrite (cddr expr))))
          ((lambda)
           `(lambda ,(cadr expr) ,@(map rewrite (cddr expr))))
          ((make-closure)
           `(make-closure ,(cadr expr)
                          ,(rewrite (caddr expr))
                          ,@(map rewrite (cdddr expr))))
          ((closure-call)
           (let* ((rator (rewrite (cadr expr)))
                  (args (map rewrite (cddr expr)))
                  (targets (closure-set rator)))
             (if (and (= (length targets) 1)
                      (hash-table-ref/default procedures (car targets) #f))
                 (let* ((proc-name (car targets))
                        (meta (hash-table-ref/default procedures proc-name #f))
                        (capture-count (car meta))
                        (params (cadr meta))
                        ;; #f for an ordinary target; the fixed-arg count k
                        ;; for a variadic one. 0CFA has already proven the
                        ;; call target, so N < k here is a provable-wrong
                        ;; program, not merely a possibly-wrong one -- raise
                        ;; it as a compile error rather than degrading to a
                        ;; generic call that could only fail later, at
                        ;; runtime, with a less specific message.
                        (rest-k (and (params-variadic? params)
                                     (- (length (params-fixed params)) capture-count)))
                        ;; The exact expected fixed-arg count regardless of
                        ;; variadic-ness -- used below to catch a
                        ;; non-variadic target called with the wrong number
                        ;; of arguments. 0CFA has already proven the call
                        ;; target here, so a mismatch (too many *or* too
                        ;; few) is provably wrong, exactly like the
                        ;; too-few-for-variadic case just above -- raise it
                        ;; as a compile error instead of emitting a
                        ;; known-call whose direct-call argument count would
                        ;; silently disagree with the target procedure's
                        ;; actual parameter list.
                        (expected-count (- (length (params-fixed params)) capture-count)))
                   (cond
                    ((and rest-k (< (length args) rest-k))
                     (error "Too few arguments to variadic procedure" proc-name expr))
                    ((and (not rest-k) (not (= (length args) expected-count)))
                     (error "Wrong number of arguments to procedure" proc-name expr))
                    (else
                     `(known-call ,proc-name ,capture-count ,rest-k ,rator ,@args))))
                 `(closure-call ,rator ,@args))))
          ((known-call)
           `(known-call ,(cadr expr)
                        ,(caddr expr)
                        ,(cadddr expr)
                        ,(rewrite (car (cddddr expr)))
                        ,@(map rewrite (cdr (cddddr expr)))))
          ((closure-apply)
           `(closure-apply ,(rewrite (cadr expr)) ,@(map rewrite (cddr expr))))
          ((closure-callcc)
           `(closure-callcc ,(rewrite (cadr expr))))
          ((self-tail-call)
           `(self-tail-call ,@(map rewrite (cdr expr))))
          ((group-tail-call)
           `(group-tail-call ,(cadr expr) ,@(map rewrite (cddr expr))))
          ((group-closures)
           `(group-closures
             ,(map (lambda (member)
                     (list (car member)
                           (cadr member)
                           (caddr member)
                           (rewrite (cadddr member))))
                   (cadr expr))
             ,(map (lambda (capture-spec)
                     (list (car capture-spec)
                           (rewrite (cadr capture-spec))))
                   (caddr expr))))
          ((cons set-box! make-vector vector-ref vector-set!)
           `(,(car expr) ,(rewrite (cadr expr)) ,(rewrite (caddr expr))))
          ((set-global!)
           `(set-global! ,(cadr expr) ,(rewrite (caddr expr))))
          ((box unbox car cdr pair? null? vector-length vector? local closure global)
           `(,(car expr) ,(rewrite (cadr expr))))
          (else
           (error "Unknown expression in known-call rewrite" (car expr)))))
       (else
        (error "Invalid expression in known-call rewrite" expr))))

    (rewrite expr)))

)) ; end define-library
