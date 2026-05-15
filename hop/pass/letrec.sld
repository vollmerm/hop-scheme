(define-library (hop pass letrec)
  ;;; Pass 1.75: Letrec Simplification
  ;;; Pass 2: Letrec Desugaring
  (export simplify-letrec
          desugar-letrec)
  (import (scheme base)
          (scheme cxr)
          (hop utils))
  (begin

(define (simplify-letrec expr)
  (define used-names
    (dedupe-symbols
     (let collect ((expr expr))
       (cond
        ((symbol? expr) (list expr))
        ((pair? expr) (append-map collect expr))
        (else '())))))

  (define fresh-counter 0)
  (define (fresh-internal-name prefix)
    (let loop ()
      (set! fresh-counter (+ fresh-counter 1))
      (let ((name (string->symbol
                   (string-append prefix (number->string fresh-counter)))))
        (if (memq name used-names)
            (loop)
            (begin
              (set! used-names (cons name used-names))
              name)))))

  (define (letrec-init-safe? expr group-names)
    (cond
     ((symbol? expr)
      (not (memq expr group-names)))
     ((literal-expr? expr) #t)
     ((pair? expr)
      (case (car expr)
        ((begin)
         (all (lambda (e) (letrec-init-safe? e group-names)) (cdr expr)))
        ((primop app)
         (all (lambda (e) (letrec-init-safe? e group-names)) (cdr expr)))
        ((if)
         (and (letrec-init-safe? (cadr expr) group-names)
              (letrec-init-safe? (caddr expr) group-names)
              (letrec-init-safe? (cadddr expr) group-names)))
        ((let)
         (and (letrec-init-safe? (cadr (caadr expr)) group-names)
              (all (lambda (e) (letrec-init-safe? e group-names)) (cddr expr))))
        ((letrec)
         (and (all (lambda (binding)
                     (letrec-init-safe? (cadr binding) group-names))
                   (cadr expr))
              (all (lambda (e) (letrec-init-safe? e group-names)) (cddr expr))))
        ((lambda)
         #t)
        ((cons make-vector vector-ref)
         (and (letrec-init-safe? (cadr expr) group-names)
              (letrec-init-safe? (caddr expr) group-names)))
        ((+ - * = < >)
         (and (letrec-init-safe? (cadr expr) group-names)
              (letrec-init-safe? (caddr expr) group-names)))
        ((box unbox car cdr pair? null? vector-length vector?)
         (letrec-init-safe? (cadr expr) group-names))
        ((set-box!)
         (and (letrec-init-safe? (cadr expr) group-names)
              (letrec-init-safe? (caddr expr) group-names)))
        ((vector-set!)
         (and (letrec-init-safe? (cadr expr) group-names)
              (letrec-init-safe? (caddr expr) group-names)
              (letrec-init-safe? (cadddr expr) group-names)))
        ((global)
         #t)
        ((set-global!)
         (letrec-init-safe? (caddr expr) group-names))
        (else
         (error "Unknown expression in letrec init safety check" (car expr)))))
     (else
      (error "Invalid expression in letrec init safety check" expr))))

  (define (partition-letrec-bindings bindings)
    (let loop ((rest bindings) (lambda-bindings '()) (value-bindings '()))
      (if (null? rest)
          (values (reverse lambda-bindings) (reverse value-bindings))
          (let ((binding (car rest)))
            (if (lambda-expr? (cadr binding))
                (loop (cdr rest) (cons binding lambda-bindings) value-bindings)
                (loop (cdr rest) lambda-bindings (cons binding value-bindings)))))))

  (define (lookup-cell name cell-env)
    (let ((binding (assoc name cell-env)))
      (if binding
          (cadr binding)
          (error "Missing letrec cell for binding" name))))

  (define (simplify-letrec-group bindings body-exprs env)
    (let-values (((lambda-bindings value-bindings)
                  (partition-letrec-bindings bindings)))
      (let ((group-names (map car bindings)))
        (for-each
         (lambda (binding)
           (if (not (letrec-init-safe? (cadr binding) group-names))
               (error "letrec init cannot read recursive bindings during initialization"
                      (car binding)
                      (cadr binding))))
         value-bindings)
        (let* ((cell-env
                (map (lambda (binding)
                       (list (car binding) (fresh-internal-name "letrec.cell.")))
                     value-bindings))
               (extended-env (append cell-env env))
               (simplified-lambda-bindings
                (map (lambda (binding)
                       (list (car binding)
                             (rewrite (cadr binding) extended-env)))
                     lambda-bindings))
               (init-exprs
                (map (lambda (binding)
                       `(set-box! ,(lookup-cell (car binding) cell-env)
                                  ,(rewrite (cadr binding) extended-env)))
                     value-bindings))
               (simplified-body
                (map (lambda (body-expr)
                       (rewrite body-expr extended-env))
                     body-exprs))
               (core-expr
                (if (null? simplified-lambda-bindings)
                    (body->expr (append init-exprs simplified-body))
                    `(letrec ,simplified-lambda-bindings
                       ,@init-exprs
                       ,@simplified-body)))
               (box-bindings
                (map (lambda (binding)
                       (list (cadr binding) '(box #f)))
                     cell-env)))
          (if (null? box-bindings)
              core-expr
              (nest-let-bindings box-bindings (list core-expr)))))))

  (define (rewrite expr env)
    (cond
     ((symbol? expr)
      (let ((binding (assoc expr env)))
        (if binding
            `(unbox ,(cadr binding))
            expr)))
     ((literal-expr? expr) expr)
     ((pair? expr)
      (case (car expr)
        ((begin)
         `(begin ,@(map (lambda (e) (rewrite e env)) (cdr expr))))
        ((primop)
         `(primop ,(cadr expr)
                  ,@(map (lambda (e) (rewrite e env)) (cddr expr))))
        ((if)
         `(if ,(rewrite (cadr expr) env)
              ,(rewrite (caddr expr) env)
              ,(rewrite (cadddr expr) env)))
        ((let)
         (let* ((bindings (map (lambda (binding)
                                 (list (car binding)
                                       (rewrite (cadr binding) env)))
                               (cadr expr)))
                (body-exprs (map (lambda (body-expr)
                                   (rewrite body-expr env))
                                 (cddr expr))))
           `(let ,bindings ,@body-exprs)))
        ((lambda)
         `(lambda ,(cadr expr)
            ,@(map (lambda (body-expr) (rewrite body-expr env)) (cddr expr))))
        ((letrec)
         (simplify-letrec-group (cadr expr) (cddr expr) env))
        ((app)
         `(app ,(rewrite (cadr expr) env)
               ,@(map (lambda (e) (rewrite e env)) (cddr expr))))
        ((cons make-vector vector-ref)
         `(,(car expr) ,(rewrite (cadr expr) env)
           ,(rewrite (caddr expr) env)))
        ((+ - * = < >)
         `(,(car expr) ,(rewrite (cadr expr) env)
           ,(rewrite (caddr expr) env)))
        ((box unbox car cdr pair? null? vector-length vector?)
         `(,(car expr) ,(rewrite (cadr expr) env)))
        ((set-box!)
         `(set-box! ,(rewrite (cadr expr) env)
                    ,(rewrite (caddr expr) env)))
        ((vector-set!)
         `(vector-set! ,(rewrite (cadr expr) env)
                       ,(rewrite (caddr expr) env)
                       ,(rewrite (cadddr expr) env)))
        ((global)
         expr)
        ((set-global!)
         `(set-global! ,(cadr expr)
                       ,(rewrite (caddr expr) env)))
        (else
         (error "Unknown expression in letrec simplification" (car expr)))))
     (else
      (error "Invalid expression in letrec simplification" expr))))

  (rewrite expr '()))

;;; ── Pass 2: Letrec Desugaring ─────────────────────────────────────────────

(define (desugar-letrec expr)

  (define (tail-recursion-safe? expr group-names tail?)
    (cond
     ((symbol? expr)
      (not (memq expr group-names)))

     ((literal-expr? expr) #t)

     ((pair? expr)
      (case (car expr)
        ((begin)
         (let loop ((rest (cdr expr)))
           (cond
            ((null? rest) #t)
            ((null? (cdr rest))
             (tail-recursion-safe? (car rest) group-names tail?))
            (else
             (and (tail-recursion-safe? (car rest) group-names #f)
                  (loop (cdr rest)))))))

        ((primop)
         (all (lambda (e) (tail-recursion-safe? e group-names #f))
              (cddr expr)))

        ((if)
         (and (tail-recursion-safe? (cadr expr) group-names #f)
              (tail-recursion-safe? (caddr expr) group-names tail?)
              (tail-recursion-safe? (cadddr expr) group-names tail?)))

        ((let)
         (and (tail-recursion-safe? (cadr (caadr expr)) group-names #f)
              (let loop ((rest (cddr expr)))
                (cond
                 ((null? rest) #t)
                 ((null? (cdr rest))
                  (tail-recursion-safe? (car rest) group-names tail?))
                 (else
                  (and (tail-recursion-safe? (car rest) group-names #f)
                       (loop (cdr rest))))))))

        ((lambda)
         (tail-recursion-safe? (body->expr (cddr expr)) group-names #f))

        ((letrec)
         (and (all (lambda (binding)
                     (tail-recursion-safe? (cadr binding) group-names #f))
                   (cadr expr))
              (tail-recursion-safe? (body->expr (cddr expr)) group-names tail?)))

        ((app)
         (let ((rator (cadr expr))
               (args (cddr expr)))
           (if (and (symbol? rator) (memq rator group-names))
               (and tail?
                    (all (lambda (arg)
                           (tail-recursion-safe? arg group-names #f))
                         args))
               (and (tail-recursion-safe? rator group-names #f)
                    (all (lambda (arg)
                           (tail-recursion-safe? arg group-names #f))
                         args)))))

        ((cons set-box!)
         (and (tail-recursion-safe? (cadr expr) group-names #f)
              (tail-recursion-safe? (caddr expr) group-names #f)))

        ((box unbox car cdr pair? null?)
         (tail-recursion-safe? (cadr expr) group-names #f))

        ((global)
         #t)

        ((set-global!)
         (tail-recursion-safe? (caddr expr) group-names #f))

        (else #f)))

     (else #f)))

  (define (free-vars-outside-group expr bound group-names)
    (define (collect expr bound)
      (cond
       ((symbol? expr)
        (if (or (memq expr bound) (memq expr group-names))
            '()
            (list expr)))

       ((literal-expr? expr) '())

       ((pair? expr)
        (case (car expr)
          ((begin)
           (append-map (lambda (e) (collect e bound)) (cdr expr)))

          ((primop)
           (append-map (lambda (e) (collect e bound)) (cddr expr)))

          ((if)
           (append (collect (cadr expr) bound)
                   (collect (caddr expr) bound)
                   (collect (cadddr expr) bound)))

          ((let)
           (let* ((binding (caadr expr))
                  (var (car binding))
                  (val (cadr binding))
                  (body (body->expr (cddr expr))))
             (append (collect val bound)
                     (collect body (cons var bound)))))

          ((lambda)
           (collect (body->expr (cddr expr))
                    (append (cadr expr) bound)))

          ((letrec)
           (let* ((bindings (cadr expr))
                  (names (map car bindings))
                  (new-bound (append names bound)))
             (append (append-map (lambda (binding)
                                   (collect (cadr binding) new-bound))
                                 bindings)
                     (append-map (lambda (body-expr)
                                   (collect body-expr new-bound))
                                 (cddr expr)))))

          ((app)
           (append-map (lambda (e) (collect e bound)) (cdr expr)))

          ((set-box!)
           (append (collect (cadr expr) bound)
                   (collect (caddr expr) bound)))

          ((box unbox)
           (collect (cadr expr) bound))

          ((primop)
           (append-map (lambda (e) (collect e bound)) (cddr expr)))

          ((global)
           '())

          ((set-global!)
           (collect (caddr expr) bound))

          (else '())))

       (else '())))

    (dedupe-symbols (collect expr bound)))

  (define (tail-call-targets expr group-names tail?)
    (cond
     ((or (symbol? expr) (literal-expr? expr)) '())

     ((pair? expr)
      (case (car expr)
        ((begin)
         (let loop ((rest (cdr expr)))
           (cond
            ((null? rest) '())
            ((null? (cdr rest))
             (tail-call-targets (car rest) group-names tail?))
            (else
             (append (tail-call-targets (car rest) group-names #f)
                     (loop (cdr rest)))))))

        ((primop)
         (append-map (lambda (e) (tail-call-targets e group-names #f))
                     (cddr expr)))

        ((if)
         (append (tail-call-targets (cadr expr) group-names #f)
                 (tail-call-targets (caddr expr) group-names tail?)
                 (tail-call-targets (cadddr expr) group-names tail?)))

        ((let)
         (append (tail-call-targets (cadr (caadr expr)) group-names #f)
                 (let loop ((rest (cddr expr)))
                   (cond
                    ((null? rest) '())
                    ((null? (cdr rest))
                     (tail-call-targets (car rest) group-names tail?))
                    (else
                     (append (tail-call-targets (car rest) group-names #f)
                             (loop (cdr rest))))))))

        ((lambda)
         (tail-call-targets (body->expr (cddr expr)) group-names #f))

        ((letrec)
         (append (append-map (lambda (binding)
                               (tail-call-targets (cadr binding) group-names #f))
                             (cadr expr))
                 (append-map (lambda (body-expr)
                               (tail-call-targets body-expr group-names tail?))
                             (cddr expr))))

        ((app)
         (let ((rator (cadr expr))
               (args (cddr expr)))
           (append (if (and tail? (symbol? rator) (memq rator group-names))
                       (list rator)
                       (tail-call-targets rator group-names #f))
                   (append-map (lambda (arg)
                                 (tail-call-targets arg group-names #f))
                               args))))

        ((set-box!)
         (append (tail-call-targets (cadr expr) group-names #f)
                 (tail-call-targets (caddr expr) group-names #f)))

        ((box unbox)
         (tail-call-targets (cadr expr) group-names #f))

        ((global)
         '())

        ((set-global!)
         (tail-call-targets (caddr expr) group-names #f))

        (else '())))

     (else '())))

  (define (mutually-tail-recursive? bindings)
    (let* ((group-names (map car bindings))
           (graph
            (map (lambda (binding)
                   (let* ((lambda-expr (cadr binding))
                          (body (body->expr (cddr lambda-expr))))
                     (list (car binding)
                           (dedupe-symbols
                            (tail-call-targets body group-names #t)))))
                 bindings)))
      (define (neighbors name)
        (let ((entry (assoc name graph)))
          (if entry (cadr entry) '())))
      (define (reachable? start target visited)
        (cond
         ((eq? start target) #t)
         ((memq start visited) #f)
         (else
          (let loop ((rest (neighbors start)))
            (cond
             ((null? rest) #f)
             ((reachable? (car rest) target (cons start visited)) #t)
             (else (loop (cdr rest))))))))
      (and (all (lambda (name)
                  (not (null? (neighbors name))))
                group-names)
           (all (lambda (name)
                  (all (lambda (other)
                         (reachable? name other '()))
                       group-names))
                group-names))))

  (define (eligible-mutual-tail-group? bindings)
    (let ((group-names (map car bindings)))
      (and (> (length bindings) 1)
           (mutually-tail-recursive? bindings)
           (all (lambda (binding)
                  (let* ((lambda-expr (cadr binding))
                         (body (body->expr (cddr lambda-expr))))
                    (tail-recursion-safe? body group-names #t)))
                bindings))))

  (define (group-entry-safe? expr group-names)
    (cond
     ((symbol? expr) (not (memq expr group-names)))
     ((literal-expr? expr) #t)
     ((pair? expr)
      (case (car expr)
        ((begin)
         (all (lambda (e) (group-entry-safe? e group-names)) (cdr expr)))
        ((primop)
         (all (lambda (e) (group-entry-safe? e group-names)) (cddr expr)))
        ((if)
         (and (group-entry-safe? (cadr expr) group-names)
              (group-entry-safe? (caddr expr) group-names)
              (group-entry-safe? (cadddr expr) group-names)))
        ((let)
         (and (group-entry-safe? (cadr (caadr expr)) group-names)
              (all (lambda (e) (group-entry-safe? e group-names)) (cddr expr))))
        ((lambda)
         #f)
        ((app)
         (let ((rator (cadr expr))
               (args (cddr expr)))
           (and (if (and (symbol? rator) (memq rator group-names))
                    #t
                    (group-entry-safe? rator group-names))
                (all (lambda (arg) (group-entry-safe? arg group-names)) args))))
        ((set-box!)
         (and (group-entry-safe? (cadr expr) group-names)
              (group-entry-safe? (caddr expr) group-names)))
        ((box unbox)
         (group-entry-safe? (cadr expr) group-names))
        ((global)
         #t)
        ((set-global!)
         (group-entry-safe? (caddr expr) group-names))
        (else #f)))
     (else #f)))

  (define (rewrite-sequence exprs env current-group tail?)
    (let loop ((rest exprs) (result '()))
      (cond
       ((null? rest) (reverse result))
       ((null? (cdr rest))
        (reverse (cons (rewrite (car rest) env current-group tail?) result)))
       (else
        (loop (cdr rest)
              (cons (rewrite (car rest) env current-group #f) result))))))

  (define (rewrite-lambda expr env current-group)
    (let* ((params (cadr expr))
           (body-env (remove-shadowed-bindings env params))
           (body-exprs (rewrite-sequence (cddr expr) body-env current-group #t)))
      `(lambda ,params ,@body-exprs)))

  (define (rewrite expr env current-group tail?)
    (cond
     ((symbol? expr)
      (let ((binding (assoc expr env)))
        (if binding
            `(unbox ,(cadr binding))
            expr)))

     ((literal-expr? expr) expr)

     ((pair? expr)
      (case (car expr)
        ((begin)
         `(begin ,@(rewrite-sequence (cdr expr) env current-group tail?)))

        ((primop)
         `(primop ,(cadr expr)
                  ,@(map (lambda (e) (rewrite e env current-group #f)) (cddr expr))))

        ((if)
         `(if ,(rewrite (cadr expr) env current-group #f)
              ,(rewrite (caddr expr) env current-group tail?)
              ,(rewrite (cadddr expr) env current-group tail?)))

        ((let)
         (let* ((bindings (map (lambda (binding)
                                 (list (car binding)
                                       (rewrite (cadr binding) env current-group #f)))
                               (cadr expr)))
                (new-vars (map car bindings))
                (body-env (remove-shadowed-bindings env new-vars))
                (body-exprs (rewrite-sequence (cddr expr) body-env current-group tail?)))
           `(let ,bindings ,@body-exprs)))

        ((lambda)
         (rewrite-lambda expr env #f))

        ((letrec)
         (let* ((bindings (cadr expr))
                (names (map car bindings))
                (group-eligible?
                 (and (eligible-mutual-tail-group? bindings)
                      (group-entry-safe? (body->expr (cddr expr)) names))))
           (if (not (all (lambda (binding)
                           (and (single-binding? binding)
                                (lambda-expr? (cadr binding))))
                         bindings))
               (error "letrec requires lambda bindings" expr)
               (let* ((base-env (remove-shadowed-bindings env names))
                      (rec-env (append (map (lambda (name) (list name name)) names)
                                       base-env))
                      (box-bindings
                       (map (lambda (name) (list name '(box #f))) names))
                      (init-exprs
                       (map (lambda (binding)
                              `(set-box! ,(car binding)
                                         ,(rewrite-lambda (cadr binding)
                                                          rec-env
                                                          (if group-eligible?
                                                              names
                                                              (list (car binding))))))
                            bindings))
                      (body-exprs
                       (append init-exprs
                               (rewrite-sequence (cddr expr)
                                                 rec-env
                                                 current-group
                                                 tail?))))
                 (nest-let-bindings box-bindings body-exprs)))))

        ((app)
         (let ((rator (cadr expr))
               (args (cddr expr)))
           (if (and tail?
                    current-group
                    (symbol? rator)
                    (memq rator current-group))
               (if (> (length current-group) 1)
                   `(group-tail-call ,rator
                                     ,@(map (lambda (e) (rewrite e env current-group #f)) args))
                   `(self-tail-call
                     ,@(map (lambda (e) (rewrite e env current-group #f)) args)))
               `(app ,(rewrite rator env current-group #f)
                     ,@(map (lambda (e) (rewrite e env current-group #f)) args)))))

        ((cons)
         (error "cons in desugar-letrec: should have been canonicalized" expr))

        ((box)
         `(box ,(rewrite (cadr expr) env current-group #f)))

        ((unbox)
         `(unbox ,(rewrite (cadr expr) env current-group #f)))

        ((car)
         (error "car in desugar-letrec: should have been canonicalized" expr))

        ((cdr)
         (error "cdr in desugar-letrec: should have been canonicalized" expr))

        ((pair?)
         (error "pair? in desugar-letrec: should have been canonicalized" expr))

        ((null?)
         (error "null? in desugar-letrec: should have been canonicalized" expr))
        ((make-vector)
         (error "make-vector in desugar-letrec: should have been canonicalized" expr))
        ((vector-length)
         (error "vector-length in desugar-letrec: should have been canonicalized" expr))
        ((vector-ref)
         (error "vector-ref in desugar-letrec: should have been canonicalized" expr))
        ((vector-set!)
         (error "vector-set! in desugar-letrec: should have been canonicalized" expr))

        ((set-box!)
         (let ((target (cadr expr)))
           (when (and (symbol? target) (assoc target env))
             (error "Cannot mutate letrec function binding" target))
           `(set-box! ,(rewrite target env current-group #f)
                      ,(rewrite (caddr expr) env current-group #f))))

        ((global)
         expr)

        ((set-global!)
         `(set-global! ,(cadr expr)
                       ,(rewrite (caddr expr) env current-group #f)))

        (else (error "Unknown expression type in letrec desugaring" (car expr)))))

     (else (error "Invalid expression in letrec desugaring" expr))))

  (rewrite expr '() #f #t))

)) ; end define-library
