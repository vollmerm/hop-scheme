(define-library (hop pass tac)
  ;;; Pass 4: Convert to Three-Address Code (TAC)
  (export make-procedure
          tac-procedure?
          procedure-name
          procedure-params
          procedure-instructions
          expr->tac)
  (import (scheme base)
          (scheme cxr)
          (hop utils))
  (begin

(define-record-type <procedure>
  (make-procedure name params instructions)
  tac-procedure?
  (name procedure-name)
  (params procedure-params)
  (instructions procedure-instructions))

(define (expr->tac expr)
  (define temp-counter 0)
  (define (fresh-temp)
    (set! temp-counter (+ temp-counter 1))
    (string->symbol (string-append "t" (number->string temp-counter))))

  (define proc-counter 0)
  (define (fresh-proc)
    (set! proc-counter (+ proc-counter 1))
    (string->symbol (string-append "proc" (number->string proc-counter))))

  (define (simple? expr)
    (or (symbol? expr) (literal-expr? expr)
        (and (pair? expr) (memq (car expr) '(local closure)))))

  (define (simple-value expr)
    (if (and (pair? expr) (memq (car expr) '(local closure)))
        (cadr expr)
        expr))

  (define (convert-list exprs)
    (let loop ((rest exprs)
               (instrs '())
               (vars '())
               (procedures '()))
      (if (null? rest)
          (values instrs vars procedures)
          (let-values (((new-instrs new-var new-procedures)
                        (convert-value (car rest) #f)))
            (loop (cdr rest)
                  (append instrs new-instrs)
                  (append vars (list new-var))
                  (append procedures new-procedures))))))

  (define (convert-call closure-expr args)
    (let-values (((closure-instrs closure-var closure-procedures)
                  (convert-value closure-expr #f))
                 ((arg-instrs arg-vars arg-procedures)
                  (convert-list args)))
      (values (append closure-instrs arg-instrs)
              closure-var
              arg-vars
              (append closure-procedures arg-procedures))))

  (define (convert-known-call proc-name capture-count closure-expr args dest tail?)
    (let-values (((closure-instrs closure-var closure-procedures)
                  (convert-value closure-expr #f))
                 ((arg-instrs arg-vars arg-procedures)
                  (convert-list args)))
      (let loop ((index 0) (env-instrs '()) (env-vars '()))
        (if (= index capture-count)
            (let ((all-args (append (reverse env-vars) arg-vars)))
              (if tail?
                  (values (append closure-instrs
                                  arg-instrs
                                  env-instrs
                                  (list `(direct-tail-call ,proc-name ,@all-args)))
                          (append closure-procedures arg-procedures))
                  (let ((result-var (or dest (fresh-temp))))
                    (values (append closure-instrs
                                    arg-instrs
                                    env-instrs
                                    (list `(assign ,result-var
                                                   (direct-call ,proc-name ,@all-args))))
                            result-var
                            (append closure-procedures arg-procedures)))))
            (let ((env-var (fresh-temp)))
              (loop (+ index 1)
                    (append env-instrs
                            (list `(assign ,env-var
                                           (closure-env-ref ,closure-var ,index))))
                    (cons env-var env-vars)))))))

  (define (local-name expr)
    (and (pair? expr)
         (eq? (car expr) 'local)
         (pair? (cdr expr))
         (symbol? (cadr expr))
         (cadr expr)))

  (define (match-cluster-init expr)
    (and (pair? expr)
         (eq? (car expr) 'set-box!)
         (let ((name (local-name (cadr expr)))
               (value (caddr expr)))
           (and name
                (pair? value)
                (eq? (car value) 'make-closure)
                (let* ((named-closure?
                        (and (symbol? (cadr value))
                             (pair? (caddr value))
                             (eq? (car (caddr value)) 'lambda)))
                       (lambda-expr (if named-closure?
                                        (caddr value)
                                        (cadr value))))
                  (and (pair? lambda-expr)
                       (eq? (car lambda-expr) 'lambda)
                       (list name
                             (cadr lambda-expr)
                             (body->expr (cddr lambda-expr)))))))))

  (define (match-group-closures expr)
    (and (pair? expr)
         (eq? (car expr) 'group-closures)
         (pair? (cdr expr))
         (pair? (cddr expr))
         (null? (cdddr expr))
         (list (cadr expr) (caddr expr))))

  (define (cluster-body-compatible? expr names)
    (cond
     ((or (symbol? expr) (literal-expr? expr)) #t)
     ((pair? expr)
      (case (car expr)
        ((begin)
         (all (lambda (e) (cluster-body-compatible? e names)) (cdr expr)))
        ((primop)
         (all (lambda (e) (cluster-body-compatible? e names)) (cddr expr)))
        ((if)
         (and (cluster-body-compatible? (cadr expr) names)
              (cluster-body-compatible? (caddr expr) names)
              (cluster-body-compatible? (cadddr expr) names)))
        ((let)
         (and (cluster-body-compatible? (cadr (caadr expr)) names)
              (all (lambda (e) (cluster-body-compatible? e names))
                   (cddr expr))))
        ((lambda)
         (cluster-body-compatible? (body->expr (cddr expr)) names))
        ((group-tail-call)
         (and (symbol? (cadr expr))
              (memq (cadr expr) names)
              (all (lambda (e) (cluster-body-compatible? e names))
                   (cddr expr))))
        ((self-tail-call) #f)
        ((app closure-call known-call set-box! cons make-vector vector-ref vector-set!)
         (all (lambda (e) (cluster-body-compatible? e names)) (cdr expr)))
        ((box unbox car cdr pair? null? vector-length vector?)
         (cluster-body-compatible? (cadr expr) names))
        ((global local closure) #t)
        ((set-global!)
         (cluster-body-compatible? (caddr expr) names))
        (else #f)))
     (else #f)))

  (define (collect-group-tail-targets expr)
    (cond
     ((or (symbol? expr) (literal-expr? expr)) '())
     ((pair? expr)
      (case (car expr)
        ((group-tail-call)
         (cons (cadr expr)
               (append-map collect-group-tail-targets (cddr expr))))
        ((begin app closure-call known-call set-box! cons make-vector vector-ref vector-set!)
         (append-map collect-group-tail-targets (cdr expr)))
        ((primop)
         (append-map collect-group-tail-targets (cddr expr)))
        ((if)
         (append (collect-group-tail-targets (cadr expr))
                 (collect-group-tail-targets (caddr expr))
                 (collect-group-tail-targets (cadddr expr))))
        ((let)
         (append (collect-group-tail-targets (cadr (caadr expr)))
                 (append-map collect-group-tail-targets (cddr expr))))
        ((lambda)
         (collect-group-tail-targets (body->expr (cddr expr))))
        ((box unbox car cdr pair? null? vector-length vector?)
         (collect-group-tail-targets (cadr expr)))
        ((global)
         '())
        ((set-global!)
         (collect-group-tail-targets (caddr expr)))
        (else '())))
     (else '())))

  (define (has-cross-group-tail-call? members names)
    (let loop ((rest members))
      (cond
       ((null? rest) #f)
       (else
        (let ((name (car (car rest)))
              (targets (collect-group-tail-targets (caddr (car rest)))))
          (if (let inner ((remaining-targets targets))
                (cond
                 ((null? remaining-targets) #f)
                 ((and (memq (car remaining-targets) names)
                       (not (eq? (car remaining-targets) name)))
                  #t)
                 (else
                  (inner (cdr remaining-targets)))))
              #t
              (loop (cdr rest))))))))

  (define (extract-cluster-prefix exprs)
    (define (finish members rest)
      (let ((names (map car members)))
        (if (and (> (length members) 1)
                 (all (lambda (member)
                        (cluster-body-compatible? (caddr member) names))
                      members)
                 (has-cross-group-tail-call? members names))
            (cons members rest)
            #f)))
    (let loop ((rest exprs) (members '()))
      (cond
       ((null? rest) (finish members '()))
       (else
        (let ((member (match-cluster-init (car rest))))
          (if member
              (loop (cdr rest) (append members (list member)))
              (finish members rest)))))))

  (define (local-refs-in-expr expr)
    (cond
     ((not (pair? expr)) '())
     ((and (eq? (car expr) 'local)
           (pair? (cdr expr))
           (null? (cddr expr))
           (symbol? (cadr expr)))
      (list (cadr expr)))
     (else
      (append-map local-refs-in-expr expr))))

  (define (build-dispatch-instructions entry-tag dispatch-label member-labels)
    (let loop ((rest member-labels)
               (index 0)
               (current-label dispatch-label)
               (instrs '()))
      (if (null? (cdr rest))
          (append instrs
                  (list `(label ,current-label)
                        `(goto ,(car rest))))
          (let ((next-label (fresh-temp))
                (cmp-var (fresh-temp)))
            (loop (cdr rest)
                  (+ index 1)
                  next-label
                  (append instrs
                          (list `(label ,current-label)
                                `(assign ,cmp-var (primop = ,entry-tag ,index))
                                `(if ,cmp-var ,(car rest) ,next-label))))))))

  (define (convert-cluster-prefix exprs)
    (define (lower-cluster members capture-specs remaining-exprs)
      (let* ((cluster-proc (fresh-proc))
             (shared-params (map (lambda (ignored) (fresh-temp))
                                 (let ((max-arity
                                        (let loop ((rest members) (m 0))
                                          (if (null? rest)
                                              m
                                              (loop (cdr rest)
                                                    (max m (length (caddr (car rest)))))))))
                                   (let loop ((n max-arity) (result '()))
                                     (if (zero? n)
                                         result
                                         (loop (- n 1) (cons #f result)))))))
             (entry-tag (fresh-temp))
             (dispatch-label
              (string->symbol
               (string-append "dispatch." (symbol->string cluster-proc))))
             (member-labels
              (map (lambda (member)
                     (string->symbol
                      (string-append "entry."
                                     (symbol->string (cadr member)))))
                   members))
             (member-arities
              (map (lambda (member) (length (caddr member))) members))
             (group-context
              (map (lambda (member label arity)
                     (list (cadr member) label arity))
                   members
                   member-labels
                   member-arities))
             (capture-param-names (map car capture-specs))
             (capture-value-exprs (map cadr capture-specs)))
        (let-values (((capture-instrs capture-vars capture-procedures)
                      (convert-list capture-value-exprs)))
          (let* ((all-local-refs (append-map local-refs-in-expr remaining-exprs))
                 (box-vars (map car members))
                 (external-box-names (filter (lambda (n) (memq n box-vars)) all-local-refs))
                 (is-external?
                  (if (null? external-box-names)
                      (lambda (m) #t)
                      (lambda (m) (memq (car m) external-box-names))))
                 (dispatch-member-labels
                  (let loop ((ms members) (ls member-labels) (result '()))
                    (if (null? ms)
                        (reverse result)
                        (loop (cdr ms) (cdr ls)
                              (if (is-external? (car ms))
                                  (cons (car ls) result)
                                  result))))))
            (let ((init-instrs
                   (let loop ((rest members) (index 0) (instrs capture-instrs))
                     (if (null? rest)
                         instrs
                         (let ((box-name (car (car rest))))
                           (if (is-external? (car rest))
                               (let ((closure-temp (fresh-temp)))
                                 (loop (cdr rest)
                                       (+ index 1)
                                       (append instrs
                                               (list `(assign ,closure-temp
                                                              (make-closure ,cluster-proc ,index ,@capture-vars))
                                                     `(set-box! ,box-name ,closure-temp)))))
                               (loop (cdr rest) index instrs)))))))
              (let loop ((rest members)
                         (labels member-labels)
                         (instrs (build-dispatch-instructions entry-tag
                                                              dispatch-label
                                                              dispatch-member-labels))
                         (procedures capture-procedures))
                (if (null? rest)
                    (values init-instrs
                            (append procedures
                                    (list (make-procedure cluster-proc
                                                          (append (list entry-tag)
                                                                  capture-param-names
                                                                  shared-params)
                                                          instrs)))
                            remaining-exprs)
                    (let* ((member (car rest))
                           (params (caddr member))
                           (body (cadddr member))
                           (entry-label (car labels)))
                      (let-values (((body-instrs body-procedures)
                                    (convert-tail body
                                                  params
                                                  entry-label
                                                  group-context
                                                  shared-params)))
                        (loop (cdr rest)
                              (cdr labels)
                              (append instrs
                                      (list `(label ,entry-label))
                                      (map (lambda (param shared)
                                             `(assign ,param ,shared))
                                           params
                                           shared-params)
                                      body-instrs)
                              (append procedures body-procedures)))))))))))
    (let ((explicit (and (pair? exprs) (match-group-closures (car exprs)))))
      (if explicit
          (lower-cluster (car explicit) (cadr explicit) (cdr exprs))
          (let ((cluster (extract-cluster-prefix exprs)))
            (if (not cluster)
                (values '() '() exprs)
                (lower-cluster
                 (map (lambda (member)
                        (list (car member) (car member) (cadr member) (caddr member)))
                      (car cluster))
                 '()
                 (cdr cluster)))))))

  (define (convert-tail expr current-params current-entry-label group-context shared-params)
    (cond
     ((simple? expr)
      (values (list `(return ,(simple-value expr))) '()))

     ((pair? expr)
      (case (car expr)
        ((begin)
         (let ((body-exprs (cdr expr)))
           (let-values (((cluster-instrs cluster-procedures remaining-exprs)
                         (convert-cluster-prefix body-exprs)))
             (let loop ((rest remaining-exprs)
                        (instrs cluster-instrs)
                        (procedures cluster-procedures))
               (cond
                ((null? rest)
                 (error "begin requires at least one expression"))
                ((null? (cdr rest))
                 (let-values (((tail-instrs tail-procedures)
                               (convert-tail (car rest)
                                             current-params
                                             current-entry-label
                                             group-context
                                             shared-params)))
                   (values (append instrs tail-instrs)
                           (append procedures tail-procedures))))
                (else
                 (let-values (((new-instrs ignored-result new-procedures)
                               (convert-value (car rest) #f)))
                   (loop (cdr rest)
                         (append instrs new-instrs)
                         (append procedures new-procedures)))))))))

        ((if)
         (let* ((then-label (fresh-temp))
                (else-label (fresh-temp)))
           (let-values (((test-instrs test-var test-procedures)
                         (convert-value (cadr expr) #f))
                        ((then-instrs then-procedures)
                         (convert-tail (caddr expr)
                                       current-params
                                       current-entry-label
                                       group-context
                                       shared-params))
                        ((else-instrs else-procedures)
                         (convert-tail (cadddr expr)
                                       current-params
                                       current-entry-label
                                       group-context
                                       shared-params)))
             (values
              (append test-instrs
                      (list `(if ,test-var ,then-label ,else-label))
                      (list `(label ,then-label))
                      then-instrs
                      (list `(label ,else-label))
                      else-instrs)
              (append test-procedures
                      then-procedures
                      else-procedures)))))

        ((let)
         (let* ((bindings (cadr expr))
                (body (body->expr (cddr expr))))
           (let loop ((rest bindings)
                      (instrs '())
                      (procedures '()))
             (if (null? rest)
                 (let-values (((body-instrs body-procedures)
                               (convert-tail body
                                             current-params
                                             current-entry-label
                                             group-context
                                             shared-params)))
                   (values (append instrs body-instrs)
                           (append procedures body-procedures)))
                 (let* ((binding (car rest))
                        (var (car binding))
                        (val (cadr binding)))
                   (let-values (((val-instrs val-result val-procedures)
                                 (convert-value val #f)))
                     (loop (cdr rest)
                           (append instrs val-instrs
                                   (list `(assign ,var ,val-result)))
                           (append procedures val-procedures))))))))

        ((self-tail-call)
         (if (not current-entry-label)
             (error "self-tail-call outside of procedure" expr)
             (let ((args (cdr expr)))
               (when (not (= (length args) (length current-params)))
                 (error "Arity mismatch in self-tail-call" expr))
               (let-values (((arg-instrs arg-vars arg-procedures)
                             (convert-list args)))
                 (values (append arg-instrs
                                 (map (lambda (param arg)
                                        `(assign ,param ,arg))
                                      current-params
                                      arg-vars)
                                 (list `(goto ,current-entry-label)))
                         arg-procedures)))))

        ((group-tail-call)
         (if (or (not group-context) (not shared-params))
             (error "group-tail-call outside of cluster" expr)
             (let* ((target (cadr expr))
                    (args (cddr expr))
                    (entry (assoc target group-context))
                    (target-arity (caddr entry)))
               (when (not entry)
                 (error "Unknown group-tail-call target" target))
               (when (not (= (length args) target-arity))
                 (error "Arity mismatch in group-tail-call" expr))
               (let-values (((arg-instrs arg-vars arg-procedures)
                             (convert-list args)))
                 (values (append arg-instrs
                                 (map (lambda (shared arg)
                                        `(assign ,shared ,arg))
                                      shared-params
                                      arg-vars)
                                 (list `(goto ,(cadr entry))))
                         arg-procedures)))))

        ((closure-call)
         (let ((closure-expr (cadr expr))
               (args (cddr expr)))
           (let-values (((call-instrs closure-var arg-vars procedures)
                         (convert-call closure-expr args)))
             (values (append call-instrs
                             (list `(tail-call ,closure-var ,@arg-vars)))
                     procedures))))

        ((known-call)
         (convert-known-call (cadr expr)
                             (caddr expr)
                             (cadddr expr)
                             (cddddr expr)
                             #f
                             #t))

        (else
         (let-values (((instrs result-var procedures)
                       (convert-value expr #f)))
           (values (append instrs (list `(return ,result-var)))
                   procedures)))))

     (else
      (error "Invalid expression in tail position" expr))))

  (define (convert-value expr dest)
    (define (convert-unary-value-op op arg-expr)
      (let-values (((instrs arg-var procedures)
                    (convert-value arg-expr #f)))
        (let ((result-var (or dest (fresh-temp))))
          (values (append instrs
                          (list `(assign ,result-var (,op ,arg-var))))
                  result-var
                  procedures))))

    (define (convert-binary-value-op op left-expr right-expr)
      (let-values (((left-instrs left-var left-procedures)
                    (convert-value left-expr #f))
                   ((right-instrs right-var right-procedures)
                    (convert-value right-expr #f)))
        (let ((result-var (or dest (fresh-temp))))
          (values (append left-instrs
                          right-instrs
                          (list `(assign ,result-var (,op ,left-var ,right-var))))
                  result-var
                  (append left-procedures right-procedures)))))

    (cond
     ((simple? expr)
      (let ((value (simple-value expr)))
        (if dest
            (if (eq? dest value)
                (values '() dest '())
                (values (list `(assign ,dest ,value)) dest '()))
            (values '() value '()))))

     ((pair? expr)
      (case (car expr)
        ((global)
         (let ((result-var (or dest (fresh-temp))))
           (values (list `(assign ,result-var ,expr))
                   result-var
                   '())))
        ((begin)
         (let ((body-exprs (cdr expr)))
           (let-values (((cluster-instrs cluster-procedures remaining-exprs)
                         (convert-cluster-prefix body-exprs)))
             (let loop ((rest remaining-exprs)
                        (instrs cluster-instrs)
                        (procedures cluster-procedures))
               (cond
                ((null? rest)
                 (error "begin requires at least one expression"))
                ((null? (cdr rest))
                 (let-values (((last-instrs last-result last-procedures)
                               (convert-value (car rest) dest)))
                   (values (append instrs last-instrs)
                           last-result
                           (append procedures last-procedures))))
                (else
                 (let-values (((new-instrs ignored-result new-procedures)
                               (convert-value (car rest) #f)))
                   (loop (cdr rest)
                         (append instrs new-instrs)
                         (append procedures new-procedures)))))))))

        ((primop)
         (let ((op (cadr expr))
               (args (cddr expr)))
           (let-values (((arg-instrs arg-vars arg-procedures)
                         (convert-list args)))
             (let ((result-var (or dest (fresh-temp))))
               (values (append arg-instrs
                               (list `(assign ,result-var
                                              (primop ,op ,@arg-vars))))
                       result-var
                       arg-procedures)))))

        ((cons)
         (error "cons in expr->tac: should have been canonicalized" expr))
        ((make-vector)
         (error "make-vector in expr->tac: should have been canonicalized" expr))
        ((vector-length)
         (error "vector-length in expr->tac: should have been canonicalized" expr))
        ((vector-ref)
         (error "vector-ref in expr->tac: should have been canonicalized" expr))
        ((vector-set!)
         (error "vector-set! in expr->tac: should have been canonicalized" expr))
        ((vector?)
         (error "vector? in expr->tac: should have been canonicalized" expr))

        ((box)
         (convert-unary-value-op 'box (cadr expr)))

        ((unbox)
         (convert-unary-value-op 'unbox (cadr expr)))

        ((car)
         (error "car in expr->tac: should have been canonicalized" expr))
        ((cdr)
         (error "cdr in expr->tac: should have been canonicalized" expr))
        ((pair?)
         (error "pair? in expr->tac: should have been canonicalized" expr))
        ((null?)
         (error "null? in expr->tac: should have been canonicalized" expr))

        ((if)
         (let* ((then-label (fresh-temp))
                (else-label (fresh-temp))
                (join-label (fresh-temp))
                (result-var (or dest (fresh-temp))))
           (let-values (((test-instrs test-var test-procedures)
                         (convert-value (cadr expr) #f))
                        ((then-instrs then-result then-procedures)
                         (convert-value (caddr expr) result-var))
                        ((else-instrs else-result else-procedures)
                         (convert-value (cadddr expr) result-var)))
             (values
              (append test-instrs
                      (list `(if ,test-var ,then-label ,else-label))
                      (list `(label ,then-label))
                      then-instrs
                      (list `(goto ,join-label))
                      (list `(label ,else-label))
                      else-instrs
                      (list `(goto ,join-label))
                      (list `(label ,join-label)))
              result-var
              (append test-procedures
                      then-procedures
                      else-procedures)))))

        ((let)
         (let* ((bindings (cadr expr))
                (body (body->expr (cddr expr))))
           (let loop ((rest bindings)
                      (instrs '())
                      (procedures '()))
             (if (null? rest)
                 (let-values (((body-instrs body-result body-procedures)
                               (convert-value body dest)))
                   (values (append instrs body-instrs)
                           body-result
                           (append procedures body-procedures)))
                 (let* ((binding (car rest))
                        (var (car binding))
                        (val (cadr binding)))
                   (let-values (((val-instrs val-result val-procedures)
                                 (convert-value val #f)))
                     (loop (cdr rest)
                           (append instrs val-instrs
                                   (list `(assign ,var ,val-result)))
                           (append procedures val-procedures))))))))

        ((make-closure)
         (let* ((named-closure?
                 (and (symbol? (cadr expr))
                      (pair? (caddr expr))
                      (eq? (car (caddr expr)) 'lambda)))
                (proc-name (if named-closure?
                               (cadr expr)
                               (fresh-proc)))
                (lambda-expr (if named-closure?
                                 (caddr expr)
                                 (cadr expr)))
                (free-vars (if named-closure?
                               (cdddr expr)
                               (cddr expr)))
                (proc-params (cadr lambda-expr))
                (proc-body (body->expr (cddr lambda-expr))))
           (let ((entry-label (fresh-temp)))
             (let-values (((body-instrs body-procedures)
                           (convert-tail proc-body
                                         proc-params
                                         entry-label
                                         #f
                                         #f))
                          ((fv-instrs fv-vars fv-procedures)
                           (convert-list free-vars)))
               (let ((result-var (or dest (fresh-temp)))
                     (procedure
                      (make-procedure proc-name
                                      proc-params
                                      (cons `(label ,entry-label) body-instrs))))
                 (values (append fv-instrs
                                 (list `(assign ,result-var
                                                (make-closure ,proc-name
                                                              ,@fv-vars))))
                         result-var
                         (append body-procedures
                                 fv-procedures
                                 (list procedure))))))))

        ((known-call)
         (convert-known-call (cadr expr)
                             (caddr expr)
                             (cadddr expr)
                             (cddddr expr)
                             dest
                             #f))

        ((closure-call)
         (let* ((closure-expr (cadr expr))
                (args (cddr expr)))
           (let-values (((call-instrs closure-var arg-vars procedures)
                         (convert-call closure-expr args)))
             (let ((result-var (or dest (fresh-temp))))
               (values (append call-instrs
                               (list `(assign ,result-var
                                              (closure-call ,closure-var
                                                            ,@arg-vars))))
                       result-var
                       procedures)))))

        ((group-tail-call)
         (error "group-tail-call is only valid in tail position" expr))

        ((set-box!)
         (let-values (((box-instrs box-var box-procedures)
                       (convert-value (cadr expr) #f))
                      ((val-instrs val-var val-procedures)
                       (convert-value (caddr expr) #f)))
           (let ((result-var (or dest val-var)))
             (values (append box-instrs
                             val-instrs
                             (list `(set-box! ,box-var ,val-var))
                             (if (eq? result-var val-var)
                                 '()
                                 (list `(assign ,result-var ,val-var))))
                     result-var
                     (append box-procedures val-procedures)))))

        ((set-global!)
         (let-values (((val-instrs val-var val-procedures)
                       (convert-value (caddr expr) #f)))
           (let ((result-var (or dest val-var)))
             (values (append val-instrs
                             (list `(set-global! ,(cadr expr) ,val-var))
                             (if (eq? result-var val-var)
                                 '()
                                 (list `(assign ,result-var ,val-var))))
                     result-var
                     val-procedures))))

        ((local closure)
         (values '() (cadr expr) '()))

        (else
         (error "Unknown expression in expr->tac" (car expr)))))

     (else
      (error "Invalid expression in expr->tac" expr))))

  (convert-tail expr '() #f #f #f))

)) ; end define-library
