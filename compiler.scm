;;; A small Scheme-to-AArch64 compiler.
;;;
;;; The file is organized as a sequence of explicit compilation passes so that
;;; each stage has a single, teachable job:
;;;
;;;   source program
;;;     -> uniquify
;;;     -> letrec desugaring
;;;     -> closure conversion
;;;     -> three-address code (TAC)
;;;     -> control-flow graph (CFG)
;;;     -> machine-like backend IR
;;;     -> register allocation / calling-convention lowering
;;;     -> AArch64 assembly
;;;
;;; The source language supported here is intentionally small: arithmetic,
;;; booleans, null, pairs, conditionals, boxes, lambdas, applications, and
;;; lambda-only letrec.

(import (scheme base)
        (scheme write))

;;; ============================================================================
;;; Shared Helpers
;;; Small utilities used across many passes. These helpers are deliberately
;;; simple so the interesting compiler logic below can read directly.
;;; ============================================================================

(define (body->expr body-exprs)
  (cond
    ((null? body-exprs)
     (error "Empty body is not supported"))
    ((null? (cdr body-exprs))
     (car body-exprs))
    (else
     `(begin ,@body-exprs))))

(define (append-map proc lst)
  (let loop ((rest lst) (result '()))
    (if (null? rest)
        result
        (append result (proc (car rest)) (loop (cdr rest) '())))))

(define (dedupe-symbols lst)
  (let loop ((rest lst) (seen '()) (result '()))
    (cond
      ((null? rest) (reverse result))
      ((memq (car rest) seen)
       (loop (cdr rest) seen result))
      (else
       (loop (cdr rest)
             (cons (car rest) seen)
             (cons (car rest) result))))))

(define (remove-shadowed-bindings env names)
  (let loop ((rest env) (result '()))
    (cond
      ((null? rest) (reverse result))
      ((memq (caar rest) names)
       (loop (cdr rest) result))
      (else
       (loop (cdr rest) (cons (car rest) result))))))

(define (all predicate lst)
  (cond
    ((null? lst) #t)
    ((predicate (car lst)) (all predicate (cdr lst)))
    (else #f)))

(define (single-binding? binding)
  (and (pair? binding)
       (pair? (cdr binding))
       (null? (cddr binding))))

(define (lambda-expr? expr)
  (and (pair? expr) (eq? (car expr) 'lambda)))

(define (literal-expr? expr)
  (or (number? expr) (boolean? expr) (null? expr)))

(define (nest-let-bindings bindings body-exprs)
  (if (null? bindings)
      (body->expr body-exprs)
      `(let (,(car bindings))
         ,(nest-let-bindings (cdr bindings) body-exprs))))

;;; ============================================================================
;;; Pass 1: Uniquify
;;; Renames every binder so that each variable name is globally unique.
;;; After this pass, later stages no longer need to reason about shadowing by
;;; name; they can treat identifiers as stable handles for bindings.
;;; ============================================================================

(define (uniquify expr)
  (define counter 0)
  
  (define (fresh-name name)
    (set! counter (+ counter 1))
    (string->symbol 
     (string-append (symbol->string name) 
                    "." 
                    (number->string counter))))
  
  (define (uniquify-expr expr env)
    (cond
      ((symbol? expr)
       ;; Variable reference
       (let ((binding (assoc expr env)))
         (if binding
             (cadr binding)  ; Return the unique name
             expr)))         ; Keep global/primitive names as-is
      
      ((literal-expr? expr) expr)
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(map (lambda (e) (uniquify-expr e env)) (cdr expr))))
         
          ((primop)
           `(primop ,(cadr expr) 
                    ,@(map (lambda (e) (uniquify-expr e env)) (cddr expr))))
         
         ((if)
          `(if ,(uniquify-expr (cadr expr) env)
               ,(uniquify-expr (caddr expr) env)
               ,(uniquify-expr (cadddr expr) env)))
         
          ((let)
           (let* ((binding (caadr expr))
                  (var (car binding))
                  (val-expr (cadr binding))
                  (body-exprs (cddr expr))
                  (unique-var (fresh-name var))
                  (new-env (cons (list var unique-var) env))
                  (val-expr-unique (uniquify-expr val-expr env))
                  (body-unique
                   (map (lambda (body-expr)
                          (uniquify-expr body-expr new-env))
                        body-exprs)))
             `(let ((,unique-var ,val-expr-unique)) ,@body-unique)))
          
          ((lambda)
           (let* ((params (cadr expr))
                  (body-exprs (cddr expr))
                  (unique-params (map fresh-name params))
                  (new-env (append (map (lambda (old new) (list old new)) 
                                        params unique-params)
                                   env))
                  (body-unique
                   (map (lambda (body-expr)
                          (uniquify-expr body-expr new-env))
                        body-exprs)))
             `(lambda ,unique-params ,@body-unique)))
          
          ((letrec)
           (let* ((bindings (cadr expr))
                  (vars (map car bindings))
                  (unique-vars (map fresh-name vars))
                  (rec-bindings (map (lambda (old new) (list old new))
                                     vars unique-vars))
                  (new-env (append rec-bindings env))
                  (unique-bindings
                   (map (lambda (binding unique-var)
                          (let ((value-expr (cadr binding)))
                            (if (not (lambda-expr? value-expr))
                                (error "letrec requires lambda bindings" value-expr)
                                (list unique-var
                                      (uniquify-expr value-expr new-env)))))
                        bindings
                        unique-vars))
                  (body-unique
                   (map (lambda (body-expr)
                          (uniquify-expr body-expr new-env))
                        (cddr expr))))
             `(letrec ,unique-bindings ,@body-unique)))
          
          ((app)
           `(app ,(uniquify-expr (cadr expr) env)
                 ,@(map (lambda (e) (uniquify-expr e env)) (cddr expr))))

          ((cons)
           `(cons ,(uniquify-expr (cadr expr) env)
                  ,(uniquify-expr (caddr expr) env)))
          
          ((box unbox car cdr pair? null?)
           `(,(car expr) ,(uniquify-expr (cadr expr) env)))
          
          ((set-box!)
           `(set-box! ,(uniquify-expr (cadr expr) env) 
                      ,(uniquify-expr (caddr expr) env)))
         
         (else (error "Unknown expression type" (car expr)))))
      
      (else (error "Invalid expression" expr))))
  
  (uniquify-expr expr '()))

;;; ============================================================================
;;; Pass 2: Letrec Desugaring
;;; Rewrites lambda-only letrec groups into explicit allocation and
;;; initialization. Recursive bindings become boxes containing closures.
;;;
;;; This pass also preserves direct tail recursion by rewriting eligible calls
;;; to explicit self/group tail-call markers, which later stages can lower into
;;; jumps instead of ordinary calls.
;;; ============================================================================

(define (desugar-letrec expr)
  (define (all-same-arity? bindings)
    (or (null? bindings)
        (let ((arity (length (cadr (cadar bindings)))))
          (all (lambda (binding)
                 (= (length (cadr (cadr binding))) arity))
               bindings))))

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
           
           ((cons set-box!)
            (append (collect (cadr expr) bound)
                    (collect (caddr expr) bound)))

           ((box unbox car cdr pair? null?)
            (collect (cadr expr) bound))
            
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
         
          ((cons set-box!)
           (append (tail-call-targets (cadr expr) group-names #f)
                   (tail-call-targets (caddr expr) group-names #f)))

          ((box unbox car cdr pair? null?)
           (tail-call-targets (cadr expr) group-names #f))
          
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
           (all-same-arity? bindings)
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
         ((cons set-box!)
          (and (group-entry-safe? (cadr expr) group-names)
               (group-entry-safe? (caddr expr) group-names)))
         ((box)
          (group-entry-safe? (cadr expr) group-names))
         ((unbox car cdr pair? null?)
          (group-entry-safe? (cadr expr) group-names))
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
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val-expr (rewrite (cadr binding) env current-group #f))
                 (body-env (remove-shadowed-bindings env (list var)))
                 (body-exprs (rewrite-sequence (cddr expr) body-env current-group tail?)))
            `(let ((,var ,val-expr)) ,@body-exprs)))
         
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
           `(cons ,(rewrite (cadr expr) env current-group #f)
                  ,(rewrite (caddr expr) env current-group #f)))
          
          ((box)
           `(box ,(rewrite (cadr expr) env current-group #f)))
          
          ((unbox)
           `(unbox ,(rewrite (cadr expr) env current-group #f)))

          ((car)
           `(car ,(rewrite (cadr expr) env current-group #f)))

          ((cdr)
           `(cdr ,(rewrite (cadr expr) env current-group #f)))

          ((pair?)
           `(pair? ,(rewrite (cadr expr) env current-group #f)))

          ((null?)
           `(null? ,(rewrite (cadr expr) env current-group #f)))
          
          ((set-box!)
           (let ((target (cadr expr)))
            (when (and (symbol? target) (assoc target env))
              (error "Cannot mutate letrec function binding" target))
            `(set-box! ,(rewrite target env current-group #f)
                       ,(rewrite (caddr expr) env current-group #f))))
         
         (else (error "Unknown expression type in letrec desugaring" (car expr)))))
      
      (else (error "Invalid expression in letrec desugaring" expr))))
  
  (rewrite expr '() #f #t))

;;; ============================================================================
;;; Pass 3: Closure Conversion
;;; Turns lambdas into explicit closure values.
;;;
;;; After this pass, a function is represented as:
;;;   1. code (a top-level procedure),
;;;   2. an explicit environment payload for captured values, and
;;;   3. closure-call / make-closure forms instead of source-level application.
;;; ============================================================================

(define (free-vars expr bound)
  ;; Return list of free variables in expr, given bound variables
  (define (collect expr bound)
    (cond
      ((symbol? expr)
       (if (memq expr bound) '() (list expr)))
      
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
          (let* ((params (cadr expr))
                 (body (body->expr (cddr expr))))
            (collect body (append params bound))))
         
          ((app)
           (append-map (lambda (e) (collect e bound)) (cdr expr)))

          ((self-tail-call)
           (append-map (lambda (e) (collect e bound)) (cdr expr)))

          ((group-tail-call)
           (append-map (lambda (e) (collect e bound)) (cddr expr)))
           
           ((box unbox car cdr pair? null?)
            (collect (cadr expr) bound))

          ((cons set-box!)
           (append (collect (cadr expr) bound)
                   (collect (caddr expr) bound)))
          
          (else (error "Unknown expression in free-vars" (car expr)))))
      
      (else '())))
  
  (dedupe-symbols (collect expr bound)))

(define (closure-convert expr)
  (define (any predicate lst)
    (cond
      ((null? lst) #f)
      ((predicate (car lst)) #t)
      (else (any predicate (cdr lst)))))

  (define (make-env-vars prefix count)
    (let loop ((i 0) (result '()))
      (if (= i count)
          (reverse result)
          (loop (+ i 1)
                (cons (string->symbol
                       (string-append prefix (number->string i)))
                      result)))))

  (define (local-repr-name repr)
    (and (pair? repr)
         (eq? (car repr) 'local)
         (pair? (cdr repr))
         (symbol? (cadr repr))
         (cadr repr)))

  (define (lookup-repr name env)
    (let ((binding (assoc name env)))
      (if binding
          (cadr binding)
          name)))

  (define (collect-group-tail-targets expr)
    (cond
      ((or (symbol? expr) (literal-expr? expr)) '())
      ((pair? expr)
       (case (car expr)
         ((group-tail-call)
          (cons (cadr expr)
                (append-map collect-group-tail-targets (cddr expr))))
         ((begin app set-box! cons)
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
         ((box unbox car cdr pair? null?)
          (collect-group-tail-targets (cadr expr)))
         (else '())))
      (else '())))

  (define (mentions-box-var? expr box-vars)
    (cond
      ((symbol? expr) (memq expr box-vars))
      ((literal-expr? expr) #f)
      ((pair? expr)
       (case (car expr)
         ((begin app primop set-box! cons)
          (any (lambda (e) (mentions-box-var? e box-vars)) (cdr expr)))
         ((if)
          (or (mentions-box-var? (cadr expr) box-vars)
              (mentions-box-var? (caddr expr) box-vars)
              (mentions-box-var? (cadddr expr) box-vars)))
         ((let)
          (or (mentions-box-var? (cadr (caadr expr)) box-vars)
              (any (lambda (e) (mentions-box-var? e box-vars)) (cddr expr))))
         ((lambda)
          (mentions-box-var? (body->expr (cddr expr)) box-vars))
         ((box unbox car cdr pair? null?)
           (mentions-box-var? (cadr expr) box-vars))
         (else #f)))
      (else #f)))

  (define (safe-group-body? expr box-vars)
    (cond
      ((symbol? expr) (not (memq expr box-vars)))
      ((literal-expr? expr) #t)
      ((pair? expr)
       (case (car expr)
         ((begin)
          (all (lambda (e) (safe-group-body? e box-vars)) (cdr expr)))
         ((primop)
          (all (lambda (e) (safe-group-body? e box-vars)) (cddr expr)))
         ((if)
          (and (safe-group-body? (cadr expr) box-vars)
               (safe-group-body? (caddr expr) box-vars)
               (safe-group-body? (cadddr expr) box-vars)))
         ((let)
          (and (safe-group-body? (cadr (caadr expr)) box-vars)
               (all (lambda (e) (safe-group-body? e box-vars)) (cddr expr))))
         ((lambda)
          (not (mentions-box-var? (body->expr (cddr expr)) box-vars)))
         ((app)
          (let ((rator (cadr expr))
                (args (cddr expr)))
            (if (and (pair? rator)
                     (eq? (car rator) 'unbox)
                     (symbol? (cadr rator))
                     (memq (cadr rator) box-vars))
                (all (lambda (arg) (safe-group-body? arg box-vars)) args)
                (and (safe-group-body? rator box-vars)
                     (all (lambda (arg) (safe-group-body? arg box-vars)) args)))))
         ((cons)
          (and (safe-group-body? (cadr expr) box-vars)
               (safe-group-body? (caddr expr) box-vars)))
         ((box)
           (safe-group-body? (cadr expr) box-vars))
         ((unbox car cdr pair? null?)
           (let ((target (cadr expr)))
             (if (and (symbol? target) (memq target box-vars))
                 #f
                 (safe-group-body? target box-vars))))
         ((set-box!)
          (and (not (and (symbol? (cadr expr)) (memq (cadr expr) box-vars)))
               (safe-group-body? (cadr expr) box-vars)
               (safe-group-body? (caddr expr) box-vars)))
         (else #f)))
      (else #f)))

  (define (extract-group-prefix exprs env)
    (define (links-other-member? member names)
      (let ((name (cadr member))
            (targets (collect-group-tail-targets (cadddr member))))
        (let loop ((rest-targets targets))
          (cond
            ((null? rest-targets) #f)
            ((and (memq (car rest-targets) names)
                  (not (eq? (car rest-targets) name)))
             #t)
            (else
             (loop (cdr rest-targets)))))))

    (define (finish members rest)
      (let ((names (map cadr members))
            (box-vars (map cadr members)))
        (if (and (> (length members) 1)
                 (safe-group-body? (body->expr rest) box-vars)
                 (any (lambda (member)
                        (links-other-member? member names))
                      members))
            (cons members rest)
            #f)))

    (let loop ((rest exprs) (members '()))
      (if (null? rest)
          (finish members '())
          (let ((expr (car rest)))
            (if (and (pair? expr)
                     (eq? (car expr) 'set-box!)
                     (symbol? (cadr expr))
                     (pair? (caddr expr))
                     (eq? (car (caddr expr)) 'lambda))
                (let* ((box-name (cadr expr))
                       (box-repr (lookup-repr box-name env))
                       (local-box (local-repr-name box-repr))
                       (lambda-expr (caddr expr)))
                  (if local-box
                      (loop (cdr rest)
                            (append members
                                    (list (list local-box
                                                box-name
                                                (cadr lambda-expr)
                                                (body->expr (cddr lambda-expr))))))
                      (finish members rest)))
                (finish members rest))))))

  (define (convert-group-prefix exprs env self-tail-prefix)
    (let ((prefix (extract-group-prefix exprs env)))
      (and prefix
            (let* ((members (car prefix))
                  (remaining (cdr prefix))
                  (member-names (map cadr members))
                  (shared-captures
                   (dedupe-symbols
                    (append-map
                     (lambda (member)
                       (free-vars (cadddr member)
                                  (append (caddr member) member-names)))
                     members)))
                  (capture-params
                   (make-env-vars "group.env." (length shared-captures)))
                  (capture-bindings
                   (map (lambda (fv capture-param)
                          (list fv `(local ,capture-param)))
                        shared-captures
                        capture-params))
                  (group-env (append capture-bindings env))
                  (converted-members
                   (map (lambda (member)
                          (let* ((box-var (car member))
                                 (member-name (cadr member))
                                 (params (caddr member))
                                 (body (cadddr member))
                                 (param-bindings
                                  (map (lambda (param)
                                         (list param `(local ,param)))
                                       params))
                             (body-env (append param-bindings group-env)))
                             (list box-var
                                   member-name
                                   params
                                   (convert body body-env '()))))
                         members))
                   (capture-values
                    (map (lambda (fv capture-param)
                           (list capture-param (lookup-repr fv env)))
                         shared-captures
                         capture-params)))
              (cons (cons `(group-closures ,converted-members ,capture-values)
                          (map (lambda (e) (convert e env self-tail-prefix)) remaining))
                    #t)))))

  (define (convert-sequence exprs env self-tail-prefix)
    (let ((group-result (convert-group-prefix exprs env self-tail-prefix)))
      (if group-result
          (car group-result)
          (map (lambda (e) (convert e env self-tail-prefix)) exprs))))

  (define (convert expr env self-tail-prefix)
    ;; env: association list mapping variable names to their representation
    ;; Either (local var) or (closure env-var) for captured variables.
    
    (cond
      ((symbol? expr)
       (let ((binding (assoc expr env)))
         (if binding
             (cadr binding)  ; Return the representation
             expr)))         ; Global/primitive
      
      ((literal-expr? expr)
       expr)
      
       ((pair? expr)
        (case (car expr)
          ((begin)
           `(begin ,@(convert-sequence (cdr expr) env self-tail-prefix)))
          
           ((primop)
            `(primop ,(cadr expr) 
                     ,@(map (lambda (e) (convert e env self-tail-prefix)) (cddr expr))))
          
          ((if)
           `(if ,(convert (cadr expr) env self-tail-prefix)
                ,(convert (caddr expr) env self-tail-prefix)
                ,(convert (cadddr expr) env self-tail-prefix)))
          
           ((let)
            (let* ((binding (caadr expr))
                   (var (car binding))
                   (val (cadr binding))
                   (body (body->expr (cddr expr)))
                   (val-converted (convert val env self-tail-prefix))
                   (new-env (cons (list var `(local ,var)) env))
                   (body-converted (convert body new-env self-tail-prefix)))
              `(let ((,var ,val-converted)) ,body-converted)))
           
            ((lambda)
            (let* ((params (cadr expr))
                   (body (body->expr (cddr expr)))
                   (fvs (free-vars body params))

                   (env-vars (make-env-vars "env." (length fvs)))

                  ;; Build new environment for lambda body
                   (param-bindings (map (lambda (p) (list p `(local ,p))) params))
                   (env-bindings (map (lambda (fv env-var)
                                        (list fv `(closure ,env-var)))
                                     fvs env-vars))
                  (new-env (append param-bindings env-bindings env))
                  (self-tail-env (map (lambda (env-var) `(local ,env-var)) env-vars))
                  
                  (body-converted (convert body new-env self-tail-env)))
             
             ;; Create closure structure
             `(make-closure 
              (lambda ,(append env-vars params) ,body-converted)
              ,@(map (lambda (fv) 
                       (let ((binding (assoc fv env)))
                         (if binding
                             (cadr binding)
                             fv)))  ; Global/primitive
                     fvs))))
         
           ((app)
            (let ((rator (cadr expr))
                  (rands (cddr expr)))
              `(closure-call ,(convert rator env self-tail-prefix)
                             ,@(map (lambda (e) (convert e env self-tail-prefix)) rands))))

            ((cons)
             `(cons ,(convert (cadr expr) env self-tail-prefix)
                    ,(convert (caddr expr) env self-tail-prefix)))

             ((self-tail-call)
              `(self-tail-call
               ,@self-tail-prefix
               ,@(map (lambda (e) (convert e env self-tail-prefix)) (cdr expr))))

          ((group-tail-call)
           `(group-tail-call
             ,(cadr expr)
             ,@(map (lambda (e) (convert e env self-tail-prefix)) (cddr expr))))

          ((group-closures)
           expr)
           
             ((box)
              `(box ,(convert (cadr expr) env self-tail-prefix)))
           
           ((unbox)
            `(unbox ,(convert (cadr expr) env self-tail-prefix)))

           ((car)
            `(car ,(convert (cadr expr) env self-tail-prefix)))

           ((cdr)
            `(cdr ,(convert (cadr expr) env self-tail-prefix)))

           ((pair?)
            `(pair? ,(convert (cadr expr) env self-tail-prefix)))

           ((null?)
            `(null? ,(convert (cadr expr) env self-tail-prefix)))
           
           ((set-box!)
            `(set-box! ,(convert (cadr expr) env self-tail-prefix)
                      ,(convert (caddr expr) env self-tail-prefix)))
          
          (else (error "Unknown expression in closure-convert" (car expr)))))
      
      (else (error "Invalid expression in closure-convert" expr))))
  
  (convert expr '() '()))

;;; ============================================================================
;;; Pass 3.5: Normalize for 0CFA and rewrite monomorphic closure calls
;;; The normalization here is intentionally lightweight: it gives every
;;; make-closure a stable procedure name and ensures closure-call operators and
;;; arguments are explicit simple names. That keeps the analysis small while
;;; preserving the source-shaped structure of the program.
;;; ============================================================================

(define (cfa-simple-expr? expr)
  (or (symbol? expr)
      (literal-expr? expr)
      (and (pair? expr) (memq (car expr) '(local closure)))))

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
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (normalize (cadr binding)))
                 (body-exprs (normalize-sequence (cddr expr))))
            `(let ((,var ,val)) ,@body-exprs)))
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
         ((cons set-box!)
          `(,(car expr)
            ,(normalize (cadr expr))
            ,(normalize (caddr expr))))
         ((box unbox car cdr pair? null?)
          `(,(car expr) ,(normalize (cadr expr))))
         ((local closure)
          expr)
         (else
          (error "Unknown expression in CFA normalization" (car expr)))))
      (else
       (error "Invalid expression in CFA normalization" expr))))

  (normalize expr))

(define (run-0cfa expr)
  (define procedures (make-hash-table))
  (define var-flow (make-hash-table))
  (define box-flow (make-hash-table))
  (define proc-results (make-hash-table))
  (define changed #f)

  (define (table-keys table)
    (map car (cdr table)))

  (define (flow-ref table key)
    (let ((value (hash-ref table key)))
      (if value value '())))

  (define (add-flow! table key values)
    (if (or (not key) (null? values))
        #f
        (let* ((current (flow-ref table key))
               (updated (dedupe-symbols (append current values))))
          (if (set-equal? current updated)
              #f
              (begin
                (hash-set! table key updated)
                (set! changed #t)
                #t)))))

  (define (repr-name expr)
    (cond
      ((symbol? expr) expr)
      ((and (pair? expr) (memq (car expr) '(local closure))) (cadr expr))
      (else #f)))

  (define (box-key expr)
    (repr-name expr))

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
            (hash-set! procedures
                       proc-name
                       (list (length captures)
                             (cadr lambda-expr)
                             (body->expr (cddr lambda-expr))))
            (collect-procedures (body->expr (cddr lambda-expr)))
            (for-each collect-procedures captures)))
         ((closure-call known-call self-tail-call)
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
         ((box unbox car cdr pair? null?)
          (collect-procedures (cadr expr)))
         ((local closure) 'done)
         (else
          (error "Unknown expression while collecting CFA procedures" (car expr)))))
      (else
       (error "Invalid expression while collecting CFA procedures" expr))))

  (collect-procedures expr)

  (define (analyze-expr expr current-proc)
    (cond
      ((literal-expr? expr) '())
      ((symbol? expr) (flow-ref var-flow expr))
      ((pair? expr)
       (case (car expr)
         ((local closure)
          (flow-ref var-flow (cadr expr)))
         ((begin)
          (let loop ((rest (cdr expr)) (last '()))
            (if (null? rest)
                last
                (loop (cdr rest)
                      (analyze-expr (car rest) current-proc)))))
         ((primop cons car cdr pair? null?)
          (begin
            (for-each (lambda (subexpr)
                        (analyze-expr subexpr current-proc))
                      (cdr expr))
            '()))
         ((if)
          (begin
            (analyze-expr (cadr expr) current-proc)
            (set-union (analyze-expr (caddr expr) current-proc)
                       (analyze-expr (cadddr expr) current-proc))))
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (value-set (analyze-expr (cadr binding) current-proc)))
            (add-flow! var-flow var value-set)
            (analyze-expr (body->expr (cddr expr)) current-proc)))
         ((make-closure)
          (let* ((proc-name (cadr expr))
                 (meta (hash-ref procedures proc-name))
                 (capture-count (car meta))
                 (params (cadr meta))
                 (captures (cdddr expr))
                 (env-params
                  (let loop ((rest params) (remaining capture-count) (result '()))
                    (if (= remaining 0)
                        (reverse result)
                        (loop (cdr rest)
                              (- remaining 1)
                              (cons (car rest) result))))))
            (let loop ((env-rest env-params) (capture-rest captures))
              (if (or (null? env-rest) (null? capture-rest))
                  'done
                  (begin
                    (add-flow! var-flow
                               (car env-rest)
                               (analyze-expr (car capture-rest) current-proc))
                    (loop (cdr env-rest) (cdr capture-rest)))))
            (list proc-name)))
         ((closure-call)
          (let* ((proc-set (analyze-expr (cadr expr) current-proc))
                 (arg-sets (map (lambda (arg)
                                  (analyze-expr arg current-proc))
                                (cddr expr))))
            (for-each
             (lambda (proc-name)
               (let* ((meta (hash-ref procedures proc-name))
                      (capture-count (car meta))
                      (params (cadr meta))
                      (actual-params (list-tail params capture-count)))
                 (let loop ((param-rest actual-params) (arg-rest arg-sets))
                   (if (or (null? param-rest) (null? arg-rest))
                       'done
                       (begin
                         (add-flow! var-flow (car param-rest) (car arg-rest))
                         (loop (cdr param-rest) (cdr arg-rest)))))))
             proc-set)
            (let loop ((rest proc-set) (result '()))
              (if (null? rest)
                  result
                  (loop (cdr rest)
                        (set-union result
                                   (flow-ref proc-results (car rest))))))))
          ((self-tail-call)
           (let ((meta (and current-proc (hash-ref procedures current-proc))))
             (if (not meta)
                 '()
                 (let* ((capture-count (car meta))
                        (params (cadr meta))
                        (actual-params (list-tail params capture-count))
                        (actual-arg-sets
                         (map (lambda (arg)
                                (analyze-expr arg current-proc))
                              (list-tail (cdr expr) capture-count))))
                   (let loop ((param-rest actual-params) (arg-rest actual-arg-sets))
                     (if (or (null? param-rest) (null? arg-rest))
                         'done
                         (begin
                           (add-flow! var-flow (car param-rest) (car arg-rest))
                           (loop (cdr param-rest) (cdr arg-rest)))))
                   (flow-ref proc-results current-proc)))))
         ((group-tail-call)
          (begin
            (for-each (lambda (arg)
                        (analyze-expr arg current-proc))
                      (cddr expr))
            '()))
         ((group-closures)
          (begin
            (for-each (lambda (capture-spec)
                        (analyze-expr (cadr capture-spec) current-proc))
                      (caddr expr))
            '()))
         ((box)
          (begin
            (analyze-expr (cadr expr) current-proc)
            '()))
         ((unbox)
          (let ((key (box-key (cadr expr))))
            (analyze-expr (cadr expr) current-proc)
            (if key
                (flow-ref box-flow key)
                '())))
         ((set-box!)
          (let ((value-set (analyze-expr (caddr expr) current-proc))
                (key (box-key (cadr expr))))
            (analyze-expr (cadr expr) current-proc)
            (add-flow! box-flow key value-set)
            value-set))
         (else
          (error "Unknown expression in 0CFA" (car expr)))))
      (else
       (error "Invalid expression in 0CFA" expr))))

  (let loop ()
    (set! changed #f)

    ;; Re-run the program body and all procedure bodies until the abstract
    ;; environments and result sets stop growing.
    (analyze-expr expr #f)
    (for-each
     (lambda (proc-name)
       (let* ((meta (hash-ref procedures proc-name))
              (body (caddr meta))
              (result-set (analyze-expr body proc-name)))
         (add-flow! proc-results proc-name result-set)))
     (table-keys procedures))
    (if changed
        (loop)
        (list procedures var-flow box-flow proc-results))))

(define (rewrite-known-calls expr analysis)
  (let ((procedures (car analysis))
        (var-flow (cadr analysis))
        (box-flow (caddr analysis)))
    (define (flow-ref table key)
      (let ((value (hash-ref table key)))
        (if value value '())))

    (define (repr-name expr)
      (cond
        ((symbol? expr) expr)
        ((and (pair? expr) (memq (car expr) '(local closure))) (cadr expr))
        (else #f)))

    (define (box-key expr)
      (repr-name expr))

    (define (closure-set expr)
      (cond
        ((symbol? expr) (flow-ref var-flow expr))
        ((literal-expr? expr) '())
        ((pair? expr)
         (case (car expr)
           ((local closure)
            (flow-ref var-flow (cadr expr)))
           ((unbox)
            (let ((key (box-key (cadr expr))))
              (if key
                  (flow-ref box-flow key)
                  '())))
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
           (else '())))
        (else '())))

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
            `(let (,(list (car (caadr expr))
                          (rewrite (cadr (caadr expr)))))
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
                       (hash-ref procedures (car targets)))
                  (let* ((proc-name (car targets))
                         (meta (hash-ref procedures proc-name))
                         (capture-count (car meta)))
                    `(known-call ,proc-name ,capture-count ,rator ,@args))
                  `(closure-call ,rator ,@args))))
           ((known-call)
            `(known-call ,(cadr expr)
                         ,(caddr expr)
                         ,(rewrite (cadddr expr))
                         ,@(map rewrite (cddddr expr))))
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
           ((cons set-box!)
            `(,(car expr) ,(rewrite (cadr expr)) ,(rewrite (caddr expr))))
           ((box unbox car cdr pair? null? local closure)
            `(,(car expr) ,(rewrite (cadr expr))))
           (else
            (error "Unknown expression in known-call rewrite" (car expr)))))
        (else
         (error "Invalid expression in known-call rewrite" expr))))

    (rewrite expr)))

;;; ============================================================================
;;; Pass 4: Convert to Three-Address Code (TAC)
;;; Lowers expression-oriented code into a flat, explicit instruction stream.
;;;
;;; TAC makes evaluation order, temporary values, branches, and returns
;;; concrete. This is the point where expression trees become something closer
;;; to an imperative program.
;;; ============================================================================

(define-record-type <procedure>
  (make-procedure name params instructions)
  procedure?
  (name procedure-name)
  (params procedure-params)
  (instructions procedure-instructions))

(define-record-type <machine-block>
  (make-machine-block label instructions successors)
  machine-block?
  (label machine-block-label)
  (instructions machine-block-instructions)
  (successors machine-block-successors))

(define-record-type <machine-procedure>
  (make-machine-procedure name params param-locations blocks homes frame-slots used-registers)
  machine-procedure?
  (name machine-procedure-name)
  (params machine-procedure-params)
  (param-locations machine-procedure-param-locations)
  (blocks machine-procedure-blocks)
  (homes machine-procedure-homes)
  (frame-slots machine-procedure-frame-slots)
  (used-registers machine-procedure-used-registers))

(define (expr->tac expr)
  ;; Convert an expression to TAC form.
  ;; Returns: (values instructions procedures)
  
  (define temp-counter 0)
  (define (fresh-temp)
    (set! temp-counter (+ temp-counter 1))
    (string->symbol (string-append "t" (number->string temp-counter))))
  
  (define proc-counter 0)
  (define (fresh-proc)
    (set! proc-counter (+ proc-counter 1))
    (string->symbol (string-append "proc" (number->string proc-counter))))
  
  (define (simple? expr)
    ;; Check if expression is simple (doesn't need temporaries)
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
          ((app closure-call known-call set-box! cons)
           (all (lambda (e) (cluster-body-compatible? e names)) (cdr expr)))
          ((box unbox car cdr pair? null?)
           (cluster-body-compatible? (cadr expr) names))
          ((local closure) #t)
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
          ((begin app closure-call known-call set-box! cons)
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
          ((box unbox car cdr pair? null?)
           (collect-group-tail-targets (cadr expr)))
          (else '())))
      (else '())))

  (define (all-same-member-arity? members)
    (or (null? members)
        (let ((arity (length (cadr (car members)))))
          (all (lambda (member)
                 (= (length (cadr member)) arity))
               members))))

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
                 (all-same-member-arity? members)
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
                                 (caddr (car members))))
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
             (group-context
              (map (lambda (member label)
                     (list (cadr member) label))
                   members
                   member-labels))
             (capture-param-names (map car capture-specs))
             (capture-value-exprs (map cadr capture-specs)))
        (let-values (((capture-instrs capture-vars capture-procedures)
                      (convert-list capture-value-exprs)))
          (let ((init-instrs
                 (let loop ((rest members) (index 0) (instrs capture-instrs))
                   (if (null? rest)
                       instrs
                       (let ((closure-temp (fresh-temp))
                             (box-name (car (car rest))))
                         (loop (cdr rest)
                               (+ index 1)
                               (append instrs
                                       (list `(assign ,closure-temp
                                                      (make-closure ,cluster-proc ,index ,@capture-vars))
                                             `(set-box! ,box-name ,closure-temp)))))))))
            (let loop ((rest members)
                       (labels member-labels)
                       (instrs (build-dispatch-instructions entry-tag
                                                           dispatch-label
                                                           member-labels))
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
                            (append procedures body-procedures))))))))))
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
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (cadr binding))
                 (body (body->expr (cddr expr))))
            (let-values (((val-instrs val-result val-procedures)
                          (convert-value val #f))
                         ((body-instrs body-procedures)
                          (convert-tail body
                                        current-params
                                        current-entry-label
                                        group-context
                                        shared-params)))
              (values (append val-instrs
                              (list `(assign ,var ,val-result))
                              body-instrs)
                      (append val-procedures body-procedures)))))
         
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
                     (entry (assoc target group-context)))
                (when (not entry)
                  (error "Unknown group-tail-call target" target))
                (when (not (= (length args) (length shared-params)))
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
    ;; dest: optional destination variable
    ;; Returns: (values instructions result-var procedures)
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
           (convert-binary-value-op 'cons (cadr expr) (caddr expr)))

          ((box)
           (convert-unary-value-op 'box (cadr expr)))
           
          ((unbox car cdr pair? null?)
           (convert-unary-value-op (car expr) (cadr expr)))
         
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
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (cadr binding))
                 (body (body->expr (cddr expr))))
            (let-values (((val-instrs val-result val-procedures)
                          (convert-value val #f)))
              (let ((assign-instr `(assign ,var ,val-result)))
                (let-values (((body-instrs body-result body-procedures)
                              (convert-value body dest)))
                  (values (append val-instrs (list assign-instr) body-instrs)
                          body-result
                          (append val-procedures body-procedures)))))))
         
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
         
         ((local closure)
          (values '() (cadr expr) '()))
         
         (else
          (error "Unknown expression in expr->tac" (car expr)))))
      
      (else
       (error "Invalid expression in expr->tac" expr))))
  
  (convert-tail expr '() #f #f #f))

;;; ============================================================================
;;; Data Structures for CFG
;;; ============================================================================

;; We need to define the record type differently for mutable fields
;; In standard Scheme, we can use a constructor with mutable fields
(define-record-type <basic-block>
  (make-basic-block label instructions)
  basic-block?
  (label basic-block-label)
  (instructions basic-block-instructions)
  (successors basic-block-successors set-basic-block-successors!))

;;; ============================================================================
;;; Pass 5: Build Control Flow Graph (CFG)
;;; Groups TAC instructions into basic blocks and records control-flow edges.
;;;
;;; The CFG is the boundary between the mostly source-shaped middle end and the
;;; backend. Once code is in CFG form, later stages can reason in terms of
;;; blocks, successors, liveness, and register allocation.
;;; ============================================================================

(define (build-cfg tac-instrs)
  ;; Build proper control flow graph from TAC instructions
  ;; Returns list of basic blocks in order
  
  (define (terminator? instr)
    (and (pair? instr)
         (memq (car instr) '(if goto return tail-call))))

  (define (is-leader? index instrs)
    ;; Determine if instruction at index is a basic block leader
    (let ((instr (list-ref instrs index)))
      (or (= index 0)  ; First instruction is always a leader
          (and (pair? instr) (eq? (car instr) 'label))  ; Labels are leaders
          (and (> index 0)  ; Instruction after a terminator is a leader
               (terminator? (list-ref instrs (- index 1)))))))
  
  (define (split-into-blocks instrs)
    ;; Split instructions into basic blocks at leaders
    (let* ((len (length instrs))
           (leaders (make-vector len #f)))
      
      ;; Mark all leaders
      (do ((i 0 (+ i 1)))
          ((= i len))
        (vector-set! leaders i (is-leader? i instrs)))
      
      ;; Collect blocks
      (let loop ((i 0) (blocks '()) (current-block '()) (current-label #f))
        (cond
          ((= i len)
           ;; End of instructions - finish last block
           (if (null? current-block)
               (reverse blocks)
               (reverse (cons (make-basic-block current-label 
                                               (reverse current-block))
                             blocks))))
          
          ((vector-ref leaders i)
           ;; Start of a new block
           (if (null? current-block)
               ;; First block
               (let ((instr (list-ref instrs i)))
                 (loop (+ i 1)
                       blocks
                       (list instr)
                       (if (and (pair? instr) (eq? (car instr) 'label))
                           (cadr instr)
                           #f)))
               ;; Finish current block and start new one
                (let ((instr (list-ref instrs i)))
                  (loop (+ i 1)
                        (cons (make-basic-block current-label
                                                (reverse current-block))
                              blocks)
                        (list instr)
                        (if (and (pair? instr) (eq? (car instr) 'label))
                            (cadr instr)
                            #f)))))
          
          (else
           ;; Continue current block
           (loop (+ i 1)
                 blocks
                 (cons (list-ref instrs i) current-block)
                 current-label))))))
  
  (define (find-successors blocks)
    ;; Determine successors for each basic block
    (let ((label->block (make-hash-table)))
      
      ;; Build mapping from label to block index
      (do ((i 0 (+ i 1)) (block-list blocks (cdr block-list)))
          ((null? block-list))
        (let* ((block (car block-list))
               (label (basic-block-label block)))
          (when label
            (hash-set! label->block label i))))
      
      ;; Determine successors for each block
      (do ((i 0 (+ i 1)) (block-list blocks (cdr block-list)))
          ((null? block-list))
        (let* ((block (car block-list))
               (instrs (basic-block-instructions block))
               (last-instr (if (null? instrs) #f (car (reverse instrs)))))
          
          (cond
            ((not last-instr)
             ;; Empty block - no successors
             (set-basic-block-successors! block '()))
            
             ((and (pair? last-instr) (eq? (car last-instr) 'if))
              ;; Conditional branch
              (let ((then-label (caddr last-instr))
                    (else-label (cadddr last-instr)))
               (set-basic-block-successors! 
                block 
                (list (hash-ref label->block then-label)
                      (hash-ref label->block else-label)))))
            
             ((and (pair? last-instr) (eq? (car last-instr) 'goto))
              ;; Unconditional jump
              (let ((target-label (cadr last-instr)))
                (set-basic-block-successors! 
                 block 
                 (list (hash-ref label->block target-label)))))
             
              ((and (pair? last-instr) (memq (car last-instr) '(return tail-call)))
               ;; Function/program exit
               (set-basic-block-successors! block '()))
             
             ((= i (- (length blocks) 1))
              ;; Last block with no jump - no successors
              (set-basic-block-successors! block '()))
            
            (else
             ;; Fall through to next block
             (set-basic-block-successors! block (list (+ i 1)))))))
      
      blocks))
  
  ;; Main CFG construction
  (let ((blocks (split-into-blocks tac-instrs)))
     (find-successors blocks)))

;;; ============================================================================
;;; Backend: instruction selection and linear-scan allocation
;;; The backend proceeds in three conceptual steps:
;;;
;;;   1. instruction selection:
;;;      TAC operations become machine-like instructions with symbolic homes
;;;      (virtual registers / abstract operands),
;;;   2. analysis and allocation:
;;;      liveness is computed and linear scan assigns registers or stack slots,
;;;   3. finalization:
;;;      calling-convention details, prologue/epilogue code, and helper calls
;;;      are made explicit before assembly emission.
;;; ============================================================================

(define aarch64-arg-registers '(x0 x1 x2 x3 x4 x5 x6 x7))
(define aarch64-return-register 'x0)
(define aarch64-callee-saved '(x19 x20 x21 x22 x23 x24 x25 x26 x27 x28))

(define (set-union xs ys)
  (dedupe-symbols (append xs ys)))

(define (set-difference xs ys)
  (let loop ((rest xs) (result '()))
    (cond
      ((null? rest) (reverse result))
      ((memq (car rest) ys)
       (loop (cdr rest) result))
      (else
       (loop (cdr rest) (cons (car rest) result))))))

(define (set-equal? xs ys)
  (and (null? (set-difference xs ys))
       (null? (set-difference ys xs))))

(define (arg-location index)
  (if (< index (length aarch64-arg-registers))
      `(arg-register ,(list-ref aarch64-arg-registers index))
      `(stack-arg ,(- index (length aarch64-arg-registers)))))

(define (make-param-locations params)
  (let loop ((rest params) (index 0) (result '()))
    (if (null? rest)
        (reverse result)
        (loop (cdr rest)
              (+ index 1)
              (cons (list (car rest) (arg-location index)) result)))))

(define (stack-align n)
  (* 16 (quotient (+ n 15) 16)))

(define (call-stack-arg-count instr)
  (case (car instr)
    ((call)
     (max 0 (- (length (cdddr instr)) (length aarch64-arg-registers))))
    ((call-known)
     (max 0 (- (length (cdddr instr)) (length aarch64-arg-registers))))
    ((tail-call)
     (max 0 (- (length (cddr instr)) (length aarch64-arg-registers))))
    ((tail-call-known)
     (max 0 (- (length (cddr instr)) (length aarch64-arg-registers))))
    (else 0)))

(define (select-machine-instruction instr)
  (define (select-assignment-rhs dst rhs)
    (cond
      ((or (symbol? rhs) (literal-expr? rhs))
       (list `(move ,dst ,rhs)))
      ((and (pair? rhs) (eq? (car rhs) 'primop))
       (list `(binop ,(cadr rhs) ,dst ,@(cddr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'cons))
       (list `(alloc-pair ,dst ,(cadr rhs) ,(caddr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'box))
       (list `(alloc-box ,dst ,(cadr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'unbox))
       (list `(load-box ,dst ,(cadr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'car))
       (list `(load-car ,dst ,(cadr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'cdr))
       (list `(load-cdr ,dst ,(cadr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'pair?))
       (list `(is-pair ,dst ,(cadr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'null?))
       (list `(is-null ,dst ,(cadr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'closure-env-ref))
       (list `(load-closure-env ,dst ,(cadr rhs) ,(caddr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'make-closure))
       (list `(alloc-closure ,dst ,@(cdr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'closure-call))
       (list `(call ,dst ,@(cdr rhs))))
      ((and (pair? rhs) (eq? (car rhs) 'direct-call))
       (list `(call-known ,dst ,@(cdr rhs))))
      (else
       (error "Unknown assignment rhs during instruction selection" rhs))))
  (cond
    ((not (pair? instr))
     (error "Invalid TAC instruction for instruction selection" instr))
    ((eq? (car instr) 'label) '())
    ((eq? (car instr) 'assign)
     (let ((dst (cadr instr))
           (rhs (caddr instr)))
       (select-assignment-rhs dst rhs)))
    ((eq? (car instr) 'if)
     (list `(branch-if ,(cadr instr) ,(caddr instr) ,(cadddr instr))))
    ((eq? (car instr) 'goto)
     (list `(jump ,(cadr instr))))
    ((eq? (car instr) 'return)
     (list `(ret ,(cadr instr))))
    ((eq? (car instr) 'tail-call)
     (list `(tail-call ,@(cdr instr))))
    ((eq? (car instr) 'direct-tail-call)
     (list `(tail-call-known ,@(cdr instr))))
    ((eq? (car instr) 'set-box!)
     (list `(store-box ,(cadr instr) ,(caddr instr))))
    (else
     (error "Unknown TAC instruction in instruction selection" instr))))

(define (select-machine-block block initial-instrs)
  (make-machine-block
   (basic-block-label block)
   (append initial-instrs
           (append-map select-machine-instruction
                       (basic-block-instructions block)))
   (basic-block-successors block)))

(define (select-machine-procedure name params cfg)
  (let ((param-locations (make-param-locations params)))
    (let loop ((blocks cfg)
               (first? #t)
               (result '()))
      (if (null? blocks)
          (make-machine-procedure name
                                  params
                                  param-locations
                                  (reverse result)
                                  '()
                                  0
                                  '())
          (let* ((initial-instrs
                  (if first?
                      (map (lambda (binding)
                             `(move-in ,(car binding) ,(cadr binding)))
                           param-locations)
                      '()))
                 (selected-block
                  (select-machine-block (car blocks) initial-instrs)))
            (loop (cdr blocks)
                  #f
                  (cons selected-block result)))))))

(define (machine-instr-uses instr)
  (case (car instr)
    ((move-in) '())
    ((move) (if (symbol? (caddr instr)) (list (caddr instr)) '()))
    ((binop)
     (append (if (symbol? (cadddr instr)) (list (cadddr instr)) '())
             (if (symbol? (car (cddddr instr))) (list (car (cddddr instr))) '())))
    ((alloc-box load-box load-car load-cdr is-pair is-null load-closure-env)
       (if (symbol? (caddr instr)) (list (caddr instr)) '()))
    ((alloc-pair)
     (append (if (symbol? (caddr instr)) (list (caddr instr)) '())
             (if (symbol? (cadddr instr)) (list (cadddr instr)) '())))
    ((store-box)
      (append (if (symbol? (cadr instr)) (list (cadr instr)) '())
              (if (symbol? (caddr instr)) (list (caddr instr)) '())))
    ((alloc-closure)
     (let loop ((rest (cdddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((call)
     (let ((closure (caddr instr))
            (args (cdddr instr)))
        (append (if (symbol? closure) (list closure) '())
                (let loop ((rest args) (result '()))
                 (if (null? rest)
                     (reverse result)
                     (loop (cdr rest)
                           (if (symbol? (car rest))
                                (cons (car rest) result)
                                result)))))))
    ((call-known)
     (let loop ((rest (cdddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((tail-call)
     (let ((closure (cadr instr))
            (args (cddr instr)))
        (append (if (symbol? closure) (list closure) '())
               (let loop ((rest args) (result '()))
                 (if (null? rest)
                     (reverse result)
                     (loop (cdr rest)
                           (if (symbol? (car rest))
                                (cons (car rest) result)
                                result)))))))
    ((tail-call-known)
     (let loop ((rest (cddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((branch-if ret)
     (if (symbol? (cadr instr)) (list (cadr instr)) '()))
    ((jump) '())
    (else (error "Unknown machine instruction in use analysis" instr))))

(define (machine-instr-defs instr)
  (case (car instr)
    ((move-in move alloc-pair alloc-box load-box load-car load-cdr
              is-pair is-null load-closure-env alloc-closure call call-known)
      (list (cadr instr)))
    ((binop)
      (list (caddr instr)))
    ((store-box branch-if jump ret tail-call tail-call-known) '())
    (else (error "Unknown machine instruction in def analysis" instr))))

(define (machine-block-use block)
  (let loop ((instrs (machine-block-instructions block))
             (defs '())
             (uses '()))
    (if (null? instrs)
        uses
        (let* ((instr (car instrs))
               (instr-uses (set-difference (machine-instr-uses instr) defs))
               (instr-defs (machine-instr-defs instr)))
          (loop (cdr instrs)
                (set-union defs instr-defs)
                (set-union uses instr-uses))))))

(define (machine-block-def block)
  (let loop ((instrs (machine-block-instructions block)) (defs '()))
    (if (null? instrs)
        defs
        (loop (cdr instrs)
              (set-union defs (machine-instr-defs (car instrs)))))))

(define (compute-liveness blocks)
  (let* ((count (length blocks))
         (use-vec (list->vector (map machine-block-use blocks)))
         (def-vec (list->vector (map machine-block-def blocks)))
         (in-vec (make-vector count '()))
         (out-vec (make-vector count '())))
    (let loop ()
      (let ((changed #f))
        (do ((i (- count 1) (- i 1)))
            ((< i 0))
          (let* ((block (list-ref blocks i))
                 (successors (machine-block-successors block))
                 (new-out
                  (let succ-loop ((rest successors) (result '()))
                    (if (null? rest)
                        result
                        (succ-loop (cdr rest)
                                   (set-union result
                                              (vector-ref in-vec (car rest)))))))
                 (new-in
                  (set-union (vector-ref use-vec i)
                             (set-difference new-out (vector-ref def-vec i)))))
            (if (not (set-equal? new-out (vector-ref out-vec i)))
                (begin
                  (vector-set! out-vec i new-out)
                  (set! changed #t)))
            (if (not (set-equal? new-in (vector-ref in-vec i)))
                (begin
                  (vector-set! in-vec i new-in)
                  (set! changed #t)))))
        (if changed
            (loop)
            (values in-vec out-vec))))))

(define (interval-start interval) (cadr interval))
(define (interval-end interval) (caddr interval))

(define (update-interval! table var point)
  (let ((entry (assoc var table)))
    (if entry
        (let ((interval (cdr entry)))
          (set-car! interval (min (car interval) point))
          (set-cdr! interval (max (cdr interval) point)))
        (set! table (cons (cons var (cons point point)) table))))
  table)

(define (collect-intervals blocks in-vec out-vec)
  (let loop-blocks ((remaining blocks)
                    (index 0)
                    (point 0)
                    (intervals '()))
    (if (null? remaining)
        (let convert ((rest intervals) (result '()))
          (if (null? rest)
              result
              (let* ((entry (car rest))
                     (range (cdr entry)))
                (convert (cdr rest)
                         (cons (list (car entry) (car range) (cdr range))
                               result)))))
        (let* ((block (car remaining))
               (block-start point)
               (intervals-with-live-in
                (let live-in-loop ((vars (vector-ref in-vec index))
                                   (current intervals))
                  (if (null? vars)
                      current
                      (live-in-loop (cdr vars)
                                    (update-interval! current (car vars) block-start)))))
               (instrs (machine-block-instructions block)))
          (let loop-instrs ((rest instrs)
                            (next-point point)
                            (current intervals-with-live-in))
            (if (null? rest)
                (let* ((block-end (if (= next-point block-start)
                                      block-start
                                      (- next-point 1)))
                       (intervals-with-live-out
                        (let live-out-loop ((vars (vector-ref out-vec index))
                                            (updated current))
                          (if (null? vars)
                              updated
                              (live-out-loop (cdr vars)
                                             (update-interval! updated (car vars) block-end))))))
                  (loop-blocks (cdr remaining)
                               (+ index 1)
                               next-point
                               intervals-with-live-out))
                (let* ((instr (car rest))
                       (uses (machine-instr-uses instr))
                       (defs (machine-instr-defs instr))
                       (with-uses
                        (let use-loop ((vars uses) (updated current))
                          (if (null? vars)
                              updated
                              (use-loop (cdr vars)
                                        (update-interval! updated (car vars) next-point)))))
                       (with-defs
                        (let def-loop ((vars defs) (updated with-uses))
                          (if (null? vars)
                              updated
                              (def-loop (cdr vars)
                                        (update-interval! updated (car vars) next-point))))))
                  (loop-instrs (cdr rest)
                               (+ next-point 1)
                               with-defs))))))))

(define (insert-by-start interval intervals)
  (if (null? intervals)
      (list interval)
      (if (< (interval-start interval) (interval-start (car intervals)))
          (cons interval intervals)
          (cons (car intervals)
                (insert-by-start interval (cdr intervals))))))

(define (sort-intervals-by-start intervals)
  (let loop ((rest intervals) (result '()))
    (if (null? rest)
        result
        (loop (cdr rest)
              (insert-by-start (car rest) result)))))

(define (insert-active interval active)
  (if (null? active)
      (list interval)
      (if (< (interval-end interval) (interval-end (car active)))
          (cons interval active)
          (cons (car active)
                (insert-active interval (cdr active))))))

(define (register-order register)
  (let loop ((rest aarch64-callee-saved) (index 0))
    (cond
      ((null? rest) index)
      ((eq? (car rest) register) index)
      (else (loop (cdr rest) (+ index 1))))))

(define (insert-register register registers)
  (if (null? registers)
      (list register)
      (if (< (register-order register) (register-order (car registers)))
          (cons register registers)
          (cons (car registers)
                (insert-register register (cdr registers))))))

(define (linear-scan-allocate intervals)
  (let loop ((remaining (sort-intervals-by-start intervals))
             (active '())
             (free-registers aarch64-callee-saved)
             (homes '())
             (next-slot 0))
    (if (null? remaining)
        (values homes next-slot)
        (let* ((current (car remaining))
               (start (interval-start current)))
          (let expire ((rest active)
                       (still-active '())
                       (available free-registers))
            (if (null? rest)
                (if (null? available)
                    (loop (cdr remaining)
                          still-active
                          available
                          (cons (cons (car current) `(stack-slot ,next-slot)) homes)
                          (+ next-slot 1))
                    (let* ((register (car available))
                           (new-active
                            (insert-active
                             (list (car current)
                                   (interval-start current)
                                   (interval-end current)
                                   register)
                             still-active)))
                      (loop (cdr remaining)
                            new-active
                            (cdr available)
                            (cons (cons (car current) `(register ,register)) homes)
                            next-slot)))
                (let* ((entry (car rest))
                       (end (caddr entry))
                       (register (cadddr entry)))
                  (if (< end start)
                      (expire (cdr rest)
                              still-active
                              (insert-register register available))
                      (expire (cdr rest)
                              (insert-active entry still-active)
                              available)))))))))

(define (lookup-home homes operand)
  (if (symbol? operand)
      (let ((binding (assoc operand homes)))
        (if binding
            (cdr binding)
            operand))
      operand))

(define (rewrite-machine-instruction instr homes)
  (case (car instr)
    ((move-in)
     `(move-in ,(lookup-home homes (cadr instr)) ,(caddr instr)))
    ((move)
     `(move ,(lookup-home homes (cadr instr))
            ,(lookup-home homes (caddr instr))))
    ((binop)
     `(binop ,(cadr instr)
             ,(lookup-home homes (caddr instr))
             ,(lookup-home homes (cadddr instr))
             ,(lookup-home homes (car (cddddr instr)))))
    ((alloc-box)
     `(alloc-box ,(lookup-home homes (cadr instr))
                 ,(lookup-home homes (caddr instr))))
    ((alloc-pair)
     `(alloc-pair ,(lookup-home homes (cadr instr))
                  ,(lookup-home homes (caddr instr))
                  ,(lookup-home homes (cadddr instr))))
    ((load-box)
     `(load-box ,(lookup-home homes (cadr instr))
                ,(lookup-home homes (caddr instr))))
    ((load-closure-env)
     `(load-closure-env ,(lookup-home homes (cadr instr))
                        ,(lookup-home homes (caddr instr))
                        ,(cadddr instr)))
    ((load-car)
     `(load-car ,(lookup-home homes (cadr instr))
                ,(lookup-home homes (caddr instr))))
    ((load-cdr)
     `(load-cdr ,(lookup-home homes (cadr instr))
                ,(lookup-home homes (caddr instr))))
    ((is-pair)
     `(is-pair ,(lookup-home homes (cadr instr))
               ,(lookup-home homes (caddr instr))))
    ((is-null)
     `(is-null ,(lookup-home homes (cadr instr))
               ,(lookup-home homes (caddr instr))))
    ((store-box)
     `(store-box ,(lookup-home homes (cadr instr))
                  ,(lookup-home homes (caddr instr))))
    ((alloc-closure)
     `(alloc-closure ,(lookup-home homes (cadr instr))
                     ,(caddr instr)
                     ,@(map (lambda (operand) (lookup-home homes operand))
                            (cdddr instr))))
    ((call)
     `(call ,(lookup-home homes (cadr instr))
            ,(lookup-home homes (caddr instr))
            ,@(map (lambda (operand) (lookup-home homes operand))
                   (cdddr instr))))
    ((call-known)
     `(call-known ,(lookup-home homes (cadr instr))
                  ,(caddr instr)
                  ,@(map (lambda (operand) (lookup-home homes operand))
                         (cdddr instr))))
    ((tail-call)
     `(tail-call ,(lookup-home homes (cadr instr))
                 ,@(map (lambda (operand) (lookup-home homes operand))
                        (cddr instr))))
    ((tail-call-known)
     `(tail-call-known ,(cadr instr)
                       ,@(map (lambda (operand) (lookup-home homes operand))
                              (cddr instr))))
    ((branch-if)
     `(branch-if ,(lookup-home homes (cadr instr))
                 ,(caddr instr)
                 ,(cadddr instr)))
    ((jump) instr)
    ((ret)
     `(ret ,(lookup-home homes (cadr instr))))
    (else
     (error "Unknown machine instruction during allocation" instr))))

(define (allocate-machine-procedure proc)
  (let ((blocks (machine-procedure-blocks proc)))
    (let-values (((in-vec out-vec) (compute-liveness blocks)))
      (let-values (((homes frame-slots)
                    (linear-scan-allocate
                     (collect-intervals blocks in-vec out-vec))))
        (let ((rewritten-blocks
               (map (lambda (block)
                      (make-machine-block
                       (machine-block-label block)
                       (map (lambda (instr)
                              (rewrite-machine-instruction instr homes))
                            (machine-block-instructions block))
                       (machine-block-successors block)))
                    blocks))
              (used-registers
               (dedupe-symbols
                (let loop ((rest homes) (result '()))
                  (if (null? rest)
                      result
                      (let ((home (cdar rest)))
                        (loop (cdr rest)
                              (if (and (pair? home) (eq? (car home) 'register))
                                  (cons (cadr home) result)
                                  result))))))))
          (make-machine-procedure
           (machine-procedure-name proc)
           (machine-procedure-params proc)
           (machine-procedure-param-locations proc)
           rewritten-blocks
           homes
           frame-slots
           used-registers))))))

(define (max-outgoing-stack-args blocks)
  (let block-loop ((remaining blocks) (best 0))
    (if (null? remaining)
        best
        (let instr-loop ((instrs (machine-block-instructions (car remaining)))
                         (block-best best))
          (if (null? instrs)
              (block-loop (cdr remaining) block-best)
              (instr-loop (cdr instrs)
                          (max block-best
                               (call-stack-arg-count (car instrs)))))))))

(define (stack-size-for proc)
  (stack-align
   (* 8 (+ (machine-procedure-frame-slots proc)
           (length (machine-procedure-used-registers proc))
           (max-outgoing-stack-args (machine-procedure-blocks proc))))))

(define (lower-arg-moves operands)
  (let loop ((rest operands) (index 0) (result '()))
    (if (null? rest)
        (reverse result)
        (loop (cdr rest)
              (+ index 1)
              (cons `(move-out ,(arg-location index) ,(car rest))
                    result)))))

(define (finalize-machine-instruction instr stack-size saved-registers)
  (case (car instr)
    ((move-in)
     (list `(move ,(cadr instr) ,(caddr instr))))
    ((call)
     (let ((dst (cadr instr))
           (closure (caddr instr))
           (args (cdddr instr)))
       (append (lower-arg-moves args)
                (list `(move-out ,(arg-location (length args)) ,closure)
                      `(call-indirect ,(length args))
                      `(move ,dst (arg-register ,aarch64-return-register))))))
    ((call-known)
     (let ((dst (cadr instr))
           (proc-name (caddr instr))
           (args (cdddr instr)))
       (append (lower-arg-moves args)
               (list `(call-label ,proc-name)
                     `(move ,dst (arg-register ,aarch64-return-register))))))
    ((tail-call)
     (let ((closure (cadr instr))
           (args (cddr instr)))
       (append (lower-arg-moves args)
               (list `(move-out ,(arg-location (length args)) ,closure)
                      `(restore-callee-saved ,saved-registers)
                      `(deallocate-frame ,stack-size)
                      `(tail-call-indirect ,(length args))))))
    ((tail-call-known)
     (let ((proc-name (cadr instr))
           (args (cddr instr)))
       (append (lower-arg-moves args)
               (list `(restore-callee-saved ,saved-registers)
                     `(deallocate-frame ,stack-size)
                     `(tail-call-label ,proc-name)))))
    ((ret)
     (list `(move-out (arg-register ,aarch64-return-register) ,(cadr instr))
           `(restore-callee-saved ,saved-registers)
           `(deallocate-frame ,stack-size)
           '(ret)))
    (else
     (list instr))))

(define (finalize-machine-procedure proc)
  (let* ((saved-registers (machine-procedure-used-registers proc))
         (stack-size (stack-size-for proc))
         (final-blocks
          (let loop ((remaining (machine-procedure-blocks proc))
                     (first? #t)
                     (result '()))
            (if (null? remaining)
                (reverse result)
                (let* ((block (car remaining))
                       (prefix
                        (if first?
                            (list `(allocate-frame ,stack-size)
                                  `(save-callee-saved ,saved-registers))
                            '()))
                       (final-instrs
                        (append prefix
                                (append-map
                                 (lambda (instr)
                                   (finalize-machine-instruction
                                    instr
                                    stack-size
                                    saved-registers))
                                 (machine-block-instructions block)))))
                  (loop (cdr remaining)
                        #f
                        (cons (make-machine-block
                               (machine-block-label block)
                               final-instrs
                               (machine-block-successors block))
                              result)))))))
    (make-machine-procedure
     (machine-procedure-name proc)
     (machine-procedure-params proc)
     (machine-procedure-param-locations proc)
     final-blocks
     (machine-procedure-homes proc)
     (machine-procedure-frame-slots proc)
     saved-registers)))

(define (cfg->allocated-machine-procedure name params cfg)
  (finalize-machine-procedure
   (allocate-machine-procedure
    (select-machine-procedure name params cfg))))

;;; ============================================================================
;;; Helper: Display results
;;; ============================================================================

(define (display-cfg cfg)
  (display "Control Flow Graph:\n")
  (do ((i 0 (+ i 1)) (blocks cfg (cdr blocks)))
      ((null? blocks))
    (let* ((block (car blocks))
           (label (basic-block-label block))
           (instrs (basic-block-instructions block))
           (successors (basic-block-successors block)))
      (display "Block ") (display i) 
      (if label 
          (begin (display " (label: ") (display label) (display ")")))
      (display ":\n")
      (for-each (lambda (instr)
                  (display "    ")
                  (write instr)
                  (newline))
                instrs)
       (display "    Successors: ")
       (write successors)
       (newline) (newline))))

(define (display-procedure-cfg procedure cfg)
  (display "Procedure ")
  (display (procedure-name procedure))
  (display " ")
  (write (procedure-params procedure))
  (display ":\n")
  (display-cfg cfg))

(define (display-machine-procedure proc)
  (display "Machine Procedure ")
  (display (machine-procedure-name proc))
  (display ":\n")
  (display "    Param locations: ")
  (write (machine-procedure-param-locations proc))
  (newline)
  (display "    Homes: ")
  (write (machine-procedure-homes proc))
  (newline)
  (display "    Frame slots: ")
  (write (machine-procedure-frame-slots proc))
  (newline)
  (display "    Used callee-saved: ")
  (write (machine-procedure-used-registers proc))
  (newline)
  (for-each
   (lambda (block)
     (display "    Block")
     (if (machine-block-label block)
         (begin
           (display " ")
           (display (machine-block-label block)))
         (display " entry"))
     (display ":\n")
     (for-each (lambda (instr)
                 (display "        ")
                 (write instr)
                 (newline))
               (machine-block-instructions block))
     (display "        Successors: ")
     (write (machine-block-successors block))
     (newline))
   (machine-procedure-blocks proc))
  (newline))

;;; ============================================================================
;;; AArch64 assembly emission
;;; The emitter converts the allocated backend IR into textual Apple-style
;;; AArch64 assembly. By this point, the interesting compiler work is already
;;; done; emission is mostly a matter of printing each lowered instruction in
;;; the right concrete form.
;;; ============================================================================

(define (procedure-saved-bytes proc)
  (* 8 (length (machine-procedure-used-registers proc))))

(define (procedure-outgoing-base proc)
  (+ (procedure-saved-bytes proc)
     (* 8 (machine-procedure-frame-slots proc))))

(define (incoming-stack-arg-offset index)
  (+ 16 (* 8 index)))

(define (stack-slot-offset proc index)
  (+ (procedure-saved-bytes proc)
     (* 8 index)))

(define (saved-register-offset proc reg)
  (let loop ((rest (machine-procedure-used-registers proc)) (offset 0))
    (cond
      ((null? rest) (error "Unknown saved register" reg))
      ((eq? (car rest) reg) offset)
      (else (loop (cdr rest) (+ offset 8))))))

(define (asm-name sym)
  (string-append "_" (symbol->string sym)))

(define (emit-asm-line port text)
  (display text port)
  (newline port))

(define fixnum-shift 3)
(define tag-mask 7)
(define pair-tag 1)
(define box-tag 2)
(define closure-tag 3)
(define null-immediate 20)
(define false-immediate 36)
(define true-immediate 52)

(define (encode-immediate value)
  (cond
    ((null? value) null-immediate)
    ((eq? value #f) false-immediate)
    ((eq? value #t) true-immediate)
    ((number? value) (ash value fixnum-shift))
    (else (error "Expected immediate value" value))))

(define (immediate->string value)
  (number->string (encode-immediate value)))

(define (register-operand? operand)
  (and (pair? operand)
       (memq (car operand) '(register arg-register))))

(define (register-name operand)
  (symbol->string (cadr operand)))

(define (emit-load-operand port target operand proc)
  (cond
    ((literal-expr? operand)
     (emit-asm-line port
                    (string-append "    mov " target ", #"
                                   (immediate->string operand))))
    ((register-operand? operand)
     (let ((src (register-name operand)))
       (when (not (string=? target src))
         (emit-asm-line port
                        (string-append "    mov " target ", " src)))))
    ((and (pair? operand) (eq? (car operand) 'stack-slot))
     (emit-asm-line port
                    (string-append "    ldr " target ", [sp, #"
                                   (number->string
                                    (stack-slot-offset proc (cadr operand)))
                                   "]")))
    ((and (pair? operand) (eq? (car operand) 'stack-arg))
     (emit-asm-line port
                    (string-append "    ldr " target ", [x29, #"
                                   (number->string
                                    (incoming-stack-arg-offset (cadr operand)))
                                   "]")))
    (else
     (error "Unsupported source operand in assembly emission" operand))))

(define (emit-store-operand port source operand proc)
  (cond
    ((register-operand? operand)
     (let ((dst (register-name operand)))
       (when (not (string=? source dst))
         (emit-asm-line port
                        (string-append "    mov " dst ", " source)))))
    ((and (pair? operand) (eq? (car operand) 'stack-slot))
     (emit-asm-line port
                    (string-append "    str " source ", [sp, #"
                                   (number->string
                                    (stack-slot-offset proc (cadr operand)))
                                   "]")))
    ((and (pair? operand) (eq? (car operand) 'stack-arg))
     (emit-asm-line port
                    (string-append "    str " source ", [sp, #"
                                   (number->string
                                    (+ (procedure-outgoing-base proc)
                                       (* 8 (cadr operand))))
                                   "]")))
    (else
     (error "Unsupported destination operand in assembly emission" operand))))

(define (emit-move port dst src proc)
  (emit-load-operand port "x9" src proc)
  (emit-store-operand port "x9" dst proc))

(define (emit-procedure-address port reg proc-name)
  (emit-asm-line port
                 (string-append "    adrp " reg ", "
                                (asm-name proc-name) "@PAGE"))
  (emit-asm-line port
                 (string-append "    add " reg ", " reg ", "
                                (asm-name proc-name) "@PAGEOFF")))

(define (emit-bool-result port condition dst proc)
  (emit-asm-line port
                 (string-append "    mov x11, #"
                                (number->string false-immediate)))
  (emit-asm-line port
                 (string-append "    mov x12, #"
                                (number->string true-immediate)))
  (emit-asm-line port
                 (string-append "    csel x11, x12, x11, " condition))
  (emit-store-operand port "x11" dst proc))

(define (emit-load-box-address port operand proc)
  (emit-load-operand port "x9" operand proc)
  (emit-asm-line port
                 (string-append "    sub x9, x9, #"
                                (number->string box-tag))))

(define (emit-load-closure-address port operand proc)
  (emit-load-operand port "x9" operand proc)
  (emit-asm-line port
                 (string-append "    sub x9, x9, #"
                                (number->string closure-tag))))

(define (emit-runtime-unary-call port helper dst operand proc)
  (emit-load-operand port "x0" operand proc)
  (emit-asm-line port (string-append "    bl " helper))
  (emit-store-operand port "x0" dst proc))

(define (emit-immediate-compare port operand immediate proc)
  (emit-load-operand port "x9" operand proc)
  (emit-asm-line port
                 (string-append "    mov x10, #"
                                (number->string immediate)))
  (emit-asm-line port "    cmp x9, x10"))

(define (emit-binop port op dst lhs rhs proc)
  (emit-load-operand port "x9" lhs proc)
  (emit-load-operand port "x10" rhs proc)
  (cond
    ((eq? op '+)
     (emit-asm-line port "    add x11, x9, x10")
     (emit-store-operand port "x11" dst proc))
    ((eq? op '-)
     (emit-asm-line port "    sub x11, x9, x10")
     (emit-store-operand port "x11" dst proc))
    ((eq? op '*)
     (emit-asm-line port "    mul x11, x9, x10")
     (emit-asm-line port
                    (string-append "    asr x11, x11, #"
                                   (number->string fixnum-shift)))
     (emit-store-operand port "x11" dst proc))
    ((eq? op '=)
      (emit-asm-line port "    cmp x9, x10")
      (emit-bool-result port "eq" dst proc))
    ((eq? op '<)
      (emit-asm-line port "    cmp x9, x10")
      (emit-bool-result port "lt" dst proc))
    ((eq? op '>)
      (emit-asm-line port "    cmp x9, x10")
      (emit-bool-result port "gt" dst proc))
    (else
     (error "Unsupported primop in assembly emission" op)))
  'done)

(define (emit-alloc-closure port dst proc-name captures proc)
  (let ((count (length captures)))
    (when (> count 3)
      (error "Too many closure captures for minimal runtime" count))
    (emit-procedure-address port "x0" proc-name)
    (let loop ((rest captures) (index 1))
      (if (null? rest)
          'done
          (begin
            (emit-load-operand port
                               (string-append "x" (number->string index))
                               (car rest)
                               proc)
            (loop (cdr rest) (+ index 1)))))
    (emit-asm-line port
                   (string-append "    bl _hop_alloc_closure_"
                                  (number->string count)))
    (emit-store-operand port "x0" dst proc)))

(define (emit-call-helper port argc tail?)
  (when (> argc 3)
    (error "Too many call arguments for minimal runtime" argc))
  (emit-asm-line port
                 (string-append "    "
                                (if tail? "b" "bl")
                                " _hop_"
                                (if tail? "tail_call_" "call_")
                                (number->string argc))))

(define (emit-call-label port proc-name tail?)
  (emit-asm-line port
                 (string-append "    "
                                (if tail? "b " "bl ")
                                (asm-name proc-name))))

(define (emit-machine-instruction port instr proc)
  (case (car instr)
    ((allocate-frame)
     (emit-asm-line port "    stp x29, x30, [sp, #-16]!")
     (emit-asm-line port "    mov x29, sp")
     (when (> (cadr instr) 0)
       (emit-asm-line port
                      (string-append "    sub sp, sp, #"
                                     (number->string (cadr instr))))))
    ((save-callee-saved)
     (for-each
      (lambda (reg)
        (emit-asm-line port
                       (string-append "    str "
                                      (symbol->string reg)
                                      ", [sp, #"
                                      (number->string
                                       (saved-register-offset proc reg))
                                      "]")))
      (cadr instr)))
    ((restore-callee-saved)
     (for-each
      (lambda (reg)
        (emit-asm-line port
                       (string-append "    ldr "
                                      (symbol->string reg)
                                      ", [sp, #"
                                      (number->string
                                       (saved-register-offset proc reg))
                                      "]")))
      (cadr instr)))
    ((deallocate-frame)
     (when (> (cadr instr) 0)
       (emit-asm-line port
                      (string-append "    add sp, sp, #"
                                     (number->string (cadr instr)))))
     (emit-asm-line port "    ldp x29, x30, [sp], #16"))
    ((move move-out)
     (emit-move port (cadr instr) (caddr instr) proc))
    ((binop)
     (emit-binop port
                 (cadr instr)
                 (caddr instr)
                 (cadddr instr)
                 (car (cddddr instr))
                 proc))
    ((alloc-box)
      (emit-runtime-unary-call port "_hop_alloc_box" (cadr instr) (caddr instr) proc))
    ((alloc-pair)
      (emit-load-operand port "x0" (caddr instr) proc)
      (emit-load-operand port "x1" (cadddr instr) proc)
      (emit-asm-line port "    bl _hop_alloc_pair")
      (emit-store-operand port "x0" (cadr instr) proc))
    ((load-box)
      (emit-load-box-address port (caddr instr) proc)
      (emit-asm-line port "    ldr x10, [x9]")
      (emit-store-operand port "x10" (cadr instr) proc))
    ((load-closure-env)
      (emit-load-closure-address port (caddr instr) proc)
      (emit-asm-line port
                     (string-append "    ldr x10, [x9, #"
                                    (number->string (+ 16 (* 8 (cadddr instr))))
                                    "]"))
      (emit-store-operand port "x10" (cadr instr) proc))
    ((load-car)
      (emit-runtime-unary-call port "_hop_car" (cadr instr) (caddr instr) proc))
    ((load-cdr)
      (emit-runtime-unary-call port "_hop_cdr" (cadr instr) (caddr instr) proc))
    ((is-pair)
      (emit-load-operand port "x9" (caddr instr) proc)
      (emit-asm-line port
                     (string-append "    and x10, x9, #"
                                    (number->string tag-mask)))
      (emit-asm-line port
                     (string-append "    cmp x10, #"
                                     (number->string pair-tag)))
      (emit-bool-result port "eq" (cadr instr) proc))
    ((is-null)
      (emit-immediate-compare port (caddr instr) null-immediate proc)
      (emit-bool-result port "eq" (cadr instr) proc))
    ((store-box)
      (emit-load-box-address port (cadr instr) proc)
      (emit-load-operand port "x10" (caddr instr) proc)
      (emit-asm-line port "    str x10, [x9]"))
    ((alloc-closure)
     (emit-alloc-closure port (cadr instr) (caddr instr) (cdddr instr) proc))
    ((call-indirect)
     (emit-call-helper port (cadr instr) #f))
    ((call-label)
      (emit-call-label port (cadr instr) #f))
    ((tail-call-indirect)
     (emit-call-helper port (cadr instr) #t))
    ((tail-call-label)
      (emit-call-label port (cadr instr) #t))
    ((branch-if)
      (emit-immediate-compare port (cadr instr) false-immediate proc)
      (emit-asm-line port
                     (string-append "    b.ne L"
                                    (symbol->string (caddr instr))))
      (emit-asm-line port
                     (string-append "    b L"
                                   (symbol->string (cadddr instr)))))
    ((jump)
     (emit-asm-line port
                    (string-append "    b L"
                                   (symbol->string (cadr instr)))))
    ((ret)
     (emit-asm-line port "    ret"))
    (else
     (error "Unsupported machine instruction in assembly emission" instr))))

(define (emit-machine-block port block proc first?)
  (define (entry-setup-instruction? instr)
    (and (pair? instr)
         (or (memq (car instr) '(allocate-frame save-callee-saved))
             (and (eq? (car instr) 'move)
                  (pair? (caddr instr))
                  (memq (car (caddr instr)) '(arg-register incoming-stack-arg))))))
  (let* ((instrs (machine-block-instructions block))
         (prologue
          (if first?
              (let loop ((rest instrs) (result '()))
                (if (and (pair? rest)
                         (entry-setup-instruction? (car rest)))
                    (loop (cdr rest) (append result (list (car rest))))
                    result))
              '()))
         (body
          (if first?
              (list-tail instrs (length prologue))
              instrs)))
    (for-each (lambda (instr)
                (emit-machine-instruction port instr proc))
              prologue)
    (if (or (not first?) (machine-block-label block))
        (emit-asm-line port
                       (string-append "L"
                                      (symbol->string (machine-block-label block))
                                      ":")))
    (for-each (lambda (instr)
                (emit-machine-instruction port instr proc))
              body)))

(define (emit-machine-procedure port proc exported-name)
  (emit-asm-line port (string-append ".globl " (asm-name exported-name)))
  (emit-asm-line port (string-append ".p2align 2"))
  (emit-asm-line port (string-append (asm-name exported-name) ":"))
  (let loop ((blocks (machine-procedure-blocks proc)) (first? #t))
    (if (null? blocks)
        'done
        (begin
          (emit-machine-block port (car blocks) proc first?)
          (loop (cdr blocks) #f))))
  (newline port))

(define (emit-aarch64-program port entry-proc procedures)
  (emit-asm-line port ".text")
  (emit-asm-line port "")
  (emit-machine-procedure port entry-proc 'scheme_entry)
  (for-each (lambda (proc)
              (emit-machine-procedure port proc (machine-procedure-name proc)))
            procedures))

;;; ============================================================================
;;; Simple hash table implementation 
;;; ============================================================================

(define (make-hash-table) (list 'hash-table))
(define (hash-set! ht key value)
  (let ((pair (assoc key (cdr ht))))
    (if pair
        (set-cdr! pair value)
        (set-cdr! ht (cons (cons key value) (cdr ht))))))
(define (hash-ref ht key)
  (let ((pair (assoc key (cdr ht))))
    (if pair (cdr pair) #f)))

;;; ============================================================================
;;; Main Compiler Driver
;;; These entry points stitch the passes together:
;;;
;;;   - compile-to-cfg: stop after the middle end
;;;   - compile-to-backend: run through allocation/finalization
;;;   - write-aarch64-program: emit assembly to a file
;;;   - compile-program: educational debugging view of the intermediate stages
;;; ============================================================================

(define (compile-to-cfg expr)
  (let* ((uniquified (uniquify expr))
         (desugared (desugar-letrec uniquified))
         (closure-converted (closure-convert desugared))
         (cfa-normalized (normalize-for-cfa closure-converted))
         (cfa-analysis (run-0cfa cfa-normalized))
         (cfa-rewritten (rewrite-known-calls cfa-normalized cfa-analysis)))
    (let-values (((tac-instrs procedures) (expr->tac cfa-rewritten)))
      (values uniquified
              desugared
              closure-converted
              cfa-normalized
              cfa-rewritten
              (build-cfg tac-instrs)
                (map (lambda (procedure)
                       (cons procedure
                             (build-cfg (procedure-instructions procedure))))
                     procedures)))))

(define (compile-to-backend expr)
  (let-values (((uniquified desugared closure-converted cfa-normalized
                            cfa-rewritten entry-cfg procedures)
                (compile-to-cfg expr)))
    (let ((entry-machine
           (cfg->allocated-machine-procedure 'scheme_entry '() entry-cfg))
          (procedure-machines
           (map (lambda (procedure+cfg)
                  (cfg->allocated-machine-procedure
                   (procedure-name (car procedure+cfg))
                   (procedure-params (car procedure+cfg))
                   (cdr procedure+cfg)))
                procedures)))
      (values uniquified
              desugared
              closure-converted
              cfa-normalized
              cfa-rewritten
              entry-cfg
              procedures
              entry-machine
              procedure-machines))))

(define (write-aarch64-program expr path)
  (let-values (((uniquified desugared closure-converted cfa-normalized
                            cfa-rewritten entry-cfg procedures
                             entry-machine procedure-machines)
                (compile-to-backend expr)))
    (call-with-output-file path
      (lambda (port)
        (emit-aarch64-program port entry-machine procedure-machines)))))

(define (compile-program expr)
  (display "=== Source Program ===\n")
  (write expr) (newline)
  
  (display "\n=== After Uniquify ===\n")
  (let-values (((uniquified desugared closure-converted cfa-normalized
                            cfa-rewritten entry-cfg procedures
                             entry-machine procedure-machines)
                (compile-to-backend expr)))
    (write uniquified) (newline)
    
    (display "\n=== After letrec Desugaring ===\n")
    (write desugared) (newline)
    
    (display "\n=== After Closure Conversion ===\n")
    (write closure-converted) (newline)

    (display "\n=== After CFA Normalization ===\n")
    (write cfa-normalized) (newline)

    (display "\n=== After 0CFA Call Rewriting ===\n")
    (write cfa-rewritten) (newline)
    
    (display "\n=== Entry CFG ===\n")
    (display-cfg entry-cfg)
    (display "Entry CFG built with ")
    (display (length entry-cfg))
    (display " basic blocks\n")
    (display "\n=== Allocated Backend ===\n")
    (display-machine-procedure entry-machine)
    (for-each display-machine-procedure procedure-machines)
    
    (when (not (null? procedures))
      (display "\n=== Procedure CFGs ===\n")
      (for-each (lambda (procedure+cfg)
                  (display-procedure-cfg (car procedure+cfg) (cdr procedure+cfg)))
                procedures))
    
    (display "\n=== Compilation Complete ===\n")))

;;; Test fixtures and demo helpers live in separate test-owned files so loading
;;; the compiler does not implicitly run or define the regression suite.
