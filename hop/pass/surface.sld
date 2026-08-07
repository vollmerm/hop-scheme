(define-library (hop pass surface)
  ;;; Pass -1: Surface Desugaring
  ;;; Rewrites surface Scheme syntax into the explicit core AST that the rest
  ;;; of the pipeline consumes. After this pass every call is an explicit
  ;;; (app ...) or a recognized builtin form, every define is (define name
  ;;; expr), and the derived conditionals/binding forms are gone:
  ;;;
  ;;;   (f x y)                  -> (app f x y)         [f not a known form]
  ;;;   (define (f x) body...)   -> (define f (lambda (x) body...))
  ;;;   internal defines         -> letrec at the head of the body
  ;;;   (if t c)                 -> (if t c #f)
  ;;;   cond / case              -> nested if (case keys compare with eq?)
  ;;;   and / or                 -> nested if (or binds a temp once)
  ;;;   when / unless / not      -> if
  ;;;   let*                     -> nested single-binding lets
  ;;;   (let name bindings body) -> letrec + call
  ;;;
  ;;; The pass is idempotent on core forms: primop, app, quote, global, and
  ;;; friends pass through with only their subexpressions rewritten, so
  ;;; already-lowered programs remain valid inputs.
  (export desugar-surface)
  (import (scheme base)
          (scheme cxr)
          (hop utils))
  (begin

;; Heads that the desugarer must not treat as applications. This mirrors the
;; forms accepted by program lowering plus the derived forms handled here.
(define surface-keywords
  '(quote begin if lambda let let* letrec
    cond case and or when unless not
    define set! quasiquote unquote unquote-splicing
    primop app global set-global!
    box unbox set-box!
    cons car cdr pair? null? symbol? eq?
    make-vector vector-length vector-ref vector-set! vector?
    + - * = < >))

(define (surface-keyword? head)
  (and (symbol? head) (memq head surface-keywords)))

(define (define-form? form)
  (and (pair? form) (eq? (car form) 'define)))

(define (proper-list? lst)
  (cond
   ((null? lst) #t)
   ((pair? lst) (proper-list? (cdr lst)))
   (else #f)))

(define (check-params params context)
  (if (proper-list? params)
      params
      (error "Variadic parameter lists are not supported yet" context)))

;; (define (f x y) body...) -> (define f (lambda (x y) body...))
;; (define x expr)          -> unchanged
(define (normalize-define form)
  (let ((head (cadr form)))
    (cond
     ((pair? head)
      `(define ,(car head)
         (lambda ,(check-params (cdr head) form) ,@(cddr form))))
     ((symbol? head)
      (if (and (pair? (cddr form)) (null? (cdddr form)))
          form
          (error "define requires exactly one value expression" form)))
     (else
      (error "Invalid define form" form)))))

(define (case-datum->literal datum context)
  (cond
   ((symbol? datum) `(quote ,datum))
   ((or (number? datum) (boolean? datum) (null? datum)) datum)
   (else
    (error "case only supports immediate and symbol datums" context))))

(define (desugar-surface source)
  (define temp-counter 0)

  (define (fresh-temp)
    (set! temp-counter (+ temp-counter 1))
    (string->symbol (string-append "ds.tmp." (number->string temp-counter))))

  ;; A body is a sequence of leading internal defines followed by at least
  ;; one expression. The defines become a letrec wrapped around the rest.
  (define (desugar-body exprs context)
    (let loop ((rest exprs) (defs '()))
      (cond
       ((and (pair? rest) (define-form? (car rest)))
        (loop (cdr rest) (cons (normalize-define (car rest)) defs)))
       ((null? rest)
        (error "Body has no expression after internal defines" context))
       (else
        (let check ((exprs-rest rest))
          (cond
           ((null? exprs-rest) 'ok)
           ((define-form? (car exprs-rest))
            (error "define is only allowed at the beginning of a body" context))
           (else (check (cdr exprs-rest)))))
        (if (null? defs)
            (map desugar-expr rest)
            (list (desugar-expr
                   `(letrec ,(map (lambda (d) (list (cadr d) (caddr d)))
                                  (reverse defs))
                      ,@rest))))))))

  (define (desugar-cond-clauses clauses)
    (cond
     ((null? clauses) #f)
     (else
      (let ((clause (car clauses)))
        (cond
         ((not (pair? clause))
          (error "Invalid cond clause" clause))
         ((eq? (car clause) 'else)
          (desugar-expr `(begin ,@(cdr clause))))
         ((and (pair? (cdr clause)) (eq? (cadr clause) '=>))
          (let ((tmp (fresh-temp)))
            `(let ((,tmp ,(desugar-expr (car clause))))
               (if ,tmp
                   (app ,(desugar-expr (caddr clause)) ,tmp)
                   ,(desugar-cond-clauses (cdr clauses))))))
         ((null? (cdr clause))
          ;; (test) clause: the test value is the result when truthy.
          (let ((tmp (fresh-temp)))
            `(let ((,tmp ,(desugar-expr (car clause))))
               (if ,tmp ,tmp ,(desugar-cond-clauses (cdr clauses))))))
         (else
          `(if ,(desugar-expr (car clause))
               ,(desugar-expr `(begin ,@(cdr clause)))
               ,(desugar-cond-clauses (cdr clauses)))))))))

  (define (desugar-case-clauses tmp clauses context)
    (cond
     ((null? clauses) #f)
     ((not (pair? (car clauses)))
      (error "Invalid case clause" context))
     ((eq? (caar clauses) 'else)
      (desugar-expr `(begin ,@(cdar clauses))))
     (else
      (let* ((clause (car clauses))
             (test (let datum-loop ((datums (car clause)))
                     (cond
                      ((null? datums) #f)
                      ((null? (cdr datums))
                       `(eq? ,tmp ,(case-datum->literal (car datums) context)))
                      (else
                       `(if (eq? ,tmp ,(case-datum->literal (car datums) context))
                            #t
                            ,(datum-loop (cdr datums))))))))
        `(if ,test
             ,(desugar-expr `(begin ,@(cdr clause)))
             ,(desugar-case-clauses tmp (cdr clauses) context))))))

  (define (desugar-expr expr)
    (cond
     ((symbol? expr) expr)
     ((literal-expr? expr) expr)
     ((pair? expr)
      (case (car expr)
        ((quote) expr)

        ((begin)
         `(begin ,@(map desugar-expr (cdr expr))))

        ((if)
         (cond
          ((null? (cdddr expr))
           ;; Two-armed if: the missing else arm produces #f.
           `(if ,(desugar-expr (cadr expr))
                ,(desugar-expr (caddr expr))
                #f))
          (else
           `(if ,(desugar-expr (cadr expr))
                ,(desugar-expr (caddr expr))
                ,(desugar-expr (cadddr expr))))))

        ((lambda)
         `(lambda ,(check-params (cadr expr) expr)
            ,@(desugar-body (cddr expr) expr)))

        ((let)
         (if (symbol? (cadr expr))
             ;; Named let becomes a letrec-bound loop lambda plus a call.
             (let ((name (cadr expr))
                   (bindings (caddr expr))
                   (body (cdddr expr)))
               (desugar-expr
                `(letrec ((,name (lambda ,(map car bindings) ,@body)))
                   (,name ,@(map cadr bindings)))))
             (if (null? (cadr expr))
                 ;; (let () body...) binds nothing; later passes assume lets
                 ;; carry at least one binding, so collapse to the body.
                 (body->expr (desugar-body (cddr expr) expr))
                 `(let ,(map (lambda (binding)
                               (list (car binding)
                                     (desugar-expr (cadr binding))))
                             (cadr expr))
                    ,@(desugar-body (cddr expr) expr)))))

        ((let*)
         (let ((bindings (cadr expr))
               (body (cddr expr)))
           (if (null? bindings)
               (desugar-expr `(let () ,@body))
               (desugar-expr
                (let nest ((rest bindings))
                  (if (null? (cdr rest))
                      `(let (,(car rest)) ,@body)
                      `(let (,(car rest)) ,(nest (cdr rest)))))))))

        ((letrec)
         `(letrec ,(map (lambda (binding)
                          (list (car binding)
                                (desugar-expr (cadr binding))))
                        (cadr expr))
            ,@(desugar-body (cddr expr) expr)))

        ((cond)
         (desugar-cond-clauses (cdr expr)))

        ((case)
         (let ((tmp (fresh-temp)))
           `(let ((,tmp ,(desugar-expr (cadr expr))))
              ,(desugar-case-clauses tmp (cddr expr) expr))))

        ((and)
         (cond
          ((null? (cdr expr)) #t)
          ((null? (cddr expr)) (desugar-expr (cadr expr)))
          (else
           `(if ,(desugar-expr (cadr expr))
                ,(desugar-expr `(and ,@(cddr expr)))
                #f))))

        ((or)
         (cond
          ((null? (cdr expr)) #f)
          ((null? (cddr expr)) (desugar-expr (cadr expr)))
          (else
           (let ((tmp (fresh-temp)))
             `(let ((,tmp ,(desugar-expr (cadr expr))))
                (if ,tmp ,tmp ,(desugar-expr `(or ,@(cddr expr)))))))))

        ((when)
         `(if ,(desugar-expr (cadr expr))
              ,(desugar-expr `(begin ,@(cddr expr)))
              #f))

        ((unless)
         `(if ,(desugar-expr (cadr expr))
              #f
              ,(desugar-expr `(begin ,@(cddr expr)))))

        ((not)
         `(if ,(desugar-expr (cadr expr)) #f #t))

        ((define)
         (error "define is only allowed at the top level or at the beginning of a body" expr))

        ((set!)
         (error "set! is not supported; rewrite the variable as a box" expr))

        ((quasiquote unquote unquote-splicing)
         (error "quasiquote is not supported yet" expr))

        ((primop)
         `(primop ,(cadr expr) ,@(map desugar-expr (cddr expr))))

        ((app)
         `(app ,@(map desugar-expr (cdr expr))))

        ((global)
         expr)

        ((set-global!)
         `(set-global! ,(cadr expr) ,(desugar-expr (caddr expr))))

        ((box unbox car cdr pair? null? symbol? vector-length vector?)
         `(,(car expr) ,(desugar-expr (cadr expr))))

        ((cons set-box! make-vector vector-ref eq? + - * = < >)
         `(,(car expr) ,(desugar-expr (cadr expr))
           ,(desugar-expr (caddr expr))))

        ((vector-set!)
         `(vector-set! ,(desugar-expr (cadr expr))
                       ,(desugar-expr (caddr expr))
                       ,(desugar-expr (cadddr expr))))

        (else
         (if (surface-keyword? (car expr))
             (error "Malformed surface form" expr)
             `(app ,@(map desugar-expr expr))))))
     (else
      (error "Invalid expression in surface desugaring" expr))))

  (define (desugar-top-form form)
    (cond
     ((and (pair? form) (eq? (car form) 'begin))
      `(begin ,@(map desugar-top-form (cdr form))))
     ((define-form? form)
      (let ((normalized (normalize-define form)))
        `(define ,(cadr normalized)
           ,(desugar-expr (caddr normalized)))))
     (else
      (desugar-expr form))))

  (if (and (pair? source) (eq? (car source) 'program))
      `(program ,@(map desugar-top-form (cdr source)))
      (desugar-top-form source)))

)) ; end define-library
