(define-library (hop pass uniquify)
  ;;; Pass 1: Uniquify
  ;;; Renames every binder so that each variable name is globally unique.
  ;;;
  ;;; Pass 1.5: Builtin Canonicalization
  ;;; Rewrites user-facing list and vector primitives into uniform (primop op ...)
  ;;; form and wraps bare builtin names in value position as lambdas.
  (export uniquify
          canonicalize-builtins)
  (import (scheme base)
          (scheme cxr)
          (hop utils))
  (begin

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
      (let ((binding (assoc expr env)))
        (if binding
            (cadr binding)
            expr)))

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
         (let* ((old-bindings (cadr expr))
                (old-vars (map car old-bindings))
                (new-vars (map fresh-name old-vars))
                (new-bindings (map (lambda (old-binding new-var)
                                     (list new-var
                                           (uniquify-expr (cadr old-binding) env)))
                                   old-bindings new-vars))
                (new-env (append (map (lambda (old-var new-var)
                                        (list old-var new-var))
                                      old-vars new-vars)
                                 env))
                (body-exprs (cddr expr))
                (body-unique
                 (map (lambda (body-expr)
                        (uniquify-expr body-expr new-env))
                      body-exprs)))
           `(let ,new-bindings ,@body-unique)))

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
                          (list unique-var
                                (uniquify-expr value-expr new-env))))
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

        ((cons make-vector vector-ref)
         `(,(car expr) ,(uniquify-expr (cadr expr) env)
           ,(uniquify-expr (caddr expr) env)))
        ((+ - * = < > eq?)
         `(,(car expr) ,(uniquify-expr (cadr expr) env)
           ,(uniquify-expr (caddr expr) env)))
        ((box unbox car cdr pair? null? symbol? vector-length vector?)
         `(,(car expr) ,(uniquify-expr (cadr expr) env)))
        ((set-box!)
         `(set-box! ,(uniquify-expr (cadr expr) env)
                    ,(uniquify-expr (caddr expr) env)))
        ((vector-set!)
         `(vector-set! ,(uniquify-expr (cadr expr) env)
                       ,(uniquify-expr (caddr expr) env)
                       ,(uniquify-expr (cadddr expr) env)))

        ((global)
         expr)

        ((set-global!)
         `(set-global! ,(cadr expr)
                       ,(uniquify-expr (caddr expr) env)))

        (else (error "Unknown expression type" (car expr)))))

     (else (error "Invalid expression" expr))))

  (uniquify-expr expr '()))

;;; ── Pass 1.5: Builtin Canonicalization ───────────────────────────────────────

(define builtin-primop-arities
  '((car . 1)
    (cdr . 1)
    (unsafe-car . 1)
    (unsafe-cdr . 1)
    (pair? . 1)
    (null? . 1)
    (symbol? . 1)
    (vector? . 1)
    (eq? . 2)
    (cons . 2)
    (make-vector . 2)
    (vector-length . 1)
    (vector-ref . 2)
    (vector-set! . 3)
    (+ . 2)
    (- . 2)
    (* . 2)
    (= . 2)
    (< . 2)
    (> . 2)))

(define (builtin-primop? name)
  (assq name builtin-primop-arities))

(define (builtin-primop-arity name)
  (cdr (assq name builtin-primop-arities)))

;; Source-level arithmetic operators canonicalize to safe-checked primop forms.
(define builtin-safe-arith-rename
  '((+ . safe-+) (- . safe--) (* . safe-*) (= . safe-=) (< . safe-<) (> . safe->)))

(define (builtin-primop-canonical-name name)
  (let ((entry (assq name builtin-safe-arith-rename)))
    (if entry (cdr entry) name)))

(define (canonicalize-builtins expr)
  (define wrap-counter 0)
  (define (fresh-wrap-name)
    (set! wrap-counter (+ wrap-counter 1))
    (string->symbol (string-append "wrap." (number->string wrap-counter))))
  (define (make-wrap-lambda name arity)
    (let loop ((i 0) (params '()))
      (if (= i arity)
          (let ((ps (reverse params)))
            `(lambda ,ps (primop ,(builtin-primop-canonical-name name) ,@ps)))
          (loop (+ i 1) (cons (fresh-wrap-name) params)))))
  (define (canon expr)
    (cond
     ((symbol? expr)
      (if (builtin-primop? expr)
          (make-wrap-lambda expr (builtin-primop-arity expr))
          expr))
     ((literal-expr? expr) expr)
     ((pair? expr)
      (let ((entry (and (symbol? (car expr)) (builtin-primop? (car expr)))))
        (if entry
            `(primop ,(builtin-primop-canonical-name (car expr)) ,@(map canon (cdr expr)))
            (case (car expr)
              ((begin)    `(begin ,@(map canon (cdr expr))))
              ((primop)   `(primop ,(cadr expr) ,@(map canon (cddr expr))))
              ((if)       `(if ,(canon (cadr expr))
                               ,(canon (caddr expr))
                               ,(canon (cadddr expr))))
              ((let)
               (let* ((bindings (cadr expr)))
                 `(let ,(map (lambda (binding)
                               (list (car binding) (canon (cadr binding))))
                             bindings)
                    ,@(map canon (cddr expr)))))
              ((lambda)   `(lambda ,(cadr expr) ,@(map canon (cddr expr))))
              ((letrec)
               `(letrec ,(map (lambda (b) `(,(car b) ,(canon (cadr b)))) (cadr expr))
                  ,@(map canon (cddr expr))))
              ((app)      `(app ,(canon (cadr expr)) ,@(map canon (cddr expr))))
              ((box)      `(box ,(canon (cadr expr))))
              ((unbox)    `(unbox ,(canon (cadr expr))))
              ((set-box!) `(set-box! ,(canon (cadr expr)) ,(canon (caddr expr))))
              ((global)   expr)
              ((set-global!) `(set-global! ,(cadr expr) ,(canon (caddr expr))))
              (else (error "Unknown expression in canonicalize-builtins" (car expr)))))))
     (else (error "Invalid expression in canonicalize-builtins" expr))))
  (canon expr))

)) ; end define-library
