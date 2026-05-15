(define-library (hop pass lower)
  ;;; Pass 0: Program Lowering
  ;;; Accept either a single expression or a `(program ...)` wrapper, flatten
  ;;; top-level begin, assign compiler-known global slots, and rewrite top-level
  ;;; define into explicit global initialization.
  (export lower-source-program)
  (import (scheme base)
          (scheme cxr)
          (hop utils))
  (begin

(define (program-source? source)
  (and (pair? source) (eq? (car source) 'program)))

(define (source->forms source)
  (if (program-source? source)
      (cdr source)
      (list source)))

(define (top-level-define-form? form)
  (and (pair? form)
       (eq? (car form) 'define)
       (pair? (cdr form))
       (symbol? (cadr form))
       (pair? (cddr form))
       (null? (cdddr form))))

(define (flatten-top-level-forms forms)
  (define (flatten-form form)
    (if (and (pair? form) (eq? (car form) 'begin))
        (flatten-top-level-forms (cdr form))
        (list form)))
  (append-map flatten-form forms))

(define (collect-top-level-global-env forms)
  (let loop ((rest forms) (next-slot 0) (env '()))
    (if (null? rest)
        env
        (let ((form (car rest)))
          (if (top-level-define-form? form)
              (let ((name (cadr form)))
                (if (assoc name env)
                    (loop (cdr rest) next-slot env)
                    (loop (cdr rest)
                          (+ next-slot 1)
                          (cons (list name next-slot) env))))
              (loop (cdr rest) next-slot env))))))

(define (global-slot name global-env)
  (let ((binding (assoc name global-env)))
    (if binding
        (cadr binding)
        (error "Unknown global binding" name))))

(define (resolve-globals expr local-env global-env)
  (cond
   ((symbol? expr)
    (if (memq expr local-env)
        expr
        (let ((binding (assoc expr global-env)))
          (if binding
              `(global ,(cadr binding))
              expr))))
   ((literal-expr? expr) expr)
   ((pair? expr)
    (case (car expr)
      ((begin)
       `(begin ,@(map (lambda (e) (resolve-globals e local-env global-env))
                      (cdr expr))))
      ((primop)
       `(primop ,(cadr expr)
                ,@(map (lambda (e) (resolve-globals e local-env global-env))
                       (cddr expr))))
      ((if)
       `(if ,(resolve-globals (cadr expr) local-env global-env)
            ,(resolve-globals (caddr expr) local-env global-env)
            ,(resolve-globals (cadddr expr) local-env global-env)))
      ((let)
       (let* ((bindings (map (lambda (binding)
                               (list (car binding)
                                     (resolve-globals (cadr binding) local-env global-env)))
                             (cadr expr)))
              (new-vars (map car bindings))
              (body-exprs (cddr expr)))
         `(let ,bindings
            ,@(map (lambda (body-expr)
                     (resolve-globals body-expr
                                      (append new-vars local-env)
                                      global-env))
                   body-exprs))))
      ((lambda)
       (let ((params (cadr expr)))
         `(lambda ,params
            ,@(map (lambda (body-expr)
                     (resolve-globals body-expr
                                      (append params local-env)
                                      global-env))
                   (cddr expr)))))
      ((letrec)
       (let* ((bindings (cadr expr))
              (names (map car bindings))
              (rec-env (append names local-env)))
         `(letrec
               ,(map (lambda (binding)
                       (list (car binding)
                             (resolve-globals (cadr binding) rec-env global-env)))
                     bindings)
            ,@(map (lambda (body-expr)
                     (resolve-globals body-expr rec-env global-env))
                   (cddr expr)))))
      ((app)
       `(app ,(resolve-globals (cadr expr) local-env global-env)
             ,@(map (lambda (e) (resolve-globals e local-env global-env))
                    (cddr expr))))
      ((cons make-vector vector-ref)
       `(,(car expr) ,(resolve-globals (cadr expr) local-env global-env)
         ,(resolve-globals (caddr expr) local-env global-env)))
      ((+ - * = < >)
       `(,(car expr) ,(resolve-globals (cadr expr) local-env global-env)
         ,(resolve-globals (caddr expr) local-env global-env)))
      ((box unbox car cdr pair? null? vector-length vector?)
       `(,(car expr) ,(resolve-globals (cadr expr) local-env global-env)))
      ((set-box!)
       `(set-box! ,(resolve-globals (cadr expr) local-env global-env)
                  ,(resolve-globals (caddr expr) local-env global-env)))
      ((vector-set!)
       `(vector-set! ,(resolve-globals (cadr expr) local-env global-env)
                     ,(resolve-globals (caddr expr) local-env global-env)
                     ,(resolve-globals (cadddr expr) local-env global-env)))
      ((define)
       (error "Internal define is not supported" expr))
      (else
       (error "Unknown expression during global resolution" (car expr)))))
   (else
    (error "Invalid expression during global resolution" expr))))

(define (lower-source-program source)
  (let* ((forms (flatten-top-level-forms (source->forms source)))
         (global-env (collect-top-level-global-env forms)))
    (if (null? forms)
        (error "Program requires at least one top-level form")
        (values
         (body->expr
          (map (lambda (form)
                 (if (top-level-define-form? form)
                     ;; Top-level define is not a local binder after this point;
                     ;; it is an ordered write into a compiler-assigned slot.
                     `(set-global! ,(global-slot (cadr form) global-env)
                                   ,(resolve-globals (caddr form) '() global-env))
                     (resolve-globals form '() global-env)))
               forms))
         (length global-env)))))

)) ; end define-library
