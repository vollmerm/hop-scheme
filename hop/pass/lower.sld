(define-library (hop pass lower)
  ;;; Pass 0: Program Lowering
  ;;; Accept either a single expression or a `(program ...)` wrapper, flatten
  ;;; top-level begin, assign compiler-known global slots, and rewrite top-level
  ;;; define into explicit global initialization.
  ;;;
  ;;; This pass also lowers quote:
  ;;;   - quoted immediates ((quote 3), (quote #t), (quote ())) become the
  ;;;     immediate itself
  ;;;   - quoted symbols stay wrapped as (quote sym) and flow through the
  ;;;     pipeline as literals (see literal-expr? in (hop utils))
  ;;;   - quoted pairs are hoisted into fresh global slots that are built with
  ;;;     cons at the top of the program, so each quoted structure is
  ;;;     constructed exactly once and every occurrence reads (global N)
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

(define (immediate-datum? datum)
  (or (number? datum) (boolean? datum) (null? datum)))

;; Build the expression that constructs a quoted datum at run time. The
;; result only uses immediates, (quote sym) literals, and cons, so it needs
;; no further global resolution.
(define (quoted-datum->constructor datum)
  (cond
   ((immediate-datum? datum) datum)
   ((symbol? datum) `(quote ,datum))
   ((pair? datum)
    `(cons ,(quoted-datum->constructor (car datum))
           ,(quoted-datum->constructor (cdr datum))))
   (else
    (error "Unsupported quoted datum" datum))))

(define (resolve-globals expr local-env global-env hoist-quote!)
  (define (resolve e local-env)
    (cond
     ((symbol? e)
      (if (memq e local-env)
          e
          (let ((binding (assoc e global-env)))
            (if binding
                `(global ,(cadr binding))
                e))))
     ((literal-expr? e) e)
     ((pair? e)
      (case (car e)
        ((quote)
         (let ((datum (cadr e)))
           (cond
            ((immediate-datum? datum) datum)
            ;; (quote sym) is caught by literal-expr? above; only structured
            ;; data reaches this branch.
            ((pair? datum) (hoist-quote! datum))
            (else (error "Unsupported quoted datum" datum)))))
        ((begin)
         `(begin ,@(map (lambda (sub) (resolve sub local-env)) (cdr e))))
        ((primop)
         `(primop ,(cadr e)
                  ,@(map (lambda (sub) (resolve sub local-env)) (cddr e))))
        ((if)
         `(if ,(resolve (cadr e) local-env)
              ,(resolve (caddr e) local-env)
              ,(resolve (cadddr e) local-env)))
        ((let)
         (let* ((bindings (map (lambda (binding)
                                 (list (car binding)
                                       (resolve (cadr binding) local-env)))
                               (cadr e)))
                (new-vars (map car bindings))
                (body-exprs (cddr e)))
           `(let ,bindings
              ,@(map (lambda (body-expr)
                       (resolve body-expr (append new-vars local-env)))
                     body-exprs))))
        ((lambda)
         (let ((params (cadr e)))
           `(lambda ,params
              ,@(map (lambda (body-expr)
                       (resolve body-expr (append params local-env)))
                     (cddr e)))))
        ((letrec)
         (let* ((bindings (cadr e))
                (names (map car bindings))
                (rec-env (append names local-env)))
           `(letrec
                ,(map (lambda (binding)
                        (list (car binding)
                              (resolve (cadr binding) rec-env)))
                      bindings)
              ,@(map (lambda (body-expr)
                       (resolve body-expr rec-env))
                     (cddr e)))))
        ((app)
         `(app ,(resolve (cadr e) local-env)
               ,@(map (lambda (sub) (resolve sub local-env)) (cddr e))))
        ((cons make-vector vector-ref)
         `(,(car e) ,(resolve (cadr e) local-env)
           ,(resolve (caddr e) local-env)))
        ((+ - * = < > eq?)
         `(,(car e) ,(resolve (cadr e) local-env)
           ,(resolve (caddr e) local-env)))
        ((box unbox car cdr pair? null? symbol? vector-length vector?)
         `(,(car e) ,(resolve (cadr e) local-env)))
        ((set-box!)
         `(set-box! ,(resolve (cadr e) local-env)
                    ,(resolve (caddr e) local-env)))
        ((vector-set!)
         `(vector-set! ,(resolve (cadr e) local-env)
                       ,(resolve (caddr e) local-env)
                       ,(resolve (cadddr e) local-env)))
        ((define)
         (error "Internal define is not supported" e))
        (else
         (error "Unknown expression during global resolution" (car e)))))
     (else
      (error "Invalid expression during global resolution" e))))
  (resolve expr local-env))

(define (lower-source-program source)
  (let* ((forms (flatten-top-level-forms (source->forms source)))
         (global-env (collect-top-level-global-env forms))
         (next-quote-slot (length global-env))
         (quote-inits '()))
    (define (hoist-quote! datum)
      ;; Quoted structure gets a compiler-assigned slot after the top-level
      ;; defines. The initializer runs before any user form, so every read of
      ;; the slot sees the fully built structure.
      (let ((slot next-quote-slot))
        (set! next-quote-slot (+ next-quote-slot 1))
        (set! quote-inits
              (cons `(set-global! ,slot ,(quoted-datum->constructor datum))
                    quote-inits))
        `(global ,slot)))
    (if (null? forms)
        (error "Program requires at least one top-level form")
        (let ((resolved-forms
               (map (lambda (form)
                      (if (top-level-define-form? form)
                          ;; Top-level define is not a local binder after this
                          ;; point; it is an ordered write into a
                          ;; compiler-assigned slot.
                          `(set-global! ,(global-slot (cadr form) global-env)
                                        ,(resolve-globals (caddr form)
                                                          '()
                                                          global-env
                                                          hoist-quote!))
                          (resolve-globals form '() global-env hoist-quote!)))
                    forms)))
          (values
           (body->expr (append (reverse quote-inits) resolved-forms))
           next-quote-slot)))))

)) ; end define-library
