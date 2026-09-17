(define-library (hop pass lower)
  ;;; Pass 0: Program Lowering
  ;;; Accept either a single expression or a `(program ...)` wrapper, flatten
  ;;; top-level begin, assign each top-level define its own mangled storage
  ;;; label, and rewrite top-level define into explicit global initialization.
  ;;;
  ;;; Globals are addressed by label, not by a dense per-program slot index:
  ;;; each top-level define gets its own individually named cell (see
  ;;; global-cell-label below), the same mechanism C uses for `extern`
  ;;; globals. That's what lets a later separate-compilation pass have one
  ;;; file's global reference resolve, at assemble/link time, against another
  ;;; file's cell without either file needing to know the other's full set of
  ;;; bindings or a shared numbering.
  ;;;
  ;;; This pass also lowers quote:
  ;;;   - quoted immediates ((quote 3), (quote #t), (quote ())) become the
  ;;;     immediate itself
  ;;;   - quoted symbols stay wrapped as (quote sym) and flow through the
  ;;;     pipeline as literals (see literal-expr? in (hop utils))
  ;;;   - quoted pairs are hoisted into fresh global cells that are built with
  ;;;     cons at the top of the program, so each quoted structure is
  ;;;     constructed exactly once and every occurrence reads (global label)
  (export lower-source-program
          lower-unit-body
          global-cell-label
          mangle-library-name
          unit-body-label)
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

;; A library name is a list of symbols (R7RS also allows exact non-negative
;; integers). Length-prefixing each component before concatenating keeps the
;; encoding self-delimiting and therefore collision-free: (math vectors) and
;; (mathvec tors), say, can never mangle to the same text, because the
;; component lengths (4/7 vs. 7/4) are baked into the output itself.
(define (mangle-library-name-component part)
  (let ((text (mangle-identifier (if (symbol? part) part (number->string part)))))
    (string-append (number->string (string-length text)) text)))

(define (mangle-library-name name)
  (apply string-append (map mangle-library-name-component name)))

;; unit-name is #f for a plain program (today's single-unit compiles: no
;; qualification needed, since nothing else can ever reference or collide
;; with a program's own globals) or a library name list, in which case every
;; label this unit emits -- its own top-level defines and its hoisted quotes
;; alike -- is qualified by it. That's what lets two independently compiled
;; libraries each have their own private top-level `helper` without their
;; storage cells colliding once both are linked into the same executable.
(define (unit-label-prefix unit-name)
  (if unit-name (string-append (mangle-library-name unit-name) "_") ""))

;; Every compiled unit -- library or program alike -- gets a body procedure
;; that runs its top-level forms in order, labeled by a caller-supplied
;; unit-id string rather than the reserved scheme_entry (compiler.scm decides
;; what id to use -- a library's own mangled name is the natural default, a
;; program needs some other caller-chosen identifier since it has no library
;; name). The generated link stub (see compiler.scm) is the only place that
;; ever defines scheme_entry itself: it calls every other unit's body
;; procedure by this label, then the program unit's, and exposes that last
;; call's result as scheme_entry's own return value.
(define (unit-body-label unit-id)
  (string->symbol (string-append "hop_unit_body_" (mangle-identifier unit-id))))

;; A top-level define's storage label. "hop_g_" keeps this namespace apart
;; from procedure labels and GC-descriptor labels.
(define (global-cell-label unit-name name)
  (string->symbol
   (string-append "hop_g_" (unit-label-prefix unit-name) (mangle-identifier name))))

(define (collect-top-level-global-env forms unit-name)
  (let loop ((rest forms) (env '()))
    (if (null? rest)
        env
        (let ((form (car rest)))
          (if (top-level-define-form? form)
              (let ((name (cadr form)))
                (if (assoc name env)
                    (loop (cdr rest) env)
                    (loop (cdr rest)
                          (cons (list name (global-cell-label unit-name name)) env))))
              (loop (cdr rest) env))))))

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

;; external-resolver is consulted for a free name this unit doesn't itself
;; define -- (lambda (name) #f) for a plain program (today's behavior: any
;; name not locally defined just passes through unresolved, same as always),
;; or a lookup across a unit's declared imports' exports, returning the
;; exporting library's own (deterministically, independently computable)
;; label for that name, or #f if no import covers it.
(define (resolve-globals expr local-env global-env external-resolver hoist-quote!)
  (define (resolve e local-env)
    (cond
     ((symbol? e)
      (if (memq e local-env)
          e
          (let ((binding (assoc e global-env)))
            (if binding
                `(global ,(cadr binding))
                (let ((external-label (external-resolver e)))
                  (if external-label
                      `(global ,external-label)
                      e))))))
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
                       (resolve body-expr (append (params-names params) local-env)))
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
        ((apply)
         `(apply ,(resolve (cadr e) local-env)
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

;; A hoisted quoted structure's storage label. These are compiler-synthesized
;; (never looked up by name -- a library never exports a quote-hoisted cell
;; directly), so a private counter-based suffix is enough to keep them
;; distinct from each other; "hop_q_" keeps them out of the user-name-derived
;; "hop_g_" namespace. Still unit-qualified, though: two libraries each
;; hoisting their own first quoted list would otherwise both produce
;; hop_q_0 and collide once linked together.
(define (quote-cell-label unit-name index)
  (string->symbol
   (string-append "hop_q_" (unit-label-prefix unit-name) (number->string index))))

;; Shared core behind both lower-source-program and lower-unit-body: resolve
;; every top-level define into a storage cell (qualified by unit-name, or
;; unqualified when unit-name is #f) and every free reference either to a
;; local cell, to whatever external-resolver reports for an imported name, or
;; -- if neither applies -- left as a bare symbol, exactly as today for a
;; plain, importless program.
(define (lower-forms forms unit-name external-resolver)
  (let* ((global-env (collect-top-level-global-env forms unit-name))
         (next-quote-index 0)
         (quote-labels '())
         (quote-inits '()))
    (define (hoist-quote! datum)
      ;; Quoted structure gets a compiler-assigned cell, initialized before
      ;; any user form runs, so every read of the label sees the fully built
      ;; structure.
      (let ((label (quote-cell-label unit-name next-quote-index)))
        (set! next-quote-index (+ next-quote-index 1))
        (set! quote-labels (cons label quote-labels))
        (set! quote-inits
              (cons `(set-global! ,label ,(quoted-datum->constructor datum))
                    quote-inits))
        `(global ,label)))
    (if (null? forms)
        (error "Program requires at least one top-level form")
        (let ((resolved-forms
               (map (lambda (form)
                      (if (top-level-define-form? form)
                          ;; Top-level define is not a local binder after this
                          ;; point; it is an ordered write into a
                          ;; compiler-assigned cell.
                          `(set-global! ,(global-slot (cadr form) global-env)
                                        ,(resolve-globals (caddr form)
                                                          '()
                                                          global-env
                                                          external-resolver
                                                          hoist-quote!))
                          (resolve-globals form '() global-env external-resolver hoist-quote!)))
                    forms)))
          (values
           (body->expr (append (reverse quote-inits) resolved-forms))
           (append (map cadr global-env) (reverse quote-labels))
           global-env)))))

(define (no-external-binding name) #f)

(define (lower-source-program source)
  (let-values (((expr labels env)
                (lower-forms (flatten-top-level-forms (source->forms source))
                             #f
                             no-external-binding)))
    (values expr labels)))

;; The define-library/import-aware entry point: forms is a unit's body (a
;; library's (begin ...) contents, or a program's forms after any leading
;; import declarations), unit-name is that library's name (or #f for a
;; program), and external-resolver looks a free name up across the unit's
;; imports (see (hop pass unit) for parsing define-library/import into that
;; shape) -- typically built by resolving each imported library's declared
;; exports to labels via global-cell-label with THAT library's name, which a
;; caller can always compute without needing that library's compiled output,
;; only its declared name and export list. Returns the lowered expression,
;; every global label this unit's own storage needs, and the local
;; (name label) environment so a caller can cross-reference it against this
;; unit's own export list.
(define (lower-unit-body forms unit-name external-resolver)
  (lower-forms (flatten-top-level-forms forms) unit-name external-resolver))

)) ; end define-library
