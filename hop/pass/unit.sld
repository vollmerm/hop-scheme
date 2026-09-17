(define-library (hop pass unit)
  ;;; Compilation-unit parsing: recognizes the two R7RS-small forms a source
  ;;; file can open with -- (define-library (name ...) ...) for a library, or
  ;;; a bare program (optionally preceded by top-level (import ...)
  ;;; declarations) -- and turns either into a <compilation-unit> record that
  ;;; (hop pass lower)'s lower-unit-body and a later per-file compile driver
  ;;; both consume.
  ;;;
  ;;; Only whole-library imports are supported for now: (import (lib name))
  ;;; pulls in everything (lib name) exports. R7RS's other import sets --
  ;;; only/except/rename/prefix -- aren't recognized yet; that's a scoped-down
  ;;; deliberate omission (see the plan this pass implements), not an
  ;;; oversight, and can be added later without disturbing anything below it.
  ;;;
  ;;; (include "path") is a different, simpler feature -- pure textual
  ;;; splicing at read time -- and is handled before this pass ever runs (see
  ;;; compiler.scm's read-program-forms), not here.
  (export make-compilation-unit
          compilation-unit?
          compilation-unit-kind
          compilation-unit-name
          compilation-unit-exports
          compilation-unit-imports
          compilation-unit-body
          library-name?
          parse-compilation-unit)
  (import (scheme base)
          (scheme cxr)
          (hop utils))
  (begin

(define-record-type <compilation-unit>
  (make-compilation-unit kind name exports imports body)
  compilation-unit?
  ;; kind is 'library or 'program.
  (kind compilation-unit-kind)
  ;; name is a library-name list for a library, #f for a program.
  (name compilation-unit-name)
  ;; exports is the list of locally-defined names a library makes visible to
  ;; importers; always '() for a program (nothing can import a program).
  (exports compilation-unit-exports)
  ;; imports is a list of library-name lists this unit pulls bindings from.
  (imports compilation-unit-imports)
  ;; body is the plain list of top-level forms (defines/expressions) this
  ;; unit contains -- a library's (begin ...) contents, or a program's forms
  ;; after any leading (import ...) declarations. Same shape either way, and
  ;; the same shape lower-source-program already accepted before this pass
  ;; existed.
  (body compilation-unit-body))

(define (library-name-part? part)
  (or (symbol? part)
      (and (integer? part) (exact? part) (>= part 0))))

(define (library-name? name)
  (and (list? name)
       (pair? name)
       (all library-name-part? name)))

(define (define-library-form? form)
  (and (pair? form) (eq? (car form) 'define-library)))

(define (import-form? form)
  (and (pair? form) (eq? (car form) 'import)))

(define (parse-import-set spec)
  (if (library-name? spec)
      spec
      (error "Unsupported import set (only whole-library imports are supported)" spec)))

(define (parse-import-clause clause)
  (map parse-import-set (cdr clause)))

(define (export-declaration? decl)
  (and (pair? decl) (eq? (car decl) 'export)))

(define (begin-declaration? decl)
  (and (pair? decl) (eq? (car decl) 'begin)))

(define (export-spec->name spec)
  ;; (export id ...) only -- R7RS also allows (rename internal external), not
  ;; supported yet for the same reason import sets are scoped down above.
  (if (symbol? spec)
      spec
      (error "Unsupported export spec (only plain identifiers are supported)" spec)))

(define (parse-library-declarations decls)
  (let loop ((rest decls) (exports '()) (imports '()) (body '()))
    (if (null? rest)
        (values (reverse exports) (reverse imports) (reverse body))
        (let ((decl (car rest)))
          (cond
           ((export-declaration? decl)
            (loop (cdr rest)
                  (append (reverse (map export-spec->name (cdr decl))) exports)
                  imports
                  body))
           ((import-form? decl)
            (loop (cdr rest)
                  exports
                  (append (reverse (parse-import-clause decl)) imports)
                  body))
           ((begin-declaration? decl)
            (loop (cdr rest) exports imports (append (reverse (cdr decl)) body)))
           (else
            (error "Unsupported library declaration" decl)))))))

(define (parse-library-unit forms)
  (if (not (null? (cdr forms)))
      (error "A library file must contain exactly one define-library form and nothing else"
             forms)
      (let* ((form (car forms))
             (name (cadr form)))
        (if (not (library-name? name))
            (error "Invalid library name" name))
        (let-values (((exports imports body) (parse-library-declarations (cddr form))))
          (make-compilation-unit 'library name exports imports body)))))

(define (parse-program-unit forms)
  (let loop ((rest forms) (imports '()))
    (if (and (pair? rest) (import-form? (car rest)))
        (loop (cdr rest) (append (reverse (parse-import-clause (car rest))) imports))
        (make-compilation-unit 'program #f '() (reverse imports) rest))))

(define (parse-compilation-unit forms)
  (if (and (pair? forms) (define-library-form? (car forms)))
      (parse-library-unit forms)
      (parse-program-unit forms)))

)) ; end define-library
