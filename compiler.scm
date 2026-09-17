;;; A small Scheme-to-AArch64 compiler.
;;;
;;; This file is the top-level driver. The compiler passes live in the hop/
;;; library directory and are imported below.
;;;
;;;   source program
;;;     -> surface desugaring        (hop pass surface)
;;;     -> program lowering          (hop pass lower)
;;;     -> uniquify                  (hop pass uniquify)
;;;     -> letrec simplification     (hop pass letrec)
;;;     -> letrec desugaring         (hop pass letrec)
;;;     -> closure conversion        (hop pass closure)
;;;     -> three-address code (TAC)  (hop pass tac)
;;;     -> control-flow graph (CFG)  (hop pass cfg)
;;;     -> backend + allocation      (hop backend)
;;;     -> AArch64 assembly          (hop backend)

;; hop/includes.scm is generated from the (import ...) clauses in hop/**/*.sld
;; by tools/gen-includes.scm (run via `make hop/includes.scm`, or the
;; build/test/repl targets that depend on it) -- it never needs to be
;; hand-edited when a pass file is added, removed, or rewired.
(include "hop/includes.scm")

(import (scheme base)
        (scheme read)
        (scheme write)
        (scheme file)
        (hop utils)
        (hop pass surface)
        (hop pass unit)
        (hop pass lower)
        (hop pass uniquify)
        (hop pass letrec)
        (hop pass closure)
        (hop pass cfa)
        (hop pass tac)
        (hop pass cfg)
        (hop backend))

;;; ============================================================================
;;; Main Compiler Driver
;;; These entry points stitch the passes together:
;;;
;;;   - compile-to-cfg: stop after the middle end
;;;   - compile-to-backend: run through allocation/finalization
;;;   - write-aarch64-program: emit assembly to a file
;;;   - write-aarch64-program-file: read forms from a source file first
;;;   - compile-program: educational debugging view of the intermediate stages
;;; ============================================================================

;; Shared by every entry point below, whichever way a lowered program's
;; top-level bindings got their labels (plain compile-to-cfg's unqualified
;; ones, or compile-unit-to-cfg's library-qualified ones): from uniquify's
;; output through the optimized entry/procedure CFGs, a lowered program looks
;; the same either way.
(define (uniquified->cfgs uniquified)
  (let* ((canonicalized (canonicalize-builtins uniquified))
         (letrec-simplified (simplify-letrec canonicalized))
         (desugared (desugar-letrec letrec-simplified))
         (closure-converted (closure-convert desugared))
         (cfa-normalized (normalize-for-cfa closure-converted))
         (cfa-analysis (run-0cfa cfa-normalized))
         (cfa-rewritten (rewrite-known-calls cfa-normalized cfa-analysis)))
    (let-values (((tac-instrs procedures) (expr->tac cfa-rewritten)))
      (let* ((entry-cfg (build-cfg tac-instrs))
             (procedure-cfgs
              (map (lambda (procedure)
                     (cons procedure
                     (build-cfg (procedure-instructions procedure))))
                   procedures))
             (optimized-entry-cfg
               (eliminate-dead-writes-cfg
                 (constant-fold-cfg
                   (optimize-unsafe-arith-cfg
                     (optimize-unsafe-car-cdr-cfg entry-cfg)))))
             (optimized-procedure-cfgs
               (map (lambda (procedure+cfg)
                      (cons (car procedure+cfg)
                      (eliminate-dead-writes-cfg
                        (constant-fold-cfg
                          (optimize-unsafe-arith-cfg
                            (optimize-unsafe-car-cdr-cfg (cdr procedure+cfg)))))))
                    procedure-cfgs)))
        (values canonicalized
                letrec-simplified
                desugared
                closure-converted
                cfa-normalized
                cfa-rewritten
                optimized-entry-cfg
                optimized-procedure-cfgs)))))

;; Turns a middle-end's optimized entry/procedure CFGs into allocated machine
;; procedures. entry-name is the entry procedure's own asm label -- always
;; scheme_entry for compile-to-backend below, but a library's own private
;; init label for compile-unit-to-backend (see (hop pass lower)'s
;; library-init-label).
(define (cfgs->machine-procedures entry-name entry-cfg procedures)
  (values (cfg->allocated-machine-procedure entry-name '() entry-cfg)
          (map (lambda (procedure+cfg)
                 (cfg->allocated-machine-procedure
                  (procedure-name (car procedure+cfg))
                  (procedure-params (car procedure+cfg))
                  (cdr procedure+cfg)))
               procedures)))

(define (compile-to-cfg expr)
  ;; Every public entry point goes through surface desugaring and program
  ;; lowering first, even the original "single expression" path. That keeps
  ;; the whole compiler talking about one uniform internal program shape.
  (let ((surface (desugar-surface expr)))
   (let-values (((lowered-program global-labels) (lower-source-program surface)))
    (let ((uniquified (uniquify lowered-program)))
      (let-values (((canonicalized letrec-simplified desugared closure-converted cfa-normalized
                     cfa-rewritten optimized-entry-cfg optimized-procedure-cfgs)
                    (uniquified->cfgs uniquified)))
        (values surface
                lowered-program
                global-labels
                uniquified
                canonicalized
                letrec-simplified
                desugared
                closure-converted
                cfa-normalized
                cfa-rewritten
                optimized-entry-cfg
                optimized-procedure-cfgs))))))

(define (compile-to-backend expr)
  (let-values (((surface lowered-program global-labels uniquified canonicalized letrec-simplified desugared closure-converted cfa-normalized
                              cfa-rewritten entry-cfg procedures)
                 (compile-to-cfg expr)))
    (let-values (((entry-machine procedure-machines)
                  (cfgs->machine-procedures 'scheme_entry entry-cfg procedures)))
      (values surface
              lowered-program
              global-labels
              uniquified
              canonicalized
              letrec-simplified
              desugared
              closure-converted
              cfa-normalized
              cfa-rewritten
              entry-cfg
              procedures
              entry-machine
              procedure-machines))))

;;; ============================================================================
;;; Compilation-unit driver (define-library / import aware)
;;; Mirrors compile-to-cfg/compile-to-backend/write-aarch64-program above, but
;;; enters through a parsed <compilation-unit> (see (hop pass unit)) instead
;;; of a bare expression, so a top-level define's storage label is qualified
;;; by the unit's own library name and a free reference can resolve against
;;; an imported library's exports instead of only this unit's own bindings.
;;; ============================================================================

;; Builds the external-resolver lower-unit-body needs: a lookup across
;; imported-units' exports to that exporting library's own label for the
;; name, computed the same deterministic way (hop pass lower)'s
;; global-cell-label always computes it -- so this never needs those
;; libraries' compiled output, only their declared name and export list.
;; imported-units is a list of <compilation-unit> records (kind 'library)
;; for every library named in unit's own imports.
(define (make-import-resolver imported-units)
  (lambda (name)
    (let loop ((rest imported-units))
      (cond
       ((null? rest) #f)
       ((memq name (compilation-unit-exports (car rest)))
        (global-cell-label (compilation-unit-name (car rest)) name))
       (else (loop (cdr rest)))))))

(define (compile-unit-to-cfg unit imported-units)
  (let* ((desugared-program (desugar-surface (cons 'program (compilation-unit-body unit))))
         (desugared-body (cdr desugared-program))
         (resolver (make-import-resolver imported-units)))
    (let-values (((lowered-program global-labels global-env)
                  (lower-unit-body desugared-body (compilation-unit-name unit) resolver)))
      (let ((uniquified (uniquify lowered-program)))
        (let-values (((canonicalized letrec-simplified desugared closure-converted cfa-normalized
                       cfa-rewritten optimized-entry-cfg optimized-procedure-cfgs)
                      (uniquified->cfgs uniquified)))
          (values desugared-program
                  lowered-program
                  global-labels
                  global-env
                  uniquified
                  canonicalized
                  letrec-simplified
                  desugared
                  closure-converted
                  cfa-normalized
                  cfa-rewritten
                  optimized-entry-cfg
                  optimized-procedure-cfgs))))))

;; A program unit keeps the reserved scheme_entry name the runtime harness
;; already expects; a library unit gets its own private init label instead
;; (see (hop pass lower)'s library-init-label), since many libraries' init
;; procedures need to coexist, and nothing outside the link step ever calls
;; one by name.
(define (unit-entry-name unit)
  (if (eq? (compilation-unit-kind unit) 'program)
      'scheme_entry
      (library-init-label (compilation-unit-name unit))))

(define (compile-unit-to-backend unit imported-units)
  (let-values (((desugared-program lowered-program global-labels global-env uniquified canonicalized
                 letrec-simplified desugared closure-converted cfa-normalized cfa-rewritten
                 entry-cfg procedures)
                (compile-unit-to-cfg unit imported-units)))
    (let-values (((entry-machine procedure-machines)
                  (cfgs->machine-procedures (unit-entry-name unit) entry-cfg procedures)))
      (values global-labels global-env entry-machine procedure-machines))))

(define (write-unit-aarch64-program unit imported-units path)
  (let-values (((global-labels global-env entry-machine procedure-machines)
                (compile-unit-to-backend unit imported-units)))
    (call-with-output-file path
      (lambda (port)
        (emit-aarch64-program port entry-machine procedure-machines global-labels
                               (unit-tag (compilation-unit-name unit)))))
    global-env))

(define (read-compilation-unit path)
  (parse-compilation-unit (read-program-forms path)))

(define (write-unit-aarch64-program-file input-path output-path imported-unit-paths)
  (write-unit-aarch64-program (read-compilation-unit input-path)
                               (map read-compilation-unit imported-unit-paths)
                               output-path))

(define (write-aarch64-program expr path)
  (let-values (((surface lowered-program global-labels uniquified canonicalized letrec-simplified desugared closure-converted cfa-normalized
                               cfa-rewritten entry-cfg procedures
                                entry-machine procedure-machines)
                   (compile-to-backend expr)))
    (call-with-output-file path
      (lambda (port)
        (emit-aarch64-program port entry-machine procedure-machines global-labels)))))

(define (write-aarch64-program-forms forms path)
  (write-aarch64-program (cons 'program forms) path))

;; (include "path") is R7RS-small's plain textual splice: it reads as though
;; the named file's forms appeared right there, in the same compilation unit
;; -- no exports, no separate storage-label namespace, nothing a linker is
;; involved in. A relative path resolves against the including file's own
;; directory (not the process's current directory), so an included file
;; reads the same regardless of where the compiler is invoked from -- the
;; same convention hop/includes.scm already relies on for the compiler's own
;; sources, just resolved per including file instead of always from the
;; project root.
(define (path-directory path)
  (let loop ((index (- (string-length path) 1)))
    (cond
     ((< index 0) "")
     ((char=? (string-ref path index) #\/) (substring path 0 index))
     (else (loop (- index 1))))))

(define (path-join dir name)
  (if (string=? dir "")
      name
      (string-append dir "/" name)))

(define (include-form? form)
  (and (pair? form)
       (eq? (car form) 'include)
       (pair? (cdr form))
       (string? (cadr form))
       (null? (cddr form))))

(define (expand-includes forms base-dir)
  (append-map
   (lambda (form)
     (if (include-form? form)
         (read-program-forms (path-join base-dir (cadr form)))
         (list form)))
   forms))

(define (read-program-forms path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((forms '()))
        (let ((form (read port)))
          (if (eof-object? form)
              (expand-includes (reverse forms) (path-directory path))
              (loop (cons form forms))))))))

(define (write-aarch64-program-file input-path output-path)
  (write-aarch64-program-forms (read-program-forms input-path) output-path))

(define (compile-program expr)
  ;; compile-program is intentionally pedagogical: it prints the major
  ;; representations in pipeline order so a reader can watch one source program
  ;; become lower-level at each pass boundary.
  (display "=== Source Program ===\n")
  (write expr) (newline)

  (let-values (((surface lowered-program global-labels uniquified canonicalized letrec-simplified desugared closure-converted cfa-normalized
                               cfa-rewritten entry-cfg procedures
                                entry-machine procedure-machines)
                 (compile-to-backend expr)))
    (display "\n=== After Surface Desugaring ===\n")
    (write surface) (newline)

    (display "\n=== After Program Lowering ===\n")
    (write lowered-program) (newline)
    (display "Global labels: ")
    (write global-labels)
    (newline)

    (display "\n=== After Uniquify ===\n")
    (write uniquified) (newline)

    (display "\n=== After Builtin Canonicalization ===\n")
    (write canonicalized) (newline)

    (display "\n=== After letrec Simplification ===\n")
    (write letrec-simplified) (newline)

    (display "\n=== After letrec Desugaring ===\n")
    (write desugared) (newline)

    (display "\n=== After Closure Conversion ===\n")
    (write closure-converted) (newline)

    (display "\n=== After CFA Normalization ===\n")
    (write cfa-normalized) (newline)

    (display "\n=== After 0CFA Call Rewriting ===\n")
    (write cfa-rewritten) (newline)

    (display "\n=== After Pair-Proven Unsafe car/cdr Rewrite (CFG) ===\n")
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

(define (compile-program-forms forms)
  (compile-program (cons 'program forms)))

;;; Test fixtures and demo helpers live in separate test-owned files so loading
;;; the compiler does not implicitly run or define the regression suite.
