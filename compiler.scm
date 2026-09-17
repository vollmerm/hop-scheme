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
;;;
;;; Compiling a unit produces two files: the AArch64 assembly (.s) and an
;;; interface (see write-interface-file below) -- a small, self-contained
;;; description of what this unit exports and what storage/GC/symbol
;;; bookkeeping it owns, meant to be read by whoever imports it or links it,
;;; without needing this unit's source or its compiled output. That's what
;;; makes compiling a dependent file not require recompiling, or even
;;; re-reading the source of, the units it imports -- only their interfaces.
;;;
;;; There is deliberately no automatic import-graph discovery here (no
;;; scanning a directory, no topological sort, no cycle detection): the
;;; caller supplies exactly the interface files a unit's imports should
;;; resolve against, and, later, the exact ordered list of units to link.
;;; That mirrors how C's own separate compilation works (and, per a mature
;;; precedent, how Chicken Scheme's own unit linking works) -- correct
;;; ordering is the caller's responsibility, not something the compiler
;;; infers by inspecting the filesystem.
;;; ============================================================================

;; Builds the external-resolver lower-unit-body needs: a lookup across
;; imported-interfaces' exports to that exporting library's own label for the
;; name. The label comes directly from the interface file rather than being
;; recomputed from the library's name here, so this file doesn't need to
;; duplicate (or stay in sync with) (hop pass lower)'s mangling scheme -- the
;; interface is the single source of truth for what a name resolves to.
(define (make-import-resolver imported-interfaces)
  (lambda (name)
    (let loop ((rest imported-interfaces))
      (cond
       ((null? rest) #f)
       ((assq name (interface-exports (car rest)))
        => cadr)
       (else (loop (cdr rest)))))))

(define (compile-unit-to-cfg unit imported-interfaces)
  (let* ((desugared-program (desugar-surface (cons 'program (compilation-unit-body unit))))
         (desugared-body (cdr desugared-program))
         (resolver (make-import-resolver imported-interfaces)))
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

(define (compile-unit-to-backend unit imported-interfaces unit-id)
  (let-values (((desugared-program lowered-program global-labels global-env uniquified canonicalized
                 letrec-simplified desugared closure-converted cfa-normalized cfa-rewritten
                 entry-cfg procedures)
                (compile-unit-to-cfg unit imported-interfaces)))
    (let-values (((body-machine procedure-machines)
                  (cfgs->machine-procedures (unit-body-label unit-id) entry-cfg procedures)))
      (values global-labels global-env body-machine procedure-machines))))

;;; ---- Interfaces -------------------------------------------------------
;;; A plain s-expression, read/written with the host Scheme's own
;;; read/write, tagged and versioned so a later format change can still
;;; recognize and reject an old file cleanly rather than misreading it:
;;;
;;;   (hop-interface (version 1)
;;;                  (unit-id "4math7vectors")
;;;                  (kind library)                 ; or program
;;;                  (library-name (math vectors))  ; or #f for a program
;;;                  (body-label hop_unit_body_4math7vectors)
;;;                  (exports ((add1 hop_g_4math7vectors_add1) ...))
;;;                  (all-globals (hop_g_4math7vectors_add1 ...))
;;;                  (symbols ((foo . 123) ...)))
;;;
;;; exports is what an importer's free references resolve against;
;;; all-globals is every storage cell this unit owns (exported or not,
;;; including hoisted quotes) and symbols is this unit's own interned-symbol
;;; table -- both needed only by the link step, to reconstruct one merged GC
;;; root table and symbol-printing table across every linked unit (see
;;; link-compiled-units below), since no single unit's own compile can see
;;; the others.
(define interface-format-version 1)

(define (write-interface-file path unit-id kind library-name body-label exports all-globals symbols)
  (call-with-output-file path
    (lambda (port)
      (write
       `(hop-interface (version ,interface-format-version)
                        (unit-id ,unit-id)
                        (kind ,kind)
                        (library-name ,library-name)
                        (body-label ,body-label)
                        (exports ,exports)
                        (all-globals ,all-globals)
                        (symbols ,symbols))
       port)
      (newline port))))

(define (interface-field iface key)
  (let ((entry (assq key (cdr iface))))
    (if entry
        (cadr entry)
        (error "Malformed hop interface: missing field" key iface))))

(define (read-interface-file path)
  (let ((form (call-with-input-file path read)))
    (if (not (and (pair? form) (eq? (car form) 'hop-interface)))
        (error "Not a hop interface file" path))
    (if (not (= (interface-field form 'version) interface-format-version))
        (error "Unsupported hop interface version" path (interface-field form 'version)))
    form))

(define (interface-kind iface) (interface-field iface 'kind))
(define (interface-body-label iface) (interface-field iface 'body-label))
(define (interface-exports iface) (interface-field iface 'exports))
(define (interface-all-globals iface) (interface-field iface 'all-globals))
(define (interface-symbols iface) (interface-field iface 'symbols))

(define (write-unit-aarch64-program unit imported-interfaces unit-id asm-path interface-path)
  (let-values (((global-labels global-env body-machine procedure-machines)
                (compile-unit-to-backend unit imported-interfaces unit-id)))
    (let ((symbols #f))
      (call-with-output-file asm-path
        (lambda (port)
          (set! symbols
                (emit-unit-aarch64-program port body-machine procedure-machines global-labels))))
      (write-interface-file
       interface-path
       unit-id
       (compilation-unit-kind unit)
       (compilation-unit-name unit)
       (machine-procedure-name body-machine)
       (filter (lambda (binding) (memq (car binding) (compilation-unit-exports unit))) global-env)
       global-labels
       symbols))))

(define (read-compilation-unit path)
  (parse-compilation-unit (read-program-forms path)))

;; A library's unit-id is always its own mangled library name -- the only
;; thing that has to line up between independent compiles is a name's
;; storage label, which (hop pass lower)'s global-cell-label already derives
;; from the library name directly, so deriving the same file's unit-id from
;; it too is just a consistent choice, not a requirement anything else
;; depends on. A program has no library name, so its unit-id instead comes
;; from its own filename -- it never needs to be predicted by anyone else,
;; only used to keep its own body-procedure label out of the way of every
;; other linked unit's.
(define (path-basename path)
  (let ((dir (path-directory path)))
    (if (string=? dir "")
        path
        (substring path (+ 1 (string-length dir)) (string-length path)))))

(define (path-strip-extension name)
  (let loop ((index (- (string-length name) 1)))
    (cond
     ((< index 0) name)
     ((char=? (string-ref name index) #\.) (substring name 0 index))
     (else (loop (- index 1))))))

(define (default-unit-id unit path)
  (if (compilation-unit-name unit)
      (mangle-library-name (compilation-unit-name unit))
      (path-strip-extension (path-basename path))))

(define (write-unit-aarch64-program-file input-path interface-paths asm-output-path interface-output-path)
  (let* ((unit (read-compilation-unit input-path))
         (unit-id (default-unit-id unit input-path))
         (imported-interfaces (map read-interface-file interface-paths)))
    (write-unit-aarch64-program unit imported-interfaces unit-id asm-output-path interface-output-path)))

;;; ---- Linking ------------------------------------------------------------
;;; Takes an explicit, caller-ordered list of already-compiled units'
;;; interface files (see above -- no discovery, no sorting) and generates one
;;; small C stub that, together with those units' .s files and runtime.c,
;;; assembles into a complete program:
;;;
;;;   - one merged hop_global_roots/hop_global_root_count, built from every
;;;     linked unit's all-globals, so the GC can still find every cell no
;;;     matter which unit it lives in;
;;;   - one merged hop_symbol_hashes/hop_symbol_name_ptrs/hop_symbol_count,
;;;     built from every linked unit's own symbol table (deduplicated by
;;;     hash -- the same symbol interned in two units is harmless to list
;;;     twice, but there's no reason to);
;;;   - scheme_entry itself: calls every library unit's body procedure, in
;;;     the order they appear in the given list, then the one program unit's,
;;;     returning its result. Nothing about this needs to know how many
;;;     imports any unit declared or in what order -- it only needs the flat
;;;     list of units the caller wants instantiated and which one is the
;;;     program.
;;;
;;; A C stub (rather than another .s file) is deliberate: calling a sequence
;;; of no-argument procedures and declaring a couple of arrays is exactly
;;; what C is for, and it sidesteps hand-rolling AArch64 prologues/epilogues
;;; for what's ultimately just glue.

(define (dedupe-symbol-entries entries)
  (let loop ((rest entries) (seen-hashes '()) (result '()))
    (cond
     ((null? rest) (reverse result))
     ((memv (cdr (car rest)) seen-hashes) (loop (cdr rest) seen-hashes result))
     (else (loop (cdr rest) (cons (cdr (car rest)) seen-hashes) (cons (car rest) result))))))

(define (check-no-duplicate-labels labels)
  (let loop ((rest labels) (seen '()))
    (cond
     ((null? rest) 'ok)
     ((memq (car rest) seen)
      (error "Duplicate global label across linked units -- same unit linked twice?" (car rest)))
     (else (loop (cdr rest) (cons (car rest) seen))))))

(define (c-string-escape text)
  (apply string-append
         (map (lambda (ch)
                (cond
                 ((char=? ch #\") "\\\"")
                 ((char=? ch #\\) "\\\\")
                 (else (string ch))))
              (string->list text))))

(define (emit-c-line port text)
  (display text port)
  (newline port))

;; Emits `decl-prefix[] = { ...items... };`, falling back to a harmless
;; single-element dummy when items is empty -- an empty C array initializer
;; ("{}") isn't portable, and the runtime never reads past this array's
;; associated *_count, which stays 0 in that case.
(define (emit-c-array port decl-prefix items render-item)
  (if (null? items)
      (emit-c-line port (string-append decl-prefix "[1] = {0};"))
      (begin
        (emit-c-line port (string-append decl-prefix "[] = {"))
        (for-each (lambda (item)
                    (emit-c-line port (string-append "    " (render-item item) ",")))
                  items)
        (emit-c-line port "};"))))

(define (emit-link-stub port interfaces library-interfaces program all-globals merged-symbols)
  (emit-c-line port "#include \"runtime.h\"")
  (emit-c-line port "")
  (for-each (lambda (label)
              (emit-c-line port (string-append "extern hop_value " (symbol->string label) ";")))
            all-globals)
  (emit-c-line port "")
  (for-each (lambda (iface)
              (emit-c-line port
                           (string-append "extern hop_value "
                                          (symbol->string (interface-body-label iface))
                                          "(void);")))
            interfaces)
  (emit-c-line port "")
  (emit-c-array port "hop_value *hop_global_roots" all-globals
                (lambda (label) (string-append "&" (symbol->string label))))
  (emit-c-line port
               (string-append "uint64_t hop_global_root_count = "
                              (number->string (length all-globals)) ";"))
  (emit-c-line port "")
  (emit-c-array port "uint64_t hop_symbol_hashes" merged-symbols
                (lambda (entry) (number->string (cdr entry))))
  (emit-c-array port "const char *hop_symbol_name_ptrs" merged-symbols
                (lambda (entry) (string-append "\"" (c-string-escape (symbol->string (car entry))) "\"")))
  (emit-c-line port
               (string-append "uint64_t hop_symbol_count = "
                              (number->string (length merged-symbols)) ";"))
  (emit-c-line port "")
  (emit-c-line port "hop_value scheme_entry(void) {")
  (for-each (lambda (iface)
              (emit-c-line port (string-append "    " (symbol->string (interface-body-label iface)) "();")))
            library-interfaces)
  (emit-c-line port
               (string-append "    return " (symbol->string (interface-body-label program)) "();"))
  (emit-c-line port "}"))

(define (link-compiled-units interface-paths stub-output-path)
  (let* ((interfaces (map read-interface-file interface-paths))
         (program-interfaces (filter (lambda (iface) (eq? (interface-kind iface) 'program)) interfaces))
         (library-interfaces (filter (lambda (iface) (eq? (interface-kind iface) 'library)) interfaces))
         (all-globals (append-map interface-all-globals interfaces))
         (merged-symbols (dedupe-symbol-entries (append-map interface-symbols interfaces))))
    (if (not (= (length program-interfaces) 1))
        (error "Linking requires exactly one program unit among the given interfaces"
               interface-paths))
    (check-no-duplicate-labels all-globals)
    (call-with-output-file stub-output-path
      (lambda (port)
        (emit-link-stub port interfaces library-interfaces (car program-interfaces)
                         all-globals merged-symbols)))))

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
