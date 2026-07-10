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

(include "hop/utils.sld")
(include "hop/pass/surface.sld")
(include "hop/pass/lower.sld")
(include "hop/pass/uniquify.sld")
(include "hop/pass/letrec.sld")
(include "hop/pass/closure.sld")
(include "hop/pass/cfa.sld")
(include "hop/pass/tac.sld")
(include "hop/pass/cfg.sld")
(include "hop/backend.sld")

(import (scheme base)
        (scheme read)
        (scheme write)
        (scheme file)
        (hop utils)
        (hop pass surface)
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

(define (compile-to-cfg expr)
  ;; Every public entry point goes through surface desugaring and program
  ;; lowering first, even the original "single expression" path. That keeps
  ;; the whole compiler talking about one uniform internal program shape.
  (let ((surface (desugar-surface expr)))
   (let-values (((lowered-program global-count) (lower-source-program surface)))
    (let* ((uniquified (uniquify lowered-program))
           (canonicalized (canonicalize-builtins uniquified))
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
             (values surface
               lowered-program
               global-count
               uniquified
               canonicalized
               letrec-simplified
               desugared
               closure-converted
               cfa-normalized
               cfa-rewritten
              optimized-entry-cfg
              optimized-procedure-cfgs)))))))

(define (compile-to-backend expr)
  (let-values (((surface lowered-program global-count uniquified canonicalized letrec-simplified desugared closure-converted cfa-normalized
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
      (values surface
              lowered-program
              global-count
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

(define (write-aarch64-program expr path)
  (let-values (((surface lowered-program global-count uniquified canonicalized letrec-simplified desugared closure-converted cfa-normalized
                               cfa-rewritten entry-cfg procedures
                                entry-machine procedure-machines)
                   (compile-to-backend expr)))
    (call-with-output-file path
      (lambda (port)
        (emit-aarch64-program port entry-machine procedure-machines global-count)))))

(define (write-aarch64-program-forms forms path)
  (write-aarch64-program (cons 'program forms) path))

(define (read-program-forms path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((forms '()))
        (let ((form (read port)))
          (if (eof-object? form)
              (reverse forms)
              (loop (cons form forms))))))))

(define (write-aarch64-program-file input-path output-path)
  (write-aarch64-program-forms (read-program-forms input-path) output-path))

(define (compile-program expr)
  ;; compile-program is intentionally pedagogical: it prints the major
  ;; representations in pipeline order so a reader can watch one source program
  ;; become lower-level at each pass boundary.
  (display "=== Source Program ===\n")
  (write expr) (newline)

  (let-values (((surface lowered-program global-count uniquified canonicalized letrec-simplified desugared closure-converted cfa-normalized
                               cfa-rewritten entry-cfg procedures
                                entry-machine procedure-machines)
                 (compile-to-backend expr)))
    (display "\n=== After Surface Desugaring ===\n")
    (write surface) (newline)

    (display "\n=== After Program Lowering ===\n")
    (write lowered-program) (newline)
    (display "Global slots: ")
    (write global-count)
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
