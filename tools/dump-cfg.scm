;;; Prints the control-flow graph (or allocated machine code) the compiler
;;; produces for one program, for inspecting what a pass did.
;;;
;;; Usage, from the repo root:
;;;   csi -R r7rs -I . -s tools/dump-cfg.scm <program.scm | testNN> [stage]
;;;   guile --r7rs -L . -s tools/dump-cfg.scm <program.scm | testNN> [stage]
;;;   make dump T=<program.scm | testNN> [STAGE=cfg|machine]
;;;
;;; <target> is a path to a source file (a sequence of top-level forms, as
;;; accepted by write-aarch64-program-file) or the name of a fixture defined
;;; in compiler_tests.scm, such as test34.
;;;
;;; stage is
;;;   cfg      (default) the middle end's final CFGs: the entry procedure and
;;;            every other procedure, after all CFG optimization passes
;;;   machine  the same procedures after instruction selection, register
;;;            allocation, and frame finalization

(import (scheme base)
        (scheme file)
        (scheme read)
        (scheme write)
        (scheme process-context))

;; HOP_COMPILER (set by tools/scheme.sh) names the compiled compiler to load.
(load (or (get-environment-variable "HOP_COMPILER") "compiler.scm"))
(load (string-append (or (get-environment-variable "HOP_ROOT") ".") "/compiler_tests.scm"))
(import (hop pass tac) (hop pass cfg) (hop backend))

(define (usage)
  (display "usage: dump-cfg.scm <program.scm | testNN> [cfg|machine]\n"
           (current-error-port))
  (exit 2))

(define (target->expr target)
  (if (file-exists? target)
      (cons 'program (read-program-forms target))
      (lookup-named-test (string->symbol target))))

(define (print-cfg title params cfg)
  (display "== ") (display title)
  (when params (display " ") (write params))
  (display " ==\n")
  (let loop ((blocks cfg) (index 0))
    (unless (null? blocks)
      (let ((block (car blocks)))
        (display "block ") (display index)
        (display " ")
        (display (or (basic-block-label block) "<entry>"))
        (display "  -> ")
        (write (basic-block-successors block))
        (newline)
        (for-each (lambda (instr) (display "    ") (write instr) (newline))
                  (basic-block-instructions block)))
      (loop (cdr blocks) (+ index 1))))
  (newline))

(define (dump-cfg expr)
  (let-values (((surface lowered global-labels uniquified canonicalized
                         letrec-simplified desugared closure-converted
                         cfa-normalized cfa-rewritten entry-cfg procedures)
                (compile-to-cfg expr)))
    (print-cfg "entry" #f entry-cfg)
    (for-each (lambda (procedure+cfg)
                (print-cfg (procedure-name (car procedure+cfg))
                           (procedure-params (car procedure+cfg))
                           (cdr procedure+cfg)))
              procedures)))

(define (dump-machine expr)
  (let-values (((surface lowered global-labels uniquified canonicalized
                         letrec-simplified desugared closure-converted
                         cfa-normalized cfa-rewritten entry-cfg procedures
                         entry-machine procedure-machines)
                (compile-to-backend expr)))
    (for-each display-machine-procedure
              (cons entry-machine procedure-machines))))

(let ((args (cdr (command-line))))
  (when (or (null? args) (> (length args) 2)) (usage))
  (let ((expr (target->expr (car args)))
        (stage (if (pair? (cdr args)) (cadr args) "cfg")))
    (cond
     ((string=? stage "cfg") (dump-cfg expr))
     ((string=? stage "machine") (dump-machine expr))
     (else (usage)))))
