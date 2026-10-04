(define-library (hop pass inline)
  ;;; Pass 4.5: inline small known procedures in TAC
  ;;;
  ;;; A known call is (assign r (direct-call P arg ...)) or a
  ;;; (direct-tail-call P arg ...); captured variables travel as leading
  ;;; arguments, so P's instructions are closed over its parameters and can be
  ;;; copied into the caller after renaming every variable and label. At a
  ;;; non-tail call site each (return v) becomes a copy into r and a jump to a
  ;;; fresh join label, and each tail call in P becomes the matching ordinary
  ;;; call; at a tail call site P's returns and tail calls stay as they are.
  ;;;
  ;;; Only procedures that are not part of a direct-call cycle (so letrec
  ;;; clusters and self-recursive procedures are left alone) and whose
  ;;; instruction count, after their own calls are inlined, is at most
  ;;; max-size are copied. Procedures are never removed, so the originals stay
  ;;; available to closures and unknown callers.
  (export inline-known-calls
          prune-dead-procedures)
  (import (scheme base)
          (scheme cxr)
          (only (srfi 1) filter delete-duplicates any)
          (srfi 69)
          (hop utils)
          (hop pass tac)
          (hop pass ssa))
  (begin

(define (direct-callee instr)
  (cond
   ((and (pair? instr) (eq? (car instr) 'direct-tail-call)) (cadr instr))
   ((and (pair? instr)
         (eq? (car instr) 'assign)
         (pair? (caddr instr))
         (eq? (car (caddr instr)) 'direct-call))
    (cadr (caddr instr)))
   (else #f)))

(define (instruction-size instrs)
  (length (filter (lambda (i) (not (eq? (car i) 'label))) instrs)))

;; The names of the procedures that can reach themselves through direct calls.
(define (recursive-procedures table)
  (let ((callees (make-hash-table))
        (recursive (make-hash-table)))
    (for-each
     (lambda (name)
       (hash-table-set!
        callees name
        (delete-duplicates
         (filter (lambda (c) c)
                 (map direct-callee
                      (procedure-instructions (hash-table-ref table name)))))))
     (hash-table-keys table))
    (for-each
     (lambda (start)
       (let ((seen (make-hash-table)))
         (let visit ((name start))
           (for-each
            (lambda (next)
              (when (eq? next start) (hash-table-set! recursive start #t))
              (unless (hash-table-exists? seen next)
                (hash-table-set! seen next #t)
                (when (hash-table-exists? table next) (visit next))))
            (hash-table-ref/default callees name '())))))
     (hash-table-keys table))
    recursive))

;; Copies callee-instrs for one call site. result is the variable that gets the
;; call's value, or #f at a tail call site.
(define (inline-site params callee-instrs args result suffix)
  (let ((names (make-hash-table))
        (labels (make-hash-table))
        (join (string->symbol (string-append "inl" suffix))))
    (define (renamed table name)
      (string->symbol (string-append (symbol->string name) "." suffix)))
    (define (note! table name)
      (unless (hash-table-exists? table name)
        (hash-table-set! table name (renamed table name))))
    (define (var v) (if (symbol? v) (hash-table-ref/default names v v) v))
    (define (label l) (hash-table-ref/default labels l l))
    (for-each (lambda (p) (note! names p)) params)
    (for-each (lambda (instr)
                (cond ((eq? (car instr) 'assign) (note! names (cadr instr)))
                      ((eq? (car instr) 'label) (note! labels (cadr instr)))))
              callee-instrs)
    (define (rename instr)
      (case (car instr)
        ((label) `(label ,(label (cadr instr))))
        ((goto) `(goto ,(label (cadr instr))))
        ((if) `(if ,(var (cadr instr)) ,(label (caddr instr)) ,(label (cadddr instr))))
        ((assign)
         (let ((renamed-uses (map-instr-uses var instr)))
           `(assign ,(var (cadr instr)) ,(caddr renamed-uses))))
        (else (map-instr-uses var instr))))
    (define (as-call instr)
      ;; The ordinary-call form of a tail call, assigned to result.
      (let ((call (rename instr)))
        (case (car call)
          ((tail-call) `(assign ,result (closure-call ,@(cdr call))))
          ((tail-apply-call) `(assign ,result (apply-call ,@(cdr call))))
          ((tail-callcc-call) `(assign ,result (callcc-call ,@(cdr call))))
          ((direct-tail-call) `(assign ,result (direct-call ,@(cdr call))))
          (else (error "inline: unexpected tail form" instr)))))
    (append
     (map (lambda (p a) `(assign ,(var p) ,a)) params args)
     (apply append
            (map (lambda (instr)
                   (cond
                    ((not result) (list (rename instr)))
                    ((eq? (car instr) 'return)
                     (list `(assign ,result ,(var (cadr instr))) `(goto ,join)))
                    ((memq (car instr) '(tail-call tail-apply-call tail-callcc-call
                                         direct-tail-call))
                     (list (as-call instr) `(goto ,join)))
                    (else (list (rename instr)))))
                 callee-instrs))
     (if result (list `(label ,join)) '()))))

(define (inline-known-calls entry-instrs procedures max-size)
  (let* ((table (make-hash-table))
         (recursive #f)
         (expanded (make-hash-table))
         (counter 0))
    (for-each (lambda (p) (hash-table-set! table (procedure-name p) p)) procedures)
    (set! recursive (recursive-procedures table))
    (define (inlinable? name)
      (and (hash-table-exists? table name)
           (not (hash-table-exists? recursive name))
           (not (params-variadic? (procedure-params (hash-table-ref table name))))
           (<= (instruction-size (expanded-body name)) max-size)))
    (define (expanded-body name)
      (or (hash-table-ref/default expanded name #f)
          (let ((body (expand (procedure-instructions (hash-table-ref table name)))))
            (hash-table-set! expanded name body)
            body)))
    (define (fresh-suffix)
      (set! counter (+ counter 1))
      (string-append "i" (number->string counter)))
    (define (expand instrs)
      (apply append
             (map (lambda (instr)
                    (let ((callee (direct-callee instr)))
                      (if (and callee (inlinable? callee))
                          (let ((p (hash-table-ref table callee)))
                            (if (eq? (car instr) 'direct-tail-call)
                                (inline-site (params-names (procedure-params p))
                                             (expanded-body callee)
                                             (cddr instr) #f (fresh-suffix))
                                (inline-site (params-names (procedure-params p))
                                             (expanded-body callee)
                                             (cddr (caddr instr))
                                             (cadr instr) (fresh-suffix))))
                          (list instr))))
                  instrs)))
    (values (expand entry-instrs)
            (map (lambda (p)
                   (make-procedure (procedure-name p)
                                   (procedure-params p)
                                   (expanded-body (procedure-name p))))
                 procedures))))

;;; --- Dropping what nothing uses ---
;;;
;;; A top-level definition is a store into a global cell. When no code reads
;;; the cell and no other unit can (it is not exported), the store is dead, and
;;; so is the closure it stores if that is all the closure was for. Procedures
;;; no remaining closure or call refers to are dropped.

(define (rhs-of instr)
  (and (pair? instr) (eq? (car instr) 'assign) (caddr instr)))

(define (global-reads instrs-lists)
  (let ((reads (make-hash-table)))
    (for-each
     (lambda (instrs)
       (for-each (lambda (instr)
                   (let ((rhs (rhs-of instr)))
                     (when (and (pair? rhs) (eq? (car rhs) 'global))
                       (hash-table-set! reads (cadr rhs) #t))))
                 instrs))
     instrs-lists)
    reads))

(define (referenced-procedure instr)
  (let ((rhs (rhs-of instr)))
    (cond
     ((and (pair? rhs) (memq (car rhs) '(make-closure make-variadic-closure direct-call)))
      (cadr rhs))
     ((and (pair? instr) (eq? (car instr) 'direct-tail-call)) (cadr instr))
     (else #f))))

;; Removes the dead stores from the entry code, then closure creations nothing
;; reads, repeating until nothing changes.
(define (prune-entry entry-instrs reads exported)
  (let loop ((instrs (filter (lambda (instr)
                               (not (and (eq? (car instr) 'set-global!)
                                         (not (hash-table-exists? reads (cadr instr)))
                                         (not (memq (cadr instr) exported)))))
                             entry-instrs)))
    (let ((used (make-hash-table)))
      (for-each (lambda (instr)
                  (for-each (lambda (v) (hash-table-set! used v #t))
                            (instr-uses instr)))
                instrs)
      (let ((kept (filter (lambda (instr)
                            (let ((rhs (rhs-of instr)))
                              (not (and (pair? rhs)
                                        (memq (car rhs) '(make-closure make-variadic-closure))
                                        (not (hash-table-exists? used (cadr instr)))))))
                          instrs)))
        (if (= (length kept) (length instrs)) kept (loop kept))))))

;; Removes assignments of side-effect-free values that nothing reads (such as
;; the loads of a closure that inlining made redundant), until none are left.
(define (drop-dead-loads instrs)
  (let ((used (make-hash-table)))
    (for-each (lambda (instr)
                (for-each (lambda (v) (hash-table-set! used v #t))
                          (instr-uses instr)))
              instrs)
    (let ((kept (filter
                 (lambda (instr)
                   (let ((rhs (rhs-of instr)))
                     (not (and rhs
                               (not (hash-table-exists? used (cadr instr)))
                               (or (symbol? rhs)
                                   (literal-expr? rhs)
                                   (and (pair? rhs)
                                        (memq (car rhs) '(global closure-env-ref))))))))
                 instrs)))
      (if (= (length kept) (length instrs)) kept (drop-dead-loads kept)))))

(define (prune-dead-procedures raw-entry raw-procedures exported-labels)
  (let* ((entry-instrs (drop-dead-loads raw-entry))
         (procedures (map (lambda (p)
                            (make-procedure (procedure-name p) (procedure-params p)
                                            (drop-dead-loads (procedure-instructions p))))
                          raw-procedures))
         (reads (global-reads (cons entry-instrs (map procedure-instructions procedures))))
         (entry (prune-entry entry-instrs reads exported-labels))
         (table (make-hash-table))
         (live (make-hash-table)))
    (for-each (lambda (p) (hash-table-set! table (procedure-name p) p)) procedures)
    (let visit-all ((instrs entry))
      (for-each
       (lambda (instr)
         (let ((name (referenced-procedure instr)))
           (when (and name (hash-table-exists? table name)
                      (not (hash-table-exists? live name)))
             (hash-table-set! live name #t)
             (visit-all (procedure-instructions (hash-table-ref table name))))))
       instrs))
    (values entry
            (filter (lambda (p) (hash-table-exists? live (procedure-name p)))
                    procedures))))

))
