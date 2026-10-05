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
          set-inline-tiny-size!
          set-inline-reader-size!
          prune-dead-procedures)
  (import (scheme base)
          (scheme cxr)
          (only (srfi 1) filter delete-duplicates any every)
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

;;; --- Deciding whether a call is worth inlining ---

;; Procedures whose only reference anywhere is one direct call.
(define (single-use-procedures entry-instrs procedures)
  (let ((counts (make-hash-table))
        (result (make-hash-table)))
    (define (count! name amount)
      (hash-table-update!/default counts name (lambda (n) (+ n amount)) 0))
    (for-each
     (lambda (instrs)
       (for-each
        (lambda (instr)
          (let ((rhs (rhs-of instr)))
            (cond
             ((direct-callee instr) => (lambda (name) (count! name 1)))
             ((and (pair? rhs) (memq (car rhs) '(make-closure make-variadic-closure)))
              (count! (cadr rhs) 1000)))))
        instrs))
     (cons entry-instrs (map procedure-instructions procedures)))
    (for-each (lambda (name)
                (when (= 1 (hash-table-ref counts name)) (hash-table-set! result name #t)))
              (hash-table-keys counts))
    result))

(define tiny-size 3)
(define (set-inline-tiny-size! n) (set! tiny-size n))
;; Procedures of at most this many instructions that read a parameter as a
;; pair are inlined whatever the argument (0: only when it is visibly a pair).
(define reader-size 0)
(define (set-inline-reader-size! n) (set! reader-size n))

(define reader-primops '(car cdr unsafe-car unsafe-cdr pair? null?))

(define (primop-of rhs)
  (and (pair? rhs) (eq? (car rhs) 'primop) (cadr rhs)))

(define (quote-cell-read? rhs)
  (and (pair? rhs) (eq? (car rhs) 'global)
       (let ((name (symbol->string (cadr rhs))))
         (and (> (string-length name) 6) (string=? (substring name 0 6) "hop_q_")))))

;; Does this right-hand side visibly produce a pair (or the empty list), given
;; the variables already known to hold one?
(define (structured-rhs? rhs structured)
  (cond
   ((symbol? rhs) (hash-table-exists? structured rhs))
   ((null? rhs) #t)
   ((not (pair? rhs)) #f)
   ((eq? (car rhs) 'cons) #t)
   ((eq? (primop-of rhs) 'cons) #t)
   ((quote-cell-read? rhs) #t)
   (else #f)))

(define (note-structured! instr structured)
  (when (and (pair? instr) (eq? (car instr) 'assign)
             (structured-rhs? (caddr instr) structured))
    (hash-table-set! structured (cadr instr) #t)))

(define (inline-known-calls entry-instrs procedures max-size)
  (let* ((table (make-hash-table))
         (recursive #f)
         (expanded (make-hash-table))
         (counter 0))
    (for-each (lambda (p) (hash-table-set! table (procedure-name p) p)) procedures)
    (set! recursive (recursive-procedures table))
    (define single-use (single-use-procedures entry-instrs procedures))
    (define (inlinable? name)
      (and (hash-table-exists? table name)
           (not (hash-table-exists? recursive name))
           (not (params-variadic? (procedure-params (hash-table-ref table name))))
           (or (hash-table-exists? single-use name)
               (<= (instruction-size (expanded-body name)) max-size))))
    (define (expanded-body name)
      (or (hash-table-ref/default expanded name #f)
          (let ((body (expand (procedure-instructions (hash-table-ref table name)))))
            (hash-table-set! expanded name body)
            body)))
    (define (fresh-suffix)
      (set! counter (+ counter 1))
      (string-append "i" (number->string counter)))

    ;; For each parameter of a procedure: does it (or a callee it passes the
    ;; parameter to) read the parameter as a pair?
    (define consumption (make-hash-table))
    (define (consumed-params name)
      (cond
       ((hash-table-ref/default consumption name #f) => (lambda (c) c))
       ((not (hash-table-exists? table name)) '())
       (else
        (let* ((p (hash-table-ref table name))
               (names (params-names (procedure-params p))))
          (hash-table-set! consumption name (map (lambda (n) #f) names))
          (let ((result (map (lambda (n) (reads-as-pair? n (procedure-instructions p)))
                             names)))
            (hash-table-set! consumption name result)
            result)))))
    (define (reads-as-pair? var instrs)
      (any (lambda (instr)
             (let ((rhs (rhs-of instr)))
               (or (and rhs (memq (primop-of rhs) reader-primops)
                        (eq? (caddr rhs) var))
                   (and (direct-callee instr)
                        (let ((args (if (eq? (car instr) 'direct-tail-call)
                                        (cddr instr)
                                        (cddr (caddr instr)))))
                          (any (lambda (arg consumed) (and consumed (eq? arg var)))
                               args (consumed-params (direct-callee instr))))))))
           instrs))
    (define (produces-pair? name)
      (let ((p (hash-table-ref table name))
            (built (make-hash-table)))
        (for-each (lambda (instr) (note-structured! instr built))
                  (procedure-instructions p))
        (any (lambda (instr)
               (and (eq? (car instr) 'return)
                    (symbol? (cadr instr))
                    (hash-table-exists? built (cadr instr))))
             (procedure-instructions p))))

    ;; Variables of a caller's instructions that the caller later reads as pairs.
    (define (demanded-variables instrs)
      (let ((demanded (make-hash-table)))
        (let pass ((n 2))
          (for-each
           (lambda (instr)
             (let ((rhs (rhs-of instr)))
               (cond
                ((and rhs (memq (primop-of rhs) reader-primops) (symbol? (caddr rhs)))
                 (hash-table-set! demanded (caddr rhs) #t))
                ((and rhs (symbol? rhs) (hash-table-exists? demanded (cadr instr)))
                 (hash-table-set! demanded rhs #t))
                ((direct-callee instr)
                 (for-each (lambda (arg consumed)
                             (when (and consumed (symbol? arg))
                               (hash-table-set! demanded arg #t)))
                           (if (eq? (car instr) 'direct-tail-call)
                               (cddr instr)
                               (cddr (caddr instr)))
                           (consumed-params (direct-callee instr)))))))
           instrs)
          (when (> n 1) (pass (- n 1))))
        demanded))

    (define (worth-inlining? callee args result structured demanded)
      (or (hash-table-exists? single-use callee)
          (<= (instruction-size (expanded-body callee)) tiny-size)
          (and (> reader-size 0)
               (<= (instruction-size (expanded-body callee)) reader-size)
               (any (lambda (consumed) consumed) (consumed-params callee)))
          (any (lambda (arg consumed)
                 (and consumed (symbol? arg) (hash-table-exists? structured arg)))
               args (consumed-params callee))
          (and result (hash-table-exists? demanded result) (produces-pair? callee))))

    (define (expand instrs)
      (let ((demanded (demanded-variables instrs))
            (structured (make-hash-table)))
        (apply append
               (map (lambda (instr)
                      (let* ((callee (direct-callee instr))
                             (tail? (eq? (car instr) 'direct-tail-call))
                             (args (and callee (if tail? (cddr instr) (cddr (caddr instr)))))
                             (result (and callee (not tail?) (cadr instr)))
                             (out (if (and callee (inlinable? callee)
                                           (worth-inlining? callee args result
                                                            structured demanded))
                                      (let ((p (hash-table-ref table callee)))
                                        (inline-site (params-names (procedure-params p))
                                                     (expanded-body callee)
                                                     args result (fresh-suffix)))
                                      (list instr))))
                        (for-each (lambda (i) (note-structured! i structured)) out)
                        out))
                    instrs))))
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

;; A box that is only ever written (letrec lowering makes one per recursive
;; binding; once inlining has removed every call through it nothing unboxes it)
;; can go together with its set-box! instructions. Aliases made by copying the
;; box count as the same box.
(define (drop-dead-boxes instrs)
  (let ((defs (make-hash-table))     ; var -> list of right-hand sides
        (candidates (make-hash-table)))
    (for-each (lambda (instr)
                (let ((rhs (rhs-of instr)))
                  (when rhs
                    (hash-table-update!/default defs (cadr instr)
                                                (lambda (l) (cons rhs l)) '()))))
              instrs)
    (for-each (lambda (var)
                (when (every (lambda (rhs) (or (symbol? rhs)
                                               (and (pair? rhs) (eq? (car rhs) 'box))))
                             (hash-table-ref defs var))
                  (when (any (lambda (rhs) (and (pair? rhs) (eq? (car rhs) 'box)))
                             (hash-table-ref defs var))
                    (hash-table-set! candidates var #t))))
              (hash-table-keys defs))
    ;; Copies of candidates are candidates when every definition is a box or a
    ;; copy of a candidate.
    (let grow ()
      (let ((changed? #f))
        (for-each
         (lambda (var)
           (when (and (not (hash-table-exists? candidates var))
                      (every (lambda (rhs)
                               (or (and (symbol? rhs) (hash-table-exists? candidates rhs))
                                   (and (pair? rhs) (eq? (car rhs) 'box))))
                             (hash-table-ref defs var)))
             (hash-table-set! candidates var #t)
             (set! changed? #t)))
         (hash-table-keys defs))
        (when changed? (grow))))
    ;; A candidate escapes when it is used for anything but being written
    ;; through or being copied into another candidate.
    (let shrink ()
      (let ((changed? #f))
        (for-each
         (lambda (instr)
           (define (escape! v)
             (when (and (symbol? v) (hash-table-exists? candidates v))
               (hash-table-delete! candidates v)
               (set! changed? #t)))
           (cond
            ((and (eq? (car instr) 'set-box!))
             (escape! (caddr instr)))
            ((and (eq? (car instr) 'assign) (symbol? (caddr instr)))
             (if (hash-table-exists? candidates (cadr instr))
                 ;; an alias of a box that is still read is not dead either
                 (unless (hash-table-exists? candidates (caddr instr))
                   (escape! (cadr instr)))
                 (escape! (caddr instr))))
            (else
             (let ((uses (instr-uses instr)))
               (for-each escape! uses)))))
         instrs)
        (when changed? (shrink))))
    (if (= 0 (hash-table-size candidates))
        instrs
        (filter (lambda (instr)
                  (not (or (and (eq? (car instr) 'set-box!)
                                (hash-table-exists? candidates (cadr instr)))
                           (and (eq? (car instr) 'assign)
                                (hash-table-exists? candidates (cadr instr))))))
                instrs))))

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
                                        (memq (car rhs) '(global closure-env-ref unbox))))))))
                 instrs)))
      (let ((without-boxes (drop-dead-boxes kept)))
        (if (= (length without-boxes) (length instrs))
            without-boxes
            (drop-dead-loads without-boxes))))))

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
