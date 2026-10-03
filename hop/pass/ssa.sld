(define-library (hop pass ssa)
  ;;; Pass 5.4: SSA construction, verification, and SSA destruction over the
  ;;; CFGs (hop pass cfg) builds, before any CFG optimization runs.
  ;;;
  ;;; A procedure in SSA form is a vector of <ssa-block>s. Each block has
  ;;; phi nodes, ordinary TAC instructions (without the leading (label ...)),
  ;;; and explicit successor/predecessor index lists. A phi's args vector is
  ;;; aligned with its block's preds list. Block order is the original layout
  ;;; order, because a block with no terminator falls through to its (only)
  ;;; successor, which must be the next block.
  ;;;
  ;;; Naming: every definition of a variable x gets a fresh name x~1, x~2, ...
  ;;; except that a procedure parameter keeps its own name as its entry
  ;;; definition, so the procedure's parameter list is unchanged.
  ;;;
  ;;; Construction is semi-pruned SSA over Cooper-Harvey-Kennedy dominators,
  ;;; which are valid for irreducible control flow (letrec clusters produce
  ;;; multi-entry loops). Unreachable blocks are dropped. If the entry block
  ;;; is a loop header, an empty synthetic entry block is put in front of it
  ;;; so parameters are defined on the way in rather than on every iteration.
  (export cfg->ssa
          ssa->cfg
          verify-ssa
          check-ssa
          ssa-round-trip-cfg
          sequentialize-copies
          set-ssa-block-instrs!
          ssa-proc?
          ssa-proc-params
          ssa-proc-blocks
          ssa-block-label
          ssa-block-phis
          ssa-block-instrs
          ssa-block-succs
          ssa-block-preds
          phi-dst
          phi-args
          display-ssa)
  (import (scheme base)
          (scheme cxr)
          (scheme write)
          (srfi 69)
          (hop utils)
          (hop pass cfg))
  (begin

(define-record-type <phi>
  (make-phi dst var args)
  phi?
  (dst phi-dst set-phi-dst!)
  (var phi-var)
  (args phi-args))

(define-record-type <ssa-block>
  (make-ssa-block label phis instrs succs preds)
  ssa-block?
  (label ssa-block-label)
  (phis ssa-block-phis set-ssa-block-phis!)
  (instrs ssa-block-instrs set-ssa-block-instrs!)
  (succs ssa-block-succs set-ssa-block-succs!)
  (preds ssa-block-preds set-ssa-block-preds!))

(define-record-type <ssa-proc>
  (make-ssa-proc params blocks)
  ssa-proc?
  (params ssa-proc-params)
  (blocks ssa-proc-blocks))

;;; --- small helpers -----------------------------------------------------------

(define (index-of x lst)
  (let loop ((rest lst) (i 0))
    (cond ((null? rest) #f)
          ((eqv? (car rest) x) i)
          (else (loop (cdr rest) (+ i 1))))))

(define (find-first pred lst)
  (let loop ((rest lst))
    (cond ((null? rest) #f)
          ((pred (car rest)) (car rest))
          (else (loop (cdr rest))))))

(define (remove-first x lst)
  (let loop ((rest lst) (acc '()))
    (cond ((null? rest) (reverse acc))
          ((eq? (car rest) x) (append (reverse acc) (cdr rest)))
          (else (loop (cdr rest) (cons (car rest) acc))))))

(define (last-of lst)
  (if (null? (cdr lst)) (car lst) (last-of (cdr lst))))

(define (all-but-last lst)
  (if (null? (cdr lst)) '() (cons (car lst) (all-but-last (cdr lst)))))

(define (symbol-append . parts)
  (string->symbol
   (apply string-append
          (map (lambda (p) (if (symbol? p) (symbol->string p) p)) parts))))

;;; --- TAC instruction operand access --------------------------------------------
;;;
;;; Which positions of each instruction form hold variable references (as
;;; opposed to labels, procedure names, arities, and literals) is spelled out
;;; here once, for both use collection and use renaming.

(define terminator-heads
  '(if goto return tail-call direct-tail-call tail-apply-call tail-callcc-call))

(define (terminator? instr)
  (and (pair? instr) (memq (car instr) terminator-heads) #t))

(define (map-operands f operands)
  (map (lambda (x) (if (symbol? x) (f x) x)) operands))

(define (map-rhs-uses f rhs)
  (cond
   ((symbol? rhs) (f rhs))
   ((not (pair? rhs)) rhs)
   (else
    (case (car rhs)
      ((quote global) rhs)
      ((primop) `(primop ,(cadr rhs) ,@(map-operands f (cddr rhs))))
      ((cons box unbox car cdr pair? null? closure-call apply-call callcc-call)
       `(,(car rhs) ,@(map-operands f (cdr rhs))))
      ((closure-env-ref)
       `(closure-env-ref ,@(map-operands f (list (cadr rhs))) ,@(cddr rhs)))
      ((make-closure make-variadic-closure)
       `(,(car rhs) ,(cadr rhs) ,(caddr rhs) ,@(map-operands f (cdddr rhs))))
      ((direct-call)
       `(direct-call ,(cadr rhs) ,@(map-operands f (cddr rhs))))
      (else (error "SSA: unknown assignment rhs" rhs))))))

(define (map-instr-uses f instr)
  (case (car instr)
    ((assign) `(assign ,(cadr instr) ,(map-rhs-uses f (caddr instr))))
    ((if) `(if ,@(map-operands f (list (cadr instr))) ,(caddr instr) ,(cadddr instr)))
    ((goto label) instr)
    ((return set-box! tail-call tail-apply-call tail-callcc-call)
     `(,(car instr) ,@(map-operands f (cdr instr))))
    ((direct-tail-call)
     `(direct-tail-call ,(cadr instr) ,@(map-operands f (cddr instr))))
    ((set-global!)
     `(set-global! ,(cadr instr) ,@(map-operands f (cddr instr))))
    (else (error "SSA: unknown TAC instruction" instr))))

(define (instr-uses instr)
  (let ((uses '()))
    (map-instr-uses (lambda (v) (set! uses (cons v uses)) v) instr)
    (reverse uses)))

(define (instr-def instr)
  (and (eq? (car instr) 'assign) (cadr instr)))

;;; --- CFG -> working blocks -----------------------------------------------------

(define (strip-label instrs)
  (if (and (pair? instrs) (pair? (car instrs)) (eq? (car (car instrs)) 'label))
      (cdr instrs)
      instrs))

;; Returns a vector of <ssa-block> with empty phis, reachable blocks only,
;; plus a synthetic entry in front when block 0 is a loop target.
(define (build-ssa-blocks cfg)
  (let* ((n (length cfg))
         (cfg-vec (list->vector cfg))
         (reachable (make-vector n #f)))
    (let visit ((i 0))
      (unless (vector-ref reachable i)
        (vector-set! reachable i #t)
        (for-each visit (basic-block-successors (vector-ref cfg-vec i)))))
    (let* ((new-index (make-vector n #f))
           (kept (let loop ((i 0) (count 0) (acc '()))
                   (cond ((= i n) (reverse acc))
                         ((vector-ref reachable i)
                          (vector-set! new-index i count)
                          (loop (+ i 1) (+ count 1) (cons i acc)))
                         (else (loop (+ i 1) count acc)))))
           (raw (map (lambda (i)
                       (let ((block (vector-ref cfg-vec i)))
                         (list (basic-block-label block)
                               (strip-label (basic-block-instructions block))
                               (map (lambda (s) (vector-ref new-index s))
                                    (basic-block-successors block)))))
                     kept))
           (loops-to-entry?
            (let loop ((rest raw))
              (and (pair? rest)
                   (or (memv 0 (caddr (car rest))) (loop (cdr rest))))))
           (shifted
            (if loops-to-entry?
                (cons (list #f '() '(1))
                      (map (lambda (b)
                             (list (car b) (cadr b)
                                   (map (lambda (s) (+ s 1)) (caddr b))))
                           raw))
                raw))
           (blocks (list->vector
                    (map (lambda (b) (make-ssa-block (car b) '() (cadr b) (caddr b) '()))
                         shifted))))
      (let ((count (vector-length blocks)))
        (do ((i 0 (+ i 1))) ((= i count))
          (let ((succs (ssa-block-succs (vector-ref blocks i))))
            (let dup ((rest succs))
              (when (pair? rest)
                (when (memv (car rest) (cdr rest))
                  (error "SSA: block has two edges to the same successor" i))
                (dup (cdr rest))))
            (for-each (lambda (s)
                        (let ((target (vector-ref blocks s)))
                          (set-ssa-block-preds! target
                                                (append (ssa-block-preds target) (list i)))))
                      succs))))
      blocks)))

;;; --- dominators (Cooper-Harvey-Kennedy) ------------------------------------------

;; Returns (values idom children dominance-frontier postorder-number), each a
;; vector indexed by block. children and frontier hold lists of block indices.
(define (compute-dominators blocks)
  (let* ((n (vector-length blocks))
         (po (make-vector n #f))
         (visited (make-vector n #f))
         (order '()))
    (let ((counter 0))
      (let visit ((i 0))
        (unless (vector-ref visited i)
          (vector-set! visited i #t)
          (for-each visit (ssa-block-succs (vector-ref blocks i)))
          (vector-set! po i counter)
          (set! counter (+ counter 1))
          (set! order (cons i order)))))
    ;; order is now reverse postorder
    (let ((idom (make-vector n #f)))
      (vector-set! idom 0 0)
      (define (intersect a b)
        (let loop ((a a) (b b))
          (cond ((= a b) a)
                ((< (vector-ref po a) (vector-ref po b)) (loop (vector-ref idom a) b))
                (else (loop a (vector-ref idom b))))))
      (let fixed-point ()
        (let ((changed #f))
          (for-each
           (lambda (b)
             (unless (= b 0)
               (let ((new-idom
                      (let loop ((preds (ssa-block-preds (vector-ref blocks b))) (cur #f))
                        (cond ((null? preds) cur)
                              ((not (vector-ref idom (car preds))) (loop (cdr preds) cur))
                              (else (loop (cdr preds)
                                          (if cur (intersect (car preds) cur) (car preds))))))))
                 (unless (eqv? new-idom (vector-ref idom b))
                   (vector-set! idom b new-idom)
                   (set! changed #t)))))
           order)
          (when changed (fixed-point))))
      (let ((children (make-vector n '()))
            (frontier (make-vector n '())))
        (for-each (lambda (b)
                    (unless (= b 0)
                      (vector-set! children (vector-ref idom b)
                                   (cons b (vector-ref children (vector-ref idom b))))))
                  (reverse order))
        (do ((b 0 (+ b 1))) ((= b n))
          (let ((preds (ssa-block-preds (vector-ref blocks b))))
            (when (and (vector-ref visited b) (pair? preds) (pair? (cdr preds)))
              (for-each
               (lambda (p)
                 (when (vector-ref visited p)
                   (let loop ((runner p))
                     (unless (= runner (vector-ref idom b))
                       (unless (memv b (vector-ref frontier runner))
                         (vector-set! frontier runner (cons b (vector-ref frontier runner))))
                       (loop (vector-ref idom runner))))))
               preds))))
        (values idom children frontier po)))))

;;; --- construction ------------------------------------------------------------------

(define (cfg->ssa params cfg)
  (let* ((blocks (build-ssa-blocks cfg))
         (n (vector-length blocks))
         (param-names (params-names params)))
    (let-values (((idom children frontier po) (compute-dominators blocks)))
      ;; --- phi placement (semi-pruned) ---
      (let ((def-blocks (make-hash-table))
            (global-vars (make-hash-table)))
        (define (note-def! var block)
          (let ((existing (hash-table-ref/default def-blocks var '())))
            (unless (memv block existing)
              (hash-table-set! def-blocks var (cons block existing)))))
        (for-each (lambda (p) (note-def! p 0)) param-names)
        (do ((i 0 (+ i 1))) ((= i n))
          (let ((defined '()))
            (for-each
             (lambda (instr)
               (for-each (lambda (v)
                           (unless (memq v defined)
                             (hash-table-set! global-vars v #t)))
                         (instr-uses instr))
               (let ((d (instr-def instr)))
                 (when d
                   (set! defined (cons d defined))
                   (note-def! d i))))
             (ssa-block-instrs (vector-ref blocks i)))))
        (let ((has-phi (make-hash-table)))
          (for-each
           (lambda (var)
             (when (hash-table-ref/default global-vars var #f)
               (let loop ((work (hash-table-ref/default def-blocks var '())))
                 (unless (null? work)
                   (let ((b (car work)) (rest (cdr work)))
                     (let inner ((fs (vector-ref frontier b)) (rest rest))
                       (if (null? fs)
                           (loop rest)
                           (let ((d (car fs)))
                             (if (hash-table-ref/default has-phi (cons d var) #f)
                                 (inner (cdr fs) rest)
                                 (let ((block (vector-ref blocks d)))
                                   (hash-table-set! has-phi (cons d var) #t)
                                   (set-ssa-block-phis!
                                    block
                                    (append (ssa-block-phis block)
                                            (list (make-phi var var
                                                            (make-vector
                                                             (length (ssa-block-preds block))
                                                             #f)))))
                                   (inner (cdr fs)
                                          (if (memv d (hash-table-ref/default def-blocks var '()))
                                              rest
                                              (cons d rest)))))))))))))
           (hash-table-keys def-blocks))))
      ;; --- renaming ---
      (let ((stacks (make-hash-table))
            (counters (make-hash-table)))
        (define (current var)
          (let ((s (hash-table-ref/default stacks var '())))
            (and (pair? s) (car s))))
        (define (fresh-name var)
          (let ((k (+ 1 (hash-table-ref/default counters var 0))))
            (hash-table-set! counters var k)
            (symbol-append var "~" (number->string k))))
        (define (push! var name)
          (hash-table-set! stacks var (cons name (hash-table-ref/default stacks var '()))))
        (define (pop! var)
          (hash-table-set! stacks var (cdr (hash-table-ref/default stacks var '()))))
        (define (rename-use v) (or (current v) v))
        (for-each (lambda (p) (push! p p)) param-names)
        (let visit ((b 0))
          (let* ((block (vector-ref blocks b))
                 (pushed '()))
            (for-each (lambda (phi)
                        (let ((name (fresh-name (phi-var phi))))
                          (set-phi-dst! phi name)
                          (push! (phi-var phi) name)
                          (set! pushed (cons (phi-var phi) pushed))))
                      (ssa-block-phis block))
            (set-ssa-block-instrs!
             block
             (map (lambda (instr)
                    (let ((renamed (map-instr-uses rename-use instr)))
                      (let ((d (instr-def instr)))
                        (if d
                            (let ((name (fresh-name d)))
                              (push! d name)
                              (set! pushed (cons d pushed))
                              `(assign ,name ,(caddr renamed)))
                            renamed))))
                  (ssa-block-instrs block)))
            (for-each
             (lambda (s)
               (let* ((target (vector-ref blocks s))
                      (j (index-of b (ssa-block-preds target))))
                 (for-each (lambda (phi)
                             (vector-set! (phi-args phi) j
                                          (or (current (phi-var phi)) 0)))
                           (ssa-block-phis target))))
             (ssa-block-succs block))
            (for-each visit (reverse (vector-ref children b)))
            (for-each pop! pushed))))
      (make-ssa-proc params blocks))))

;;; --- verification ------------------------------------------------------------------

;; Returns a list of error strings; empty means the procedure is valid SSA.
(define (verify-ssa ssa)
  (let* ((blocks (ssa-proc-blocks ssa))
         (n (vector-length blocks))
         (errors '())
         (def-site (make-hash-table)))
    (define (err! . parts)
      (set! errors (cons (apply string-append
                                (map (lambda (p)
                                       (cond ((string? p) p)
                                             ((symbol? p) (symbol->string p))
                                             ((number? p) (number->string p))
                                             (else "?")))
                                     parts))
                         errors)))
    (define (block-name b)
      (or (ssa-block-label (vector-ref blocks b)) (string-append "#" (number->string b))))
    (define (def! name block index)
      (if (hash-table-ref/default def-site name #f)
          (err! "multiple definitions of " name)
          (hash-table-set! def-site name (cons block index))))
    ;; edges
    (do ((b 0 (+ b 1))) ((= b n))
      (let ((block (vector-ref blocks b)))
        (for-each
         (lambda (s)
           (if (or (< s 0) (>= s n))
               (err! "block " (block-name b) " has out-of-range successor")
               (unless (memv b (ssa-block-preds (vector-ref blocks s)))
                 (err! "edge " (block-name b) " -> " (block-name s) " missing from preds"))))
         (ssa-block-succs block))
        (for-each
         (lambda (p)
           (unless (and (>= p 0) (< p n) (memv b (ssa-block-succs (vector-ref blocks p))))
             (err! "pred edge into " (block-name b) " missing from succs")))
         (ssa-block-preds block))
        (for-each
         (lambda (phi)
           (unless (= (vector-length (phi-args phi)) (length (ssa-block-preds block)))
             (err! "phi " (phi-dst phi) " arity differs from pred count")))
         (ssa-block-phis block))))
    ;; definitions
    (for-each (lambda (p) (def! p 0 -1)) (params-names (ssa-proc-params ssa)))
    (do ((b 0 (+ b 1))) ((= b n))
      (let ((block (vector-ref blocks b)))
        (for-each (lambda (phi) (def! (phi-dst phi) b -1)) (ssa-block-phis block))
        (let loop ((instrs (ssa-block-instrs block)) (i 0))
          (unless (null? instrs)
            (let ((d (instr-def (car instrs))))
              (when d (def! d b i)))
            (loop (cdr instrs) (+ i 1))))))
    ;; dominance of definitions over uses
    (let-values (((idom children frontier po) (compute-dominators blocks)))
      (define (dominates? a b)
        (let loop ((b b))
          (cond ((= a b) #t)
                ((= b 0) #f)
                (else (loop (vector-ref idom b))))))
      (define (check-use! name use-block use-index)
        (let ((site (hash-table-ref/default def-site name #f)))
          (cond
           ((not site) (err! "use of undefined name " name " in " (block-name use-block)))
           ((= (car site) use-block)
            (unless (< (cdr site) use-index)
              (err! "use of " name " before its definition in " (block-name use-block))))
           ((not (dominates? (car site) use-block))
            (err! "definition of " name " does not dominate its use in "
                  (block-name use-block))))))
      (do ((b 0 (+ b 1))) ((= b n))
        (let ((block (vector-ref blocks b)))
          (for-each
           (lambda (phi)
             (let ((preds (ssa-block-preds block)))
               (let loop ((j 0) (ps preds))
                 (unless (or (null? ps) (>= j (vector-length (phi-args phi))))
                   (let ((arg (vector-ref (phi-args phi) j)))
                     (when (symbol? arg)
                       ;; a phi argument is used at the end of its predecessor
                       (check-use! arg (car ps) 1000000000)))
                   (loop (+ j 1) (cdr ps))))))
           (ssa-block-phis block))
          (let loop ((instrs (ssa-block-instrs block)) (i 0))
            (unless (null? instrs)
              (for-each (lambda (v) (check-use! v b i)) (instr-uses (car instrs)))
              (loop (cdr instrs) (+ i 1)))))))
    (reverse errors)))

(define (check-ssa ssa)
  (let ((errors (verify-ssa ssa)))
    (unless (null? errors)
      (error "Invalid SSA" errors))
    ssa))

;;; --- destruction ---------------------------------------------------------------------

;; copies: list of (dst . src), to be performed as one parallel move.
;; Returns TAC (assign dst src) instructions that give the same result when
;; run in order, using a fresh temp only to break a cycle.
(define (sequentialize-copies copies fresh-temp)
  (let loop ((pending (filter (lambda (c) (not (eq? (car c) (cdr c)))) copies))
             (out '()))
    (if (null? pending)
        (reverse out)
        (let ((ready (find-first
                      (lambda (c)
                        (not (find-first (lambda (other)
                                           (and (not (eq? other c))
                                                (eq? (cdr other) (car c))))
                                         pending)))
                      pending)))
          (if ready
              (loop (remove-first ready pending)
                    (cons `(assign ,(car ready) ,(cdr ready)) out))
              (let* ((victim (car (car pending)))
                     (tmp (fresh-temp)))
                (loop (map (lambda (c)
                             (if (eq? (cdr c) victim) (cons (car c) tmp) c))
                           pending)
                      (cons `(assign ,tmp ,victim) out))))))))

(define (insert-before-terminator instrs new)
  (if (and (pair? instrs) (terminator? (last-of instrs)))
      (append (all-but-last instrs) new (list (last-of instrs)))
      (append instrs new)))

(define (replace-branch-label instr old new)
  ;; (if v then else): rewrites the first edge label equal to old.
  (let ((then-label (caddr instr)) (else-label (cadddr instr)))
    (cond ((eq? then-label old) `(if ,(cadr instr) ,new ,else-label))
          ((eq? else-label old) `(if ,(cadr instr) ,then-label ,new))
          (else (error "SSA: branch does not target the expected label" instr old)))))

(define (ssa->cfg ssa)
  (let* ((blocks (ssa-proc-blocks ssa))
         (n (vector-length blocks))
         (bodies (make-vector n '()))
         (succs (make-vector n '()))
         (extras '())
         (temp-counter 0)
         (edge-counter 0))
    (define (fresh-temp)
      (set! temp-counter (+ temp-counter 1))
      (symbol-append "ssa.tmp." (number->string temp-counter)))
    (do ((i 0 (+ i 1))) ((= i n))
      (vector-set! bodies i (ssa-block-instrs (vector-ref blocks i)))
      (vector-set! succs i (ssa-block-succs (vector-ref blocks i))))
    (do ((b 0 (+ b 1))) ((= b n))
      (let* ((block (vector-ref blocks b))
             (phis (ssa-block-phis block)))
        (unless (null? phis)
          (let loop ((preds (ssa-block-preds block)) (j 0))
            (unless (null? preds)
              (let* ((p (car preds))
                     (copies (map (lambda (phi) (cons (phi-dst phi) (vector-ref (phi-args phi) j)))
                                  phis))
                     (code (sequentialize-copies copies fresh-temp)))
                (cond
                 ((null? code) 'nothing-to-copy)
                 ((null? (cdr (vector-ref succs p)))
                  (vector-set! bodies p (insert-before-terminator (vector-ref bodies p) code)))
                 (else
                  ;; critical edge: route it through a new block holding the copies
                  (set! edge-counter (+ edge-counter 1))
                  (let* ((edge-label (symbol-append "ssa.edge." (number->string edge-counter)))
                         (new-index (+ n (length extras)))
                         (target-label (ssa-block-label block))
                         (pred-body (vector-ref bodies p)))
                    (unless target-label
                      (error "SSA: critical edge into an unlabeled block"))
                    (vector-set! bodies p
                                 (append (all-but-last pred-body)
                                         (list (replace-branch-label (last-of pred-body)
                                                                     target-label edge-label))))
                    (vector-set! succs p
                                 (map (lambda (s) (if (= s b) new-index s)) (vector-ref succs p)))
                    (set! extras
                          (append extras
                                  (list (list edge-label
                                              (append code (list `(goto ,target-label)))
                                              (list b))))))))
                (loop (cdr preds) (+ j 1))))))))
    (append
     (let loop ((i 0) (acc '()))
       (if (= i n)
           (reverse acc)
           (let* ((block (vector-ref blocks i))
                  (label (ssa-block-label block))
                  (out (make-basic-block
                        label
                        (if label
                            (cons `(label ,label) (vector-ref bodies i))
                            (vector-ref bodies i)))))
             (set-basic-block-successors! out (vector-ref succs i))
             (loop (+ i 1) (cons out acc)))))
     (map (lambda (extra)
            (let ((out (make-basic-block (car extra)
                                         (cons `(label ,(car extra)) (cadr extra)))))
              (set-basic-block-successors! out
                                           (caddr extra))
              out))
          extras))))

;; CFG -> SSA -> CFG with no optimization in between. The verifier always runs.
(define (ssa-round-trip-cfg params cfg)
  (ssa->cfg (check-ssa (cfg->ssa params cfg))))

;;; --- debugging display ---------------------------------------------------------------

(define (display-ssa ssa)
  (let* ((blocks (ssa-proc-blocks ssa)) (n (vector-length blocks)))
    (display "SSA procedure") (write (ssa-proc-params ssa)) (newline)
    (do ((i 0 (+ i 1))) ((= i n))
      (let ((block (vector-ref blocks i)))
        (display "block ") (display i) (display " ")
        (display (or (ssa-block-label block) "<entry>"))
        (display "  preds ") (write (ssa-block-preds block))
        (display "  succs ") (write (ssa-block-succs block)) (newline)
        (for-each (lambda (phi)
                    (display "    ") (write (phi-dst phi)) (display " = phi ")
                    (write (vector->list (phi-args phi))) (newline))
                  (ssa-block-phis block))
        (for-each (lambda (instr) (display "    ") (write instr) (newline))
                  (ssa-block-instrs block))))))

)) ; end define-library
