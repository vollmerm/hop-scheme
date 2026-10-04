(define-library (hop pass sccp)
  ;;; Pass 5.5: sparse conditional propagation over SSA (the k=0 baseline)
  ;;;
  ;;; Wegman-Zadeck propagation of a small lattice over the SSA form of one
  ;;; procedure (see (hop pass ssa)):
  ;;;
  ;;;   bot       not computed yet (the block or definition is unreachable)
  ;;;   (const c) the literal c; '() is (const ()), a quoted symbol is a const
  ;;;   pair      known to be a cons cell, contents unknown
  ;;;   unknown   anything
  ;;;
  ;;; Values flow along executable edges only, so a branch on a known value
  ;;; makes the other arm dead and keeps its values out of joins.
  ;;;
  ;;; Before the analysis, pi nodes record what a branch learned: at the head of
  ;;; the then-arm of (if (pair? x) ...) or (if (null? x) ...) a fresh name for
  ;;; x is bound by (pi pair x) or (pi null x), and uses of x dominated by that
  ;;; arm read the fresh name. This only applies to arms with a single
  ;;; predecessor, so the refinement is not lost to a join. Pi nodes become
  ;;; plain copies afterwards.
  ;;;
  ;;; The rewrite replaces constant definitions with literals, makes car/cdr of
  ;;; a known pair unsafe, turns decided branches into jumps, drops dead edges
  ;;; and blocks, and removes definitions nobody reads.
  (export sccp-cfg
          sccp-ssa
          control-cfg
          control-ssa)
  (import (scheme base)
          (scheme cxr)
          (only (srfi 1) append-map filter find last list-index)
          (srfi 69)
          (hop utils)
          (hop pass cfg)
          (hop pass ssa))
  (begin

(define (for-each-index proc vec)
  (do ((i 0 (+ i 1)))
      ((= i (vector-length vec)))
    (proc i (vector-ref vec i))))

(define (symbol-append . parts)
  (string->symbol
   (apply string-append
          (map (lambda (part) (if (symbol? part) (symbol->string part) part))
               parts))))

(define (instr-rhs instr)
  (and (eq? (car instr) 'assign) (caddr instr)))

(define (primop-rhs? rhs)
  (and (pair? rhs) (eq? (car rhs) 'primop)))

;;; --- Pi nodes ---

;; (kind subject) when block b ends in a branch on a pair? or null? test of a
;; variable, where the test is computed in the same block.
(define (branch-test blocks b)
  (let ((instrs (ssa-block-instrs (vector-ref blocks b))))
    (and (pair? instrs)
         (let ((term (last instrs)))
           (and (eq? (car term) 'if)
                (symbol? (cadr term))
                (let ((def (find (lambda (i) (eq? (instr-def i) (cadr term)))
                                 instrs)))
                  (and def
                       (primop-rhs? (caddr def))
                       (memq (cadr (caddr def)) '(pair? null?))
                       (symbol? (caddr (caddr def)))
                       (list (cadr (caddr def)) (caddr (caddr def))))))))))

(define (insert-pis! blocks)
  (let* ((children (dominator-children (immediate-dominators blocks)))
         (counter 0))
    (define (subtree b)
      (cons b (append-map subtree (vector-ref children b))))
    (define (rename-uses! members from to)
      (define (rename v) (if (eq? v from) to v))
      (for-each
       (lambda (m)
         (let ((block (vector-ref blocks m)))
           (set-ssa-block-instrs!
            block
            (map (lambda (instr) (map-instr-uses rename instr))
                 (ssa-block-instrs block)))))
       members)
      (for-each-index
       (lambda (j block)
         (for-each
          (lambda (phi)
            (let ((args (phi-args phi)))
              (for-each-index
               (lambda (slot pred)
                 (when (and (memv pred members) (eq? (vector-ref args slot) from))
                   (vector-set! args slot to)))
               (list->vector (ssa-block-preds block)))))
          (ssa-block-phis block)))
       blocks))
    (for-each-index
     (lambda (b block)
       (let ((test (branch-test blocks b)))
         (when test
           (let* ((then-block (car (ssa-block-succs block)))
                  (target (vector-ref blocks then-block)))
             (when (= (length (ssa-block-preds target)) 1)
               (let* ((kind (car test))
                      (subject (cadr test))
                      (fresh (begin (set! counter (+ counter 1))
                                    (symbol-append subject "%pi"
                                                   (number->string counter)))))
                 (rename-uses! (subtree then-block) subject fresh)
                 (set-ssa-block-instrs!
                  target
                  (cons `(assign ,fresh
                                 (pi ,(if (eq? kind 'pair?) 'pair 'null) ,subject))
                        (ssa-block-instrs target)))))))))
     blocks)))

;;; --- Lattice ---

(define unknown 'unknown)
(define bot 'bot)
(define pair-value 'pair)
(define (const c) (list 'const c))
(define (const? v) (and (pair? v) (eq? (car v) 'const)))
(define (const-value v) (cadr v))
(define nil-value (const '()))
(define (bot? v) (eq? v bot))
(define (nil? v) (and (const? v) (null? (const-value v))))

(define (join a b)
  (cond
   ((bot? a) b)
   ((bot? b) a)
   ((equal? a b) a)
   (else unknown)))

;; The constant for a literal expression, or unknown for other operands.
(define (literal-value expr)
  (if (literal-expr? expr) (const expr) unknown))

(define (truthy? v) (not (and (const? v) (eq? (const-value v) #f))))

(define (bool-value b) (const (if b #t #f)))

(define foldable-arithmetic
  `((+ . ,+) (- . ,-) (* . ,*) (= . ,=) (< . ,<) (> . ,>)))

(define (eval-primop op args)
  (cond
   ((memq #f (map (lambda (a) (not (bot? a))) args)) bot)
   ((and (eq? op 'cons) (= (length args) 2)) pair-value)
   ((and (assq op foldable-arithmetic) (= (length args) 2))
    (if (and (const? (car args)) (const? (cadr args))
             (number? (const-value (car args)))
             (number? (const-value (cadr args))))
        (let ((result ((cdr (assq op foldable-arithmetic))
                       (const-value (car args)) (const-value (cadr args)))))
          (if (boolean? result) (bool-value result) (const result)))
        unknown))
   ((and (eq? op 'eq?) (= (length args) 2))
    (if (and (const? (car args)) (const? (cadr args)))
        (bool-value (equal? (const-value (car args)) (const-value (cadr args))))
        unknown))
   ((and (eq? op 'null?) (= (length args) 1))
    (cond ((nil? (car args)) (bool-value #t))
          ((or (const? (car args)) (eq? (car args) pair-value)) (bool-value #f))
          (else unknown)))
   ((and (eq? op 'pair?) (= (length args) 1))
    (cond ((eq? (car args) pair-value) (bool-value #t))
          ((const? (car args)) (bool-value #f))
          (else unknown)))
   ((and (eq? op 'symbol?) (= (length args) 1))
    (cond ((const? (car args))
           (bool-value (quoted-symbol-expr? (const-value (car args)))))
          ((eq? (car args) pair-value) (bool-value #f))
          (else unknown)))
   (else unknown)))

(define (eval-pi kind v)
  (cond
   ((bot? v) bot)
   ((eq? kind 'pair)
    (if (const? v) bot pair-value))
   (else
    (if (or (const? v) (eq? v pair-value))
        (if (nil? v) v bot)
        nil-value))))

;;; --- Analysis ---

;; Result of the analysis: the value of each name, and which blocks and edges
;; can execute. Edges are keyed by (from . to) block indices.
(define-record-type <analysis>
  (make-analysis values visited edges iterations)
  analysis?
  (values analysis-values)
  (visited analysis-visited)
  (edges analysis-edges)
  (iterations analysis-iterations))

(define (edge-key from to) (cons from to))

(define (analyze ssa)
  (let* ((blocks (ssa-proc-blocks ssa))
         (values (make-hash-table))
         (visited (make-vector (vector-length blocks) #f))
         (edges (make-hash-table))
         (use-sites (make-hash-table))
         (flow-list '())
         (ssa-list '())
         (iterations 0))
    (define (value-of operand)
      (cond
       ((symbol? operand) (hash-table-ref/default values operand bot))
       (else (literal-value operand))))
    (define (update! var new)
      (let* ((old (hash-table-ref/default values var bot))
             (merged (join old new)))
        (unless (equal? old merged)
          (hash-table-set! values var merged)
          (set! ssa-list (append (hash-table-ref/default use-sites var '())
                                 ssa-list)))))
    (define (mark-edge! from to)
      (let ((key (edge-key from to)))
        (unless (hash-table-ref/default edges key #f)
          (hash-table-set! edges key #t)
          (set! flow-list (cons key flow-list)))))
    (define (executable? from to)
      (hash-table-ref/default edges (edge-key from to) #f))
    (define (eval-rhs rhs)
      (cond
       ((symbol? rhs) (value-of rhs))
       ((literal-expr? rhs) (const rhs))
       ((primop-rhs? rhs)
        (eval-primop (cadr rhs) (map value-of (cddr rhs))))
       ((and (pair? rhs) (eq? (car rhs) 'cons))
        (eval-primop 'cons (map value-of (cdr rhs))))
       ((and (pair? rhs) (eq? (car rhs) 'pi))
        (eval-pi (cadr rhs) (value-of (caddr rhs))))
       (else unknown)))
    (define (visit-phi! b phi)
      (let ((preds (ssa-block-preds (vector-ref blocks b)))
            (args (phi-args phi)))
        (update! (phi-dst phi)
                 (let loop ((slot 0) (preds preds) (acc bot))
                   (if (null? preds)
                       acc
                       (loop (+ slot 1) (cdr preds)
                             (if (executable? (car preds) b)
                                 (join acc (value-of (vector-ref args slot)))
                                 acc)))))))
    (define (visit-instr! b instr)
      (set! iterations (+ iterations 1))
      (case (car instr)
        ((assign) (update! (cadr instr) (eval-rhs (caddr instr))))
        ((if)
         (let ((v (value-of (cadr instr)))
               (succs (ssa-block-succs (vector-ref blocks b))))
           (cond
            ((bot? v) #f)
            ((truthy? v) (mark-edge! b (car succs)))
            (else (mark-edge! b (cadr succs))))
           (when (eq? v unknown)
             (for-each (lambda (s) (mark-edge! b s)) succs))))
        (else #f)))
    (define (visit-item! b item)
      (if (phi? item) (visit-phi! b item) (visit-instr! b item)))
    (define (visit-block! b)
      (let* ((block (vector-ref blocks b))
             (instrs (ssa-block-instrs block)))
        (vector-set! visited b #t)
        (for-each (lambda (phi) (visit-phi! b phi)) (ssa-block-phis block))
        (for-each (lambda (instr) (visit-instr! b instr)) instrs)
        (unless (and (pair? instrs) (eq? (car (last instrs)) 'if))
          (for-each (lambda (s) (mark-edge! b s)) (ssa-block-succs block)))))
    (define (note-use! var site)
      (when (symbol? var)
        (hash-table-update!/default use-sites var (lambda (l) (cons site l)) '())))
    (for-each-index
     (lambda (b block)
       (for-each (lambda (phi)
                   (let ((site (cons b phi)))
                     (for-each (lambda (arg) (note-use! arg site))
                               (vector->list (phi-args phi)))))
                 (ssa-block-phis block))
       (for-each (lambda (instr)
                   (let ((site (cons b instr)))
                     (for-each (lambda (var) (note-use! var site))
                               (instr-uses instr))))
                 (ssa-block-instrs block)))
     blocks)
    (for-each (lambda (param) (hash-table-set! values param unknown))
              (ssa-proc-param-names ssa))
    (visit-block! 0)
    (let loop ()
      (cond
       ((pair? flow-list)
        (let* ((edge (car flow-list)) (to (cdr edge)))
          (set! flow-list (cdr flow-list))
          (if (vector-ref visited to)
              (for-each (lambda (phi) (visit-phi! to phi))
                        (ssa-block-phis (vector-ref blocks to)))
              (visit-block! to))
          (loop)))
       ((pair? ssa-list)
        (let ((site (car ssa-list)))
          (set! ssa-list (cdr ssa-list))
          (when (vector-ref visited (car site))
            (visit-item! (car site) (cdr site)))
          (loop)))))
    ;; An executed branch with no live edge (its test never got a value) keeps
    ;; both edges rather than leaving the block without successors.
    (for-each-index
     (lambda (b block)
       (when (and (vector-ref visited b)
                  (pair? (ssa-block-succs block))
                  (not (find (lambda (s) (executable? b s)) (ssa-block-succs block))))
         (for-each (lambda (s) (mark-edge! b s)) (ssa-block-succs block))))
     blocks)
    (make-analysis values visited edges iterations)))

(define (ssa-proc-param-names ssa)
  (params-names (ssa-proc-params ssa)))

;;; --- Rewriting ---

(define (rewrite-instr analysis instr)
  (define (value-of var)
    (hash-table-ref/default (analysis-values analysis) var bot))
  (case (car instr)
    ((assign)
     (let ((dst (cadr instr)) (rhs (caddr instr)))
       (cond
        ((and (pair? rhs) (eq? (car rhs) 'pi))
         `(assign ,dst ,(caddr rhs)))
        ((literal-expr? rhs) instr)
        ((and (const? (value-of dst))
              (or (symbol? rhs)
                  (and (primop-rhs? rhs)
                       (memq (cadr rhs) '(+ - * = < > eq? null? pair? symbol?)))))
         `(assign ,dst ,(const-value (value-of dst))))
        ((and (primop-rhs? rhs)
              (memq (cadr rhs) '(car cdr))
              (symbol? (caddr rhs))
              (eq? (value-of (caddr rhs)) pair-value))
         `(assign ,dst (primop ,(if (eq? (cadr rhs) 'car) 'unsafe-car 'unsafe-cdr)
                               ,(caddr rhs))))
        (else instr))))
    (else instr)))

;; Drops blocks that cannot execute and edges that are never taken, keeping the
;; layout order of the rest, and turns decided branches into jumps.
(define (prune-dead-code! analysis blocks)
  (let* ((count (vector-length blocks))
         (new-index (make-vector count #f))
         (kept '()))
    (define (live-edge? from to)
      (and (vector-ref (analysis-visited analysis) from)
           (hash-table-ref/default (analysis-edges analysis)
                                   (edge-key from to) #f)))
    (for-each-index
     (lambda (b block)
       (when (vector-ref (analysis-visited analysis) b)
         (vector-set! new-index b (length kept))
         (set! kept (cons b kept))))
     blocks)
    (set! kept (reverse kept))
    (for-each
     (lambda (b)
       (let* ((block (vector-ref blocks b))
              (old-succs (ssa-block-succs block))
              (live-succs (filter (lambda (s) (live-edge? b s)) old-succs))
              (instrs (ssa-block-instrs block))
              (last-instr (and (pair? instrs) (last instrs))))
         (when (and last-instr (eq? (car last-instr) 'if)
                    (= (length live-succs) 1))
           (let ((label (if (eqv? (car live-succs) (car old-succs))
                            (caddr last-instr)
                            (cadddr last-instr))))
             (set-ssa-block-instrs!
              block
              (append (reverse (cdr (reverse instrs))) (list `(goto ,label))))))
         (let* ((old-preds (ssa-block-preds block))
                (keep-slot? (map (lambda (p) (and (live-edge? p b) #t)) old-preds)))
           (for-each
            (lambda (phi)
              (let ((args (phi-args phi)))
                (let ((filtered
                       (let loop ((slot 0) (keep keep-slot?) (acc '()))
                         (cond ((null? keep) (reverse acc))
                               ((car keep)
                                (loop (+ slot 1) (cdr keep)
                                      (cons (vector-ref args slot) acc)))
                               (else (loop (+ slot 1) (cdr keep) acc))))))
                  (set-ssa-block-phis!
                   block
                   (map (lambda (p)
                          (if (eq? p phi)
                              (make-phi (phi-dst p) (phi-var p)
                                        (list->vector filtered))
                              p))
                        (ssa-block-phis block))))))
            (ssa-block-phis block))
           (set-ssa-block-preds!
            block
            (map (lambda (p) (vector-ref new-index p))
                 (filter (lambda (p) (live-edge? p b)) old-preds))))
         (set-ssa-block-succs!
          block
          (map (lambda (s) (vector-ref new-index s)) live-succs))))
     kept)
    (list->vector (map (lambda (b) (vector-ref blocks b)) kept))))

;;; --- Dead definitions ---

(define pure-primops
  '(+ - * = < > eq? null? pair? symbol? vector? unsafe-car unsafe-cdr))

(define (removable-rhs? rhs remove-allocation?)
  (cond
   ((symbol? rhs) #t)
   ((literal-expr? rhs) #t)
   ((not (pair? rhs)) #f)
   (else
    (case (car rhs)
      ((pi global closure-env-ref unbox) #t)
      ((primop)
       (or (and (memq (cadr rhs) pure-primops) #t)
           (and remove-allocation? (eq? (cadr rhs) 'cons))))
      ((cons) remove-allocation?)
      (else #f)))))

(define (remove-dead-definitions! blocks remove-allocation?)
  (let ((counts (make-hash-table)))
    (define (bump! var delta)
      (when (symbol? var)
        (hash-table-update!/default counts var (lambda (n) (+ n delta)) 0)))
    (define (uses instr) (instr-uses instr))
    (define (dead? var)
      (= 0 (hash-table-ref/default counts var 0)))
    (for-each-index
     (lambda (b block)
       (for-each (lambda (phi)
                   (for-each (lambda (arg) (bump! arg 1))
                             (vector->list (phi-args phi))))
                 (ssa-block-phis block))
       (for-each (lambda (instr)
                   (for-each (lambda (v) (bump! v 1)) (uses instr)))
                 (ssa-block-instrs block)))
     blocks)
    (let loop ()
      (let ((changed? #f))
        (for-each-index
         (lambda (b block)
           (set-ssa-block-phis!
            block
            (filter (lambda (phi)
                      (if (dead? (phi-dst phi))
                          (begin
                            (for-each (lambda (arg) (bump! arg -1))
                                      (vector->list (phi-args phi)))
                            (set! changed? #t)
                            #f)
                          #t))
                    (ssa-block-phis block)))
           (set-ssa-block-instrs!
            block
            (filter (lambda (instr)
                      (if (and (eq? (car instr) 'assign)
                               (dead? (cadr instr))
                               (removable-rhs? (caddr instr) remove-allocation?))
                          (begin
                            (for-each (lambda (v) (bump! v -1)) (uses instr))
                            (set! changed? #t)
                            #f)
                          #t))
                    (ssa-block-instrs block))))
         blocks)
        (when changed? (loop))))))

;;; --- Copy propagation ---

;; Replaces every read of x in (assign x y) by y. SSA makes this valid
;; everywhere; the copies themselves are left for dead definition removal.
(define (propagate-copies! blocks)
  (let ((source (make-hash-table)))
    (define (resolve var)
      (let ((next (hash-table-ref/default source var #f)))
        (if next (resolve next) var)))
    (for-each-index
     (lambda (b block)
       (for-each (lambda (instr)
                   (when (and (eq? (car instr) 'assign) (symbol? (caddr instr)))
                     (hash-table-set! source (cadr instr) (caddr instr))))
                 (ssa-block-instrs block)))
     blocks)
    (for-each-index
     (lambda (b block)
       (for-each (lambda (phi)
                   (let ((args (phi-args phi)))
                     (for-each-index
                      (lambda (slot arg)
                        (when (symbol? arg) (vector-set! args slot (resolve arg))))
                      args)))
                 (ssa-block-phis block))
       (set-ssa-block-instrs!
        block
        (map (lambda (instr) (map-instr-uses resolve instr))
             (ssa-block-instrs block))))
     blocks)))

;;; --- Entry points ---

;; Phis whose value is a known constant become assignments at the block head.
(define (materialize-constant-phis! analysis blocks)
  (for-each-index
   (lambda (b block)
     (let ((constant-phis
            (filter (lambda (phi)
                      (const? (hash-table-ref/default (analysis-values analysis)
                                                      (phi-dst phi) bot)))
                    (ssa-block-phis block))))
       (unless (null? constant-phis)
         (set-ssa-block-phis!
          block
          (filter (lambda (phi) (not (memq phi constant-phis)))
                  (ssa-block-phis block)))
         (set-ssa-block-instrs!
          block
          (append
           (map (lambda (phi)
                  `(assign ,(phi-dst phi)
                           ,(const-value
                             (hash-table-ref (analysis-values analysis)
                                             (phi-dst phi)))))
                constant-phis)
           (ssa-block-instrs block))))))
   blocks))

;; Optimizes an SSA procedure (with pi nodes inserted and removed inside).
;; remove-allocation? also deletes unread cons cells.
(define (sccp-ssa ssa . options)
  (let ((remove-allocation? (and (pair? options) (car options)))
        (blocks (ssa-proc-blocks ssa)))
    (insert-pis! blocks)
    (let ((analysis (analyze ssa)))
      (for-each-index
       (lambda (b block)
         (set-ssa-block-instrs!
          block
          (map (lambda (instr) (rewrite-instr analysis instr))
               (ssa-block-instrs block))))
       blocks)
      (materialize-constant-phis! analysis blocks)
      (let ((pruned (prune-dead-code! analysis blocks)))
        (propagate-copies! pruned)
        (remove-dead-definitions! pruned remove-allocation?)
        (make-ssa-proc (ssa-proc-params ssa) pruned)))))

(define (sccp-cfg params cfg)
  (ssa->cfg (check-ssa (sccp-ssa (check-ssa (cfg->ssa params cfg))))))

;; The control for measurements: the same SSA round trip and cleanup (pi nodes,
;; copy propagation, dead definition removal) with the analysis switched off,
;; so nothing is learned about values and no branch or block is removed.
(define (control-ssa ssa)
  (let ((blocks (ssa-proc-blocks ssa)))
    (insert-pis! blocks)
    (for-each-index
     (lambda (b block)
       (set-ssa-block-instrs!
        block
        (map (lambda (instr)
               (let ((rhs (instr-rhs instr)))
                 (if (and (pair? rhs) (eq? (car rhs) 'pi))
                     `(assign ,(cadr instr) ,(caddr rhs))
                     instr)))
             (ssa-block-instrs block))))
     blocks)
    (propagate-copies! blocks)
    (remove-dead-definitions! blocks #f)
    ssa))

(define (control-cfg params cfg)
  (ssa->cfg (check-ssa (control-ssa (check-ssa (cfg->ssa params cfg))))))

))
