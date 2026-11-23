(define-library (hop pass sccp)
  ;;; Pass 5.5: the cons analysis, sparse conditional propagation over SSA
  ;;;
  ;;; Wegman-Zadeck propagation over the SSA form of one procedure (see
  ;;; (hop pass ssa)), or over all the procedures of a unit with sccp-program.
  ;;; The lattice (see "Lattice" below) describes constants, proper lists, and
  ;;; pairs whose car and cdr are described in turn, to a depth bound k.
  ;;;
  ;;; Values flow along executable edges only, so a branch on a known value
  ;;; makes the other arm dead and keeps its values out of joins.
  ;;;
  ;;; Before the analysis, refinement nodes record what is known about a
  ;;; variable x at a point in the program:
  ;;;
  ;;;   (pi kind x)           at the head of an arm of (if (pair? x) ...) or
  ;;;                         (if (null? x) ...); kind is pair or non-pair,
  ;;;                         null or non-null. On a list, non-pair gives '()
  ;;;                         and non-null gives a list pair. Only arms with a
  ;;;                         single predecessor get one, so the refinement is
  ;;;                         not lost to a join.
  ;;;   (pi-field which x a)  after (assign a (primop car x)) succeeds (or the
  ;;;                         cdr equivalent, with which = cdr): x is a pair
  ;;;                         whose car is a. A repeated accessor of x becomes
  ;;;                         a copy of a.
  ;;;
  ;;; Each one binds a fresh name for x, and the uses of x it dominates read
  ;;; that name. After the analysis they become plain copies of x.
  ;;;
  ;;; The rewrite replaces constant definitions with literals, makes car/cdr of
  ;;; a known pair unsafe or a copy of a known component, turns decided
  ;;; branches into jumps, drops dead edges and blocks, and removes definitions
  ;;; nobody reads. Scalar replacement can then split a loop-carried pair into
  ;;; its fields.
  (export sccp-cfg
          sccp-ssa
          sccp-program
          set-shape-depth!
          set-remove-dead-allocation!
          set-scalar-replacement!
          set-sccp-stats!
          analyze            ; exported for the unit tests
          scalar-replace!    ; exported for the unit tests
          value-table-size
          control-cfg
          control-ssa)
  (import (scheme base)
          (hop compat)
          (only (srfi 1) any drop-right filter filter-map find fold fold-right iota last
                list-index map-in-order)
          (scheme time)
          (scheme write)
          (srfi 69)
          (hop match)
          (hop utils)
          (hop pass cfg)
          (hop ir)
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
  (match instr
    (('assign _ rhs) rhs)
    (_ #f)))

;; 'car or 'cdr when op is a safe or unsafe accessor, else #f.
(define (accessor-kind op)
  (case op
    ((car unsafe-car) 'car)
    ((cdr unsafe-cdr) 'cdr)
    (else #f)))

(define (unsafe-accessor kind)
  (if (eq? kind 'car) 'unsafe-car 'unsafe-cdr))

;; (which . x) when rhs is a car or cdr, safe or not, of the variable x;
;; which is car or cdr.
(define (accessor-read rhs)
  (match rhs
    (('primop (= accessor-kind (? symbol? which)) (? symbol? x)) (cons which x))
    (_ #f)))

;; Calls (proc slot arg pred) for each argument of phi, where pred is the
;; index of the predecessor block that argument flows in from.
(define (for-each-phi-arg proc block phi)
  (let ((args (phi-args phi))
        (preds (ssa-block-preds block)))
    (for-each (lambda (slot pred) (proc slot (vector-ref args slot) pred))
              (iota (length preds))
              preds)))

;; The value of an operand: a name's analysis value (bot when never computed),
;; or the constant of a literal.
(define (analysis-value analysis operand)
  (if (symbol? operand)
      (hash-table-ref/default (analysis-values analysis) operand bot)
      (literal-value operand)))

;;; --- Threading branches on constant phis ---
;;;
;;; (not e), (and a b) and (or a b) become a join block whose phi t collects
;;; constants and test results, followed by (if t ...). A predecessor that
;;; passes a constant into t already decides the branch, so its edge is moved
;;; to the arm the constant selects. Then the then-arm of a pair? or null?
;;; test reaches the code it guards without a join, and gets its pi node.
;;;
;;; Only a join block that holds nothing but the branch and the phi t, with t
;;; read by nothing else, is threaded: it defines no value any moved edge
;;; could miss. A join left with no predecessors is removed.

(define (remove-slot vec slot)
  (let loop ((i (- (vector-length vec) 1)) (acc '()))
    (cond ((< i 0) (list->vector acc))
          ((= i slot) (loop (- i 1) acc))
          (else (loop (- i 1) (cons (vector-ref vec i) acc))))))

(define (remove-index lst index)
  (let loop ((lst lst) (i 0))
    (match lst
      (() '())
      ((x . rest) (if (= i index) rest (cons x (loop rest (+ i 1))))))))

(define (replace-phi-args! block phi args)
  (set-ssa-block-phis!
   block
   (map (lambda (p) (if (eq? p phi) (make-phi (phi-dst p) (phi-var p) args) p))
        (ssa-block-phis block))))

;; Removes the edge from block p (at slot of b's predecessors) into block b.
(define (drop-pred-slot! block slot)
  (for-each (lambda (phi) (replace-phi-args! block phi (remove-slot (phi-args phi) slot)))
            (ssa-block-phis block))
  (set-ssa-block-preds! block (remove-index (ssa-block-preds block) slot)))

;; Returns the blocks, possibly a new vector.
(define (thread-constant-branches blocks)
  (let ((defs (make-hash-table))
        (uses (make-hash-table))
        (dead (make-slots (vector-length blocks) #f)))
    (define (note-use! v)
      (when (symbol? v)
        (hash-table-update!/default uses v (lambda (n) (+ n 1)) 0)))
    (for-each-index
     (lambda (b block)
       (for-each (lambda (phi) (for-each note-use! (vector->list (phi-args phi))))
                 (ssa-block-phis block))
       (for-each (lambda (instr)
                   (for-each note-use! (instr-uses instr))
                   (match instr
                     (('assign dst rhs) (hash-table-set! defs dst rhs))
                     (_ #f)))
                 (ssa-block-instrs block)))
     blocks)
    ;; (literal) when operand is a literal or a name defined as one, else #f
    (define (constant-of operand)
      (cond ((literal-expr? operand) (list operand))
            ((and (symbol? operand)
                  (literal-expr? (hash-table-ref/default defs operand '(none))))
             (list (hash-table-ref defs operand)))
            (else #f)))
    ;; (then else) block indices when block j is a join to thread
    (define (join-branch j)
      (let ((block (vector-ref blocks j)))
        (and (> j 0)
             (not (vector-ref dead j))
             (match (list (ssa-block-phis block)
                          (ssa-block-instrs block)
                          (ssa-block-succs block))
               (((phi) (('if test _ _)) (and succs (then-block else-block)))
                (and (eq? test (phi-dst phi))
                     (= 1 (hash-table-ref/default uses test 0))
                     (not (= then-block else-block))
                     (not (memv j succs))
                     succs))
               (_ #f)))))
    ;; Points the end of block p, which goes to block from, at block to.
    (define (retarget! p from to)
      (let* ((block (vector-ref blocks p))
             (instrs (ssa-block-instrs block))
             (from-label (ssa-block-label (vector-ref blocks from)))
             (to-label (ssa-block-label (vector-ref blocks to))))
        (define (relabel l) (if (eq? l from-label) to-label l))
        (define (replace-terminator term)
          (append (drop-right instrs 1) (list term)))
        (set-ssa-block-instrs!
         block
         (match (and (pair? instrs) (last instrs))
           (('goto _) (replace-terminator `(goto ,to-label)))
           (('if test then-label else-label)
            (replace-terminator `(if ,test ,(relabel then-label) ,(relabel else-label))))
           ;; falls through into from
           (_ (append instrs (list `(goto ,to-label))))))
        (set-ssa-block-succs! block (map (lambda (s) (if (= s from) to s))
                                         (ssa-block-succs block)))))
    ;; The arm of targets, a (then else) pair of block indices, that the
    ;; phi argument arg selects; #f when arg is not a constant.
    (define (selected-arm arg targets)
      (match (list (constant-of arg) targets)
        (((value) (then-block else-block)) (if value then-block else-block))
        (_ #f)))
    ;; Gives block p an edge to block to that carries what its edge into join
    ;; j carried into to's phis.
    (define (add-edge-from-join! p j to)
      (let* ((target (vector-ref blocks to))
             (j-slot (list-index (lambda (q) (= q j)) (ssa-block-preds target))))
        (for-each
         (lambda (tphi)
           (replace-phi-args!
            target tphi
            (vector-append (phi-args tphi)
                           (vector (vector-ref (phi-args tphi) j-slot)))))
         (ssa-block-phis target))
        (set-ssa-block-preds! target (append (ssa-block-preds target) (list p)))))
    ;; Moves one constant-passing edge into join j; #f when there is none.
    (define (thread-one! j targets)
      (match-let* ((block (vector-ref blocks j))
                   ((phi) (ssa-block-phis block)))
        (let loop ((slot 0) (preds (ssa-block-preds block)))
          (match preds
            (() #f)
            ((p . rest)
             (let* ((to (selected-arm (vector-ref (phi-args phi) slot) targets))
                    (p-succs (ssa-block-succs (vector-ref blocks p))))
               (if (and to
                        (not (= p j))
                        (not (memv to p-succs))
                        (= 1 (length (filter (lambda (s) (= s j)) p-succs))))
                   (begin
                     (add-edge-from-join! p j to)
                     (retarget! p j to)
                     (drop-pred-slot! block slot)
                     #t)
                   (loop (+ slot 1) rest))))))))
    (define (kill-if-unreached! j)
      (when (null? (ssa-block-preds (vector-ref blocks j)))
        (vector-set! dead j #t)
        (for-each
         (lambda (s)
           (let ((succ (vector-ref blocks s)))
             (drop-pred-slot! succ (list-index (lambda (q) (= q j)) (ssa-block-preds succ)))))
         (ssa-block-succs (vector-ref blocks j)))
        (set-ssa-block-succs! (vector-ref blocks j) '())))
    (let loop ()
      (let ((changed #f))
        (for-each-index
         (lambda (j block)
           (let ((targets (join-branch j)))
             (when targets
               (let thread ()
                 (when (and (join-branch j) (thread-one! j targets))
                   (set! changed #t)
                   (thread)))
               (kill-if-unreached! j))))
         blocks)
        (when changed (loop))))
    (if (not (any (lambda (x) x) (vector->list dead)))
        blocks
        (let ((new-index (make-slots (vector-length blocks) #f))
              (kept '()))
          (for-each-index
           (lambda (b block)
             (unless (vector-ref dead b)
               (vector-set! new-index b (length kept))
               (set! kept (cons block kept))))
           blocks)
          (for-each
           (lambda (block)
             (set-ssa-block-preds! block (map (lambda (p) (vector-ref new-index p))
                                              (ssa-block-preds block)))
             (set-ssa-block-succs! block (map (lambda (s) (vector-ref new-index s))
                                              (ssa-block-succs block))))
           kept)
          (list->vector (reverse kept))))))

(define (thread-constant-branches-ssa ssa)
  (make-ssa-proc (ssa-proc-params ssa) (thread-constant-branches (ssa-proc-blocks ssa))))

;;; --- Pi nodes ---

;; (kind subject) when block b ends in a branch on a pair? or null? test of a
;; variable. The test may be computed in any block and reach the branch
;; through copies and one-argument phis (what threading leaves of a join).
;; defs maps each name to the block defining it, or a one-argument phi to the
;; phi; the right-hand side is read as it is now, after earlier renaming.
(define (branch-test blocks b defs)
  ;; The right-hand side that defines v, or #f when there is none to follow.
  (define (defining-rhs v)
    (match (hash-table-ref/default defs v #f)
      (#f #f)
      ((? phi? phi) (vector-ref (phi-args phi) 0))
      (site (let ((def (find (lambda (i) (eq? (instr-def i) v))
                             (ssa-block-instrs (vector-ref blocks site)))))
              (and def (instr-rhs def))))))
  (match (ssa-block-instrs (vector-ref blocks b))
    (() #f)
    (instrs
     (match (last instrs)
       (('if test _ _)
        (let follow ((v test) (steps 0))
          (match (and (symbol? v) (< steps 64) (defining-rhs v))
            ((? symbol? source) (follow source (+ steps 1)))
            (('primop (and op (or 'pair? 'null?)) (? symbol? subject))
             (list op subject))
            (_ #f))))
       (_ #f)))))

(define (branch-test-defs blocks)
  (let ((defs (make-hash-table)))
    (for-each-index
     (lambda (b block)
       (for-each (lambda (phi)
                   (when (= (vector-length (phi-args phi)) 1)
                     (hash-table-set! defs (phi-dst phi) phi)))
                 (ssa-block-phis block))
       (for-each (lambda (instr)
                   (let ((dst (instr-def instr)))
                     (when dst (hash-table-set! defs dst b))))
                 (ssa-block-instrs block)))
     blocks)
    defs))

;; accessors? also adds the pis of car and cdr (see insert-accessor-pis!);
;; the control leaves them out.
(define (insert-pis! blocks accessors?)
  (let* ((children (dominator-children (immediate-dominators blocks)))
         (defs (branch-test-defs blocks))
         (counter 0))
    (define (fresh-name subject)
      (set! counter (+ counter 1))
      (symbol-append subject "%pi" (number->string counter)))
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
            (for-each-phi-arg
             (lambda (slot arg pred)
               (when (and (memv pred members) (eq? arg from))
                 (vector-set! (phi-args phi) slot to)))
             block phi))
          (ssa-block-phis block)))
       blocks))
    (for-each-index
     (lambda (b block)
       (match (list (branch-test blocks b defs) (ssa-block-succs block))
         (((test-op subject) (_ _))
          (for-each
           (lambda (arm kind)
             (let ((target (vector-ref blocks arm)))
               (when (= (length (ssa-block-preds target)) 1)
                 (let ((fresh (fresh-name subject)))
                   (rename-uses! (subtree arm) subject fresh)
                   (set-ssa-block-instrs!
                    target
                    (cons `(assign ,fresh (pi ,kind ,subject))
                          (ssa-block-instrs target)))))))
           (ssa-block-succs block)
           (if (eq? test-op 'pair?) '(pair non-pair) '(null non-null))))
         (_ #f)))
     blocks)
    (when accessors?
      (insert-accessor-pis! blocks children fresh-name))))

;; After (assign a (primop car x)) succeeds, x is a pair whose car is a (a
;; failed accessor does not return). The instruction is followed by
;; (assign x' (pi-field car x a)), and the uses of x it dominates read x': the rest
;; of the block, the blocks it dominates, and phi arguments on edges leaving
;; the block. A later (cdr x') is then unsafe.
;;
;; Pairs are immutable, so a later (car y) of the same value as x, where y is
;; x or a pi or copy of it, becomes a copy of a, and its uses read a's newest
;; name, so they see what has been learned about a since (car x) ran.
;;
;; Walks the dominator tree, so what a block learns is seen only below it.
(define (insert-accessor-pis! blocks children fresh-name)
  (let ((renames (make-hash-table))     ; name -> the name its uses read now
        (roots (make-hash-table))       ; pi or copy -> the name it copies
        (available (make-hash-table equal?)))  ; (car . root) -> its result
    (define (current v)
      (let ((next (hash-table-ref/default renames v #f)))
        (if next (current next) v)))
    (define (root v)
      (let ((next (hash-table-ref/default roots v #f)))
        (if next (root next) v)))
    (define (visit! b)
      (let ((block (vector-ref blocks b))
            (renamed '())
            (made-available '()))
        (define (rename! from to)
          (hash-table-set! renames from to)
          (set! renamed (cons from renamed)))
        ;; in order: each rename applies to the instructions after it
        (set-ssa-block-instrs!
         block
         (let loop ((instrs (ssa-block-instrs block)) (acc '()))
           (match instrs
             (() (reverse acc))
             ((next . rest)
              (let ((instr (map-instr-uses current next)))
                (match instr
                  (('assign dst (= accessor-read (which . subject)))
                   (let* ((key (cons which (root subject)))
                          (earlier (hash-table-ref/default available key #f)))
                     (if earlier
                         (begin
                           (rename! dst earlier)
                           (loop rest (cons `(assign ,dst ,(current earlier)) acc)))
                         (let ((fresh (fresh-name subject)))
                           (hash-table-set! available key dst)
                           (set! made-available (cons key made-available))
                           (hash-table-set! roots fresh subject)
                           (rename! subject fresh)
                           (loop rest
                                 (cons `(assign ,fresh (pi-field ,which ,subject ,dst))
                                       (cons instr acc)))))))
                  (('assign dst (? symbol? source))
                   (hash-table-set! roots dst source)
                   (loop rest (cons instr acc)))
                  (('assign dst ('pi _ (? symbol? subject)))
                   ;; a branch's pi: the uses below already read dst, and so
                   ;; do reused results that are copies of its subject
                   (hash-table-set! roots dst subject)
                   (rename! subject dst)
                   (loop rest (cons instr acc)))
                  (_ (loop rest (cons instr acc)))))))))
        (for-each
         (lambda (s)
           (let ((succ (vector-ref blocks s)))
             (for-each
              (lambda (phi)
                (for-each-phi-arg
                 (lambda (slot arg pred)
                   (when (and (= pred b) (symbol? arg))
                     (vector-set! (phi-args phi) slot (current arg))))
                 succ phi))
              (ssa-block-phis succ))))
         (ssa-block-succs block))
        (for-each visit! (vector-ref children b))
        (for-each (lambda (name) (hash-table-delete! renames name)) renamed)
        (for-each (lambda (key) (hash-table-delete! available key)) made-available)))
    (visit! 0)))

;;; --- Lattice ---
;;;
;;; Values are interned, so equal values are eq?.
;;;
;;;   bot       nothing yet (unreachable)
;;;   unknown   anything
;;;   const     a literal: number, boolean, '(), or (quote sym)
;;;   cons      a pair whose car and cdr are described by values, each with an
;;;             optional SSA name that is known to hold exactly that component
;;;   list      a proper list of unknown elements: '() or list-pair, the cons
;;;             whose car is unknown and whose cdr is list
;;;
;;; A join of '() or list with a cons whose cdrs end in '() or list is list,
;;; so a loop walking down a list keeps knowing it has a list, and the
;;; else-arm of its null? test knows it has a pair.
;;;
;;; The depth bound k limits how much structure a cons keeps: a cons keeps its
;;; children only while the nesting below it is at most k deep, and a cons
;;; beyond that is crushed to list-pair when it is a list, and otherwise to
;;; pair-value (a pair of unknown contents). The
;;; depth counts nesting along any path, through car or cdr alike. k = 0 keeps
;;; only "this is a pair", which is what the old unsafe-car/cdr pass knew.
;;; Component names are dropped at k = 0.
;;;
;;; A component name is only valid where the name is in scope. It is: the name
;;; was an operand of the cons that built the pair, so it dominates the pair,
;;; and joins keep a name only when every incoming pair has it.

(define shape-depth 0)
(define (set-shape-depth! k) (set! shape-depth k))
(define remove-dead-allocation #f)
(define (set-remove-dead-allocation! flag) (set! remove-dead-allocation flag))

(define unknown 'unknown)
(define bot 'bot)
(define (bot? v) (eq? v bot))
(define list-value 'list)

(define node-count 0)
(define (next-id!) (set! node-count (+ node-count 1)) node-count)
(define const-table (make-hash-table))
(define cons-table (make-hash-table))
(define (value-table-size) node-count)

(define-record-type <const-value>
  (make-const-value literal id)
  const?
  (literal const-value)
  (id const-id))

;; A pair whose car and cdr are described by values. car-name and cdr-name are
;; SSA names known to hold the components, or #f. depth is the nesting depth
;; of cons values below and including this one.
(define-record-type <cons-value>
  (make-cons-node car car-name cdr cdr-name depth id)
  cons?
  (car cons-car)
  (car-name cons-car-name)
  (cdr cons-cdr)
  (cdr-name cons-cdr-name)
  (depth cons-depth)
  (id cons-id))

(define (const c)
  (or (hash-table-ref/default const-table c #f)
      (let ((node (make-const-value c (next-id!))))
        (hash-table-set! const-table c node)
        node)))
(define nil-value (const '()))
(define (nil? v) (and (const? v) (null? (const-value v))))

(define (value-depth v) (if (cons? v) (cons-depth v) 0))
(define (value-id v)
  (cond ((eq? v unknown) 0)
        ((eq? v bot) -1)
        ((eq? v list-value) -2)
        ((const? v) (const-id v))
        (else (cons-id v))))

(define (make-cons-value a an d dn)
  (let ((key (list (value-id a) an (value-id d) dn)))
    (or (hash-table-ref/default cons-table key #f)
        (let ((node (make-cons-node a an d dn
                                    (+ 1 (max (value-depth a) (value-depth d)))
                                    (next-id!))))
          (hash-table-set! cons-table key node)
          node))))

(define pair-value (make-cons-value unknown #f unknown #f))
(define list-pair (make-cons-value unknown #f list-value #f))

;; Is v '() or a pair whose cdrs end in '() or list (or nothing yet)?
(define (list-shaped? v)
  (or (bot? v) (nil? v) (eq? v list-value)
      (and (cons? v) (list-shaped? (cons-cdr v)))))

(define (limit v k)
  (cond
   ((not (cons? v)) v)
   ((or (eq? v pair-value) (eq? v list-pair) (<= (cons-depth v) k)) v)
   ((<= k 0) (if (list-shaped? v) list-pair pair-value))
   (else
    (make-cons-value (limit (cons-car v) (- k 1)) (cons-car-name v)
                     (limit (cons-cdr v) (- k 1)) (cons-cdr-name v)))))

(define (join a b)
  (cond
   ((bot? a) b)
   ((bot? b) a)
   ((eq? a b) a)
   ((and (cons? a) (cons? b))
    (make-cons-value (join (cons-car a) (cons-car b))
                     (and (eq? (cons-car-name a) (cons-car-name b)) (cons-car-name a))
                     (join (cons-cdr a) (cons-cdr b))
                     (and (eq? (cons-cdr-name a) (cons-cdr-name b)) (cons-cdr-name a))))
   ((and (or (nil? a) (eq? a list-value) (cons? a))
         (or (nil? b) (eq? b list-value) (cons? b))
         (list-shaped? a) (list-shaped? b))
    list-value)
   (else unknown)))

(define (strip-names v)
  (if (cons? v)
      (make-cons-value (strip-names (cons-car v)) #f (strip-names (cons-cdr v)) #f)
      v))

;; The constant for a literal expression, or unknown for other operands.
(define (literal-value expr)
  (if (literal-expr? expr) (const expr) unknown))

(define (truthy? v) (not (eq? v (const #f))))

(define (bool-value b) (const (if b #t #f)))

;; The host procedure that folds the arithmetic primop op, or #f.
(define (arithmetic-procedure op)
  (match (assq op `((+ . ,+) (- . ,-) (* . ,*) (= . ,=) (< . ,<) (> . ,>)))
    ((_ . proc) proc)
    (#f #f)))

;; The car or cdr (which) of a pair value, as two values: the component's
;; value and the SSA name known to hold it, or #f.
(define (component v which)
  (cond
   ((bot? v) (values bot #f))
   ((cons? v) (if (eq? which 'car)
                  (values (cons-car v) (cons-car-name v))
                  (values (cons-cdr v) (cons-cdr-name v))))
   ;; an accessor on '() fails, so a cdr that returns is the cdr of a list pair
   ((and (eq? v list-value) (eq? which 'cdr)) (values list-value #f))
   (else (values unknown #f))))

(define (number-const? v)
  (and (const? v) (number? (const-value v))))

;; names holds each operand's variable name, or #f for a literal.
(define (eval-primop op args names)
  (if (any bot? args)
      bot
      (match (list op args names)
        (('cons (a d) (a-name d-name))
         (limit (make-cons-value a (and (not (const? a)) a-name)
                                 d (and (not (const? d)) d-name))
                shape-depth))
        (((= accessor-kind (? symbol? which)) (v) _)
         (let-values (((value name) (component v which)))
           value))
        (((= arithmetic-procedure (? procedure? proc)) (a b) _)
         (if (and (number-const? a) (number-const? b))
             (let ((result (proc (const-value a) (const-value b))))
               (if (boolean? result) (bool-value result) (const result)))
             unknown))
        (('eq? (a b) _)
         (if (and (const? a) (const? b))
             (bool-value (equal? (const-value a) (const-value b)))
             unknown))
        (('null? (v) _)
         (cond ((nil? v) (bool-value #t))
               ((or (const? v) (cons? v)) (bool-value #f))
               (else unknown)))
        (('pair? (v) _)
         (cond ((cons? v) (bool-value #t))
               ((const? v) (bool-value #f))
               (else unknown)))
        (('symbol? (v) _)
         (cond ((const? v) (bool-value (quoted-symbol-expr? (const-value v))))
               ((or (cons? v) (eq? v list-value)) (bool-value #f))
               (else unknown)))
        (_ unknown))))

;; (pi-field car x a) or (pi-field cdr x a): x is a pair whose car (or cdr)
;; is a, with value av. A non-pair x would have stopped the accessor, so
;; nothing flows.
(define (eval-accessor-pi which v name av)
  (if (or (bot? v) (bot? av) (const? v))
      bot
      (let-values (((other other-name) (component v (if (eq? which 'car) 'cdr 'car))))
        (limit (if (eq? which 'car)
                   (make-cons-value av name other other-name)
                   (make-cons-value other other-name av name))
               shape-depth))))

(define (eval-pi kind v)
  (cond
   ((bot? v) bot)
   ((eq? kind 'pair)
    (cond ((const? v) bot) ((cons? v) v) ((eq? v list-value) list-pair) (else pair-value)))
   ((eq? kind 'null)
    (cond ((nil? v) v)
          ((or (const? v) (cons? v)) bot)
          (else nil-value)))
   ((eq? kind 'non-pair)
    (cond ((cons? v) bot) ((eq? v list-value) nil-value) (else v)))
   (else
    (cond ((nil? v) bot) ((eq? v list-value) list-pair) (else v)))))

;; Values the pass has learned for hoisted quote cells (hop_q_...), which are
;; written once, by the program's entry code, before any procedure runs. Cleared
;; when a new entry procedure is processed.
(define quote-cell-values (make-hash-table))
(define (reset-quote-cells!) (set! quote-cell-values (make-hash-table)))
(define (quote-cell? label)
  (and (symbol? label)
       (let ((name (symbol->string label)))
         (and (> (string-length name) 6)
              (string=? (substring name 0 6) "hop_q_")))))

;;; --- Analysis ---

;;; --- Scalar replacement of pairs carried by phis ---
;;;
;;; A phi p whose value is a known cons (a loop-carried record) is split into
;;; one phi per field, a tree of phis for nested conses. A field the analysis
;;; knows to be a constant becomes that literal. Each incoming pair
;;; contributes its operands when it is a cons instruction, and otherwise a
;;; pair of loads (unsafe-car/cdr) at the end of the predecessor; pairs are
;;; immutable, so the loads may run early. Reads of p become copies of the
;;; field phis. Uses of p as a whole get one fresh cons chain, built at the
;;; nearest block that dominates all of them, and only when that block is
;;; outside the loops of p's block; otherwise nothing changes. One chain for
;;; all whole uses keeps eq? on them as before. Nothing is done when a
;;; component pair would be used as a whole, or in a procedure with
;;; irreducible loops.

(define scalar-replacement #f)
(define (set-scalar-replacement! flag) (set! scalar-replacement flag))
(define sroa-count 0)
(define (fresh-sroa-name)
  (set! sroa-count (+ sroa-count 1))
  (string->symbol (string-append "sr." (number->string sroa-count) "~1")))

(define (append-before-terminator! block instr)
  (let ((instrs (ssa-block-instrs block)))
    (set-ssa-block-instrs!
     block
     (if (and (pair? instrs) (terminator? (last instrs)))
         (append (drop-right instrs 1) (list instr (last instrs)))
         (append instrs (list instr))))))

(define (dominates? idom a b)
  (let walk ((x b))
    (cond ((not x) #f) ((= x a) #t) ((= x 0) #f) (else (walk (vector-ref idom x))))))

;; Number of natural loops containing each block, or #f when removing the back
;; edges leaves a cycle (an irreducible loop).
(define (loop-depths blocks idom)
  (let* ((n (vector-length blocks))
         (depth (make-slots n 0))
         (headers (make-hash-table))
         (color (make-slots n 0)))
    (define (back-edge? a b) (dominates? idom b a))
    (define (cyclic? x)
      (vector-set! color x 1)
      (let ((found (any (lambda (y)
                          (and (not (back-edge? x y))
                               (or (= (vector-ref color y) 1)
                                   (and (= (vector-ref color y) 0) (cyclic? y)))))
                        (ssa-block-succs (vector-ref blocks x)))))
        (vector-set! color x 2)
        found))
    ;; The blocks of the natural loop with header h, as a table.
    (define (loop-body h)
      (let ((body (make-hash-table)))
        (hash-table-set! body h #t)
        (let walk ((stack (hash-table-ref headers h)))
          (match stack
            (() body)
            ((x . rest)
             (if (hash-table-exists? body x)
                 (walk rest)
                 (begin
                   (hash-table-set! body x #t)
                   (walk (append (ssa-block-preds (vector-ref blocks x)) rest)))))))))
    (for-each-index
     (lambda (a block)
       (for-each (lambda (b)
                   (when (back-edge? a b)
                     (hash-table-update!/default headers b (lambda (l) (cons a l)) '())))
                 (ssa-block-succs block)))
     blocks)
    (and (not (cyclic? 0))
         (begin
           (for-each
            (lambda (h)
              (for-each (lambda (x) (vector-set! depth x (+ 1 (vector-ref depth x))))
                        (hash-table-keys (loop-body h))))
            (hash-table-keys headers))
           depth))))

(define (scalar-replace! analysis blocks)
  (let* ((idom (immediate-dominators blocks))
         (depth (loop-depths blocks idom))
         (dom-depth (make-slots (vector-length blocks) #f))
         (defs (make-hash-table))       ; name -> its right-hand side
         (phi-defs (make-hash-table))   ; name -> (phi . block index)
         (fields (make-hash-table equal?))
         (loads (make-hash-table equal?)))
    (define (value-of name) (analysis-value analysis name))
    (define (dom-depth-of x)
      (or (vector-ref dom-depth x)
          (let ((d (if (= x 0) 0 (+ 1 (dom-depth-of (vector-ref idom x))))))
            (vector-set! dom-depth x d)
            d)))
    (define (common-dominator a b)
      (cond ((= a b) a)
            ((> (dom-depth-of a) (dom-depth-of b)) (common-dominator (vector-ref idom a) b))
            (else (common-dominator a (vector-ref idom b)))))
    (define (refresh-defs!)
      (set! defs (make-hash-table))
      (set! phi-defs (make-hash-table))
      (for-each-index
       (lambda (b block)
         (for-each (lambda (phi) (hash-table-set! phi-defs (phi-dst phi) (cons phi b)))
                   (ssa-block-phis block))
         (for-each (lambda (instr)
                     (match instr
                       (('assign dst rhs) (hash-table-set! defs dst rhs))
                       (_ #f)))
                   (ssa-block-instrs block)))
       blocks))
    ;; (car-operand . cdr-operand) when name is defined by a cons, else #f
    (define (operands-of name)
      (match (and (symbol? name) (hash-table-ref/default defs name #f))
        (('primop 'cons a d) (cons a d))
        (_ #f)))
    ;; Does a cons instruction feed name, possibly through phis?
    (define (web-has-fresh? name)
      (let ((seen (make-hash-table)))
        (let visit ((x name))
          (and (symbol? x)
               (not (hash-table-exists? seen x))
               (begin
                 (hash-table-set! seen x #t)
                 (or (and (operands-of x) #t)
                     (match (hash-table-ref/default phi-defs x #f)
                       ((phi . _) (any visit (vector->list (phi-args phi))))
                       (#f #f))))))))
    ;; car or cdr when instr reads that field of base, else #f
    (define (read-of instr base)
      (match (accessor-read (instr-rhs instr))
        ((which . x) (and (eq? x base) which))
        (#f #f)))
    (define (component-value value which)
      (if (eq? which 'car) (cons-car value) (cons-cdr value)))
    ;; Reads of name as (dst base which), a base before its readers, and the
    ;; blocks of its whole uses; #f when a component pair (a read of a cons
    ;; valued field) is used as a whole.
    (define (classify name value)
      (let ((reads '()) (escapes '()))
        (for-each-index
         (lambda (b block)
           (for-each
            (lambda (phi)
              (for-each-phi-arg
               (lambda (slot arg pred)
                 (when (eq? arg name) (set! escapes (cons pred escapes))))
               block phi))
            (ssa-block-phis block))
           (for-each
            (lambda (instr)
              (when (memq name (instr-uses instr))
                (let ((which (read-of instr name)))
                  (if which
                      (set! reads (cons (list (instr-def instr) name which) reads))
                      (set! escapes (cons b escapes))))))
            (ssa-block-instrs block)))
         blocks)
        (let loop ((rs (reverse reads)) (nested '()))
          (match rs
            (() (cons (append (reverse reads) nested) escapes))
            (((dst _ which) . rest)
             (let ((child (component-value value which)))
               (if (cons? child)
                   (match (classify dst child)
                     ((child-reads) (loop rest (append nested child-reads)))
                     (_ #f))
                   (loop rest nested))))))))
    ;; The name holding the field at path (a list of car/cdr) of the pair name.
    ;; where: block index at whose end loads may be placed.
    (define (field name path where)
      (match path
        (() name)
        ((step . deeper)
         (cond
          ((not (symbol? name)) (raise 'scalar-replacement-abort))
          ((operands-of name)
           => (match-lambda
                ((a . d) (field (if (eq? step 'car) a d) deeper where))))
          ((hash-table-ref/default phi-defs name #f)
           => (match-lambda
                ((phi . block-index) (phi-field name path phi block-index))))
          (else (load-field name path where))))))
    ;; The field at path of the pair phi defines, as a new phi of the fields
    ;; at path of its arguments.
    (define (phi-field name path phi block-index)
      (let ((key (cons name path)))
        (or (hash-table-ref/default fields key #f)
            (let ((dst (fresh-sroa-name)))
              (hash-table-set! fields key dst)
              (let* ((block (vector-ref blocks block-index))
                     ;; in predecessor order, so fresh names do not depend on
                     ;; the order the host's map happens to use
                     (args (map-in-order (lambda (arg pred) (field arg path pred))
                                         (vector->list (phi-args phi))
                                         (ssa-block-preds block))))
                (set-ssa-block-phis!
                 block
                 (append (ssa-block-phis block)
                         (list (make-phi dst dst (list->vector args))))))
              dst))))
    ;; The field at path of the pair name, loaded at the end of block where.
    (define (load-field name path where)
      (let ((key (list name path where)))
        (or (hash-table-ref/default loads key #f)
            (let ((result
                   (let chain ((from name) (steps path))
                     (match steps
                       (() from)
                       ((step . more)
                        (let ((t (fresh-sroa-name)))
                          (append-before-terminator!
                           (vector-ref blocks where)
                           `(assign ,t (primop ,(unsafe-accessor step) ,from)))
                          (chain t more)))))))
              (hash-table-set! loads key result)
              result))))
    ;; The leaf at path: its literal when the analysis knows it, else a field.
    (define (leaf root value path)
      (if (const? value) (const-value value) (field root path #f)))
    ;; (instructions . name) building the pair of value at path from fields
    (define (materialize root value path)
      (if (cons? value)
          (let ((a (materialize root (cons-car value) (append path '(car))))
                (d (materialize root (cons-cdr value) (append path '(cdr))))
                (name (fresh-sroa-name)))
            (match-let (((a-instrs . a-name) a)
                        ((d-instrs . d-name) d))
              (cons (append a-instrs d-instrs
                            (list `(assign ,name (primop cons ,a-name ,d-name))))
                    name)))
          (cons '() (leaf root value path))))
    ;; A copy of every block's phis and instructions, and putting it back.
    (define (snapshot-blocks)
      (vector-map (lambda (block) (cons (ssa-block-phis block) (ssa-block-instrs block)))
                  blocks))
    (define (restore-blocks! saved)
      (for-each-index
       (lambda (i block)
         (match (vector-ref saved i)
           ((phis . instrs)
            (set-ssa-block-phis! block phis)
            (set-ssa-block-instrs! block instrs))))
       blocks))
    ;; Splits the phi name, whose analysis value is the cons value, into
    ;; field phis. reads are its component reads (see classify); target is
    ;; the block that rebuilds the pair for its whole uses, or #f when it has
    ;; none.
    (define (replace-phi! name value reads target)
      (let ((virtual (make-hash-table))   ; name -> (value . path)
            (copies (make-hash-table))    ; read -> the field or literal it becomes
            (gone (make-hash-table)))     ; reads of component pairs
        (hash-table-set! virtual name (cons value '()))
        (for-each
         (match-lambda
           ((dst base which)
            (match-let* (((base-value . base-path) (hash-table-ref virtual base))
                         (child (component-value base-value which))
                         (path (append base-path (list which))))
              (if (cons? child)
                  (begin (hash-table-set! virtual dst (cons child path))
                         (hash-table-set! gone dst #t))
                  (hash-table-set! copies dst (leaf name child path))))))
         reads)
        (match-let (((built . whole) (if target (materialize name value '()) (cons '() #f))))
          (define (rewrite instr)
            (let ((dst (instr-def instr)))
              (cond
               ((and dst (hash-table-exists? gone dst)) '())
               ((and dst (hash-table-exists? copies dst))
                (list `(assign ,dst ,(hash-table-ref copies dst))))
               (target
                (list (map-instr-uses (lambda (v) (if (eq? v name) whole v)) instr)))
               (else (list instr)))))
          (for-each-index
           (lambda (i block)
             (set-ssa-block-phis!
              block
              (filter (lambda (p) (not (eq? (phi-dst p) name))) (ssa-block-phis block)))
             (set-ssa-block-instrs!
              block
              (append (if (and target (= i target)) built '())
                      (append-map rewrite (ssa-block-instrs block)))))
           blocks)
          (when target
            (for-each-index
             (lambda (i block)
               (for-each
                (lambda (phi)
                  (for-each-phi-arg
                   (lambda (slot arg pred)
                     (when (eq? arg name)
                       (vector-set! (phi-args phi) slot whole)))
                   block phi))
                (ssa-block-phis block)))
             blocks)))))
    (define (try-phi! b phi)
      (let* ((name (phi-dst phi))
             (value (value-of name))
             (found (and (cons? value)
                         (> (vector-ref depth b) 0)
                         (web-has-fresh? name)
                         (classify name value))))
        (match found
          (#f #f)
          ((reads . escapes)
           (let ((target (match escapes
                           (() #f)
                           ((first . more) (fold common-dominator first more)))))
             (when (or (not target) (< (vector-ref depth target) (vector-ref depth b)))
               (set! fields (make-hash-table equal?))
               (set! loads (make-hash-table equal?))
               ;; Building the fields adds phis and loads before anything is
               ;; rewritten; if that finds a shape it cannot handle (a literal
               ;; where a pair should flow), put the blocks back and skip this
               ;; phi.
               (let ((saved (snapshot-blocks)))
                 (guard (e ((eq? e 'scalar-replacement-abort)
                            (restore-blocks! saved)
                            (refresh-defs!)))
                   (replace-phi! name value reads target)
                   (refresh-defs!)))))))))
    (when depth
      (refresh-defs!)
      (for-each-index
       (lambda (b block)
         (for-each (lambda (phi) (try-phi! b phi)) (ssa-block-phis block)))
       blocks))))

;;; --- Interprocedural summaries ---
;;;
;;; With sccp-program the procedures of a unit are analyzed together. A
;;; procedure that is closed (every reference to it is a direct call, so it
;;; has no unknown callers) starts with the join of its call sites' arguments
;;; as the values of its parameters, and the value of a direct call is the join
;;; of what the callee returns. Everything crossing a procedure boundary loses
;;; its component names (they are SSA names of the other procedure). Start
;;; optimistic (bot) and iterate whole rounds until no table changes; values
;;; only grow and the lattice is finite, so this terminates.

(define ipa-seeds (make-hash-table))     ; closed procedure -> vector of values
(define ipa-called (make-hash-table))    ; closed procedure -> seen at a live call
(define ipa-returns (make-hash-table))   ; procedure -> joined return value
(define ipa-changed #f)
(define ipa-active #f)
(define ipa-solving #f)  ; while solving, a procedure not yet called is all bot

(define (ipa-join! table key new)
  (let* ((old (hash-table-ref/default table key bot))
         (merged (join old new)))
    (unless (eq? old merged)
      (hash-table-set! table key merged)
      (set! ipa-changed #t))))

(define (ipa-reset! closed all)
  (set! ipa-seeds (make-hash-table))
  (set! ipa-called (make-hash-table))
  (set! ipa-returns (make-hash-table))
  (set! ipa-active #t)
  (for-each (lambda (name) (hash-table-set! ipa-returns name bot)) all)
  (for-each (match-lambda
              ((name . arity) (hash-table-set! ipa-seeds name (make-slots arity bot))))
            closed))

(define (ipa-clear!)
  (set! ipa-seeds (make-hash-table))
  (set! ipa-called (make-hash-table))
  (set! ipa-returns (make-hash-table))
  (set! ipa-solving #f)
  (set! ipa-active #f))

;; Reads off what an analyzed procedure contributes: arguments at its live
;; direct calls, and its return values. name is #f for the entry code.
(define (ipa-collect! name analysis blocks)
  (define (value-of operand)
    (strip-names (analysis-value analysis operand)))
  (define (note-call! callee args)
    (let ((seed (hash-table-ref/default ipa-seeds callee #f)))
      (when seed
        (unless (hash-table-ref/default ipa-called callee #f)
          (hash-table-set! ipa-called callee #t)
          (set! ipa-changed #t))
        (for-each (lambda (i arg)
                    (let* ((old (vector-ref seed i))
                           (merged (join old (value-of arg))))
                      (unless (eq? old merged)
                        (vector-set! seed i merged)
                        (set! ipa-changed #t))))
                  (iota (min (vector-length seed) (length args)))
                  args))))
  (define (note-return! v) (when name (ipa-join! ipa-returns name v)))
  (for-each-index
   (lambda (b block)
     (when (vector-ref (analysis-visited analysis) b)
       (for-each
        (lambda (instr)
          (match instr
            (('assign _ ('direct-call callee . args))
             (note-call! callee args))
            (('direct-tail-call callee . args)
             (note-call! callee args)
             (note-return! (hash-table-ref/default ipa-returns callee unknown)))
            (('return v)
             (note-return! (value-of v)))
            (((or 'tail-call 'tail-apply-call 'tail-callcc-call) . _)
             (note-return! unknown))
            (_ #f)))
        (ssa-block-instrs block))))
   blocks))

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

(define (ends-in-branch? instrs)
  (match (and (pair? instrs) (last instrs))
    (('if . _) #t)
    (_ #f)))

;; name, when given, is the procedure's label, for its interprocedural seeds.
(define (analyze ssa . maybe-name)
  (let* ((name (match maybe-name ((name) name) (() #f)))
         (blocks (ssa-proc-blocks ssa))
         (values (make-hash-table))
         (visited (make-slots (vector-length blocks) #f))
         (edges (make-hash-table))
         (use-sites (make-hash-table))
         (flow-list '())
         (ssa-list '())
         (iterations 0))
    (define (value-of operand)
      (cond
       ((symbol? operand) (hash-table-ref/default values operand bot))
       (else (literal-value operand))))
    (define (operand-name operand) (and (symbol? operand) operand))
    (define (update! var new)
      (let* ((old (hash-table-ref/default values var bot))
             (merged (join old new)))
        (unless (eq? old merged)
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
      (match rhs
        ((? symbol?) (value-of rhs))
        ((? literal-expr?) (const rhs))
        (('primop op . args)
         (eval-primop op (map value-of args) (map operand-name args)))
        (('global label)
         (hash-table-ref/default quote-cell-values label unknown))
        (('direct-call callee . _)
         (if ipa-active
             (hash-table-ref/default ipa-returns callee unknown)
             unknown))
        (('pi-field which x field)
         (eval-accessor-pi which (value-of x) field (value-of field)))
        (('pi kind x)
         (eval-pi kind (value-of x)))
        (_ unknown)))
    (define (visit-phi! b phi)
      (update! (phi-dst phi)
               (fold (lambda (pred arg acc)
                       (if (executable? pred b)
                           (join acc (value-of arg))
                           acc))
                     bot
                     (ssa-block-preds (vector-ref blocks b))
                     (vector->list (phi-args phi)))))
    (define (visit-instr! b instr)
      (set! iterations (+ iterations 1))
      (match instr
        (('assign dst rhs) (update! dst (eval-rhs rhs)))
        (('if test _ _)
         (let ((v (value-of test))
               (succs (ssa-block-succs (vector-ref blocks b))))
           (match-let (((then-block else-block) succs))
             (cond
              ((bot? v) #f)
              ((truthy? v) (mark-edge! b then-block))
              (else (mark-edge! b else-block))))
           (when (eq? v unknown)
             (for-each (lambda (s) (mark-edge! b s)) succs))))
        (_ #f)))
    (define (visit-item! b item)
      (if (phi? item) (visit-phi! b item) (visit-instr! b item)))
    (define (visit-block! b)
      (let* ((block (vector-ref blocks b))
             (instrs (ssa-block-instrs block)))
        (vector-set! visited b #t)
        (for-each (lambda (phi) (visit-phi! b phi)) (ssa-block-phis block))
        (for-each (lambda (instr) (visit-instr! b instr)) instrs)
        (unless (ends-in-branch? instrs)
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
    (let ((seed (and ipa-active name
                     (or ipa-solving (hash-table-ref/default ipa-called name #f))
                     (hash-table-ref/default ipa-seeds name #f)))
          (params (ssa-proc-param-names ssa)))
      (for-each (lambda (param i)
                  (hash-table-set! values param
                                   (if (and seed (< i (vector-length seed)))
                                       (vector-ref seed i)
                                       unknown)))
                params
                (iota (length params))))
    (visit-block! 0)
    ;; Flow edges first; then SSA use sites, each a (block . phi-or-instr).
    (let loop ()
      (match flow-list
        (((_ . to) . rest)
         (set! flow-list rest)
         (if (vector-ref visited to)
             (for-each (lambda (phi) (visit-phi! to phi))
                       (ssa-block-phis (vector-ref blocks to)))
             (visit-block! to))
         (loop))
        (()
         (match ssa-list
           (((b . item) . rest)
            (set! ssa-list rest)
            (when (vector-ref visited b)
              (visit-item! b item))
            (loop))
           (() #f)))))
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

;; Records what the entry code stored in each hoisted quote cell, without
;; component names (they belong to the entry procedure). The values of all
;; stores to one cell in this analysis are joined, so a cell written on several
;; paths is described soundly; a later pass replaces the recorded value (it may
;; be more precise once the interprocedural values have settled).
(define (harvest-quote-cells! analysis blocks)
  (let ((stored (make-hash-table)))
    (for-each-index
     (lambda (b block)
       (when (vector-ref (analysis-visited analysis) b)
         (for-each
          (lambda (instr)
            (match instr
              (('set-global! (? quote-cell? cell) operand)
               (let ((v (analysis-value analysis operand)))
                 (hash-table-update!/default
                  stored cell
                  (lambda (old) (join old (strip-names (if (bot? v) unknown v))))
                  bot)))
              (_ #f)))
          (ssa-block-instrs block))))
     blocks)
    (hash-table-walk
     stored
     (lambda (cell new)
       (unless (eq? new (hash-table-ref/default quote-cell-values cell #f))
         (hash-table-set! quote-cell-values cell new)
         (when ipa-active (set! ipa-changed #t)))))))

(define (ssa-proc-param-names ssa)
  (params-names (ssa-proc-params ssa)))

;;; --- Rewriting ---

;; x when rhs is a refinement node (pi kind x) or (pi-field which x a).
(define (refinement-subject rhs)
  (match rhs
    (('pi _ subject) subject)
    (('pi-field _ subject _) subject)
    (_ #f)))

(define (rewrite-instr analysis instr)
  (define (value-of var) (analysis-value analysis var))
  (define (foldable-rhs? rhs)
    (match rhs
      ((? symbol?) #t)
      (('primop op . _) (and (memq op foldable-primops) #t))
      (_ #f)))
  ;; For a car or cdr of a known pair: a copy of the component's name when
  ;; the analysis knows one, else the unchecked accessor. #f otherwise.
  (define (known-pair-read rhs)
    (match (accessor-read rhs)
      ((which . x)
       (and (cons? (value-of x))
            (let-values (((value name) (component (value-of x) which)))
              (or name `(primop ,(unsafe-accessor which) ,x)))))
      (#f #f)))
  (match instr
    (('assign dst rhs)
     (cond
      ((refinement-subject rhs)
       => (lambda (subject) `(assign ,dst ,subject)))
      ((literal-expr? rhs) instr)
      ((and (const? (value-of dst)) (foldable-rhs? rhs))
       `(assign ,dst ,(const-value (value-of dst))))
      ((known-pair-read rhs)
       => (lambda (new-rhs) `(assign ,dst ,new-rhs)))
      (else instr)))
    (_ instr)))

;; Drops blocks that cannot execute and edges that are never taken, keeping the
;; layout order of the rest, and turns decided branches into jumps.
(define (prune-dead-code! analysis blocks)
  (let* ((count (vector-length blocks))
         (new-index (make-slots count #f))
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
              (instrs (ssa-block-instrs block)))
         ;; a branch with one live arm becomes a jump to it
         (match (list (and (pair? instrs) (last instrs)) live-succs old-succs)
           ((('if _ then-label else-label) (live) (then-block _))
            (set-ssa-block-instrs!
             block
             (append (drop-right instrs 1)
                     (list `(goto ,(if (eqv? live then-block) then-label else-label))))))
           (_ #f))
         (let ((old-preds (ssa-block-preds block)))
           (for-each
            (lambda (phi)
              (let ((filtered
                     (fold-right (lambda (p arg acc)
                                   (if (live-edge? p b) (cons arg acc) acc))
                                 '()
                                 old-preds
                                 (vector->list (phi-args phi)))))
                (set-ssa-block-phis!
                 block
                 (map (lambda (p)
                        (if (eq? p phi)
                            (make-phi (phi-dst p) (phi-var p) (list->vector filtered))
                            p))
                      (ssa-block-phis block)))))
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

;; Primops whose result the analysis can compute, so that a definition it finds
;; constant may be replaced by the literal.
(define foldable-primops
  '(+ - * = < > eq? null? pair? symbol? car cdr unsafe-car unsafe-cdr))

(define (removable-rhs? rhs remove-allocation?)
  (match rhs
    ((? symbol?) #t)
    ((? literal-expr?) #t)
    (((or 'pi 'pi-field 'global 'closure-env-ref 'unbox) . _) #t)
    (('primop op . _)
     (or (and (memq op pure-primops) #t)
         (and remove-allocation? (eq? op 'cons))))
    (_ #f)))

(define (remove-dead-definitions! blocks remove-allocation?)
  ;; Mark what essential instructions need, through phis as well, so that
  ;; loop-carried values nobody reads (cycles of phis) die too.
  (let ((live (make-hash-table))
        (phi-of (make-hash-table))
        (instr-of (make-hash-table))
        (work '()))
    (define (removable? instr)
      (match instr
        (('assign _ rhs) (removable-rhs? rhs remove-allocation?))
        (_ #f)))
    (define (mark! var)
      (when (and (symbol? var) (not (hash-table-exists? live var)))
        (hash-table-set! live var #t)
        (set! work (cons var work))))
    (for-each-index
     (lambda (b block)
       (for-each (lambda (phi) (hash-table-set! phi-of (phi-dst phi) phi))
                 (ssa-block-phis block))
       (for-each (lambda (instr)
                   (if (removable? instr)
                       (hash-table-set! instr-of (instr-def instr) instr)
                       (for-each mark! (instr-uses instr))))
                 (ssa-block-instrs block)))
     blocks)
    (let loop ()
      (match work
        (() #f)
        ((var . rest)
         (set! work rest)
         (cond
          ((hash-table-ref/default phi-of var #f)
           => (lambda (phi) (for-each mark! (vector->list (phi-args phi)))))
          ((hash-table-ref/default instr-of var #f)
           => (lambda (instr) (for-each mark! (instr-uses instr)))))
         (loop))))
    (for-each-index
     (lambda (b block)
       (set-ssa-block-phis!
        block
        (filter (lambda (phi) (hash-table-exists? live (phi-dst phi)))
                (ssa-block-phis block)))
       (set-ssa-block-instrs!
        block
        (filter (lambda (instr)
                  (not (and (removable? instr)
                            (not (hash-table-exists? live (instr-def instr))))))
                (ssa-block-instrs block))))
     blocks)))

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
                   (match instr
                     (('assign dst (? symbol? from)) (hash-table-set! source dst from))
                     (_ #f)))
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
                      (const? (analysis-value analysis (phi-dst phi))))
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
                           ,(const-value (analysis-value analysis (phi-dst phi)))))
                constant-phis)
           (ssa-block-instrs block))))))
   blocks))

;; Optimizes an SSA procedure (with pi nodes inserted and removed inside).
;; remove-allocation? also deletes unread cons cells.
;; entry? marks the program's entry procedure: what it stores in hoisted quote
;; cells is recorded for the procedures processed after it.
(define (sccp-ssa ssa . options)
  (match-let (((remove-allocation? entry? . _) (append options '(#f #f))))
    (run-sccp ssa (or remove-allocation? remove-dead-allocation) entry? #f #f)))

;; name: the procedure's label when its parameters have interprocedural seeds;
;; pis-done?: insert-pis! and the quote cells were handled by sccp-program.
(define (run-sccp ssa remove-allocation? entry? name pis-done?)
  (let* ((ssa (if pis-done? ssa (thread-constant-branches-ssa ssa)))
         (blocks (ssa-proc-blocks ssa)))
    (unless pis-done? (insert-pis! blocks #t))
    (when (and entry? (not pis-done?))
      (reset-quote-cells!)
      (harvest-quote-cells! (analyze ssa) blocks))
    (let* ((start (current-jiffy))
           (ops-before (and sccp-stats? (count-ops blocks)))
           (analysis (analyze ssa name)))
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
        (when (and scalar-replacement remove-allocation?)
          (remove-dead-definitions! pruned remove-allocation?)
          (scalar-replace! analysis pruned)
          (propagate-copies! pruned))
        (remove-dead-definitions! pruned remove-allocation?)
        (when sccp-stats?
          (report-stats name analysis ops-before (count-ops pruned)
                        (- (current-jiffy) start)))
        (make-ssa-proc (ssa-proc-params ssa) pruned)))))

;;; --- Static statistics (HOP_SSA_STATS=1) ---
;;;
;;; One line per analyzed procedure on stderr: analysis iterations, how the
;;; analysis values of its SSA names split (unknown / constant / pair of unknown
;;; contents / structured cons), the number of each shape-related operation
;;; before and after the rewrite (before:after), analysis plus rewrite time in
;;; microseconds, and the size of the interned value table so far.

(define sccp-stats? #f)
(define (set-sccp-stats! flag) (set! sccp-stats? flag))

(define stat-ops '(car cdr cons pair? null?))

;; counts for car, cdr, cons, pair?, null? (unsafe accessors count as car/cdr)
(define (count-ops blocks)
  (define (instr-op instr)
    (match (instr-rhs instr)
      (('primop op . _) (or (accessor-kind op) op))
      (_ #f)))
  (let ((ops (append-map (lambda (block) (filter-map instr-op (ssa-block-instrs block)))
                         (vector->list blocks))))
    (map (lambda (op) (length (filter (lambda (o) (eq? o op)) ops)))
         stat-ops)))

(define (report-stats name analysis before after jiffies)
  (let ((unknowns 0) (consts 0) (pairs 0) (structs 0))
    (hash-table-walk
     (analysis-values analysis)
     (lambda (var v)
       (cond ((eq? v unknown) (set! unknowns (+ unknowns 1)))
             ((const? v) (set! consts (+ consts 1)))
             ((eq? v pair-value) (set! pairs (+ pairs 1)))
             ((cons? v) (set! structs (+ structs 1))))))
    (let ((out (current-error-port)))
      (display "hop-ssa-stats" out)
      (display " proc=" out) (display (or name "-") out)
      (display " iters=" out) (display (analysis-iterations analysis) out)
      (display " unknown=" out) (display unknowns out)
      (display " const=" out) (display consts out)
      (display " pair=" out) (display pairs out)
      (display " struct=" out) (display structs out)
      (for-each (lambda (op b a)
                  (display " " out) (display op out) (display "=" out)
                  (display b out) (display ":" out) (display a out))
                stat-ops before after)
      (display " us=" out)
      (display (quotient (* jiffies 1000000) (jiffies-per-second)) out)
      (display " values=" out) (display node-count out)
      (newline out))))

;; Optimizes a whole unit at once. specs: a list of (name params cfg) for the
;; non-entry procedures; closed: (name . parameter-count) of those whose every
;; reference is a direct call. Returns the entry CFG and the other CFGs in the
;; order of specs.
(define (sccp-program entry-cfg specs closed)
  (let* ((entry-ssa (thread-constant-branches-ssa (check-ssa (cfg->ssa '() entry-cfg))))
         (ssas (map (match-lambda
                      ((_ params cfg)
                       (thread-constant-branches-ssa (check-ssa (cfg->ssa params cfg)))))
                    specs))
         (names (map (match-lambda ((name _ _) name)) specs)))
    (ipa-reset! closed names)
    (for-each (lambda (ssa) (insert-pis! (ssa-proc-blocks ssa) #t)) (cons entry-ssa ssas))
    (reset-quote-cells!)
    ;; the quote cells are written first and do not depend on any call result
    (harvest-quote-cells! (analyze entry-ssa) (ssa-proc-blocks entry-ssa))
    (set! ipa-solving #t)
    (let loop ()
      (set! ipa-changed #f)
      (let ((analysis (analyze entry-ssa)))
        (harvest-quote-cells! analysis (ssa-proc-blocks entry-ssa))
        (ipa-collect! #f analysis (ssa-proc-blocks entry-ssa)))
      (for-each (lambda (name ssa)
                  (let ((analysis (analyze ssa name)))
                    (ipa-collect! name analysis (ssa-proc-blocks ssa))))
                names ssas)
      (when ipa-changed (loop)))
    (set! ipa-solving #f)
    (let* ((entry-out (run-sccp entry-ssa remove-dead-allocation #f #f #t))
           (outs (map (lambda (name ssa)
                        (run-sccp ssa remove-dead-allocation #f name #t))
                      names ssas)))
      (ipa-clear!)
      (values (ssa->cfg (check-ssa entry-out))
              (map (lambda (out) (ssa->cfg (check-ssa out))) outs)))))

(define (sccp-cfg params cfg . maybe-entry?)
  (let ((entry? (match maybe-entry? ((entry?) entry?) (() #f))))
    (ssa->cfg (check-ssa (sccp-ssa (check-ssa (cfg->ssa params cfg)) #f entry?)))))

;; The control for measurements: the same SSA round trip and cleanup (pi nodes,
;; copy propagation, dead definition removal) with the analysis switched off,
;; so nothing is learned about values and no branch or block is removed.
(define (control-ssa ssa)
  (let ((blocks (ssa-proc-blocks ssa)))
    (insert-pis! blocks #f)
    (for-each-index
     (lambda (b block)
       (set-ssa-block-instrs!
        block
        (map (lambda (instr)
               (match instr
                 (('assign dst (= refinement-subject (? symbol? subject)))
                  `(assign ,dst ,subject))
                 (_ instr)))
             (ssa-block-instrs block))))
     blocks)
    (propagate-copies! blocks)
    (remove-dead-definitions! blocks #f)
    ssa))

(define (control-cfg params cfg)
  (ssa->cfg (check-ssa (control-ssa (check-ssa (cfg->ssa params cfg))))))

))
