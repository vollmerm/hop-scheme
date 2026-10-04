(define-library (hop pass ssa)
  ;;; Pass 5.4: SSA construction, verification, and destruction
  ;;;
  ;;; Converts the CFG of one procedure (see (hop pass cfg)) to static single
  ;;; assignment form and back, so analyses in between can treat each name as
  ;;; having exactly one definition.
  ;;;
  ;;; A procedure in SSA form is a vector of <ssa-block>s. Each block has phi
  ;;; nodes, ordinary TAC instructions (without the leading (label ...)), and
  ;;; successor and predecessor index lists. A phi's args vector lines up with
  ;;; its block's predecessor list. Blocks keep their original layout order:
  ;;; a block with no terminator falls through to the next block.
  ;;;
  ;;; Every definition of a variable x gets a fresh name x~1, x~2, ... except
  ;;; that a parameter keeps its own name as its definition on entry, so the
  ;;; procedure's parameter list is unchanged.
  ;;;
  ;;; Construction places phis at iterated dominance frontiers of definitions
  ;;; of names used across blocks (semi-pruned SSA). It uses dominators from
  ;;; the Cooper-Harvey-Kennedy algorithm, which also handles the irreducible
  ;;; loops that letrec clusters produce. Unreachable blocks are dropped. When
  ;;; the entry block is itself a loop header, an empty block is placed in
  ;;; front of it so that parameters are defined once, on entry, rather than
  ;;; on every iteration.
  ;;;
  ;;; Destruction splits critical edges into blocks with phis, then replaces
  ;;; each phi with copies at the end of its predecessors, sequenced so that
  ;;; simultaneous copies cannot overwrite each other's sources.
  (export cfg->ssa
          ssa->cfg
          verify-ssa
          check-ssa
          ssa-round-trip-cfg
          make-ssa-proc
          make-phi
          phi?
          phi-var
          set-ssa-block-instrs!
          set-ssa-block-phis!
          set-ssa-block-succs!
          set-ssa-block-preds!
          map-instr-uses
          instr-uses
          instr-def
          immediate-dominators
          dominator-children
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
          (only (srfi 1)
                delete-duplicates drop-right filter-map find fold iota
                last list-index reduce)
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

;;; --- Helpers ---

(define (for-each-block proc blocks)
  (do ((b 0 (+ b 1)))
      ((= b (vector-length blocks)))
    (proc b (vector-ref blocks b))))

(define (map-in-order proc lst)
  (reverse (fold (lambda (x acc) (cons (proc x) acc)) '() lst)))

(define (replace-element old new lst)
  (map (lambda (x) (if (eqv? x old) new x)) lst))

(define (symbol-append . parts)
  (string->symbol
   (apply string-append
          (map (lambda (part) (if (symbol? part) (symbol->string part) part))
               parts))))

(define (message . parts)
  (let ((port (open-output-string)))
    (for-each (lambda (part) (display part port)) parts)
    (get-output-string port)))

(define (make-name-generator prefix)
  (let ((count 0))
    (lambda ()
      (set! count (+ count 1))
      (symbol-append prefix (number->string count)))))

;;; --- Instruction operands ---
;;; The positions of each TAC instruction that hold variable references, as
;;; opposed to labels, procedure names, arities, and literals.

(define terminator-heads
  '(if goto return tail-call direct-tail-call tail-apply-call tail-callcc-call))

(define (terminator? instr)
  (and (pair? instr) (memq (car instr) terminator-heads) #t))

(define (map-operand f operand)
  (if (symbol? operand) (f operand) operand))

(define (map-operands f operands)
  (map (lambda (operand) (map-operand f operand)) operands))

(define (map-rhs-uses f rhs)
  (cond
   ((symbol? rhs) (f rhs))
   ((not (pair? rhs)) rhs)
   (else
    (case (car rhs)
      ((quote global) rhs)
      ((primop)
       `(primop ,(cadr rhs) ,@(map-operands f (cddr rhs))))
      ((cons box unbox car cdr pair? null? closure-call apply-call callcc-call)
       `(,(car rhs) ,@(map-operands f (cdr rhs))))
      ((closure-env-ref)
       `(closure-env-ref ,(map-operand f (cadr rhs)) ,@(cddr rhs)))
      ((pi)
       `(pi ,(cadr rhs) ,@(map-operands f (cddr rhs))))
      ((make-closure make-variadic-closure)
       `(,(car rhs) ,(cadr rhs) ,(caddr rhs) ,@(map-operands f (cdddr rhs))))
      ((direct-call)
       `(direct-call ,(cadr rhs) ,@(map-operands f (cddr rhs))))
      (else (error "SSA: unknown assignment right-hand side" rhs))))))

;; Rebuilds instr with f applied to each variable it reads.
(define (map-instr-uses f instr)
  (case (car instr)
    ((assign)
     `(assign ,(cadr instr) ,(map-rhs-uses f (caddr instr))))
    ((if)
     `(if ,(map-operand f (cadr instr)) ,(caddr instr) ,(cadddr instr)))
    ((goto label)
     instr)
    ((return set-box! tail-call tail-apply-call tail-callcc-call)
     `(,(car instr) ,@(map-operands f (cdr instr))))
    ((direct-tail-call)
     `(direct-tail-call ,(cadr instr) ,@(map-operands f (cddr instr))))
    ((set-global!)
     `(set-global! ,(cadr instr) ,@(map-operands f (cddr instr))))
    (else (error "SSA: unknown TAC instruction" instr))))

(define (instr-uses instr)
  (let ((uses '()))
    (map-instr-uses (lambda (var) (set! uses (cons var uses)) var) instr)
    (reverse uses)))

(define (instr-def instr)
  (and (eq? (car instr) 'assign) (cadr instr)))

;;; --- Building blocks from a CFG ---

(define (strip-label instrs)
  (if (and (pair? instrs)
           (pair? (car instrs))
           (eq? (car (car instrs)) 'label))
      (cdr instrs)
      instrs))

;; The blocks reachable from block 0, renumbered, as <ssa-block>s with no phis
;; or predecessors yet.
(define (reachable-blocks cfg)
  (let* ((cfg-blocks (list->vector cfg))
         (count (vector-length cfg-blocks))
         (reachable (make-vector count #f))
         (new-index (make-vector count #f)))
    (let visit ((i 0))
      (unless (vector-ref reachable i)
        (vector-set! reachable i #t)
        (for-each visit (basic-block-successors (vector-ref cfg-blocks i)))))
    (let ((kept (filter (lambda (i) (vector-ref reachable i)) (iota count))))
      (for-each (lambda (i k) (vector-set! new-index i k))
                kept
                (iota (length kept)))
      (map (lambda (i)
             (let ((block (vector-ref cfg-blocks i)))
               (make-ssa-block
                (basic-block-label block)
                '()
                (strip-label (basic-block-instructions block))
                (map (lambda (s) (vector-ref new-index s))
                     (basic-block-successors block))
                '())))
           kept))))

(define (jumps-to-entry? block)
  (and (memv 0 (ssa-block-succs block)) #t))

;; Puts an empty block in front when some block jumps back to block 0.
(define (with-entry-block blocks)
  (if (find jumps-to-entry? blocks)
      (cons (make-ssa-block #f '() '() '(1) '())
            (map (lambda (block)
                   (make-ssa-block (ssa-block-label block)
                                   '()
                                   (ssa-block-instrs block)
                                   (map (lambda (s) (+ s 1)) (ssa-block-succs block))
                                   '()))
                 blocks))
      blocks))

(define (link-predecessors! blocks)
  (for-each-block
   (lambda (b block)
     (let ((succs (ssa-block-succs block)))
       (unless (= (length succs) (length (delete-duplicates succs)))
         (error "SSA: block has two edges to the same successor" b))
       (for-each (lambda (s)
                   (let ((target (vector-ref blocks s)))
                     (set-ssa-block-preds!
                      target
                      (append (ssa-block-preds target) (list b)))))
                 succs)))
   blocks))

(define (build-ssa-blocks cfg)
  (let ((blocks (list->vector (with-entry-block (reachable-blocks cfg)))))
    (link-predecessors! blocks)
    blocks))

;;; --- Dominators ---
;;; Every block is reachable from block 0, so each has an immediate dominator.

;; Block indices in reverse postorder of a depth-first search from block 0.
(define (reverse-postorder blocks)
  (let ((visited (make-vector (vector-length blocks) #f)))
    (let visit ((b 0) (order '()))
      (cond
       ((vector-ref visited b) order)
       (else
        (vector-set! visited b #t)
        (cons b (fold visit order (ssa-block-succs (vector-ref blocks b)))))))))

;; A vector giving each block's immediate dominator (block 0 is its own).
(define (immediate-dominators blocks)
  (let* ((order (reverse-postorder blocks))
         (rank (make-vector (vector-length blocks) #f))
         (idom (make-vector (vector-length blocks) #f)))
    (define (intersect a b)
      (cond
       ((= a b) a)
       ((> (vector-ref rank a) (vector-ref rank b))
        (intersect (vector-ref idom a) b))
       (else
        (intersect a (vector-ref idom b)))))
    (define (new-idom b)
      (reduce intersect
              #f
              (filter (lambda (p) (vector-ref idom p))
                      (ssa-block-preds (vector-ref blocks b)))))
    (for-each (lambda (b r) (vector-set! rank b r))
              order
              (iota (length order)))
    (vector-set! idom 0 0)
    (let refine ()
      (let ((changed? #f))
        (for-each (lambda (b)
                    (let ((d (new-idom b)))
                      (unless (eqv? d (vector-ref idom b))
                        (vector-set! idom b d)
                        (set! changed? #t))))
                  (cdr order))
        (when changed? (refine))))
    idom))

;; A vector giving each block's children in the dominator tree.
(define (dominator-children idom)
  (let ((children (make-vector (vector-length idom) '())))
    (do ((b 1 (+ b 1)))
        ((= b (vector-length idom)) children)
      (let ((parent (vector-ref idom b)))
        (vector-set! children parent (cons b (vector-ref children parent)))))))

;; A vector giving each block's dominance frontier: the join blocks that it
;; reaches but does not strictly dominate.
(define (dominance-frontiers blocks idom)
  (let ((frontier (make-vector (vector-length blocks) '())))
    (for-each-block
     (lambda (b block)
       (when (> (length (ssa-block-preds block)) 1)
         (for-each
          (lambda (p)
            (let climb ((runner p))
              (unless (= runner (vector-ref idom b))
                (unless (memv b (vector-ref frontier runner))
                  (vector-set! frontier runner (cons b (vector-ref frontier runner))))
                (climb (vector-ref idom runner)))))
          (ssa-block-preds block))))
     blocks)
    frontier))

;;; --- Construction ---

;; For each variable, the blocks that define it. Parameters are defined in
;; block 0.
(define (definition-blocks blocks param-names)
  (let ((table (make-hash-table)))
    (define (note-definition! var b)
      (hash-table-update!/default
       table var (lambda (defs) (if (memv b defs) defs (cons b defs))) '()))
    (for-each (lambda (param) (note-definition! param 0)) param-names)
    (for-each-block
     (lambda (b block)
       (for-each (lambda (instr)
                   (let ((var (instr-def instr)))
                     (when var (note-definition! var b))))
                 (ssa-block-instrs block)))
     blocks)
    table))

;; The variables read in some block before that block defines them. Only these
;; can need a phi.
(define (variables-live-across-blocks blocks)
  (let ((table (make-hash-table)))
    (for-each-block
     (lambda (b block)
       (let scan ((instrs (ssa-block-instrs block)) (defined '()))
         (unless (null? instrs)
           (for-each (lambda (var)
                       (unless (memq var defined)
                         (hash-table-set! table var #t)))
                     (instr-uses (car instrs)))
           (let ((var (instr-def (car instrs))))
             (scan (cdr instrs) (if var (cons var defined) defined))))))
     blocks)
    table))

(define (add-phi! block var)
  (set-ssa-block-phis!
   block
   (append (ssa-block-phis block)
           (list (make-phi var var
                           (make-vector (length (ssa-block-preds block)) #f))))))

;; Gives var a phi in every block of the iterated dominance frontier of its
;; defining blocks.
(define (place-phis! blocks frontier var def-blocks)
  (let place ((work def-blocks) (has-phi '()))
    (unless (null? work)
      (let ((new-blocks (filter (lambda (d) (not (memv d has-phi)))
                                (vector-ref frontier (car work)))))
        (for-each (lambda (d) (add-phi! (vector-ref blocks d) var)) new-blocks)
        (place (append (cdr work)
                       (filter (lambda (d) (not (memv d def-blocks))) new-blocks))
               (append new-blocks has-phi))))))

(define (insert-phis! blocks frontier param-names)
  (let ((cross-block (variables-live-across-blocks blocks)))
    (hash-table-walk
     (definition-blocks blocks param-names)
     (lambda (var def-blocks)
       (when (hash-table-ref/default cross-block var #f)
         (place-phis! blocks frontier var def-blocks))))))

;; Variables a block defines, by their original names.
(define (block-defined-variables block)
  (append (map phi-var (ssa-block-phis block))
          (filter-map instr-def (ssa-block-instrs block))))

;; Walks the dominator tree giving each definition a fresh name and pointing
;; each use, and each phi argument in a successor, at the definition that
;; reaches it. A phi argument with no reaching definition becomes 0.
(define (rename-variables! blocks children param-names)
  (let ((reaching (make-hash-table))   ; variable -> its current names, innermost first
        (versions (make-hash-table)))  ; variable -> number of names made so far
    (define (current var)
      (let ((names (hash-table-ref/default reaching var '())))
        (and (pair? names) (car names))))
    (define (push! var name)
      (hash-table-set! reaching var (cons name (hash-table-ref/default reaching var '()))))
    (define (pop! var)
      (hash-table-set! reaching var (cdr (hash-table-ref reaching var))))
    (define (new-name! var)
      (let ((version (+ 1 (hash-table-ref/default versions var 0))))
        (hash-table-set! versions var version)
        (let ((name (symbol-append var "~" (number->string version))))
          (push! var name)
          name)))
    (define (rename-use var)
      (or (current var) var))
    (define (rename-instr! instr)
      (let ((renamed (map-instr-uses rename-use instr))
            (var (instr-def instr)))
        (if var
            `(assign ,(new-name! var) ,(caddr renamed))
            renamed)))
    (define (fill-phi-args! pred-index target)
      (let ((slot (list-index (lambda (p) (= p pred-index)) (ssa-block-preds target))))
        (for-each (lambda (phi)
                    (vector-set! (phi-args phi) slot (or (current (phi-var phi)) 0)))
                  (ssa-block-phis target))))
    (define (rename-block! b)
      (let* ((block (vector-ref blocks b))
             (defined (block-defined-variables block)))
        (for-each (lambda (phi) (set-phi-dst! phi (new-name! (phi-var phi))))
                  (ssa-block-phis block))
        (set-ssa-block-instrs! block (map-in-order rename-instr! (ssa-block-instrs block)))
        (for-each (lambda (s) (fill-phi-args! b (vector-ref blocks s)))
                  (ssa-block-succs block))
        (for-each rename-block! (vector-ref children b))
        (for-each pop! defined)))
    (for-each (lambda (param) (push! param param)) param-names)
    (rename-block! 0)))

;; Converts the CFG of a procedure with the given parameter list to SSA form.
(define (cfg->ssa params cfg)
  (let* ((blocks (build-ssa-blocks cfg))
         (idom (immediate-dominators blocks))
         (param-names (params-names params)))
    (insert-phis! blocks (dominance-frontiers blocks idom) param-names)
    (rename-variables! blocks (dominator-children idom) param-names)
    (make-ssa-proc params blocks)))

;;; --- Verification ---

(define (check-edges blocks report!)
  (let ((count (vector-length blocks)))
    (define (block-name b)
      (or (ssa-block-label (vector-ref blocks b)) (message "#" b)))
    (define (valid-index? b)
      (and (>= b 0) (< b count)))
    (for-each-block
     (lambda (b block)
       (for-each (lambda (s)
                   (cond
                    ((not (valid-index? s))
                     (report! "block " (block-name b) " has an out-of-range successor"))
                    ((not (memv b (ssa-block-preds (vector-ref blocks s))))
                     (report! "edge " (block-name b) " -> " (block-name s)
                              " is missing from the predecessor list"))))
                 (ssa-block-succs block))
       (for-each (lambda (p)
                   (unless (and (valid-index? p)
                                (memv b (ssa-block-succs (vector-ref blocks p))))
                     (report! "predecessor edge into " (block-name b)
                              " is missing from the successor list")))
                 (ssa-block-preds block))
       (for-each (lambda (phi)
                   (unless (= (vector-length (phi-args phi))
                              (length (ssa-block-preds block)))
                     (report! "phi " (phi-dst phi) " has a different arity than "
                              (block-name b) " has predecessors")))
                 (ssa-block-phis block)))
     blocks)))

;; A table from each defined name to (block . position), where position -1
;; means a phi or parameter. Reports names defined more than once.
(define (definition-sites ssa report!)
  (let ((sites (make-hash-table))
        (blocks (ssa-proc-blocks ssa)))
    (define (define! name b position)
      (if (hash-table-exists? sites name)
          (report! "multiple definitions of " name)
          (hash-table-set! sites name (cons b position))))
    (for-each (lambda (param) (define! param 0 -1))
              (params-names (ssa-proc-params ssa)))
    (for-each-block
     (lambda (b block)
       (for-each (lambda (phi) (define! (phi-dst phi) b -1))
                 (ssa-block-phis block))
       (for-each (lambda (instr position)
                   (let ((var (instr-def instr)))
                     (when var (define! var b position))))
                 (ssa-block-instrs block)
                 (iota (length (ssa-block-instrs block)))))
     blocks)
    sites))

;; Checks that every name read is defined, and that its definition dominates
;; the read.
(define (check-uses blocks sites report!)
  (let ((idom (immediate-dominators blocks)))
    (define (block-name b)
      (or (ssa-block-label (vector-ref blocks b)) (message "#" b)))
    (define (dominates? a b)
      (cond ((= a b) #t)
            ((= b 0) #f)
            (else (dominates? a (vector-ref idom b)))))
    ;; position is the index of the reading instruction in its block.
    (define (check-use! name b position)
      (let ((site (hash-table-ref/default sites name #f)))
        (cond
         ((not site)
          (report! "use of undefined name " name " in " (block-name b)))
         ((= (car site) b)
          (unless (< (cdr site) position)
            (report! "use of " name " before its definition in " (block-name b))))
         ((not (dominates? (car site) b))
          (report! "definition of " name " does not dominate its use in "
                   (block-name b))))))
    (for-each-block
     (lambda (b block)
       ;; A phi argument is read at the end of its predecessor.
       (for-each (lambda (phi)
                   (for-each (lambda (pred arg)
                               (when (symbol? arg)
                                 (check-use! arg pred
                                             (length (ssa-block-instrs (vector-ref blocks pred))))))
                             (ssa-block-preds block)
                             (vector->list (phi-args phi))))
                 (ssa-block-phis block))
       (for-each (lambda (instr position)
                   (for-each (lambda (var) (check-use! var b position))
                             (instr-uses instr)))
                 (ssa-block-instrs block)
                 (iota (length (ssa-block-instrs block)))))
     blocks)))

;; Returns a list of messages describing every way ssa is not valid SSA form;
;; the list is empty for a valid procedure.
(define (verify-ssa ssa)
  (let ((problems '()))
    (define (report! . parts)
      (set! problems (cons (apply message parts) problems)))
    (check-edges (ssa-proc-blocks ssa) report!)
    (check-uses (ssa-proc-blocks ssa) (definition-sites ssa report!) report!)
    (reverse problems)))

(define (check-ssa ssa)
  (let ((problems (verify-ssa ssa)))
    (unless (null? problems)
      (error "Invalid SSA" problems))
    ssa))

;;; --- Destruction ---

(define (insert-before-terminator instrs new-instrs)
  (if (and (pair? instrs) (terminator? (last instrs)))
      (append (drop-right instrs 1) new-instrs (list (last instrs)))
      (append instrs new-instrs)))

;; Rewrites the (if test then else) branch so its edge to old goes to new.
(define (retarget-branch branch old new)
  (let ((test (cadr branch))
        (then-label (caddr branch))
        (else-label (cadddr branch)))
    (cond
     ((eq? then-label old) `(if ,test ,new ,else-label))
     ((eq? else-label old) `(if ,test ,then-label ,new))
     (else (error "SSA: branch does not target the expected label" branch old)))))

;; Routes the edge from block p into block b through a new block at index
;; new-index, and returns that block. Phi arguments in b stay lined up with
;; its predecessors because the new block takes p's place in the list.
(define (split-edge! blocks p b new-index)
  (let* ((pred (vector-ref blocks p))
         (target (vector-ref blocks b))
         (target-label (ssa-block-label target))
         (edge-label (symbol-append "ssa.edge."
                                    (or (ssa-block-label pred) "entry")
                                    "." target-label)))
    (unless target-label
      (error "SSA: critical edge into an unlabeled block"))
    (set-ssa-block-instrs!
     pred
     (append (drop-right (ssa-block-instrs pred) 1)
             (list (retarget-branch (last (ssa-block-instrs pred))
                                    target-label
                                    edge-label))))
    (set-ssa-block-succs! pred (replace-element b new-index (ssa-block-succs pred)))
    (set-ssa-block-preds! target (replace-element p new-index (ssa-block-preds target)))
    (make-ssa-block edge-label '() `((goto ,target-label)) (list b) (list p))))

;; Returns a vector of blocks in which every predecessor of a block with phis
;; has that block as its only successor.
(define (split-critical-edges! blocks)
  (let ((count (vector-length blocks))
        (edge-blocks '()))
    (for-each-block
     (lambda (b block)
       (unless (null? (ssa-block-phis block))
         (for-each (lambda (p)
                     (when (pair? (cdr (ssa-block-succs (vector-ref blocks p))))
                       (set! edge-blocks
                             (append edge-blocks
                                     (list (split-edge! blocks p b
                                                        (+ count (length edge-blocks))))))))
                   (ssa-block-preds block))))
     blocks)
    (vector-append blocks (list->vector edge-blocks))))

;; Replaces every phi with copies at the end of the matching predecessor.
(define (lower-phis! blocks)
  (let ((fresh-temp (make-name-generator "ssa.tmp.")))
    (for-each-block
     (lambda (b block)
       (let ((phis (ssa-block-phis block)))
         (unless (null? phis)
           (for-each
            (lambda (p arg-index)
              (let ((pred (vector-ref blocks p))
                    (copies (map (lambda (phi)
                                   (cons (phi-dst phi)
                                         (vector-ref (phi-args phi) arg-index)))
                                 phis)))
                (set-ssa-block-instrs!
                 pred
                 (insert-before-terminator
                  (ssa-block-instrs pred)
                  (sequentialize-copies copies fresh-temp)))))
            (ssa-block-preds block)
            (iota (length (ssa-block-preds block))))
           (set-ssa-block-phis! block '()))))
     blocks)))

(define (ssa-block->basic-block block)
  (let* ((label (ssa-block-label block))
         (instrs (ssa-block-instrs block))
         (basic-block (make-basic-block label
                                        (if label
                                            (cons `(label ,label) instrs)
                                            instrs))))
    (set-basic-block-successors! basic-block (ssa-block-succs block))
    basic-block))

;; Converts a procedure in SSA form back to a CFG.
(define (ssa->cfg ssa)
  (let ((blocks (split-critical-edges! (ssa-proc-blocks ssa))))
    (lower-phis! blocks)
    (vector->list (vector-map ssa-block->basic-block blocks))))

;; CFG -> SSA -> CFG with nothing in between, checking the SSA on the way.
(define (ssa-round-trip-cfg params cfg)
  (ssa->cfg (check-ssa (cfg->ssa params cfg))))

;;; --- Display ---

(define (display-ssa ssa)
  (display "SSA procedure ")
  (write (ssa-proc-params ssa))
  (newline)
  (for-each-block
   (lambda (b block)
     (display "block ") (display b) (display " ")
     (display (or (ssa-block-label block) "<entry>"))
     (display "  preds ") (write (ssa-block-preds block))
     (display "  succs ") (write (ssa-block-succs block))
     (newline)
     (for-each (lambda (phi)
                 (display "    ") (write (phi-dst phi))
                 (display " = phi ") (write (vector->list (phi-args phi)))
                 (newline))
               (ssa-block-phis block))
     (for-each (lambda (instr)
                 (display "    ") (write instr) (newline))
               (ssa-block-instrs block)))
   (ssa-proc-blocks ssa)))

)) ; end define-library
