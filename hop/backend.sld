(define-library (hop backend)
  ;;; Backend: instruction selection, register allocation, and AArch64 emission.
  (export make-machine-block
          machine-block?
          machine-block-label
          machine-block-instructions
          machine-block-successors
          make-machine-procedure
          machine-procedure?
          machine-procedure-name
          machine-procedure-params
          machine-procedure-param-locations
          machine-procedure-blocks
          machine-procedure-homes
          machine-procedure-root-homes
          machine-procedure-frame-slots
          machine-procedure-used-registers
          cfg->allocated-machine-procedure
          emit-aarch64-program
          emit-unit-aarch64-program
          display-cfg
          display-procedure-cfg
          display-machine-procedure)
  (import (scheme base)
          (scheme cxr)
          (scheme write)
          (scheme process-context)
          (hop compat)
          (only (srfi 69) make-hash-table hash-table-set! hash-table-ref
                hash-table-ref/default hash-table-exists?
                hash-table-delete! hash-table-size)
          (hop utils)
          (hop pass tac)
          (hop pass cfg))
  (begin

(define-record-type <machine-block>
  (make-machine-block label instructions successors)
  machine-block?
  (label machine-block-label)
  (instructions machine-block-instructions)
  (successors machine-block-successors))

(define-record-type <machine-procedure>
  (make-machine-procedure name params param-locations blocks homes root-homes frame-slots used-registers)
  machine-procedure?
  (name machine-procedure-name)
  (params machine-procedure-params)
  (param-locations machine-procedure-param-locations)
  (blocks machine-procedure-blocks)
  (homes machine-procedure-homes)
  (root-homes machine-procedure-root-homes)
  (frame-slots machine-procedure-frame-slots)
  (used-registers machine-procedure-used-registers))

;;; ── AArch64 constants ──────────────────────────────────────────────────────

(define aarch64-arg-registers '(x0 x1 x2 x3 x4 x5 x6 x7))
(define aarch64-return-register 'x0)
(define aarch64-callee-saved '(x19 x20 x21 x22 x23 x24 x25 x26 x27 x28))
(define gc-frame-header-bytes 16)

;;; ── Backend utility helpers ────────────────────────────────────────────────

(define (arg-location index)
  (if (< index (length aarch64-arg-registers))
      `(arg-register ,(list-ref aarch64-arg-registers index))
      `(stack-arg ,(- index (length aarch64-arg-registers)))))

(define (make-param-locations params)
  (let loop ((rest params) (index 0) (result '()))
    (if (null? rest)
        (reverse result)
        (loop (cdr rest)
              (+ index 1)
              (cons (list (car rest) (arg-location index)) result)))))

(define (stack-align n)
  (* 16 (quotient (+ n 15) 16)))

(define (call-stack-arg-count instr)
  (case (car instr)
    ((call)
     (max 0 (- (length (cdddr instr)) (length aarch64-arg-registers))))
    ((call-known)
     (max 0 (- (length (cdddr instr)) (length aarch64-arg-registers))))
    ((tail-call)
     (max 0 (- (length (cddr instr)) (length aarch64-arg-registers))))
    ((tail-call-known)
     (max 0 (- (length (cddr instr)) (length aarch64-arg-registers))))
    ;; call-apply/tail-call-apply always carry exactly 3 fixed operands
    ;; (closure, leading-list, list-arg), well under the register budget --
    ;; no stack args needed regardless of how many leading args or how long
    ;; the spread list is, since both were already consed into ordinary
    ;; list values before the call (see (hop pass tac)). call-callcc and
    ;; tail-call-callcc likewise carry exactly 1 operand (the procedure).
    ((alloc-closure)
     ;; emit-alloc-closure writes captures to the same [sp, #...] outgoing
     ;; area as call argument spilling whenever it takes the general (>3
     ;; captures) path; account for that here so the frame is sized to
     ;; actually cover those writes instead of aliasing the GC frame header
     ;; just above the outgoing-args area. (alloc-closure dst proc-name
     ;; arity captures...) -- captures start after the arity field.
     (let ((count (length (cddddr instr))))
       (if (> count 3) count 0)))
    ((alloc-closure-variadic)
     ;; Always uses the general captures-to-stack path (see
     ;; emit-alloc-closure-variadic), regardless of capture count.
     (length (cddddr instr)))
    (else 0)))

;;; ── Step 1: Instruction Selection ─────────────────────────────────────────

(define (select-machine-instruction instr)
  (define (select-assignment-rhs dst rhs)
    (cond
     ((or (symbol? rhs) (literal-expr? rhs))
      (list `(move ,dst ,rhs)))
     ((and (pair? rhs) (eq? (car rhs) 'primop))
      (case (cadr rhs)
        ((car)  (list `(load-car  ,dst ,(caddr rhs))))
        ((cdr)  (list `(load-cdr  ,dst ,(caddr rhs))))
        ((unsafe-car) (list `(unsafe-load-car ,dst ,(caddr rhs))))
        ((unsafe-cdr) (list `(unsafe-load-cdr ,dst ,(caddr rhs))))
        ((pair?) (list `(is-pair   ,dst ,(caddr rhs))))
        ((null?) (list `(is-null   ,dst ,(caddr rhs))))
        ((symbol?) (list `(is-symbol ,dst ,(caddr rhs))))
        ((make-vector) (list `(alloc-vector ,dst ,(caddr rhs) ,(cadddr rhs))))
        ((vector-length) (list `(vector-length ,dst ,(caddr rhs))))
        ((vector-ref) (list `(vector-ref ,dst ,(caddr rhs) ,(cadddr rhs))))
        ((vector-set!) (list `(vector-set! ,dst ,(caddr rhs) ,(cadddr rhs) ,(cadddr (cdr rhs)))))
        ((vector?) (list `(is-vector ,dst ,(caddr rhs))))
        ((cons) (list `(alloc-pair ,dst ,(caddr rhs) ,(cadddr rhs))))
        ((safe-+ safe-- safe-* safe-= safe-< safe->)
         (list `(safe-binop ,(cadr rhs) ,dst ,(caddr rhs) ,(cadddr rhs))))
        (else   (list `(binop ,(cadr rhs) ,dst ,@(cddr rhs))))))
     ((and (pair? rhs) (eq? (car rhs) 'cons))
      (error "cons in instruction selection: should have been canonicalized" rhs))
     ((and (pair? rhs) (eq? (car rhs) 'box))
      (list `(alloc-box ,dst ,(cadr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'unbox))
      (list `(load-box ,dst ,(cadr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'car))
      (error "car in instruction selection: should have been canonicalized" rhs))
     ((and (pair? rhs) (eq? (car rhs) 'cdr))
      (error "cdr in instruction selection: should have been canonicalized" rhs))
     ((and (pair? rhs) (eq? (car rhs) 'pair?))
      (error "pair? in instruction selection: should have been canonicalized" rhs))
     ((and (pair? rhs) (eq? (car rhs) 'null?))
      (error "null? in instruction selection: should have been canonicalized" rhs))
     ((and (pair? rhs) (eq? (car rhs) 'global))
      (list `(load-global ,dst ,(cadr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'closure-env-ref))
      (list `(load-closure-env ,dst ,(cadr rhs) ,(caddr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'make-closure))
      (list `(alloc-closure ,dst ,@(cdr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'make-variadic-closure))
      (list `(alloc-closure-variadic ,dst ,@(cdr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'closure-call))
      (list `(call ,dst ,@(cdr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'direct-call))
      (list `(call-known ,dst ,@(cdr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'apply-call))
      (list `(call-apply ,dst ,@(cdr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'callcc-call))
      (list `(call-callcc ,dst ,@(cdr rhs))))
     (else
      (error "Unknown assignment rhs during instruction selection" rhs))))
  (cond
   ((not (pair? instr))
    (error "Invalid TAC instruction for instruction selection" instr))
   ((eq? (car instr) 'label) '())
   ((eq? (car instr) 'assign)
    (let ((dst (cadr instr))
          (rhs (caddr instr)))
      (select-assignment-rhs dst rhs)))
   ((eq? (car instr) 'if)
    (list `(branch-if ,(cadr instr) ,(caddr instr) ,(cadddr instr))))
   ((eq? (car instr) 'goto)
    (list `(jump ,(cadr instr))))
   ((eq? (car instr) 'return)
    (list `(ret ,(cadr instr))))
   ((eq? (car instr) 'tail-call)
    (list `(tail-call ,@(cdr instr))))
   ((eq? (car instr) 'direct-tail-call)
    (list `(tail-call-known ,@(cdr instr))))
   ((eq? (car instr) 'tail-apply-call)
    (list `(tail-call-apply ,@(cdr instr))))
   ((eq? (car instr) 'tail-callcc-call)
    (list `(tail-call-callcc ,@(cdr instr))))
   ((eq? (car instr) 'set-box!)
    (list `(store-box ,(cadr instr) ,(caddr instr))))
   ((eq? (car instr) 'set-global!)
    (list `(store-global ,(cadr instr) ,(caddr instr))))
   (else
    (error "Unknown TAC instruction in instruction selection" instr))))

(define (select-machine-block block initial-instrs)
  (make-machine-block
   (basic-block-label block)
   (append initial-instrs
           (append-map select-machine-instruction
                       (basic-block-instructions block)))
   (basic-block-successors block)))

;; True if some block jumps to block 0.
(define (entry-is-jump-target? blocks)
  (not (all (lambda (block) (not (memv 0 (machine-block-successors block))))
            blocks)))

(define (param-move? instr)
  (eq? (car instr) 'move-in))

;; The entry block starts with a move-in for each incoming param. When a loop
;; jumps back to the entry block (a self tail call or a letrec cluster), those
;; moves are not run again (emit-machine-block places the prologue before the
;; block's label), but liveness would still see every param as redefined at
;; the top of the loop. A param the loop never reassigns would then look dead
;; on the back edge, and its register could be reused. So when block 0 is a
;; jump target, the param moves go in their own block ahead of it.
(define (split-looping-entry-block blocks)
  (define (shift-successors block)
    (make-machine-block (machine-block-label block)
                        (machine-block-instructions block)
                        (map (lambda (index) (+ index 1))
                             (machine-block-successors block))))
  (if (entry-is-jump-target? blocks)
      (let* ((entry (car blocks))
             (instrs (machine-block-instructions entry))
             (param-moves (let take ((rest instrs))
                            (if (and (pair? rest) (param-move? (car rest)))
                                (cons (car rest) (take (cdr rest)))
                                '()))))
        (cons (make-machine-block #f param-moves '(1))
              (map shift-successors
                   (cons (make-machine-block (machine-block-label entry)
                                             (list-tail instrs (length param-moves))
                                             (machine-block-successors entry))
                         (cdr blocks)))))
      blocks))

(define (select-machine-procedure name params cfg)
  (let ((param-locations (make-param-locations (params-names params))))
    (let loop ((blocks cfg)
               (first? #t)
               (result '()))
      (if (null? blocks)
          (make-machine-procedure name
                                  params
                                  param-locations
                                  (split-looping-entry-block (reverse result))
                                  '()
                                  '()
                                  0
                                  '())
          (let* ((initial-instrs
                  (if first?
                      (map (lambda (binding)
                             `(move-in ,(car binding) ,(cadr binding)))
                           param-locations)
                      '()))
                 (selected-block
                  (select-machine-block (car blocks) initial-instrs)))
            (loop (cdr blocks)
                  #f
                  (cons selected-block result)))))))

;;; ── Step 2: Liveness Analysis ──────────────────────────────────────────────

(define (machine-instr-uses instr)
  (case (car instr)
    ((move-in) '())
    ((move) (if (symbol? (caddr instr)) (list (caddr instr)) '()))
    ((binop safe-binop)
     (append (if (symbol? (cadddr instr)) (list (cadddr instr)) '())
             (if (symbol? (car (cddddr instr))) (list (car (cddddr instr))) '())))
    ((alloc-box load-box load-car load-cdr is-pair is-null is-symbol is-vector vector-length load-closure-env)
     (if (symbol? (caddr instr)) (list (caddr instr)) '()))
    ((unsafe-load-car unsafe-load-cdr)
     (if (symbol? (caddr instr)) (list (caddr instr)) '()))
    ((load-global) '())
    ((alloc-pair alloc-vector vector-ref)
     (append (if (symbol? (caddr instr)) (list (caddr instr)) '())
             (if (symbol? (cadddr instr)) (list (cadddr instr)) '())))
    ((vector-set!)
     (append (if (symbol? (caddr instr)) (list (caddr instr)) '())
             (if (symbol? (cadddr instr)) (list (cadddr instr)) '())
             (if (symbol? (cadddr (cdr instr))) (list (cadddr (cdr instr))) '())))
    ((store-box)
     (append (if (symbol? (cadr instr)) (list (cadr instr)) '())
             (if (symbol? (caddr instr)) (list (caddr instr)) '())))
    ((store-global)
     (if (symbol? (caddr instr)) (list (caddr instr)) '()))
    ((alloc-closure)
     ;; (alloc-closure dst proc-name arity captures...) -- proc-name and
     ;; arity are literal/label operands, not registers; the generic symbol
     ;; filter below already skips them (see the alloc-closure-variadic
     ;; comment right below for the identical pattern).
     (let loop ((rest (cddddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((alloc-closure-variadic)
     ;; (alloc-closure-variadic dst proc-name k captures...) -- proc-name and
     ;; k are literal/label operands, not registers; the generic symbol
     ;; filter below already skips them.
     (let loop ((rest (cddddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((call)
     (let ((closure (caddr instr))
           (args (cdddr instr)))
       (append (if (symbol? closure) (list closure) '())
               (let loop ((rest args) (result '()))
                 (if (null? rest)
                     (reverse result)
                     (loop (cdr rest)
                           (if (symbol? (car rest))
                               (cons (car rest) result)
                               result)))))))
    ((call-known)
     (let loop ((rest (cdddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((tail-call)
     (let ((closure (cadr instr))
           (args (cddr instr)))
       (append (if (symbol? closure) (list closure) '())
               (let loop ((rest args) (result '()))
                 (if (null? rest)
                     (reverse result)
                     (loop (cdr rest)
                           (if (symbol? (car rest))
                               (cons (car rest) result)
                               result)))))))
    ((tail-call-known)
     (let loop ((rest (cddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((call-apply call-callcc)
     ;; (call-apply dst closure leading-list list-arg) -- all three operands
     ;; are used, dst is a def handled separately below; (call-callcc dst
     ;; proc) has the same shape with a single operand.
     (let loop ((rest (cddr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((tail-call-apply tail-call-callcc)
     ;; (tail-call-apply closure leading-list list-arg) / (tail-call-callcc proc)
     (let loop ((rest (cdr instr)) (result '()))
       (if (null? rest)
           (reverse result)
           (loop (cdr rest)
                 (if (symbol? (car rest))
                     (cons (car rest) result)
                     result)))))
    ((branch-if ret)
     (if (symbol? (cadr instr)) (list (cadr instr)) '()))
    ((cmp-branch)
     (append (if (symbol? (caddr instr)) (list (caddr instr)) '())
             (if (symbol? (cadddr instr)) (list (cadddr instr)) '())))
    ((jump) '())
    (else (error "Unknown machine instruction in use analysis" instr))))

(define (machine-instr-defs instr)
  (case (car instr)
    ((move-in move alloc-pair alloc-vector alloc-box load-box load-car load-cdr
             unsafe-load-car unsafe-load-cdr is-pair is-null is-symbol is-vector
             vector-length vector-ref vector-set!
             load-closure-env load-global alloc-closure alloc-closure-variadic
             call call-known call-apply call-callcc)
      (list (cadr instr)))
    ((binop safe-binop)
      (list (caddr instr)))
    ((store-box store-global branch-if cmp-branch jump ret tail-call tail-call-known tail-call-apply
      tail-call-callcc) '())
    (else (error "Unknown machine instruction in def analysis" instr))))

(define (machine-instr-bias-source instr)
  (case (car instr)
    ((move)
     (if (symbol? (caddr instr))
         (caddr instr)
         #f))
    (else #f)))

;;; Liveness and allocation work on small integers. build-numbering gives every
;;; variable an index, and a set of variables is an exact integer with bit i
;;; set when variable i is a member.

(define-record-type <numbering>
  (make-numbering ids names)
  numbering?
  (ids numbering-ids)       ; hash table: variable -> index
  (names numbering-names))  ; vector: index -> variable

(define (build-numbering blocks)
  (let ((ids (make-hash-table eq?))
        (order '())
        (count 0))
    (define (note! var)
      (unless (hash-table-exists? ids var)
        (hash-table-set! ids var count)
        (set! order (cons var order))
        (set! count (+ count 1))))
    (for-each
     (lambda (block)
       (for-each (lambda (instr)
                   (for-each note! (machine-instr-uses instr))
                   (for-each note! (machine-instr-defs instr)))
                 (machine-block-instructions block)))
     blocks)
    (make-numbering ids (list->vector (reverse order)))))

(define (bitset-empty) 0)
(define (bitset-singleton id) (arithmetic-shift 1 id))
(define (bitset-union a b) (bitwise-ior a b))
(define (bitset-difference a b) (bitwise-and a (bitwise-not b)))

;; Member indices in ascending order.
(define (bitset-ids set)
  (let loop ((rest set) (id 0) (result '()))
    (if (zero? rest)
        (reverse result)
        (loop (arithmetic-shift rest -1)
              (+ id 1)
              (if (odd? rest) (cons id result) result)))))

(define (ids->bitset ids)
  (let loop ((rest ids) (set 0))
    (if (null? rest)
        set
        (loop (cdr rest) (bitset-union set (bitset-singleton (car rest)))))))

(define (bitset-vars numbering set)
  (map (lambda (id) (vector-ref (numbering-names numbering) id))
       (bitset-ids set)))

;; What an instruction reads and writes, as sorted-by-first-mention index
;; lists and as sets. Computed once per instruction.
(define-record-type <instr-info>
  (make-instr-info instr use-ids def-ids use-set def-set)
  instr-info?
  (instr instr-info-instr)
  (use-ids instr-info-use-ids)
  (def-ids instr-info-def-ids)
  (use-set instr-info-use-set)
  (def-set instr-info-def-set))

(define (analyze-instruction numbering instr)
  (define (ids-of vars)
    (map (lambda (var) (hash-table-ref (numbering-ids numbering) var)) vars))
  (let ((use-ids (ids-of (machine-instr-uses instr)))
        (def-ids (ids-of (machine-instr-defs instr))))
    (make-instr-info instr use-ids def-ids
                     (ids->bitset use-ids) (ids->bitset def-ids))))

(define (analyze-block numbering block)
  (map (lambda (instr) (analyze-instruction numbering instr))
       (machine-block-instructions block)))

;; Upward-exposed uses and definitions of one block.
(define (block-use-and-def infos)
  (let loop ((rest infos) (defs 0) (uses 0))
    (if (null? rest)
        (values uses defs)
        (let ((info (car rest)))
          (loop (cdr rest)
                (bitset-union defs (instr-info-def-set info))
                (bitset-union uses
                              (bitset-difference (instr-info-use-set info)
                                                 defs)))))))

(define (compute-liveness blocks block-infos)
  (let* ((count (length blocks))
         (successor-vec (list->vector (map machine-block-successors blocks)))
         (use-vec (make-slots count 0))
         (def-vec (make-slots count 0))
         (in-vec (make-slots count 0))
         (out-vec (make-slots count 0)))
    (let fill ((rest block-infos) (i 0))
      (unless (null? rest)
        (let-values (((uses defs) (block-use-and-def (car rest))))
          (vector-set! use-vec i uses)
          (vector-set! def-vec i defs))
        (fill (cdr rest) (+ i 1))))
    (let loop ()
      (let ((changed #f))
        (do ((i (- count 1) (- i 1)))
            ((< i 0))
          (let* ((new-out
                  (let succ-loop ((rest (vector-ref successor-vec i)) (result 0))
                    (if (null? rest)
                        result
                        (succ-loop (cdr rest)
                                   (bitset-union result
                                                 (vector-ref in-vec (car rest)))))))
                 (new-in
                  (bitset-union (vector-ref use-vec i)
                                (bitset-difference new-out (vector-ref def-vec i)))))
            (unless (= new-out (vector-ref out-vec i))
              (vector-set! out-vec i new-out)
              (set! changed #t))
            (unless (= new-in (vector-ref in-vec i))
              (vector-set! in-vec i new-in)
              (set! changed #t))))
        (if changed
            (loop)
            (values in-vec out-vec))))))

;; For each block, the set live before each of its instructions.
(define (compute-instruction-live-before block-infos out-vec)
  (let block-loop ((remaining block-infos) (index 0) (result '()))
    (if (null? remaining)
        (reverse result)
        (let instr-loop ((rest (reverse (car remaining)))
                         (live-after (vector-ref out-vec index))
                         (live-befores '()))
          (if (null? rest)
              (block-loop (cdr remaining) (+ index 1) (cons live-befores result))
              (let* ((info (car rest))
                     (live-before
                      (bitset-union (instr-info-use-set info)
                                    (bitset-difference live-after
                                                       (instr-info-def-set info)))))
                (instr-loop (cdr rest)
                            live-before
                            (cons live-before live-befores))))))))

;;; ── Live intervals ─────────────────────────────────────────────────────────

(define (interval-start interval) (cadr interval))
(define (interval-end interval) (caddr interval))

;; One (var start end ranges) per variable. ranges is the ascending list of
;; (first . last) point ranges where the variable occupies its home: points
;; where it is live before or after the instruction, or defined by it. The gaps
;; between ranges are lifetime holes. start and end bound the whole thing.
;; Points number instructions consecutively across blocks, in block order.
(define (collect-intervals numbering block-infos out-vec instruction-live-before)
  (let* ((names (numbering-names numbering))
         (count (vector-length names))
         (open-starts (make-slots count #f))
         (open-lasts (make-slots count #f))
         (closed (make-slots count '())))
    (define (close! id)
      (when (vector-ref open-starts id)
        (vector-set! closed id
                     (cons (cons (vector-ref open-starts id)
                                 (vector-ref open-lasts id))
                           (vector-ref closed id)))
        (vector-set! open-starts id #f)))
    (define (touch! id point)
      (cond
        ((and (vector-ref open-starts id)
              (= (vector-ref open-lasts id) point))
         #f)
        ((and (vector-ref open-starts id)
              (= (+ (vector-ref open-lasts id) 1) point))
         (vector-set! open-lasts id point))
        (else
         (close! id)
         (vector-set! open-starts id point)
         (vector-set! open-lasts id point))))
    (let loop-blocks ((remaining block-infos)
                      (live-before-lists instruction-live-before)
                      (index 0)
                      (point 0))
      (unless (null? remaining)
        (let loop-instrs ((rest (car remaining))
                          (befores (car live-before-lists))
                          (next-point point))
          (if (null? rest)
              (loop-blocks (cdr remaining) (cdr live-before-lists)
                           (+ index 1) next-point)
              (let* ((live-after (if (null? (cdr befores))
                                     (vector-ref out-vec index)
                                     (cadr befores)))
                     (occupied (bitset-union
                                (bitset-union (car befores) live-after)
                                (instr-info-def-set (car rest)))))
                (for-each (lambda (id) (touch! id next-point))
                          (bitset-ids occupied))
                (loop-instrs (cdr rest) (cdr befores) (+ next-point 1)))))))
    (let loop ((id (- count 1)) (result '()))
      (if (< id 0)
          result
          (begin
            (close! id)
            (let ((ranges (reverse (vector-ref closed id))))
              (loop (- id 1)
                    (if (null? ranges)
                        result
                        (cons (list (vector-ref names id)
                                    (car (car ranges))
                                    (cdr (car (reverse ranges)))
                                    ranges)
                              result)))))))))

;; Stable, so intervals starting together keep their numbering order.
(define (sort-intervals-by-start intervals)
  (sort intervals
        (lambda (a b) (< (interval-start a) (interval-start b)))))

;; Maps a variable to the variable it was last copied from.
(define (collect-move-biases blocks)
  (let ((biases (make-hash-table eq?)))
    (for-each
     (lambda (block)
       (for-each
        (lambda (instr)
          (let ((bias-source (machine-instr-bias-source instr))
                (defs (machine-instr-defs instr)))
            (when (and bias-source (pair? defs))
              (hash-table-set! biases (car defs) bias-source))))
        (machine-block-instructions block)))
     blocks)
    biases))

;;; ── Copy coalescing ────────────────────────────────────────────────────────
;;; Runs before allocation. A (move dst src) between two variables disappears
;;; when both can share one name, which happens when they never need different
;;; values at the same time. SSA destruction leaves many such copies (phi
;;; moves), and the allocator's one-variable hint only catches a few.

;; Briggs threshold: a neighbor blocks a register once it has this many.
(define coalesce-register-count (length aarch64-callee-saved))

;; (dst . src) when instr copies one variable to another.
(define (copy-pair instr)
  (and (eq? (car instr) 'move)
       (symbol? (cadr instr))
       (symbol? (caddr instr))
       (not (eq? (cadr instr) (caddr instr)))
       (cons (cadr instr) (caddr instr))))

;; adj[v] is the set of variables that cannot share a name with v: whatever is
;; live just after an instruction that defines v. A copy's source is exempt
;; there, since after the copy it holds the same value.
(define (build-interference numbering blocks block-infos in-vec out-vec)
  (let* ((count (vector-length (numbering-names numbering)))
         (adj (make-slots count 0)))
    (define (add-edge! a b)
      (unless (= a b)
        (vector-set! adj a (bitset-union (vector-ref adj a) (bitset-singleton b)))
        (vector-set! adj b (bitset-union (vector-ref adj b) (bitset-singleton a)))))
    (define (add-clique! set)
      (let ((ids (bitset-ids set)))
        (for-each (lambda (a) (for-each (lambda (b) (add-edge! a b)) ids)) ids)))
    ;; Whatever is live on entry has no defining instruction to record this.
    (unless (null? blocks)
      (add-clique! (vector-ref in-vec 0)))
    (let block-loop ((remaining block-infos) (index 0))
      (unless (null? remaining)
        (let instr-loop ((rest (reverse (car remaining)))
                         (live-after (vector-ref out-vec index)))
          (if (null? rest)
              (block-loop (cdr remaining) (+ index 1))
              (let* ((info (car rest))
                     (copy (copy-pair (instr-info-instr info)))
                     (others (if copy
                                 (bitset-difference
                                  live-after
                                  (bitset-singleton
                                   (hash-table-ref (numbering-ids numbering)
                                                   (cdr copy))))
                                 live-after))
                     (other-ids (bitset-ids others)))
                (for-each (lambda (d)
                            (for-each (lambda (v) (add-edge! d v)) other-ids))
                          (instr-info-def-ids info))
                (instr-loop (cdr rest)
                            (bitset-union (instr-info-use-set info)
                                          (bitset-difference
                                           live-after
                                           (instr-info-def-set info)))))))))
    adj))

;; Number of loops around each block, taking every jump to an earlier or
;; equal block index as a back edge that covers the blocks in between.
(define (block-loop-depths blocks)
  (let* ((count (length blocks))
         (depths (make-slots count 0)))
    (let loop ((rest blocks) (index 0))
      (unless (null? rest)
        (for-each
         (lambda (target)
           (when (<= target index)
             (do ((i target (+ i 1)))
                 ((> i index))
               (vector-set! depths i (+ 1 (vector-ref depths i))))))
         (machine-block-successors (car rest)))
        (loop (cdr rest) (+ index 1))))
    depths))

(define (rename-block-variables block renames)
  (make-machine-block
   (machine-block-label block)
   (append-map
    (lambda (instr)
      (let ((renamed (rewrite-machine-instruction instr renames)))
        (if (and (eq? (car renamed) 'move)
                 (equal? (cadr renamed) (caddr renamed)))
            '()
            (list renamed))))
    (machine-block-instructions block))
   (machine-block-successors block)))

(define (coalesce-copies blocks)
  (let* ((numbering (build-numbering blocks))
         (ids (numbering-ids numbering))
         (names (numbering-names numbering))
         (count (vector-length names))
         (block-infos (map (lambda (block) (analyze-block numbering block))
                           blocks))
         (depths (block-loop-depths blocks)))
    (let-values (((in-vec out-vec) (compute-liveness blocks block-infos)))
      (let* ((adj (build-interference numbering blocks block-infos
                                      in-vec out-vec))
             (parent (make-slots count 0))
             (members (make-slots count 0))
             (merged? #f))
        (do ((i 0 (+ i 1))) ((= i count))
          (vector-set! parent i i)
          (vector-set! members i (bitset-singleton i)))
        (define (find id)
          (let ((up (vector-ref parent id)))
            (if (= up id)
                id
                (let ((root (find up)))
                  (vector-set! parent id root)
                  root))))
        ;; Classes adjacent to class a, as a set of class representatives.
        (define (neighbor-classes a)
          (ids->bitset (map find (bitset-ids (vector-ref adj a)))))
        (define (interferes? a b)
          (not (zero? (bitwise-and (vector-ref adj a) (vector-ref members b)))))
        ;; Briggs: merging is safe when few neighbors have enough neighbors of
        ;; their own to block a register, since the rest can always be colored.
        (define (safe-to-merge? a b)
          (let* ((a-neighbors (neighbor-classes a))
                 (b-neighbors (neighbor-classes b))
                 (both (bitwise-and a-neighbors b-neighbors))
                 (significant
                  (let loop ((rest (bitset-ids (bitset-union a-neighbors
                                                             b-neighbors)))
                             (total 0))
                    (if (null? rest)
                        total
                        (let* ((n (car rest))
                               (degree
                                (- (length (bitset-ids (neighbor-classes n)))
                                   (if (zero? (bitwise-and both
                                                           (bitset-singleton n)))
                                       0
                                       1))))
                          (loop (cdr rest)
                                (if (>= degree coalesce-register-count)
                                    (+ total 1)
                                    total)))))))
            (< significant coalesce-register-count)))
        (define (merge! a b)
          (vector-set! parent b a)
          (vector-set! members a (bitset-union (vector-ref members a)
                                               (vector-ref members b)))
          (vector-set! adj a (bitset-union (vector-ref adj a)
                                           (vector-ref adj b)))
          (set! merged? #t))
        ;; Copies in deeper loops first; stable within a depth.
        (let ((copies
               (let block-loop ((remaining blocks) (index 0) (result '()))
                 (if (null? remaining)
                     (reverse result)
                     (block-loop
                      (cdr remaining)
                      (+ index 1)
                      (let instr-loop ((rest (machine-block-instructions
                                              (car remaining)))
                                       (acc result))
                        (if (null? rest)
                            acc
                            (let ((copy (copy-pair (car rest))))
                              (instr-loop
                               (cdr rest)
                               (if copy
                                   (cons (list (vector-ref depths index)
                                               (hash-table-ref ids (car copy))
                                               (hash-table-ref ids (cdr copy)))
                                         acc)
                                   acc))))))))))
          (for-each
           (lambda (copy)
             (let ((a (find (cadr copy)))
                   (b (find (caddr copy))))
               (unless (or (= a b)
                           (interferes? a b)
                           (not (safe-to-merge? a b)))
                 (merge! a b))))
           (sort copies (lambda (x y) (> (car x) (car y))))))
        (if (not merged?)
            blocks
            (let ((renames (make-hash-table eq?)))
              (do ((i 0 (+ i 1))) ((= i count))
                (unless (= (find i) i)
                  (hash-table-set! renames
                                   (vector-ref names i)
                                   (vector-ref names (find i)))))
              (map (lambda (block) (rename-block-variables block renames))
                   blocks)))))))

;;; ── Linear-scan allocation ─────────────────────────────────────────────────

(define (lookup-bias biases var)
  (hash-table-ref/default biases var #f))

(define (preferred-register-for var home-table biases)
  (let ((preferred-var (lookup-bias biases var)))
    (if preferred-var
        (let ((preferred-home (lookup-home home-table preferred-var)))
          (if (and (pair? preferred-home) (eq? (car preferred-home) 'register))
              (cadr preferred-home)
              #f))
        #f)))

;; True when two ascending range lists share a point.
(define (ranges-intersect? a b)
  (cond
    ((or (null? a) (null? b)) #f)
    ((< (cdar a) (caar b)) (ranges-intersect? (cdr a) b))
    ((< (cdar b) (caar a)) (ranges-intersect? a (cdr b)))
    (else #t)))

;; The ranges without their final point.
(define (ranges-without-last-point ranges)
  (let loop ((rest ranges))
    (cond
      ((null? (cdr rest))
       (if (= (caar rest) (cdar rest))
           '()
           (list (cons (caar rest) (- (cdar rest) 1)))))
      (else (cons (car rest) (loop (cdr rest)))))))

;; Fills home-table (variable -> home) and returns the same bindings as an
;; alist, newest first, together with the number of stack slots used.
;;
;; Linear scan over intervals with lifetime holes. A variable keeps one home
;; for its whole life, but shares a register with any variable whose ranges
;; fit in its holes. assigned maps each register to the intervals placed in
;; it that have not yet ended; since intervals are taken in order of start,
;; one that has ended can never conflict again.
(define (linear-scan-allocate intervals biases home-table)
  (let ((assigned (make-hash-table eq?)))
    (for-each (lambda (register) (hash-table-set! assigned register '()))
              aarch64-callee-saved)
    (let loop ((remaining (sort-intervals-by-start intervals))
               (homes '())
               (next-slot 0))
      (define (assign! var home)
        (hash-table-set! home-table var home)
        (cons (cons var home) homes))
      (if (null? remaining)
          (values homes next-slot)
          (let* ((current (car remaining))
                 (current-var (car current))
                 (start (interval-start current))
                 (current-ranges (cadddr current))
                 (preferred-var (lookup-bias biases current-var))
                 (preferred-register
                  (preferred-register-for current-var home-table biases)))
            (for-each
             (lambda (register)
               (hash-table-set!
                assigned register
                (filter (lambda (entry) (>= (interval-end entry) start))
                        (hash-table-ref assigned register))))
             aarch64-callee-saved)
            ;; A copy's destination may take over its source's register when
            ;; the source dies at the copy, so the source's last point is
            ;; ignored.
            (let ((free?
                   (lambda (register)
                     (all (lambda (entry)
                            (not (ranges-intersect?
                                  (if (and preferred-var
                                           (eq? (car entry) preferred-var)
                                           (= (interval-end entry) start))
                                      (ranges-without-last-point (cadddr entry))
                                      (cadddr entry))
                                  current-ranges)))
                          (hash-table-ref assigned register)))))
              (let ((register
                     (if (and preferred-register (free? preferred-register))
                         preferred-register
                         (let first-free ((rest aarch64-callee-saved))
                           (cond ((null? rest) #f)
                                 ((free? (car rest)) (car rest))
                                 (else (first-free (cdr rest))))))))
                (if register
                    (begin
                      (hash-table-set!
                       assigned register
                       (cons current (hash-table-ref assigned register)))
                      (loop (cdr remaining)
                            (assign! current-var `(register ,register))
                            next-slot))
                    (loop (cdr remaining)
                          (assign! current-var `(stack-slot ,next-slot))
                          (+ next-slot 1))))))))))

(define (allocate-root-homes homes next-slot)
  (let loop ((rest homes) (slot next-slot) (result '()))
    (if (null? rest)
        (values result slot)
        (let ((var (caar rest))
              (home (cdar rest)))
          (if (and (pair? home) (eq? (car home) 'register))
              (loop (cdr rest)
                    (+ slot 1)
                    (cons (cons var `(stack-slot ,slot)) result))
              (loop (cdr rest) slot result))))))

(define (alist->home-table alist)
  (let ((table (make-hash-table eq?)))
    (for-each (lambda (binding) (hash-table-set! table (car binding) (cdr binding)))
              alist)
    table))

(define (lookup-home home-table operand)
  (if (symbol? operand)
      (hash-table-ref/default home-table operand operand)
      operand))

(define (lookup-root-home root-table var)
  (hash-table-ref/default root-table var #f))

;;; ── Home rewriting ─────────────────────────────────────────────────────────

(define (rewrite-machine-instruction instr homes)
  (case (car instr)
    ((move-in)
     `(move-in ,(lookup-home homes (cadr instr)) ,(caddr instr)))
    ((move)
     `(move ,(lookup-home homes (cadr instr))
            ,(lookup-home homes (caddr instr))))
    ((binop)
     `(binop ,(cadr instr)
             ,(lookup-home homes (caddr instr))
             ,(lookup-home homes (cadddr instr))
             ,(lookup-home homes (car (cddddr instr)))))
    ((safe-binop)
     `(safe-binop ,(cadr instr)
                  ,(lookup-home homes (caddr instr))
                  ,(lookup-home homes (cadddr instr))
                  ,(lookup-home homes (car (cddddr instr)))))
    ((alloc-box)
     `(alloc-box ,(lookup-home homes (cadr instr))
                 ,(lookup-home homes (caddr instr))))
    ((alloc-pair)
     `(alloc-pair ,(lookup-home homes (cadr instr))
                  ,(lookup-home homes (caddr instr))
                  ,(lookup-home homes (cadddr instr))))
    ((load-box)
     `(load-box ,(lookup-home homes (cadr instr))
                ,(lookup-home homes (caddr instr))))
    ((load-closure-env)
     `(load-closure-env ,(lookup-home homes (cadr instr))
                        ,(lookup-home homes (caddr instr))
                        ,(cadddr instr)))
    ((load-global)
     `(load-global ,(lookup-home homes (cadr instr))
                   ,(caddr instr)))
    ((load-car)
     `(load-car ,(lookup-home homes (cadr instr))
                ,(lookup-home homes (caddr instr))))
    ((load-cdr)
     `(load-cdr ,(lookup-home homes (cadr instr))
                ,(lookup-home homes (caddr instr))))
    ((unsafe-load-car)
     `(unsafe-load-car ,(lookup-home homes (cadr instr))
                       ,(lookup-home homes (caddr instr))))
    ((unsafe-load-cdr)
     `(unsafe-load-cdr ,(lookup-home homes (cadr instr))
                       ,(lookup-home homes (caddr instr))))
    ((is-pair)
     `(is-pair ,(lookup-home homes (cadr instr))
               ,(lookup-home homes (caddr instr))))
    ((is-null)
     `(is-null ,(lookup-home homes (cadr instr))
               ,(lookup-home homes (caddr instr))))
    ((is-symbol)
     `(is-symbol ,(lookup-home homes (cadr instr))
                 ,(lookup-home homes (caddr instr))))
    ((is-vector)
     `(is-vector ,(lookup-home homes (cadr instr))
                 ,(lookup-home homes (caddr instr))))
    ((alloc-vector)
     `(alloc-vector ,(lookup-home homes (cadr instr))
                    ,(lookup-home homes (caddr instr))
                    ,(lookup-home homes (cadddr instr))))
    ((vector-length)
     `(vector-length ,(lookup-home homes (cadr instr))
                     ,(lookup-home homes (caddr instr))))
    ((vector-ref)
     `(vector-ref ,(lookup-home homes (cadr instr))
                  ,(lookup-home homes (caddr instr))
                  ,(lookup-home homes (cadddr instr))))
    ((vector-set!)
     `(vector-set! ,(lookup-home homes (cadr instr))
                   ,(lookup-home homes (caddr instr))
                   ,(lookup-home homes (cadddr instr))
                   ,(lookup-home homes (cadddr (cdr instr)))))
    ((store-box)
     `(store-box ,(lookup-home homes (cadr instr))
                 ,(lookup-home homes (caddr instr))))
    ((store-global)
     `(store-global ,(cadr instr)
                    ,(lookup-home homes (caddr instr))))
    ((alloc-closure)
     `(alloc-closure ,(lookup-home homes (cadr instr))
                     ,(caddr instr)
                     ,(cadddr instr)
                     ,@(map (lambda (operand) (lookup-home homes operand))
                            (cddddr instr))))
    ((alloc-closure-variadic)
     `(alloc-closure-variadic ,(lookup-home homes (cadr instr))
                              ,(caddr instr)
                              ,(cadddr instr)
                              ,@(map (lambda (operand) (lookup-home homes operand))
                                     (cddddr instr))))
    ((call)
     `(call ,(lookup-home homes (cadr instr))
            ,(lookup-home homes (caddr instr))
            ,@(map (lambda (operand) (lookup-home homes operand))
                   (cdddr instr))))
    ((call-known)
     `(call-known ,(lookup-home homes (cadr instr))
                  ,(caddr instr)
                  ,@(map (lambda (operand) (lookup-home homes operand))
                         (cdddr instr))))
    ((call-apply call-callcc)
     `(,(car instr) ,(lookup-home homes (cadr instr))
                    ,@(map (lambda (operand) (lookup-home homes operand))
                           (cddr instr))))
    ((tail-call)
     `(tail-call ,(lookup-home homes (cadr instr))
                 ,@(map (lambda (operand) (lookup-home homes operand))
                        (cddr instr))))
    ((tail-call-known)
     `(tail-call-known ,(cadr instr)
                       ,@(map (lambda (operand) (lookup-home homes operand))
                              (cddr instr))))
    ((tail-call-apply tail-call-callcc)
     `(,(car instr) ,@(map (lambda (operand) (lookup-home homes operand))
                           (cdr instr))))
    ((branch-if)
     `(branch-if ,(lookup-home homes (cadr instr))
                 ,(caddr instr)
                 ,(cadddr instr)))
    ((cmp-branch)
     `(cmp-branch ,(cadr instr)
                  ,(lookup-home homes (caddr instr))
                  ,(lookup-home homes (cadddr instr))
                  ,@(cddddr instr)))
    ((jump) instr)
    ((ret)
     `(ret ,(lookup-home homes (cadr instr))))
    (else
     (error "Unknown machine instruction during allocation" instr))))

(define (safepoint-machine-instruction? instr)
  ;; tail-call/tail-call-known/tail-call-apply are deliberately excluded:
  ;; the current frame is already popped from the GC frame chain (and its
  ;; values have nothing left to be reloaded into) by the time the actual
  ;; jump executes, so there is nothing in this frame left to sync.
  (memq (car instr)
        '(alloc-box alloc-pair alloc-vector alloc-closure alloc-closure-variadic
          call call-known call-apply call-callcc)))

(define (register-operand? operand)
  (and (pair? operand)
       (memq (car operand) '(register arg-register))))

(define (live-root-syncs live-before homes root-homes)
  (append-map
   (lambda (var)
      (let ((root-home (lookup-root-home root-homes var))
            (home (lookup-home homes var)))
        (if root-home
            (list `(move ,root-home ,home))
            '())))
   live-before))

(define (live-root-reloads live-after def-var homes root-homes)
  (append-map
   (lambda (var)
     (if (eq? var def-var)
         '()
         (let ((root-home (lookup-root-home root-homes var))
               (home (lookup-home homes var)))
           (if (and root-home (register-operand? home))
               (list `(move ,home ,root-home))
               '()))))
   live-after))

(define (instruction->list instr)
  (if (and (pair? instr)
           (eq? (car instr) 'move)
           (equal? (cadr instr) (caddr instr)))
      '()
      (list instr)))

(define (rewrite-machine-instruction-with-safepoint-sync
          instr
          live-before
          live-after
          numbering
          homes
          root-homes)
  (append
   (if (safepoint-machine-instruction? instr)
       (live-root-syncs (bitset-vars numbering live-before) homes root-homes)
       '())
    (instruction->list (rewrite-machine-instruction instr homes))
    (if (safepoint-machine-instruction? instr)
        (live-root-reloads (bitset-vars numbering live-after)
                           (cadr instr) homes root-homes)
        '())))

(define (rewrite-machine-block-instructions
         instrs live-befores numbering homes root-homes)
  (if (null? instrs)
      '()
      (let ((live-after (if (null? (cdr live-befores))
                            (bitset-empty)
                            (cadr live-befores))))
        (append
         (rewrite-machine-instruction-with-safepoint-sync
          (car instrs)
          (car live-befores)
          live-after
          numbering
          homes
          root-homes)
         (rewrite-machine-block-instructions
          (cdr instrs)
          (cdr live-befores)
          numbering
          homes
          root-homes)))))

;;; Debug check (HOP_CHECK_ALLOC=1): after allocation, no two variables that
;;; are live at the same time may share a home, and no instruction's
;;; destination may share a home with a variable that stays live past it
;;; (even if the destination itself is never read). A violation means the
;;; allocator's idea of liveness disagrees with the code's real control flow,
;;; which shows up at run time as a silently wrong value.
(define (check-register-allocation name blocks numbering home-table out-vec
                                   instruction-live-before)
  (define (home-of var)
    (hash-table-ref/default home-table var #f))
  (define (check-no-sharing! block instr live)
    (let loop ((vars live))
      (unless (null? vars)
        (let ((home (home-of (car vars))))
          (for-each (lambda (other)
                      (when (and home (equal? home (home-of other)))
                        (error "register allocation conflict"
                               name (machine-block-label block) instr
                               (car vars) other home)))
                    (cdr vars)))
        (loop (cdr vars)))))
  ;; Liveness treats move-in as an ordinary definition, which is only right if
  ;; the entry block is never re-entered (see split-looping-entry-block).
  (when (and (entry-is-jump-target? blocks)
             (not (all (lambda (instr) (not (param-move? instr)))
                       (machine-block-instructions (car blocks)))))
    (error "entry block with parameter moves is a loop target" name))
  (for-each
   (lambda (block live-befores live-out)
     (for-each
      (lambda (instr live-after)
        (check-no-sharing! block instr
                           (set-union (bitset-vars numbering live-after)
                                      (machine-instr-defs instr))))
      (machine-block-instructions block)
      (if (null? live-befores)
          '()
          (append (cdr live-befores) (list live-out)))))
   blocks
   instruction-live-before
   (vector->list out-vec)))

(define (allocate-machine-procedure proc)
  (let* ((blocks (coalesce-copies (machine-procedure-blocks proc)))
         (numbering (build-numbering blocks))
         (block-infos (map (lambda (block) (analyze-block numbering block))
                           blocks))
         (home-table (make-hash-table eq?)))
    (let-values (((in-vec out-vec) (compute-liveness blocks block-infos)))
      (let* ((instruction-live-before
              (compute-instruction-live-before block-infos out-vec))
             (biases (collect-move-biases blocks)))
        (let-values (((homes next-slot)
                      (linear-scan-allocate
                       (collect-intervals numbering block-infos out-vec
                                          instruction-live-before)
                       biases
                       home-table)))
          (when (equal? (get-environment-variable "HOP_CHECK_ALLOC") "1")
            (check-register-allocation (machine-procedure-name proc) blocks
                                       numbering home-table
                                       out-vec instruction-live-before))
          (let-values (((root-homes frame-slots)
                        (allocate-root-homes homes next-slot)))
            (let* ((root-table (alist->home-table root-homes))
                   (rewritten-blocks
                    (let loop ((remaining-blocks blocks)
                               (remaining-live-before instruction-live-before)
                               (result '()))
                      (if (null? remaining-blocks)
                          (reverse result)
                          (let ((block (car remaining-blocks))
                                (live-befores (car remaining-live-before)))
                            (loop
                             (cdr remaining-blocks)
                             (cdr remaining-live-before)
                             (cons
                              (make-machine-block
                               (machine-block-label block)
                               (rewrite-machine-block-instructions
                                (machine-block-instructions block)
                                live-befores
                                numbering
                                home-table
                                root-table)
                               (machine-block-successors block))
                              result))))))
                   (used-registers
                    (dedupe-symbols
                     (let loop ((rest homes) (result '()))
                       (if (null? rest)
                           result
                           (let ((home (cdar rest)))
                             (loop (cdr rest)
                                   (if (and (pair? home) (eq? (car home) 'register))
                                       (cons (cadr home) result)
                                       result))))))))
              (make-machine-procedure
               (machine-procedure-name proc)
               (machine-procedure-params proc)
               (machine-procedure-param-locations proc)
               rewritten-blocks
               homes
               root-homes
               frame-slots
               used-registers))))))))

(define (max-outgoing-stack-args blocks)
  (let block-loop ((remaining blocks) (best 0))
    (if (null? remaining)
        best
        (let instr-loop ((instrs (machine-block-instructions (car remaining)))
                         (block-best best))
          (if (null? instrs)
              (block-loop (cdr remaining) block-best)
              (instr-loop (cdr instrs)
                          (max block-best
                               (call-stack-arg-count (car instrs)))))))))

(define (stack-size-for proc)
  (stack-align
   (+ gc-frame-header-bytes
      (* 8 (+ (machine-procedure-frame-slots proc)
              (length (machine-procedure-used-registers proc))
              (max-outgoing-stack-args (machine-procedure-blocks proc)))))))

(define (lower-arg-moves operands)
  (let loop ((rest operands) (index 0) (result '()))
    (if (null? rest)
        (reverse result)
        (loop (cdr rest)
              (+ index 1)
              (cons `(move-out ,(arg-location index) ,(car rest))
                    result)))))

;;; ── Step 3: ABI Finalization ───────────────────────────────────────────────

(define (finalize-machine-instruction instr stack-size saved-registers)
  (case (car instr)
    ((move-in)
     (list `(move ,(cadr instr) ,(caddr instr))))
    ((call)
     (let ((dst (cadr instr))
           (closure (caddr instr))
           (args (cdddr instr)))
       (append (lower-arg-moves args)
               (list `(move-out ,(arg-location (length args)) ,closure)
                     `(call-indirect ,(length args))
                     `(move ,dst (arg-register ,aarch64-return-register))))))
    ((call-known)
     (let ((dst (cadr instr))
           (proc-name (caddr instr))
           (args (cdddr instr)))
       (append (lower-arg-moves args)
               (list `(call-label ,proc-name)
                     `(move ,dst (arg-register ,aarch64-return-register))))))
    ((tail-call)
     (let ((closure (cadr instr))
           (args (cddr instr)))
       (append (lower-arg-moves args)
               (list `(move-out ,(arg-location (length args)) ,closure)
                     '(gc-pop-frame)
                     `(restore-callee-saved ,saved-registers)
                     `(deallocate-frame ,stack-size)
                     `(tail-call-indirect ,(length args))))))
    ((tail-call-known)
     (let ((proc-name (cadr instr))
           (args (cddr instr)))
       (append (lower-arg-moves args)
               (list '(gc-pop-frame)
                     `(restore-callee-saved ,saved-registers)
                     `(deallocate-frame ,stack-size)
                     `(tail-call-label ,proc-name)))))
    ;; apply's argument count is a runtime-unknown quantity even when its
    ;; target is statically known (see (hop pass cfa)), so it can never use
    ;; the call-known fast path; it always goes through a single fixed
    ;; runtime entry point with a fixed 3-argument shape (closure,
    ;; leading-args-list, spread-list) -- the leading args and the spread
    ;; list were already consed into ordinary lists in TAC (hop pass tac),
    ;; so no per-arity family of apply helpers, and no variable-arity
    ;; marshaling, is needed here: this lowers exactly like an ordinary
    ;; 3-argument call to a fixed runtime label.
    ((call-apply)
     (let ((dst (cadr instr))
           (args (cddr instr)))
       (append (lower-arg-moves args)
               (list '(call-label hop_apply)
                     `(move ,dst (arg-register ,aarch64-return-register))))))
    ((tail-call-apply)
     (let ((args (cdr instr)))
       (append (lower-arg-moves args)
               (list '(gc-pop-frame)
                     `(restore-callee-saved ,saved-registers)
                     `(deallocate-frame ,stack-size)
                     '(tail-call-label hop_apply)))))
    ;; call/cc is an ordinary 1-argument call to the fixed runtime entry
    ;; point hop_callcc (see runtime.c's "Continuations"). Being a
    ;; safepoint, every live value is already synced to its root slot
    ;; before the call and reloaded after it -- which is exactly what
    ;; makes a later re-entry through the captured continuation (which
    ;; "returns" from this same call again) read correct values.
    ((call-callcc)
     (let ((dst (cadr instr))
           (args (cddr instr)))
       (append (lower-arg-moves args)
               (list '(call-label hop_callcc)
                     `(move ,dst (arg-register ,aarch64-return-register))))))
    ((tail-call-callcc)
     (let ((args (cdr instr)))
       (append (lower-arg-moves args)
               (list '(gc-pop-frame)
                     `(restore-callee-saved ,saved-registers)
                     `(deallocate-frame ,stack-size)
                     '(tail-call-label hop_callcc)))))
    ((ret)
     (list `(move-out (arg-register ,aarch64-return-register) ,(cadr instr))
           '(gc-pop-frame)
           `(restore-callee-saved ,saved-registers)
           `(deallocate-frame ,stack-size)
           '(ret)))
    (else
     (list instr))))

(define (finalize-machine-procedure proc)
  (let* ((saved-registers (machine-procedure-used-registers proc))
         (stack-size (stack-size-for proc))
         (final-blocks
          (let loop ((remaining (machine-procedure-blocks proc))
                     (first? #t)
                     (result '()))
            (if (null? remaining)
                (reverse result)
                (let* ((block (car remaining))
                       (prefix
                        (if first?
                            (list `(allocate-frame ,stack-size)
                                  `(save-callee-saved ,saved-registers)
                                  `(init-frame-slots ,(machine-procedure-frame-slots proc))
                                  `(gc-push-frame ,(machine-procedure-name proc)))
                            '()))
                       (final-instrs
                        (append prefix
                                (append-map
                                 (lambda (instr)
                                   (finalize-machine-instruction
                                    instr
                                    stack-size
                                    saved-registers))
                                 (machine-block-instructions block)))))
                  (loop (cdr remaining)
                        #f
                        (cons (make-machine-block
                               (machine-block-label block)
                               final-instrs
                               (machine-block-successors block))
                              result)))))))
    (make-machine-procedure
     (machine-procedure-name proc)
     (machine-procedure-params proc)
     (machine-procedure-param-locations proc)
     final-blocks
     (machine-procedure-homes proc)
     (machine-procedure-root-homes proc)
     (machine-procedure-frame-slots proc)
     saved-registers)))

;;; ── Peephole: compare-and-branch fusion ───────────────────────────────────
;;
;; A comparison (or null?) whose boolean result feeds only the branch right
;; after it becomes one (cmp-branch op lhs rhs then-label else-label), which
;; emits a cmp and a conditional branch with no boolean materialized. The
;; boolean's only use must be that branch, so dropping its definition is safe.

(define (count-variable-uses blocks)
  (let ((counts (make-hash-table eq?)))
    (for-each
     (lambda (block)
       (for-each
        (lambda (instr)
          (for-each
           (lambda (var)
             (hash-table-set! counts var
                              (+ 1 (hash-table-ref/default counts var 0))))
           (machine-instr-uses instr)))
        (machine-block-instructions block)))
     blocks)
    counts))

(define (fusable-comparison instr)
  ;; (op dst lhs rhs) for an instruction computing a boolean, else #f.
  (case (car instr)
    ((binop)
     (and (memq (cadr instr) '(= < > eq?))
          (list (cadr instr) (caddr instr) (cadddr instr)
                (car (cddddr instr)))))
    ((safe-binop)
     (and (memq (cadr instr) '(safe-= safe-< safe->))
          (list (cadr instr) (caddr instr) (cadddr instr)
                (car (cddddr instr)))))
    ((is-null)
     (list 'eq? (cadr instr) (caddr instr) '()))
    (else #f)))

(define (fuse-block-compare-branches instrs uses)
  (let loop ((rest instrs) (result '()))
    (cond
     ((null? rest) (reverse result))
     ((and (pair? (cdr rest))
           (fusable-comparison (car rest))
           (eq? (car (cadr rest)) 'branch-if))
      (let ((cmp (fusable-comparison (car rest)))
            (branch (cadr rest)))
        (if (and (eq? (cadr cmp) (cadr branch))
                 (= 1 (hash-table-ref/default uses (cadr cmp) 0)))
            (loop (cddr rest)
                  (cons `(cmp-branch ,(car cmp) ,(caddr cmp) ,(cadddr cmp)
                                     ,(caddr branch) ,(cadddr branch))
                        result))
            (loop (cdr rest) (cons (car rest) result)))))
     (else (loop (cdr rest) (cons (car rest) result))))))

(define (fuse-compare-branches proc)
  (let ((uses (count-variable-uses (machine-procedure-blocks proc))))
    (make-machine-procedure
     (machine-procedure-name proc)
     (machine-procedure-params proc)
     (machine-procedure-param-locations proc)
     (map (lambda (block)
            (make-machine-block
             (machine-block-label block)
             (fuse-block-compare-branches (machine-block-instructions block)
                                          uses)
             (machine-block-successors block)))
          (machine-procedure-blocks proc))
     (machine-procedure-homes proc)
     (machine-procedure-root-homes proc)
     (machine-procedure-frame-slots proc)
     (machine-procedure-used-registers proc))))

;;; ── Peephole: redundant moves after allocation ─────────────────────────────

;; (move a b) immediately followed by (move b a) leaves both unchanged, so
;; the second is dropped. Allocation already removes (move a a).
(define (move-like? instr)
  (memq (car instr) '(move move-out)))

(define (stack-arg-operand? operand)
  (and (pair? operand) (eq? (car operand) 'stack-arg)))

(define (drop-redundant-moves instrs)
  (let loop ((rest instrs) (result '()))
    (cond
     ((null? rest) (reverse result))
     ((and (pair? result)
           (move-like? (car rest))
           (move-like? (car result))
           (equal? (cadr (car rest)) (caddr (car result)))
           (equal? (caddr (car rest)) (cadr (car result)))
           ;; a stack-arg is read from the incoming area but written to the
           ;; outgoing one, so the pair is not a round trip
           (not (stack-arg-operand? (cadr (car rest))))
           (not (stack-arg-operand? (caddr (car rest)))))
      (loop (cdr rest) result))
     (else (loop (cdr rest) (cons (car rest) result))))))

;;; ── Peephole: jump-only blocks ─────────────────────────────────────────────
;;
;; A block holding nothing but (jump L) is a trampoline: every branch to it
;; goes straight to L instead, and the block is removed. A chain of
;; trampolines collapses to its final target. The entry block, an unlabeled
;; block, a trampoline cycle (L: jump L), and a block the previous one falls
;; into are all left alone.

(define (terminator-instruction? instr)
  (memq (car instr)
        '(jump branch-if cmp-branch ret tail-call-indirect tail-call-label)))

(define (jump-only-target block)
  (let ((instrs (machine-block-instructions block)))
    (and (machine-block-label block)
         (pair? instrs)
         (null? (cdr instrs))
         (eq? (car (car instrs)) 'jump)
         (cadr (car instrs)))))

(define (ends-in-terminator? block)
  (let ((instrs (machine-block-instructions block)))
    (and (pair? instrs)
         (terminator-instruction? (list-ref instrs (- (length instrs) 1))))))

(define (remove-jump-only-blocks blocks)
  (let* ((vec (list->vector blocks))
         (count (vector-length vec))
         (forward (make-hash-table eq?)))
    (define (follow label)
      ;; Final label after the trampolines, or #f on a cycle.
      (let loop ((label label) (fuel count))
        (let ((next (hash-table-ref/default forward label #f)))
          (cond ((not next) label)
                ((= fuel 0) #f)
                (else (loop next (- fuel 1)))))))
    (do ((i 1 (+ i 1)))
        ((>= i count))
      (let ((target (jump-only-target (vector-ref vec i))))
        (when (and target (ends-in-terminator? (vector-ref vec (- i 1))))
          (hash-table-set! forward (machine-block-label (vector-ref vec i))
                           target))))
    ;; Drop trampolines that lead into a cycle.
    (for-each
     (lambda (block)
       (let ((label (machine-block-label block)))
         (when (and label
                    (hash-table-exists? forward label)
                    (not (follow label)))
           (hash-table-delete! forward label))))
     blocks)
    (if (= 0 (hash-table-size forward))
        blocks
        (let ((new-index (make-vector count #f))
              (label-index (make-hash-table eq?)))
          (let loop ((i 0) (next 0))
            (when (< i count)
              (let ((label (machine-block-label (vector-ref vec i))))
                (if (and label (hash-table-exists? forward label))
                    (loop (+ i 1) next)
                    (begin
                      (vector-set! new-index i next)
                      (when label (hash-table-set! label-index label next))
                      (loop (+ i 1) (+ next 1)))))))
          (letrec ((retarget (lambda (label) (follow label)))
                   (successor
                    (lambda (i)
                      (let ((label (machine-block-label (vector-ref vec i))))
                        (if (and label (hash-table-exists? forward label))
                            (hash-table-ref label-index (follow label))
                            (vector-ref new-index i)))))
                   (rewrite
                    (lambda (instr)
                      (case (car instr)
                        ((jump) `(jump ,(retarget (cadr instr))))
                        ((branch-if)
                         `(branch-if ,(cadr instr)
                                     ,(retarget (caddr instr))
                                     ,(retarget (cadddr instr))))
                        ((cmp-branch)
                         `(cmp-branch ,(cadr instr) ,(caddr instr)
                                      ,(cadddr instr)
                                      ,(retarget (car (cddddr instr)))
                                      ,(retarget (cadr (cddddr instr)))))
                        (else instr)))))
            (let loop ((i (- count 1)) (result '()))
              (if (< i 0)
                  result
                  (let* ((block (vector-ref vec i))
                         (label (machine-block-label block)))
                    (if (and label (hash-table-exists? forward label))
                        (loop (- i 1) result)
                        (loop (- i 1)
                              (cons (make-machine-block
                                     label
                                     (map rewrite
                                          (machine-block-instructions block))
                                     (dedupe-successors
                                      (map successor
                                           (machine-block-successors block))))
                                    result)))))))))))

(define (dedupe-successors indices)
  (let loop ((rest indices) (result '()))
    (cond ((null? rest) (reverse result))
          ((memv (car rest) result) (loop (cdr rest) result))
          (else (loop (cdr rest) (cons (car rest) result))))))

;;; ── Peephole: shared return epilogue ───────────────────────────────────────
;;
;; Every plain (ret) finalizes to the same four-instruction epilogue
;; (gc-pop-frame, restore-callee-saved, deallocate-frame, ret) after its
;; move-out. When a procedure has two or more of them, one copy is kept as a
;; block and the other sites jump to it. If the last block is itself a return
;; site it becomes that copy, with the code before its epilogue falling
;; through, so that return pays no extra jump.

(define (epilogue-suffix instrs)
  (let ((n (length instrs)))
    (and (>= n 4)
         (let ((tail (list-tail instrs (- n 4))))
           (and (equal? (car tail) '(gc-pop-frame))
                (eq? (car (cadr tail)) 'restore-callee-saved)
                (eq? (car (caddr tail)) 'deallocate-frame)
                (equal? (cadddr tail) '(ret))
                tail)))))

(define (without-last instrs k)
  (reverse (list-tail (reverse instrs) k)))

(define (merge-return-epilogues name blocks)
  (let* ((count (length blocks))
         (suffix (let find ((rest blocks))
                   (cond ((null? rest) #f)
                         ((epilogue-suffix (machine-block-instructions (car rest))))
                         (else (find (cdr rest))))))
         (site? (lambda (block)
                  (and suffix
                       (equal? (epilogue-suffix (machine-block-instructions block))
                               suffix)))))
    (if (< (length (filter site? blocks)) 2)
        blocks
        (let* ((last-block (list-ref blocks (- count 1)))
               (last-instrs (machine-block-instructions last-block))
               (reuse-last? (and (site? last-block)
                                 (= (length last-instrs) 4)
                                 (machine-block-label last-block)))
               (label (if reuse-last?
                          (machine-block-label last-block)
                          (string->symbol
                           (string-append "epilogue."
                                          (symbol->string name)))))
               (index (if reuse-last? (- count 1) count))
               (jump-site
                (lambda (block)
                  (make-machine-block
                   (machine-block-label block)
                   (append (without-last (machine-block-instructions block) 4)
                           (list `(jump ,label)))
                   (list index))))
               (rewritten
                (let loop ((rest blocks) (i 0) (result '()))
                  (cond
                    ((null? rest) (reverse result))
                    ((and (= i (- count 1)) (site? (car rest)))
                     ;; The last block: keep it as the epilogue itself, or
                     ;; split it so its prefix falls into the epilogue block.
                     (loop (cdr rest) (+ i 1)
                           (cons (if reuse-last?
                                     (car rest)
                                     (make-machine-block
                                      (machine-block-label (car rest))
                                      (without-last (machine-block-instructions
                                                     (car rest))
                                                    4)
                                      (list index)))
                                 result)))
                    ((site? (car rest))
                     (loop (cdr rest) (+ i 1) (cons (jump-site (car rest)) result)))
                    (else (loop (cdr rest) (+ i 1) (cons (car rest) result)))))))
          (if reuse-last?
              rewritten
              (append rewritten
                      (list (make-machine-block label suffix '()))))))))

(define (peephole-machine-procedure proc)
  (make-machine-procedure
   (machine-procedure-name proc)
   (machine-procedure-params proc)
   (machine-procedure-param-locations proc)
   (map (lambda (block)
          (make-machine-block
           (machine-block-label block)
           (drop-redundant-moves (machine-block-instructions block))
           (machine-block-successors block)))
        (remove-jump-only-blocks
         (merge-return-epilogues (machine-procedure-name proc)
                                 (machine-procedure-blocks proc))))
   (machine-procedure-homes proc)
   (machine-procedure-root-homes proc)
   (machine-procedure-frame-slots proc)
   (machine-procedure-used-registers proc)))

(define (cfg->allocated-machine-procedure name params cfg)
  (peephole-machine-procedure
   (finalize-machine-procedure
    (allocate-machine-procedure
     (fuse-compare-branches
      (select-machine-procedure name params cfg))))))

;;; ── Display helpers ────────────────────────────────────────────────────────

(define (display-cfg cfg)
  (display "Control Flow Graph:\n")
  (do ((i 0 (+ i 1)) (blocks cfg (cdr blocks)))
      ((null? blocks))
    (let* ((block (car blocks))
           (label (basic-block-label block))
           (instrs (basic-block-instructions block))
           (successors (basic-block-successors block)))
      (display "Block ") (display i)
      (if label
          (begin (display " (label: ") (display label) (display ")")))
      (display ":\n")
      (for-each (lambda (instr)
                  (display "    ")
                  (write instr)
                  (newline))
                instrs)
       (display "    Successors: ")
       (write successors)
       (newline) (newline))))

(define (display-procedure-cfg procedure cfg)
  (display "Procedure ")
  (display (procedure-name procedure))
  (display " ")
  (write (procedure-params procedure))
  (display ":\n")
  (display-cfg cfg))

(define (display-machine-procedure proc)
  (display "Machine Procedure ")
  (display (machine-procedure-name proc))
  (display ":\n")
  (display "    Param locations: ")
  (write (machine-procedure-param-locations proc))
  (newline)
  (display "    Homes: ")
  (write (machine-procedure-homes proc))
  (newline)
  (display "    Root homes: ")
  (write (machine-procedure-root-homes proc))
  (newline)
  (display "    Frame slots: ")
  (write (machine-procedure-frame-slots proc))
  (newline)
  (display "    Used callee-saved: ")
  (write (machine-procedure-used-registers proc))
  (newline)
  (for-each
   (lambda (block)
     (display "    Block")
     (if (machine-block-label block)
         (begin
           (display " ")
           (display (machine-block-label block)))
         (display " entry"))
     (display ":\n")
     (for-each (lambda (instr)
                 (display "        ")
                 (write instr)
                 (newline))
               (machine-block-instructions block))
     (display "        Successors: ")
     (write (machine-block-successors block))
     (newline))
   (machine-procedure-blocks proc))
  (newline))

;;; ── AArch64 assembly emission ──────────────────────────────────────────────

(define (procedure-saved-bytes proc)
  (* 8 (length (machine-procedure-used-registers proc))))

(define (procedure-outgoing-bytes proc)
  (* 8 (max-outgoing-stack-args (machine-procedure-blocks proc))))

(define (procedure-outgoing-base proc)
  0)

(define (incoming-stack-arg-offset index)
  (+ 16 (* 8 index)))

(define (stack-slot-offset proc index)
  (+ (procedure-outgoing-bytes proc)
     (procedure-saved-bytes proc)
     (* 8 index)))

(define (saved-register-offset proc reg)
  (let loop ((rest (machine-procedure-used-registers proc))
             (offset (procedure-outgoing-bytes proc)))
    (cond
      ((null? rest) (error "Unknown saved register" reg))
      ((eq? (car rest) reg) offset)
      (else (loop (cdr rest) (+ offset 8))))))

(define (asm-name sym)
  (string-append "_" (symbol->string sym)))

(define (emit-asm-line port text)
  (display text port)
  (newline port))

(define fixnum-shift 3)
(define tag-mask 7)
(define pair-tag 1)
(define box-tag 2)
(define closure-tag 3)
(define vector-tag 4)
(define symbol-tag 5)
(define null-immediate 20)
(define false-immediate 36)
(define true-immediate 52)
(define uninitialized-immediate 68)
(define unsafe-pair-load-mode 'fast)

;;; ── Symbol interning ───────────────────────────────────────────────────────
;;; Symbols are immediates: (hash << fixnum-shift) | symbol-tag, where hash is
;;; a deterministic function of the symbol's print name (not a per-program
;;; table position). Two files compiling the same symbol name independently
;;; therefore produce the identical immediate with no coordination between
;;; them, so eq?/case/memq on symbols keep working once files are linked
;;; together without ever needing a runtime interning step. The table below
;;; only exists so the runtime can recover a symbol's printed name (hash ->
;;; name); it plays no part in identity. It's per-program state that
;;; emit-aarch64-program resets.

;; A 61-bit (2^61 - 1, a Mersenne prime) multiplicative polynomial hash over
;; the symbol name's UTF-8 bytes. 61 bits is exactly the space available
;; above the 3-bit tag in a 64-bit immediate. This only needs to be a fixed,
;; well-distributed function computable identically by every independent
;; compilation -- it does not need to be cryptographic, and the compiler
;; itself runs on an arbitrary-precision host Scheme so overflow during the
;; fold below isn't a concern.
(define symbol-hash-modulus 2305843009213693951)
(define symbol-hash-multiplier 131)

(define (symbol-hash sym)
  (let ((bytes (string->utf8 (symbol->string sym))))
    (let loop ((index 0) (acc 1469598103934665603))
      (if (= index (bytevector-length bytes))
          (modulo acc symbol-hash-modulus)
          (loop (+ index 1)
                (modulo (+ (* acc symbol-hash-multiplier)
                           (bytevector-u8-ref bytes index)
                           1)
                        symbol-hash-modulus))))))

(define interned-symbols '())   ; assq list of (sym . hash), most recent first

(define (reset-interned-symbols!)
  (set! interned-symbols '()))

(define (intern-symbol! sym)
  (let ((entry (assq sym interned-symbols)))
    (if entry
        (cdr entry)
        (let ((hash (symbol-hash sym)))
          (set! interned-symbols (cons (cons sym hash) interned-symbols))
          hash))))

(define (encode-immediate value)
  (cond
    ((null? value) null-immediate)
    ((eq? value #f) false-immediate)
    ((eq? value #t) true-immediate)
    ((number? value) (ash value fixnum-shift))
    ((quoted-symbol-expr? value)
     (+ (ash (intern-symbol! (cadr value)) fixnum-shift) symbol-tag))
    (else (error "Expected immediate value" value))))

(define (immediate->string value)
  (number->string (encode-immediate value)))

;; AArch64's `mov reg, #imm` alias only accepts a 16-bit value (optionally
;; shifted) or a repeating-bit-pattern "logical immediate" -- not an
;; arbitrary 64-bit constant. Symbol immediates are now a 61-bit hash (see
;; symbol-hash above) and essentially never happen to fit either form, so
;; every literal load goes through an explicit movz + up-to-3-movk sequence,
;; which can represent any 64-bit pattern regardless of magnitude or sign.
(define u64-modulus (expt 2 64))

(define (u16-chunk unsigned-value shift)
  (modulo (quotient unsigned-value (expt 2 shift)) 65536))

(define (emit-load-immediate port target value)
  (let* ((unsigned (modulo value u64-modulus))
         (chunk1 (u16-chunk unsigned 16))
         (chunk2 (u16-chunk unsigned 32))
         (chunk3 (u16-chunk unsigned 48)))
    (emit-asm-line port
                   (string-append "    movz " target ", #"
                                  (number->string (u16-chunk unsigned 0))))
    (unless (= chunk1 0)
      (emit-asm-line port
                     (string-append "    movk " target ", #"
                                    (number->string chunk1) ", lsl #16")))
    (unless (= chunk2 0)
      (emit-asm-line port
                     (string-append "    movk " target ", #"
                                    (number->string chunk2) ", lsl #32")))
    (unless (= chunk3 0)
      (emit-asm-line port
                     (string-append "    movk " target ", #"
                                    (number->string chunk3) ", lsl #48")))))

(define (emit-load-operand port target operand proc)
  (cond
    ((literal-expr? operand)
     (emit-load-immediate port target (encode-immediate operand)))
    ((register-operand? operand)
     (let ((src (register-name operand)))
       (when (not (string=? target src))
         (emit-asm-line port
                        (string-append "    mov " target ", " src)))))
    ((and (pair? operand) (eq? (car operand) 'stack-slot))
      (emit-asm-line port
                     (string-append "    ldr " target ", [sp, #"
                                    (number->string
                                    (stack-slot-offset proc (cadr operand)))
                                   "]")))
    ((and (pair? operand) (eq? (car operand) 'stack-arg))
     (emit-asm-line port
                    (string-append "    ldr " target ", [x29, #"
                                   (number->string
                                    (incoming-stack-arg-offset (cadr operand)))
                                   "]")))
    (else
     (error "Unsupported source operand in assembly emission" operand))))

(define (emit-store-operand port source operand proc)
  (cond
    ((register-operand? operand)
     (let ((dst (register-name operand)))
       (when (not (string=? source dst))
         (emit-asm-line port
                        (string-append "    mov " dst ", " source)))))
    ((and (pair? operand) (eq? (car operand) 'stack-slot))
     (emit-asm-line port
                    (string-append "    str " source ", [sp, #"
                                   (number->string
                                    (stack-slot-offset proc (cadr operand)))
                                   "]")))
    ((and (pair? operand) (eq? (car operand) 'stack-arg))
     (emit-asm-line port
                    (string-append "    str " source ", [sp, #"
                                   (number->string
                                    (+ (procedure-outgoing-base proc)
                                       (* 8 (cadr operand))))
                                   "]")))
    (else
     (error "Unsupported destination operand in assembly emission" operand))))

;; Register destinations load straight into place and register sources store
;; straight out; only memory-to-memory and literal-to-memory go through x9.
(define (emit-move port dst src proc)
  (cond
    ((equal? dst src) 'done)
    ((register-operand? dst)
     (emit-load-operand port (register-name dst) src proc))
    ((register-operand? src)
     (emit-store-operand port (register-name src) dst proc))
    (else
     (emit-load-operand port "x9" src proc)
     (emit-store-operand port "x9" dst proc))))

;; The register holding operand: its own if it lives in one, else scratch
;; after loading it there.
(define (operand-source port operand scratch proc)
  (if (register-operand? operand)
      (register-name operand)
      (begin
        (emit-load-operand port scratch operand proc)
        scratch)))

;; Where to compute a result for dst: dst's register, or scratch if it lives
;; in memory (then store-result writes it back).
(define (result-register dst scratch)
  (if (register-operand? dst) (register-name dst) scratch))

(define (store-result port reg dst proc)
  (unless (register-operand? dst)
    (emit-store-operand port reg dst proc)))

;; The encoded value of a literal operand if it fits an AArch64 12-bit
;; arithmetic/compare immediate, else #f.
(define (small-immediate operand)
  (and (literal-expr? operand)
       (let ((value (encode-immediate operand)))
         (and (<= 0 value 4095) value))))

(define (immediate-text value)
  (string-append "#" (number->string value)))

(define (emit-procedure-address port reg proc-name)
  (emit-asm-line port
                 (string-append "    adrp " reg ", "
                                (asm-name proc-name) "@PAGE"))
  (emit-asm-line port
                 (string-append "    add " reg ", " reg ", "
                                (asm-name proc-name) "@PAGEOFF")))

(define (emit-bool-result port condition dst proc)
  (emit-asm-line port
                 (string-append "    mov x11, #"
                                (number->string false-immediate)))
  (emit-asm-line port
                 (string-append "    mov x12, #"
                                (number->string true-immediate)))
  (let ((target (result-register dst "x11")))
    (emit-asm-line port
                   (string-append "    csel " target ", x12, x11, " condition))
    (store-result port target dst proc)))

(define (emit-load-box-address port operand proc)
  (emit-load-operand port "x9" operand proc)
  (emit-asm-line port
                 (string-append "    sub x9, x9, #"
                                (number->string box-tag))))

(define (emit-load-closure-address port operand proc)
  (emit-load-operand port "x9" operand proc)
  (emit-asm-line port
                 (string-append "    sub x9, x9, #"
                                (number->string closure-tag))))

(define (emit-unsafe-pair-load port dst operand offset checked-helper proc)
  (if (eq? unsafe-pair-load-mode 'debug-assert)
      (emit-runtime-unary-call port checked-helper dst operand proc)
      (begin
        (emit-load-operand port "x9" operand proc)
        (emit-asm-line port
                       (string-append "    sub x9, x9, #"
                                      (number->string pair-tag)))
        (emit-asm-line port
                       (string-append "    ldr x10, [x9, #"
                                      (number->string offset)
                                      "]"))
        (emit-store-operand port "x10" dst proc))))

(define (emit-runtime-unary-call port helper dst operand proc)
  (emit-load-operand port "x0" operand proc)
  (emit-asm-line port (string-append "    bl " helper))
  (emit-store-operand port "x0" dst proc))

;; Out-of-line failure paths. A checked operation tests its operands' tags
;; inline and, when the test fails, branches to a stub emitted after the
;; procedure's last block. The stub calls the same runtime helper the
;; operation used to call unconditionally; given a bad operand the helper
;; reports the error and exits, so a stub never returns and needs neither
;; saved registers nor a GC safepoint.
(define pending-slow-stubs '())
(define slow-stub-counter 0)
(define slow-stub-prefix "")

(define (begin-slow-stubs! name)
  (set! pending-slow-stubs '())
  (set! slow-stub-counter 0)
  (set! slow-stub-prefix name))

(define (new-slow-stub! emit-body)
  (set! slow-stub-counter (+ slow-stub-counter 1))
  (let ((label (string-append "Lslow." slow-stub-prefix "."
                              (number->string slow-stub-counter))))
    (set! pending-slow-stubs (cons (cons label emit-body) pending-slow-stubs))
    label))

;; A fresh file-local label for code a stub jumps back to.
(define (new-local-label! kind)
  (set! slow-stub-counter (+ slow-stub-counter 1))
  (string-append kind "." slow-stub-prefix "." (number->string slow-stub-counter)))

(define (flush-slow-stubs! port)
  (for-each (lambda (stub)
              (emit-asm-line port (string-append (car stub) ":"))
              ((cdr stub)))
            (reverse pending-slow-stubs))
  (set! pending-slow-stubs '()))

(define (safe-binop-helper op)
  (case op
    ((safe-+) "_hop_safe_add")
    ((safe--) "_hop_safe_sub")
    ((safe-*) "_hop_safe_mul")
    ((safe-=) "_hop_safe_eq")
    ((safe-<) "_hop_safe_lt")
    ((safe->) "_hop_safe_gt")
    (else (error "Unknown safe binop op" op))))

(define (fixnum-literal? operand)
  (and (literal-expr? operand) (number? operand)))

;; The operation done once both operands are known to be fixnums.
(define (emit-checked-binop-fast port op dst a b proc)
  (case op
    ((safe-+) (emit-binop port '+ dst a b proc))
    ((safe--) (emit-binop port '- dst a b proc))
    ((safe-=) (emit-binop port '= dst a b proc))
    ((safe-<) (emit-binop port '< dst a b proc))
    ((safe->) (emit-binop port '> dst a b proc))
    ((safe-*)
     ;; Same arithmetic as hop_safe_mul: unshift one operand, multiply.
     (let* ((ra (operand-source port a "x9" proc))
            (rb (operand-source port b "x10" proc))
            (target (result-register dst "x11")))
       (emit-asm-line port (string-append "    asr x12, " ra ", #"
                                          (number->string fixnum-shift)))
       (emit-asm-line port (string-append "    mul " target ", x12, " rb))
       (store-result port target dst proc)))
    (else (error "Unknown safe binop op" op))))

(define (non-fixnum-literal? operand)
  (and (literal-expr? operand) (not (number? operand))))

;; Branches to a stub calling helper (which reports the error) unless both
;; operands are fixnums. Returns #f, emitting nothing, when an operand is a
;; literal that can never be one: the caller then just calls the helper.
(define (emit-fixnum-guard port helper a b proc)
  (let ((slow (new-slow-stub!
               (lambda ()
                 (emit-load-operand port "x0" a proc)
                 (emit-load-operand port "x1" b proc)
                 (emit-asm-line port (string-append "    bl " helper))))))
    (cond
      ((and (fixnum-literal? a) (fixnum-literal? b)) 'no-test)
      ((fixnum-literal? a)
       (emit-asm-line port (string-append "    tst "
                                          (operand-source port b "x10" proc)
                                          ", #" (number->string tag-mask)))
       (emit-asm-line port (string-append "    b.ne " slow)))
      ((fixnum-literal? b)
       (emit-asm-line port (string-append "    tst "
                                          (operand-source port a "x9" proc)
                                          ", #" (number->string tag-mask)))
       (emit-asm-line port (string-append "    b.ne " slow)))
      (else
       (let ((ra (operand-source port a "x9" proc))
             (rb (operand-source port b "x10" proc)))
         (emit-asm-line port (string-append "    orr x11, " ra ", " rb))
         (emit-asm-line port (string-append "    tst x11, #"
                                            (number->string tag-mask)))
         (emit-asm-line port (string-append "    b.ne " slow)))))))

(define (emit-safe-binop port op dst a b proc)
  (define helper (safe-binop-helper op))
  (cond
    ;; A literal that is not a fixnum can never succeed: leave it to the helper.
    ((or (non-fixnum-literal? a) (non-fixnum-literal? b))
     (emit-load-operand port "x0" a proc)
     (emit-load-operand port "x1" b proc)
     (emit-asm-line port (string-append "    bl " helper))
     (emit-store-operand port "x0" dst proc))
    (else
     (emit-fixnum-guard port helper a b proc)
     (emit-checked-binop-fast port op dst a b proc))))

;; Pair allocation. The fast path bumps the runtime heap's alloc_ptr (struct
;; hop_heap in runtime.c, exported as hop_runtime_heap: alloc_ptr at +24,
;; alloc_limit at +32) and writes the header, car and cdr; when the pair does not
;; fit, a stub calls hop_alloc_pair, which collects, and rejoins after the
;; allocation. The heap is initialized lazily and starts with both pointers 0, so
;; the first allocation always takes the stub. The GC root syncs and reloads
;; around the instruction are unchanged: alloc-pair is still a safepoint.
;; HOP_ALLOC_COUNT=0 leaves out the counter the inline path bumps for HOP_STATS.
(define pair-object-type 2)  ; HOP_OBJ_PAIR in runtime.c, with no header aux bits

(define (alloc-count-enabled?)
  (not (equal? (get-environment-variable "HOP_ALLOC_COUNT") "0")))

(define (emit-inline-alloc-pair port dst car-operand cdr-operand proc)
  (let* ((target (result-register dst "x10"))
         (back (new-local-label! "Lback"))
         (slow (new-slow-stub!
                (lambda ()
                  (emit-load-operand port "x0" car-operand proc)
                  (emit-load-operand port "x1" cdr-operand proc)
                  (emit-asm-line port "    bl _hop_alloc_pair")
                  (emit-asm-line port (string-append "    mov " target ", x0"))
                  (emit-asm-line port (string-append "    b " back))))))
    (emit-asm-line port "    adrp x9, _hop_runtime_heap@PAGE")
    (emit-asm-line port "    add x9, x9, _hop_runtime_heap@PAGEOFF")
    (emit-asm-line port "    ldp x10, x11, [x9, #24]")
    (emit-asm-line port "    add x12, x10, #24")
    (emit-asm-line port "    cmp x12, x11")
    (emit-asm-line port (string-append "    b.hi " slow))
    (emit-asm-line port "    str x12, [x9, #24]")
    (when (alloc-count-enabled?)
      (emit-asm-line port "    adrp x13, _hop_stat_inline_pairs@PAGE")
      (emit-asm-line port "    add x13, x13, _hop_stat_inline_pairs@PAGEOFF")
      (emit-asm-line port "    ldr x14, [x13]")
      (emit-asm-line port "    add x14, x14, #1")
      (emit-asm-line port "    str x14, [x13]"))
    (emit-asm-line port (string-append "    mov x11, #" (number->string pair-object-type)))
    (emit-asm-line port "    str x11, [x10]")
    (emit-asm-line port (string-append "    str "
                                       (operand-source port car-operand "x13" proc)
                                       ", [x10, #8]"))
    (emit-asm-line port (string-append "    str "
                                       (operand-source port cdr-operand "x14" proc)
                                       ", [x10, #16]"))
    (emit-asm-line port (string-append "    add " target ", x10, #"
                                       (number->string pair-tag)))
    (emit-asm-line port (string-append back ":"))
    (store-result port target dst proc)))

;; The fixnum test in front of a fused safe comparison. A literal operand that
;; is not a fixnum always fails, so it branches straight to the helper.
(define (emit-safe-compare-guard port op a b proc)
  (let ((helper (safe-binop-helper op)))
    (if (or (non-fixnum-literal? a) (non-fixnum-literal? b))
        (begin
          (emit-load-operand port "x0" a proc)
          (emit-load-operand port "x1" b proc)
          (emit-asm-line port (string-append "    bl " helper)))
        (emit-fixnum-guard port helper a b proc))))

;; car/cdr of a value that may not be a pair: test the pair tag inline, load
;; the field directly, and leave the error to the helper (see above). The
;; header word is not re-checked, as in unsafe-car/unsafe-cdr: the pair tag
;; belongs to pairs alone.
(define (emit-checked-pair-load port dst operand offset helper proc)
  (if (literal-expr? operand)
      (emit-runtime-unary-call port helper dst operand proc)
      (let ((slow (new-slow-stub!
                   (lambda ()
                     (emit-load-operand port "x0" operand proc)
                     (emit-asm-line port (string-append "    bl " helper)))))
            (reg (operand-source port operand "x9" proc))
            (target (result-register dst "x10")))
        (emit-asm-line port (string-append "    sub x11, " reg ", #"
                                           (number->string pair-tag)))
        (emit-asm-line port (string-append "    tst x11, #"
                                           (number->string tag-mask)))
        (emit-asm-line port (string-append "    b.ne " slow))
        (emit-asm-line port (string-append "    ldr " target ", [x11, #"
                                           (number->string offset) "]"))
        (store-result port target dst proc))))

;; A global read/write addresses its own labeled cell directly (adrp/add,
;; same as a procedure address) instead of going through a runtime helper --
;; there is no per-program slot array to bounds-check against any more, so
;; the label's assembler/linker resolution IS the lookup.
(define (emit-runtime-global-read port dst label proc)
  (emit-procedure-address port "x9" label)
  (emit-asm-line port "    ldr x10, [x9]")
  (emit-store-operand port "x10" dst proc))

(define (emit-runtime-global-write port label operand proc)
  (emit-procedure-address port "x9" label)
  (emit-load-operand port "x10" operand proc)
  (emit-asm-line port "    str x10, [x9]"))

(define (gc-desc-label proc-name)
  (string-append "Lgcdesc." (symbol->string proc-name)))

(define (emit-procedure-descriptor-address port reg proc-name)
  (emit-asm-line port
                 (string-append "    adrp " reg ", "
                                (gc-desc-label proc-name) "@PAGE"))
  (emit-asm-line port
                 (string-append "    add " reg ", " reg ", "
                                (gc-desc-label proc-name) "@PAGEOFF")))

(define (emit-immediate-compare port operand immediate proc)
  (let ((reg (operand-source port operand "x9" proc)))
    (if (<= 0 immediate 4095)
        (emit-asm-line port
                       (string-append "    cmp " reg ", "
                                      (immediate-text immediate)))
        (begin
          (emit-asm-line port
                         (string-append "    mov x10, #"
                                        (number->string immediate)))
          (emit-asm-line port (string-append "    cmp " reg ", x10"))))))

(define (emit-compare port lhs rhs proc)
  (let* ((lhs-reg (operand-source port lhs "x9" proc))
         (imm (small-immediate rhs)))
    (if imm
        (emit-asm-line port
                       (string-append "    cmp " lhs-reg ", "
                                      (immediate-text imm)))
        (emit-asm-line port
                       (string-append "    cmp " lhs-reg ", "
                                      (operand-source port rhs "x10" proc))))))

(define (comparison-condition op)
  (case op
    ((= eq? safe-=) '("eq" . "ne"))
    ((< safe-<) '("lt" . "ge"))
    ((> safe->) '("gt" . "le"))
    (else (error "Unsupported comparison in assembly emission" op))))

;; Branches to then-label if condition holds, else to else-label, leaving out
;; whichever jump falls through to next-label (the block emitted next).
(define (emit-conditional-branch port condition inverse then-label else-label next-label)
  (define (label-text label) (string-append "L" (symbol->string label)))
  (cond
    ((eq? then-label else-label)
     (unless (eq? then-label next-label)
       (emit-asm-line port (string-append "    b " (label-text then-label)))))
    ((eq? then-label next-label)
     (emit-asm-line port (string-append "    b." inverse " "
                                        (label-text else-label))))
    ((eq? else-label next-label)
     (emit-asm-line port (string-append "    b." condition " "
                                        (label-text then-label))))
    (else
     (emit-asm-line port (string-append "    b." condition " "
                                        (label-text then-label)))
     (emit-asm-line port (string-append "    b " (label-text else-label))))))

(define (emit-tag-compare port operand tag proc)
  (emit-asm-line port
                 (string-append "    and x10, "
                                (operand-source port operand "x9" proc)
                                ", #" (number->string tag-mask)))
  (emit-asm-line port
                 (string-append "    cmp x10, #" (number->string tag))))

(define (emit-binop port op dst lhs rhs proc)
  (define (emit-add-sub mnemonic commutative?)
    (let* ((target (result-register dst "x11"))
           (rhs-imm (small-immediate rhs))
           (lhs-imm (and commutative? (not rhs-imm) (small-immediate lhs))))
      (cond
        (rhs-imm
         (emit-asm-line port
                        (string-append "    " mnemonic " " target ", "
                                       (operand-source port lhs "x9" proc)
                                       ", " (immediate-text rhs-imm))))
        (lhs-imm
         (emit-asm-line port
                        (string-append "    " mnemonic " " target ", "
                                       (operand-source port rhs "x10" proc)
                                       ", " (immediate-text lhs-imm))))
        (else
         (let* ((a (operand-source port lhs "x9" proc))
                (b (operand-source port rhs "x10" proc)))
           (emit-asm-line port
                          (string-append "    " mnemonic " " target ", "
                                         a ", " b)))))
      (store-result port target dst proc)))
  (define (emit-comparison condition)
    (emit-compare port lhs rhs proc)
    (emit-bool-result port condition dst proc))
  (cond
    ((eq? op '+) (emit-add-sub "add" #t))
    ((eq? op '-) (emit-add-sub "sub" #f))
    ((eq? op '*)
     (let* ((a (operand-source port lhs "x9" proc))
            (b (operand-source port rhs "x10" proc))
            (target (result-register dst "x11")))
       (emit-asm-line port (string-append "    mul x11, " a ", " b))
       (emit-asm-line port
                      (string-append "    asr " target ", x11, #"
                                     (number->string fixnum-shift)))
       (store-result port target dst proc)))
    ((eq? op '=) (emit-comparison "eq"))
    ;; eq? compares the full tagged words, so it is valid for any two Scheme
    ;; values: fixnums, symbols, immediates, and heap pointers alike.
    ((eq? op 'eq?) (emit-comparison "eq"))
    ((eq? op '<) (emit-comparison "lt"))
    ((eq? op '>) (emit-comparison "gt"))
    (else
     (error "Unsupported primop in assembly emission" op)))
  'done)

(define (register-name operand)
  (symbol->string (cadr operand)))

(define (emit-alloc-closure port dst proc-name arity captures proc)
  (let ((count (length captures)))
    (if (<= count 3)
        (begin
          (emit-procedure-address port "x0" proc-name)
          (let loop ((rest captures) (index 1))
            (if (null? rest)
                'done
                (begin
                  (emit-load-operand port
                                     (string-append "x" (number->string index))
                                     (car rest)
                                     proc)
                  (loop (cdr rest) (+ index 1)))))
          (emit-asm-line port
                         (string-append "    mov x"
                                        (number->string (+ count 1))
                                        ", #"
                                        (number->string arity)))
          (emit-asm-line port
                         (string-append "    bl _hop_alloc_closure_"
                                        (number->string count))))
        (begin
          (let loop ((rest captures) (index 0))
            (unless (null? rest)
              (emit-load-operand port "x9" (car rest) proc)
              (emit-asm-line port
                             (string-append "    str x9, [sp, #"
                                            (number->string (* 8 index))
                                            "]"))
              (loop (cdr rest) (+ index 1))))
          (emit-procedure-address port "x0" proc-name)
          (emit-asm-line port
                         (string-append "    mov x1, #"
                                        (number->string count)))
          (emit-asm-line port "    mov x2, sp")
          (emit-asm-line port
                         (string-append "    mov x3, #"
                                        (number->string arity)))
          (emit-asm-line port "    bl _hop_alloc_closure_n")))
    (emit-store-operand port "x0" dst proc)))

;; Variadic closures are a new, unoptimized-for-speed path (ordinary
;; closures never route through here), so there is no need to special-case
;; small capture counts the way emit-alloc-closure does above -- always
;; write captures to the outgoing-stack area and go through the one general
;; runtime helper, exactly like the >3-capture branch of emit-alloc-closure.
(define (emit-alloc-closure-variadic port dst proc-name k captures proc)
  (let ((count (length captures)))
    (let loop ((rest captures) (index 0))
      (unless (null? rest)
        (emit-load-operand port "x9" (car rest) proc)
        (emit-asm-line port
                       (string-append "    str x9, [sp, #"
                                      (number->string (* 8 index))
                                      "]"))
        (loop (cdr rest) (+ index 1))))
    (emit-procedure-address port "x0" proc-name)
    (emit-asm-line port (string-append "    mov x1, #" (number->string k)))
    (emit-asm-line port (string-append "    mov x2, #" (number->string count)))
    (emit-asm-line port "    mov x3, sp")
    (emit-asm-line port "    bl _hop_alloc_closure_variadic")
    (emit-store-operand port "x0" dst proc)))

(define (emit-call-helper port argc tail?)
  (emit-asm-line port
                 (string-append "    "
                                (if tail? "b" "bl")
                                " _hop_"
                                (if tail? "tail_call_" "call_")
                                (number->string argc))))

(define (emit-call-label port proc-name tail?)
  (emit-asm-line port
                 (string-append "    "
                                (if tail? "b " "bl ")
                                (asm-name proc-name))))

(define (emit-machine-instruction port instr proc next-label)
  (case (car instr)
    ((allocate-frame)
     (emit-asm-line port "    stp x29, x30, [sp, #-16]!")
     (emit-asm-line port "    mov x29, sp")
     (when (> (cadr instr) 0)
       (emit-asm-line port
                      (string-append "    sub sp, sp, #"
                                     (number->string (cadr instr))))))
    ((save-callee-saved)
     (for-each
      (lambda (reg)
        (emit-asm-line port
                       (string-append "    str "
                                      (symbol->string reg)
                                      ", [sp, #"
                                      (number->string
                                       (saved-register-offset proc reg))
                                       "]")))
       (cadr instr)))
    ((init-frame-slots)
     (let loop ((index 0))
       (if (= index (cadr instr))
           'done
           (begin
             (emit-asm-line port
                            (string-append "    str xzr, [sp, #"
                                           (number->string
                                            (stack-slot-offset proc index))
                                           "]"))
             (loop (+ index 1))))))
    ((gc-push-frame)
     (emit-procedure-descriptor-address port "x9" (cadr instr))
     (emit-procedure-address port "x10" 'hop_gc_top_frame)
     (emit-asm-line port "    ldr x11, [x10]")
     (emit-asm-line port "    str x11, [x29, #-16]")
     (emit-asm-line port "    str x9, [x29, #-8]")
     (emit-asm-line port "    mov x11, x29")
     (emit-asm-line port "    str x11, [x10]"))
    ((gc-pop-frame)
     (emit-procedure-address port "x9" 'hop_gc_top_frame)
     (emit-asm-line port "    ldr x10, [x29, #-16]")
     (emit-asm-line port "    str x10, [x9]"))
    ((restore-callee-saved)
     (for-each
      (lambda (reg)
        (emit-asm-line port
                       (string-append "    ldr "
                                      (symbol->string reg)
                                      ", [sp, #"
                                      (number->string
                                       (saved-register-offset proc reg))
                                       "]")))
      (cadr instr)))
    ((deallocate-frame)
     (when (> (cadr instr) 0)
       (emit-asm-line port
                      (string-append "    add sp, sp, #"
                                     (number->string (cadr instr)))))
     (emit-asm-line port "    ldp x29, x30, [sp], #16"))
    ((move move-out)
     (emit-move port (cadr instr) (caddr instr) proc))
    ((binop)
     (emit-binop port
                 (cadr instr)
                 (caddr instr)
                 (cadddr instr)
                 (car (cddddr instr))
                 proc))
    ((safe-binop)
     (emit-safe-binop port
                      (cadr instr)
                      (caddr instr)
                      (cadddr instr)
                      (car (cddddr instr))
                      proc))
    ((alloc-box)
      (emit-runtime-unary-call port "_hop_alloc_box" (cadr instr) (caddr instr) proc))
    ((alloc-pair)
      (emit-inline-alloc-pair port (cadr instr) (caddr instr) (cadddr instr) proc))
    ((alloc-vector)
      (emit-load-operand port "x0" (caddr instr) proc)
      (emit-load-operand port "x1" (cadddr instr) proc)
      (emit-asm-line port "    bl _hop_alloc_vector")
      (emit-store-operand port "x0" (cadr instr) proc))
    ((vector-length)
      (emit-runtime-unary-call port "_hop_vector_length" (cadr instr) (caddr instr) proc))
    ((vector-ref)
      (emit-load-operand port "x0" (caddr instr) proc)
      (emit-load-operand port "x1" (cadddr instr) proc)
      (emit-asm-line port "    bl _hop_vector_ref")
      (emit-store-operand port "x0" (cadr instr) proc))
    ((vector-set!)
      (emit-load-operand port "x0" (caddr instr) proc)
      (emit-load-operand port "x1" (cadddr instr) proc)
      (emit-load-operand port "x2" (cadddr (cdr instr)) proc)
      (emit-asm-line port "    bl _hop_vector_set")
      (emit-store-operand port "x0" (cadr instr) proc))
    ((is-vector)
      (emit-tag-compare port (caddr instr) vector-tag proc)
      (emit-bool-result port "eq" (cadr instr) proc))
    ((load-box)
       (emit-load-box-address port (caddr instr) proc)
       (emit-asm-line port "    ldr x10, [x9, #8]")
       (emit-store-operand port "x10" (cadr instr) proc))
    ((load-closure-env)
      (emit-load-closure-address port (caddr instr) proc)
      (emit-asm-line port
                     (string-append "    ldr x10, [x9, #"
                                    (number->string (+ 16 (* 8 (cadddr instr))))
                                    "]"))
      (emit-store-operand port "x10" (cadr instr) proc))
    ((load-global)
      (emit-runtime-global-read port (cadr instr) (caddr instr) proc))
    ((load-car)
      (emit-checked-pair-load port (cadr instr) (caddr instr) 8 "_hop_car" proc))
    ((load-cdr)
      (emit-checked-pair-load port (cadr instr) (caddr instr) 16 "_hop_cdr" proc))
    ((unsafe-load-car)
      (emit-unsafe-pair-load port (cadr instr) (caddr instr) 8 "_hop_car" proc))
    ((unsafe-load-cdr)
      (emit-unsafe-pair-load port (cadr instr) (caddr instr) 16 "_hop_cdr" proc))
    ((is-pair)
      (emit-tag-compare port (caddr instr) pair-tag proc)
      (emit-bool-result port "eq" (cadr instr) proc))
    ((is-null)
      (emit-immediate-compare port (caddr instr) null-immediate proc)
      (emit-bool-result port "eq" (cadr instr) proc))
    ((is-symbol)
      (emit-tag-compare port (caddr instr) symbol-tag proc)
      (emit-bool-result port "eq" (cadr instr) proc))
    ((store-box)
        (emit-load-box-address port (cadr instr) proc)
        (emit-load-operand port "x10" (caddr instr) proc)
        (emit-asm-line port "    str x10, [x9, #8]"))
    ((store-global)
      (emit-runtime-global-write port (cadr instr) (caddr instr) proc))
    ((alloc-closure)
     (emit-alloc-closure port (cadr instr) (caddr instr) (cadddr instr) (cddddr instr) proc))
    ((alloc-closure-variadic)
     (emit-alloc-closure-variadic port (cadr instr) (caddr instr) (cadddr instr) (cddddr instr) proc))
    ((call-indirect)
     (emit-call-helper port (cadr instr) #f))
    ((call-label)
      (emit-call-label port (cadr instr) #f))
    ((tail-call-indirect)
     (emit-call-helper port (cadr instr) #t))
    ((tail-call-label)
      (emit-call-label port (cadr instr) #t))
    ((branch-if)
      (emit-immediate-compare port (cadr instr) false-immediate proc)
      (emit-conditional-branch port "ne" "eq" (caddr instr) (cadddr instr)
                               next-label))
    ((cmp-branch)
      (when (memq (cadr instr) '(safe-= safe-< safe->))
        (emit-safe-compare-guard port (cadr instr) (caddr instr) (cadddr instr) proc))
      (emit-compare port (caddr instr) (cadddr instr) proc)
      (let ((condition (comparison-condition (cadr instr))))
        (emit-conditional-branch port (car condition) (cdr condition)
                                 (car (cddddr instr))
                                 (cadr (cddddr instr))
                                 next-label)))
    ((jump)
     (unless (eq? (cadr instr) next-label)
       (emit-asm-line port
                      (string-append "    b L"
                                     (symbol->string (cadr instr))))))
    ((ret)
     (emit-asm-line port "    ret"))
    (else
     (error "Unsupported machine instruction in assembly emission" instr))))

(define (emit-machine-block port block proc first? next-label)
  (define (entry-setup-instruction? instr)
    (and (pair? instr)
         (or (memq (car instr) '(allocate-frame save-callee-saved init-frame-slots gc-push-frame))
              (and (eq? (car instr) 'move)
                   (pair? (caddr instr))
                   (memq (car (caddr instr)) '(arg-register incoming-stack-arg))))))
  (let* ((instrs (machine-block-instructions block))
         (prologue
          (if first?
              (let loop ((rest instrs) (result '()))
                (if (and (pair? rest)
                         (entry-setup-instruction? (car rest)))
                    (loop (cdr rest) (append result (list (car rest))))
                    result))
              '()))
         (body
          (if first?
              (list-tail instrs (length prologue))
              instrs)))
    (for-each (lambda (instr)
                (emit-machine-instruction port instr proc next-label))
              prologue)
    (if (or (not first?) (machine-block-label block))
        (emit-asm-line port
                       (string-append "L"
                                      (symbol->string (machine-block-label block))
                                      ":")))
    (for-each (lambda (instr)
                (emit-machine-instruction port instr proc next-label))
              body)))

(define (emit-machine-procedure port proc exported-name)
  (emit-asm-line port (string-append ".globl " (asm-name exported-name)))
  (emit-machine-procedure-body port proc exported-name))

;; Emits proc under a file-local (non-.globl) label. Used for every compiled
;; procedure but the body in a multi-unit build: each unit's CFA names its
;; procedures cfa.proc.N from its own counter, so two units' labels collide
;; if both are external symbols. Nothing outside a unit ever references one
;; of its procedure labels directly -- cross-unit calls go through global
;; cells holding closures -- so keeping them local to the object file is
;; enough to make them unique at link time.
(define (emit-local-machine-procedure port proc)
  (emit-machine-procedure-body port proc (machine-procedure-name proc)))

(define (emit-machine-procedure-body port proc exported-name)
  (emit-asm-line port (string-append ".p2align 2"))
  (emit-asm-line port (string-append (asm-name exported-name) ":"))
  (begin-slow-stubs! (asm-name exported-name))
  (let loop ((blocks (machine-procedure-blocks proc)) (first? #t))
    (if (null? blocks)
        'done
        (begin
          (emit-machine-block port (car blocks) proc first?
                              (and (pair? (cdr blocks))
                                   (machine-block-label (cadr blocks))))
          (loop (cdr blocks) #f))))
  (flush-slow-stubs! port)
  (newline port))

(define (emit-procedure-descriptor port proc)
  (emit-asm-line port (string-append ".p2align 3"))
  (emit-asm-line port (string-append (gc-desc-label (machine-procedure-name proc)) ":"))
  (emit-asm-line port
                 (string-append "    .quad "
                                (number->string (machine-procedure-frame-slots proc))))
  (emit-asm-line port
                 (string-append "    .quad "
                                (number->string (- (stack-size-for proc)
                                                   (procedure-outgoing-bytes proc)
                                                   (procedure-saved-bytes proc))))))

;; Each top-level global gets its own labeled 8-byte cell instead of a shared
;; array slot -- see (hop pass lower)'s global-cell-label. emit-aarch64-program
;; also builds a root table of their addresses (below) so the GC can still
;; find and scan every one of them without a single indexed array to walk.
;;
;; Only a label in exported-labels gets .globl; every other cell (a unit's
;; internal, non-exported defines, and every quote-hoisted literal, which is
;; never exported) gets .private_extern instead -- still resolvable via
;; `extern` by another translation unit at static-link time (the generated
;; link stub always needs that, to rebuild the merged GC root table across
;; every linked unit), but no longer visible in the final binary's
;; exported/dynamic symbol table. Mach-O only: this project always targets
;; `clang -arch arm64`.
(define (emit-global-cells port global-labels exported-labels)
  (for-each
   (lambda (label)
     (emit-asm-line port (string-append (if (memq label exported-labels)
                                             ".globl " ".private_extern ")
                                         (asm-name label)))
     (emit-asm-line port ".p2align 3")
     (emit-asm-line port (string-append (asm-name label) ":"))
     (emit-asm-line port
                    (string-append "    .quad "
                                   (number->string uninitialized-immediate))))
   global-labels))

(define (global-roots-label) (asm-name 'hop_global_roots))
(define (global-root-count-label) (asm-name 'hop_global_root_count))

;; Only the single self-contained emit-aarch64-program path (below) ever
;; emits this: it's the whole program's own complete root table. A unit
;; compiled for multi-unit linking (emit-unit-aarch64-program) does not --
;; there, the generated link stub reconstructs one merged root table by
;; reading every linked unit's interface file (see compiler.scm), because by
;; then it knows every unit's global cells and can build one real array
;; instead of each unit guessing at a naming scheme to avoid colliding with
;; the others.
(define (emit-global-roots port global-labels)
  (let ((count-label (global-root-count-label))
        (roots-label (global-roots-label)))
    (emit-asm-line port (string-append ".globl " count-label))
    (emit-asm-line port ".p2align 3")
    (emit-asm-line port (string-append count-label ":"))
    (emit-asm-line port
                   (string-append "    .quad "
                                  (number->string (length global-labels))))
    (emit-asm-line port (string-append ".globl " roots-label))
    (emit-asm-line port ".p2align 3")
    (emit-asm-line port (string-append roots-label ":"))
    (for-each
     (lambda (label)
       (emit-asm-line port (string-append "    .quad " (asm-name label))))
     global-labels)))

(define (asciz-escape text)
  (let loop ((chars (string->list text)) (result '()))
    (if (null? chars)
        (list->string (reverse result))
        (let ((ch (car chars)))
          (loop (cdr chars)
                (if (or (char=? ch #\") (char=? ch #\\))
                    (cons ch (cons #\\ result))
                    (cons ch result)))))))

(define (symbol-name-label index)
  (string-append "Lsymname." (number->string index)))

(define (emit-symbol-table port)
  ;; hop_symbol_hashes[i]/hop_symbol_name_ptrs[i] are parallel arrays; the
  ;; runtime finds a symbol's name with a linear scan for a matching hash
  ;; (see hop_symbol_name in runtime.c). Interning order is most-recent-first
  ;; in the assq list; emission order doesn't matter since lookup is by
  ;; value, not position. Same one-unit-only caveat as emit-global-roots.
  (let ((entries (reverse interned-symbols))
        (count-label (asm-name 'hop_symbol_count))
        (hashes-label (asm-name 'hop_symbol_hashes))
        (name-ptrs-label (asm-name 'hop_symbol_name_ptrs)))
    (emit-asm-line port (string-append ".globl " count-label))
    (emit-asm-line port ".p2align 3")
    (emit-asm-line port (string-append count-label ":"))
    (emit-asm-line port
                   (string-append "    .quad " (number->string (length entries))))
    (emit-asm-line port (string-append ".globl " hashes-label))
    (emit-asm-line port ".p2align 3")
    (emit-asm-line port (string-append hashes-label ":"))
    (let loop ((rest entries) (index 0))
      (unless (null? rest)
        (emit-asm-line port
                       (string-append "    .quad " (number->string (cdr (car rest)))))
        (loop (cdr rest) (+ index 1))))
    (emit-asm-line port (string-append ".globl " name-ptrs-label))
    (emit-asm-line port ".p2align 3")
    (emit-asm-line port (string-append name-ptrs-label ":"))
    (let loop ((rest entries) (index 0))
      (unless (null? rest)
        (emit-asm-line port
                       (string-append "    .quad " (symbol-name-label index)))
        (loop (cdr rest) (+ index 1))))
    (let loop ((rest entries) (index 0))
      (unless (null? rest)
        (emit-asm-line port (string-append (symbol-name-label index) ":"))
        (emit-asm-line port
                       (string-append "    .asciz \""
                                      (asciz-escape
                                       (symbol->string (car (car rest))))
                                      "\""))
        (loop (cdr rest) (+ index 1))))))

;; The original, self-contained single-unit path: everything a program needs
;; -- code, storage cells, a complete root table, and a complete
;; symbol-printing table -- in one file with the plain unqualified names
;; runtime.c expects, exactly as before separate compilation existed.
(define (emit-aarch64-program port entry-proc procedures global-labels)
  (reset-interned-symbols!)
  (emit-asm-line port ".text")
  (emit-asm-line port "")
  (emit-machine-procedure port entry-proc (machine-procedure-name entry-proc))
  (for-each (lambda (proc)
              (emit-machine-procedure port proc (machine-procedure-name proc)))
            procedures)
  (emit-asm-line port ".data")
  (emit-asm-line port "")
  (emit-procedure-descriptor port entry-proc)
  (for-each (lambda (proc)
              (emit-procedure-descriptor port proc))
            procedures)
  ;; No define-library exports exist in this self-contained single-unit
  ;; path, so every cell is "exported" -- .globl for all of them, same as
  ;; before this parameter existed.
  (emit-global-cells port global-labels global-labels)
  (emit-global-roots port global-labels)
  (emit-symbol-table port))

;; The multi-unit path: emits code and this unit's own storage cells (using
;; whatever label body-proc's own name already is -- e.g. a unit-qualified
;; hop_unit_body_<id> from (hop pass lower)'s unit-body-label, not the
;; reserved scheme_entry) but no root table or symbol-printing table. Those
;; only make sense assembled from every unit being linked together, which a
;; single unit's own compile can't see -- that's the generated link stub's
;; job (see compiler.scm). Returns this unit's own (symbol . hash) interning
;; table so the caller can save it into this unit's interface file for the
;; link step to read later.
(define (emit-unit-aarch64-program port body-proc procedures global-labels exported-labels)
  (reset-interned-symbols!)
  (emit-asm-line port ".text")
  (emit-asm-line port "")
  (emit-machine-procedure port body-proc (machine-procedure-name body-proc))
  (for-each (lambda (proc)
              (emit-local-machine-procedure port proc))
            procedures)
  (emit-asm-line port ".data")
  (emit-asm-line port "")
  (emit-procedure-descriptor port body-proc)
  (for-each (lambda (proc)
              (emit-procedure-descriptor port proc))
            procedures)
  (emit-global-cells port global-labels exported-labels)
  (reverse interned-symbols))

)) ; end define-library
