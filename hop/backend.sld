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
          display-cfg
          display-procedure-cfg
          display-machine-procedure)
  (import (scheme base)
          (scheme cxr)
          (scheme write)
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
     ((and (pair? rhs) (eq? (car rhs) 'closure-call))
      (list `(call ,dst ,@(cdr rhs))))
     ((and (pair? rhs) (eq? (car rhs) 'direct-call))
      (list `(call-known ,dst ,@(cdr rhs))))
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

(define (select-machine-procedure name params cfg)
  (let ((param-locations (make-param-locations params)))
    (let loop ((blocks cfg)
               (first? #t)
               (result '()))
      (if (null? blocks)
          (make-machine-procedure name
                                  params
                                  param-locations
                                  (reverse result)
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
    ((alloc-box load-box load-car load-cdr is-pair is-null is-vector vector-length load-closure-env)
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
     (let loop ((rest (cdddr instr)) (result '()))
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
    ((branch-if ret)
     (if (symbol? (cadr instr)) (list (cadr instr)) '()))
    ((jump) '())
    (else (error "Unknown machine instruction in use analysis" instr))))

(define (machine-instr-defs instr)
  (case (car instr)
    ((move-in move alloc-pair alloc-vector alloc-box load-box load-car load-cdr
             unsafe-load-car unsafe-load-cdr is-pair is-null is-vector
             vector-length vector-ref vector-set!
             load-closure-env load-global alloc-closure call call-known)
      (list (cadr instr)))
    ((binop safe-binop)
      (list (caddr instr)))
    ((store-box store-global branch-if jump ret tail-call tail-call-known) '())
    (else (error "Unknown machine instruction in def analysis" instr))))

(define (machine-instr-bias-source instr)
  (case (car instr)
    ((move)
     (if (symbol? (caddr instr))
         (caddr instr)
         #f))
    (else #f)))

(define (machine-block-use block)
  (let loop ((instrs (machine-block-instructions block))
             (defs '())
             (uses '()))
    (if (null? instrs)
        uses
        (let* ((instr (car instrs))
               (instr-uses (set-difference (machine-instr-uses instr) defs))
               (instr-defs (machine-instr-defs instr)))
          (loop (cdr instrs)
                (set-union defs instr-defs)
                (set-union uses instr-uses))))))

(define (machine-block-def block)
  (let loop ((instrs (machine-block-instructions block)) (defs '()))
    (if (null? instrs)
        defs
        (loop (cdr instrs)
              (set-union defs (machine-instr-defs (car instrs)))))))

(define (compute-liveness blocks)
  (let* ((count (length blocks))
         (use-vec (list->vector (map machine-block-use blocks)))
         (def-vec (list->vector (map machine-block-def blocks)))
         (in-vec (make-vector count '()))
         (out-vec (make-vector count '())))
    (let loop ()
      (let ((changed #f))
        (do ((i (- count 1) (- i 1)))
            ((< i 0))
          (let* ((block (list-ref blocks i))
                 (successors (machine-block-successors block))
                 (new-out
                  (let succ-loop ((rest successors) (result '()))
                    (if (null? rest)
                        result
                        (succ-loop (cdr rest)
                                   (set-union result
                                              (vector-ref in-vec (car rest)))))))
                 (new-in
                  (set-union (vector-ref use-vec i)
                             (set-difference new-out (vector-ref def-vec i)))))
            (if (not (set-equal? new-out (vector-ref out-vec i)))
                (begin
                  (vector-set! out-vec i new-out)
                  (set! changed #t)))
            (if (not (set-equal? new-in (vector-ref in-vec i)))
                (begin
                  (vector-set! in-vec i new-in)
                  (set! changed #t)))))
        (if changed
            (loop)
            (values in-vec out-vec))))))

(define (compute-instruction-live-before blocks out-vec)
  (let block-loop ((remaining blocks) (index 0) (result '()))
    (if (null? remaining)
        (reverse result)
        (let ((instrs (machine-block-instructions (car remaining))))
          (let instr-loop ((rest (reverse instrs))
                           (live-after (vector-ref out-vec index))
                           (live-befores '()))
            (if (null? rest)
                (block-loop (cdr remaining)
                            (+ index 1)
                            (cons live-befores result))
                (let* ((instr (car rest))
                       (defs (machine-instr-defs instr))
                       (uses (machine-instr-uses instr))
                       (live-before
                        (set-union uses
                                   (set-difference live-after defs))))
                  (instr-loop (cdr rest)
                              live-before
                              (cons live-before live-befores)))))))))

;;; ── Live interval helpers ──────────────────────────────────────────────────

(define (interval-start interval) (cadr interval))
(define (interval-end interval) (caddr interval))

(define (update-interval! table var point)
  (let ((entry (assoc var table)))
    (if entry
        (let ((interval (cdr entry)))
          (set-car! interval (min (car interval) point))
          (set-cdr! interval (max (cdr interval) point)))
        (set! table (cons (cons var (cons point point)) table))))
  table)

(define (collect-intervals blocks in-vec out-vec)
  (let loop-blocks ((remaining blocks)
                    (index 0)
                    (point 0)
                    (intervals '()))
    (if (null? remaining)
        (let convert ((rest intervals) (result '()))
          (if (null? rest)
              result
              (let* ((entry (car rest))
                     (range (cdr entry)))
                (convert (cdr rest)
                         (cons (list (car entry) (car range) (cdr range))
                               result)))))
        (let* ((block (car remaining))
               (block-start point)
               (intervals-with-live-in
                (let live-in-loop ((vars (vector-ref in-vec index))
                                   (current intervals))
                  (if (null? vars)
                      current
                      (live-in-loop (cdr vars)
                                    (update-interval! current (car vars) block-start)))))
               (instrs (machine-block-instructions block)))
          (let loop-instrs ((rest instrs)
                            (next-point point)
                            (current intervals-with-live-in))
            (if (null? rest)
                (let* ((block-end (if (= next-point block-start)
                                      block-start
                                      (- next-point 1)))
                       (intervals-with-live-out
                        (let live-out-loop ((vars (vector-ref out-vec index))
                                            (updated current))
                          (if (null? vars)
                              updated
                              (live-out-loop (cdr vars)
                                             (update-interval! updated (car vars) block-end))))))
                  (loop-blocks (cdr remaining)
                               (+ index 1)
                               next-point
                               intervals-with-live-out))
                (let* ((instr (car rest))
                       (uses (machine-instr-uses instr))
                       (defs (machine-instr-defs instr))
                       (with-uses
                        (let use-loop ((vars uses) (updated current))
                          (if (null? vars)
                              updated
                              (use-loop (cdr vars)
                                        (update-interval! updated (car vars) next-point)))))
                       (with-defs
                        (let def-loop ((vars defs) (updated with-uses))
                          (if (null? vars)
                              updated
                              (def-loop (cdr vars)
                                (update-interval! updated (car vars) next-point))))))
                  (loop-instrs (cdr rest)
                               (+ next-point 1)
                               with-defs))))))))

(define (insert-by-start interval intervals)
  (if (null? intervals)
      (list interval)
      (if (< (interval-start interval) (interval-start (car intervals)))
          (cons interval intervals)
          (cons (car intervals)
                (insert-by-start interval (cdr intervals))))))

(define (sort-intervals-by-start intervals)
  (let loop ((rest intervals) (result '()))
    (if (null? rest)
        result
        (loop (cdr rest)
              (insert-by-start (car rest) result)))))

(define (collect-move-biases blocks)
  (let block-loop ((remaining blocks) (biases '()))
    (if (null? remaining)
        biases
        (let instr-loop ((instrs (machine-block-instructions (car remaining)))
                         (current biases))
          (if (null? instrs)
              (block-loop (cdr remaining) current)
              (let* ((instr (car instrs))
                     (defs (machine-instr-defs instr))
                     (bias-source (machine-instr-bias-source instr)))
                (instr-loop
                 (cdr instrs)
                 (if (and bias-source (pair? defs))
                     (cons (cons (car defs) bias-source) current)
                     current))))))))

(define (insert-active interval active)
  (if (null? active)
      (list interval)
      (if (< (interval-end interval) (interval-end (car active)))
          (cons interval active)
          (cons (car active)
                (insert-active interval (cdr active))))))

(define (register-order register)
  (let loop ((rest aarch64-callee-saved) (index 0))
    (cond
      ((null? rest) index)
      ((eq? (car rest) register) index)
      (else (loop (cdr rest) (+ index 1))))))

;;; ── Linear-scan allocation ─────────────────────────────────────────────────

(define (insert-register register registers)
  (if (null? registers)
      (list register)
      (if (< (register-order register) (register-order (car registers)))
          (cons register registers)
          (cons (car registers)
                (insert-register register (cdr registers))))))

(define (remove-register register registers)
  (cond
    ((null? registers) '())
    ((eq? (car registers) register) (cdr registers))
    (else
     (cons (car registers)
           (remove-register register (cdr registers))))))

(define (lookup-bias biases var)
  (let ((binding (assoc var biases)))
    (if binding
        (cdr binding)
        #f)))

(define (preferred-register-for var homes biases)
  (let ((preferred-var (lookup-bias biases var)))
    (if preferred-var
        (let ((preferred-home (lookup-home homes preferred-var)))
          (if (and (pair? preferred-home) (eq? (car preferred-home) 'register))
              (cadr preferred-home)
              #f))
        #f)))

(define (linear-scan-allocate intervals biases)
  (let loop ((remaining (sort-intervals-by-start intervals))
             (active '())
             (free-registers aarch64-callee-saved)
             (homes '())
             (next-slot 0))
    (if (null? remaining)
        (values homes next-slot)
        (let* ((current (car remaining))
               (current-var (car current))
               (start (interval-start current))
               (preferred-var (lookup-bias biases current-var))
               (preferred-register
                (preferred-register-for current-var homes biases)))
          (let expire ((rest active)
                       (still-active '())
                       (available free-registers))
            (if (null? rest)
                (if (null? available)
                    (loop (cdr remaining)
                          still-active
                          available
                          (cons (cons (car current) `(stack-slot ,next-slot)) homes)
                          (+ next-slot 1))
                    (let* ((register
                            (if (and preferred-register
                                     (memq preferred-register available))
                                preferred-register
                                (car available)))
                           (remaining-registers
                            (remove-register register available))
                           (new-active
                            (insert-active
                             (list (car current)
                                   (interval-start current)
                                   (interval-end current)
                                   register)
                             still-active)))
                      (loop (cdr remaining)
                            new-active
                            remaining-registers
                            (cons (cons (car current) `(register ,register)) homes)
                            next-slot)))
                (let* ((entry (car rest))
                       (entry-var (car entry))
                       (end (caddr entry))
                       (register (cadddr entry)))
                  (if (or (< end start)
                          (and preferred-var
                               (eq? entry-var preferred-var)
                               (= end start)))
                      (expire (cdr rest)
                              still-active
                              (insert-register register available))
                      (expire (cdr rest)
                              (insert-active entry still-active)
                              available)))))))))

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

(define (lookup-home homes operand)
  (if (symbol? operand)
      (let ((binding (assoc operand homes)))
        (if binding
            (cdr binding)
            operand))
      operand))

(define (lookup-root-home root-homes var)
  (let ((binding (assoc var root-homes)))
    (if binding
        (cdr binding)
        #f)))

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
                     ,@(map (lambda (operand) (lookup-home homes operand))
                            (cdddr instr))))
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
    ((tail-call)
     `(tail-call ,(lookup-home homes (cadr instr))
                 ,@(map (lambda (operand) (lookup-home homes operand))
                        (cddr instr))))
    ((tail-call-known)
     `(tail-call-known ,(cadr instr)
                       ,@(map (lambda (operand) (lookup-home homes operand))
                              (cddr instr))))
    ((branch-if)
     `(branch-if ,(lookup-home homes (cadr instr))
                 ,(caddr instr)
                 ,(cadddr instr)))
    ((jump) instr)
    ((ret)
     `(ret ,(lookup-home homes (cadr instr))))
    (else
     (error "Unknown machine instruction during allocation" instr))))

(define (safepoint-machine-instruction? instr)
  (memq (car instr) '(alloc-box alloc-pair alloc-vector alloc-closure call call-known)))

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
          homes
          root-homes)
  (append
   (if (safepoint-machine-instruction? instr)
       (live-root-syncs live-before homes root-homes)
       '())
    (instruction->list (rewrite-machine-instruction instr homes))
    (if (safepoint-machine-instruction? instr)
        (live-root-reloads live-after (cadr instr) homes root-homes)
        '())))

(define (rewrite-machine-block-instructions instrs live-befores homes root-homes)
  (if (null? instrs)
      '()
      (let ((live-after (if (null? (cdr live-befores)) '() (cadr live-befores))))
        (append
         (rewrite-machine-instruction-with-safepoint-sync
          (car instrs)
          (car live-befores)
          live-after
          homes
          root-homes)
         (rewrite-machine-block-instructions
          (cdr instrs)
          (cdr live-befores)
          homes
          root-homes)))))

(define (allocate-machine-procedure proc)
  (let ((blocks (machine-procedure-blocks proc)))
    (let-values (((in-vec out-vec) (compute-liveness blocks)))
      (let* ((instruction-live-before
              (compute-instruction-live-before blocks out-vec))
             (biases (collect-move-biases blocks)))
        (let-values (((homes next-slot)
                      (linear-scan-allocate
                       (collect-intervals blocks in-vec out-vec)
                       biases)))
          (let-values (((root-homes frame-slots)
                        (allocate-root-homes homes next-slot)))
            (let* ((rewritten-blocks
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
                                homes
                                root-homes)
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

(define (cfg->allocated-machine-procedure name params cfg)
  (finalize-machine-procedure
   (allocate-machine-procedure
     (select-machine-procedure name params cfg))))

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
(define null-immediate 20)
(define false-immediate 36)
(define true-immediate 52)
(define uninitialized-immediate 68)
(define unsafe-pair-load-mode 'fast)

(define (encode-immediate value)
  (cond
    ((null? value) null-immediate)
    ((eq? value #f) false-immediate)
    ((eq? value #t) true-immediate)
    ((number? value) (ash value fixnum-shift))
    (else (error "Expected immediate value" value))))

(define (immediate->string value)
  (number->string (encode-immediate value)))

(define (emit-load-operand port target operand proc)
  (cond
    ((literal-expr? operand)
     (emit-asm-line port
                    (string-append "    mov " target ", #"
                                   (immediate->string operand))))
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

(define (emit-move port dst src proc)
  (if (equal? dst src)
      'done
      (begin
        (emit-load-operand port "x9" src proc)
        (emit-store-operand port "x9" dst proc))))

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
  (emit-asm-line port
                 (string-append "    csel x11, x12, x11, " condition))
  (emit-store-operand port "x11" dst proc))

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

(define (emit-safe-binop port op dst a b proc)
  (emit-load-operand port "x0" a proc)
  (emit-load-operand port "x1" b proc)
  (case op
    ((safe-+) (emit-asm-line port "    bl _hop_safe_add"))
    ((safe--) (emit-asm-line port "    bl _hop_safe_sub"))
    ((safe-*) (emit-asm-line port "    bl _hop_safe_mul"))
    ((safe-=) (emit-asm-line port "    bl _hop_safe_eq"))
    ((safe-<) (emit-asm-line port "    bl _hop_safe_lt"))
    ((safe->) (emit-asm-line port "    bl _hop_safe_gt"))
    (else (error "Unknown safe binop op" op)))
  (emit-store-operand port "x0" dst proc))

(define (emit-runtime-global-read port dst slot proc)
  (emit-asm-line port
                 (string-append "    mov x0, #"
                                (number->string slot)))
  (emit-asm-line port "    bl _hop_global_ref")
  (emit-store-operand port "x0" dst proc))

(define (emit-runtime-global-write port slot operand proc)
  (emit-asm-line port
                 (string-append "    mov x0, #"
                                (number->string slot)))
  (emit-load-operand port "x1" operand proc)
  (emit-asm-line port "    bl _hop_global_set"))

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
  (emit-load-operand port "x9" operand proc)
  (emit-asm-line port
                 (string-append "    mov x10, #"
                                (number->string immediate)))
  (emit-asm-line port "    cmp x9, x10"))

(define (emit-binop port op dst lhs rhs proc)
  (emit-load-operand port "x9" lhs proc)
  (emit-load-operand port "x10" rhs proc)
  (cond
    ((eq? op '+)
     (emit-asm-line port "    add x11, x9, x10")
     (emit-store-operand port "x11" dst proc))
    ((eq? op '-)
     (emit-asm-line port "    sub x11, x9, x10")
     (emit-store-operand port "x11" dst proc))
    ((eq? op '*)
     (emit-asm-line port "    mul x11, x9, x10")
     (emit-asm-line port
                    (string-append "    asr x11, x11, #"
                                   (number->string fixnum-shift)))
     (emit-store-operand port "x11" dst proc))
    ((eq? op '=)
      (emit-asm-line port "    cmp x9, x10")
      (emit-bool-result port "eq" dst proc))
    ((eq? op '<)
      (emit-asm-line port "    cmp x9, x10")
      (emit-bool-result port "lt" dst proc))
    ((eq? op '>)
      (emit-asm-line port "    cmp x9, x10")
      (emit-bool-result port "gt" dst proc))
    (else
     (error "Unsupported primop in assembly emission" op)))
  'done)

(define (register-name operand)
  (symbol->string (cadr operand)))

(define (emit-alloc-closure port dst proc-name captures proc)
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
          (emit-asm-line port "    bl _hop_alloc_closure_n")))
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

(define (emit-machine-instruction port instr proc)
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
      (emit-load-operand port "x0" (caddr instr) proc)
      (emit-load-operand port "x1" (cadddr instr) proc)
      (emit-asm-line port "    bl _hop_alloc_pair")
      (emit-store-operand port "x0" (cadr instr) proc))
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
      (emit-load-operand port "x9" (caddr instr) proc)
      (emit-asm-line port
                     (string-append "    and x10, x9, #"
                                    (number->string tag-mask)))
      (emit-asm-line port
                     (string-append "    cmp x10, #"
                                     (number->string vector-tag)))
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
      (emit-runtime-unary-call port "_hop_car" (cadr instr) (caddr instr) proc))
    ((load-cdr)
      (emit-runtime-unary-call port "_hop_cdr" (cadr instr) (caddr instr) proc))
    ((unsafe-load-car)
      (emit-unsafe-pair-load port (cadr instr) (caddr instr) 8 "_hop_car" proc))
    ((unsafe-load-cdr)
      (emit-unsafe-pair-load port (cadr instr) (caddr instr) 16 "_hop_cdr" proc))
    ((is-pair)
      (emit-load-operand port "x9" (caddr instr) proc)
      (emit-asm-line port
                     (string-append "    and x10, x9, #"
                                    (number->string tag-mask)))
      (emit-asm-line port
                     (string-append "    cmp x10, #"
                                     (number->string pair-tag)))
      (emit-bool-result port "eq" (cadr instr) proc))
    ((is-null)
      (emit-immediate-compare port (caddr instr) null-immediate proc)
      (emit-bool-result port "eq" (cadr instr) proc))
    ((store-box)
        (emit-load-box-address port (cadr instr) proc)
        (emit-load-operand port "x10" (caddr instr) proc)
        (emit-asm-line port "    str x10, [x9, #8]"))
    ((store-global)
      (emit-runtime-global-write port (cadr instr) (caddr instr) proc))
    ((alloc-closure)
     (emit-alloc-closure port (cadr instr) (caddr instr) (cdddr instr) proc))
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
      (emit-asm-line port
                     (string-append "    b.ne L"
                                    (symbol->string (caddr instr))))
      (emit-asm-line port
                     (string-append "    b L"
                                   (symbol->string (cadddr instr)))))
    ((jump)
     (emit-asm-line port
                    (string-append "    b L"
                                   (symbol->string (cadr instr)))))
    ((ret)
     (emit-asm-line port "    ret"))
    (else
     (error "Unsupported machine instruction in assembly emission" instr))))

(define (emit-machine-block port block proc first?)
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
                (emit-machine-instruction port instr proc))
              prologue)
    (if (or (not first?) (machine-block-label block))
        (emit-asm-line port
                       (string-append "L"
                                      (symbol->string (machine-block-label block))
                                      ":")))
    (for-each (lambda (instr)
                (emit-machine-instruction port instr proc))
              body)))

(define (emit-machine-procedure port proc exported-name)
  (emit-asm-line port (string-append ".globl " (asm-name exported-name)))
  (emit-asm-line port (string-append ".p2align 2"))
  (emit-asm-line port (string-append (asm-name exported-name) ":"))
  (let loop ((blocks (machine-procedure-blocks proc)) (first? #t))
    (if (null? blocks)
        'done
        (begin
          (emit-machine-block port (car blocks) proc first?)
          (loop (cdr blocks) #f))))
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

(define (emit-global-slots port global-count)
  (emit-asm-line port (string-append ".globl " (asm-name 'hop_global_slot_count)))
  (emit-asm-line port ".p2align 3")
  (emit-asm-line port (string-append (asm-name 'hop_global_slot_count) ":"))
  (emit-asm-line port
                 (string-append "    .quad "
                                (number->string global-count)))
  (emit-asm-line port (string-append ".globl " (asm-name 'hop_global_slots)))
  (emit-asm-line port ".p2align 3")
  (emit-asm-line port (string-append (asm-name 'hop_global_slots) ":"))
  (let loop ((index 0))
    (if (= index global-count)
        'done
        (begin
          (emit-asm-line port
                         (string-append "    .quad "
                                        (number->string uninitialized-immediate)))
          (loop (+ index 1))))))

(define (emit-aarch64-program port entry-proc procedures global-count)
  (emit-asm-line port ".text")
  (emit-asm-line port "")
  (emit-machine-procedure port entry-proc 'scheme_entry)
  (for-each (lambda (proc)
              (emit-machine-procedure port proc (machine-procedure-name proc)))
            procedures)
  (emit-asm-line port ".data")
  (emit-asm-line port "")
  (emit-procedure-descriptor port entry-proc)
  (for-each (lambda (proc)
              (emit-procedure-descriptor port proc))
            procedures)
  (emit-global-slots port global-count))

)) ; end define-library
