(define-library (hop pass cfg)
  ;;; Pass 5: Build CFG + CFG optimization passes (5.5, 5.5b, 5.6, 5.7)
  (export make-basic-block
          basic-block?
          basic-block-label
          basic-block-instructions
          basic-block-successors
          set-basic-block-successors!
          build-cfg
          optimize-unsafe-car-cdr-cfg
          optimize-unsafe-arith-cfg
          constant-fold-cfg
          eliminate-dead-writes-cfg)
  (import (scheme base)
          (scheme cxr)
          (srfi 69)
          (hop utils))
  (begin

(define-record-type <basic-block>
  (make-basic-block label instructions)
  basic-block?
  (label basic-block-label)
  (instructions basic-block-instructions)
  (successors basic-block-successors set-basic-block-successors!))

(define (build-cfg tac-instrs)
  (define (terminator? instr)
    (and (pair? instr)
         (memq (car instr) '(if goto return tail-call direct-tail-call))))

  (define (is-leader? index instrs)
    (let ((instr (list-ref instrs index)))
      (or (= index 0)
          (and (pair? instr) (eq? (car instr) 'label))
          (and (> index 0)
               (terminator? (list-ref instrs (- index 1)))))))

  (define (split-into-blocks instrs)
    (let* ((len (length instrs))
           (leaders (make-vector len #f)))
      (do ((i 0 (+ i 1)))
          ((= i len))
        (vector-set! leaders i (is-leader? i instrs)))
      (let loop ((i 0) (blocks '()) (current-block '()) (current-label #f))
        (cond
         ((= i len)
          (if (null? current-block)
              (reverse blocks)
              (reverse (cons (make-basic-block current-label
                                               (reverse current-block))
                             blocks))))
         ((vector-ref leaders i)
          (if (null? current-block)
              (let ((instr (list-ref instrs i)))
                (loop (+ i 1)
                      blocks
                      (list instr)
                      (if (and (pair? instr) (eq? (car instr) 'label))
                          (cadr instr)
                          #f)))
              (let ((instr (list-ref instrs i)))
                (loop (+ i 1)
                      (cons (make-basic-block current-label
                                              (reverse current-block))
                            blocks)
                      (list instr)
                      (if (and (pair? instr) (eq? (car instr) 'label))
                          (cadr instr)
                          #f)))))
         (else
          (loop (+ i 1)
                blocks
                (cons (list-ref instrs i) current-block)
                current-label))))))

  (define (find-successors blocks)
    (let ((label->block (make-hash-table)))
      (do ((i 0 (+ i 1)) (block-list blocks (cdr block-list)))
          ((null? block-list))
        (let* ((block (car block-list))
               (label (basic-block-label block)))
          (when label
            (hash-table-set! label->block label i))))
      (do ((i 0 (+ i 1)) (block-list blocks (cdr block-list)))
          ((null? block-list))
        (let* ((block (car block-list))
               (instrs (basic-block-instructions block))
               (last-instr (if (null? instrs) #f (car (reverse instrs)))))
          (cond
           ((not last-instr)
            (set-basic-block-successors! block '()))
           ((and (pair? last-instr) (eq? (car last-instr) 'if))
            (let ((then-label (caddr last-instr))
                  (else-label (cadddr last-instr)))
              (set-basic-block-successors!
               block
               (list (hash-table-ref/default label->block then-label #f)
                     (hash-table-ref/default label->block else-label #f)))))
           ((and (pair? last-instr) (eq? (car last-instr) 'goto))
            (let ((target-label (cadr last-instr)))
              (set-basic-block-successors!
               block
               (list (hash-table-ref/default label->block target-label #f)))))
           ((and (pair? last-instr) (memq (car last-instr) '(return tail-call direct-tail-call)))
            (set-basic-block-successors! block '()))
           ((= i (- (length blocks) 1))
            (set-basic-block-successors! block '()))
           (else
            (set-basic-block-successors! block (list (+ i 1)))))))
      blocks))

  (let ((blocks (split-into-blocks tac-instrs)))
    (find-successors blocks)))

;;; --- set helpers (must-analysis shared) ---

(define (set-add set var) (if (memq var set) set (cons var set)))

(define (set-remove set var)
  (let loop ((rest set) (acc '()))
    (cond ((null? rest)          (reverse acc))
          ((eq? (car rest) var)  (loop (cdr rest) acc))
          (else                  (loop (cdr rest) (cons (car rest) acc))))))

(define (set-intersection xs ys)
  (let loop ((rest xs) (acc '()))
    (if (null? rest)
        (reverse acc)
        (loop (cdr rest) (if (memq (car rest) ys) (cons (car rest) acc) acc)))))

(define (rewrite-cfg-with-must-analysis cfg transfer-instr edge-facts rewrite-instr)
  (define block-count (length cfg))

  (define (cfg-set-equal? xs ys)
    (and (null? (set-difference xs ys)) (null? (set-difference ys xs))))

  (define (transfer-block facts block)
    (let loop ((rest (basic-block-instructions block)) (f facts))
      (if (null? rest) f (loop (cdr rest) (transfer-instr f (car rest))))))

  (define predecessors (make-vector block-count '()))
  (let loop ((i 0))
    (when (< i block-count)
      (for-each (lambda (succ)
                  (vector-set! predecessors succ (cons i (vector-ref predecessors succ))))
                (basic-block-successors (list-ref cfg i)))
      (loop (+ i 1))))

  (define in-facts  (make-vector block-count '()))
  (define out-facts (make-vector block-count '()))

  (let fixed-point ((changed #t))
    (when changed
      (let ((any-changed #f))
        (let loop ((i 0))
          (when (< i block-count)
            (let* ((block   (list-ref cfg i))
                   (preds   (vector-ref predecessors i))
                   (new-in  (if (or (= i 0) (null? preds))
                                '()
                                (let ((first (edge-facts (list-ref cfg (car preds)) i
                                                         (vector-ref out-facts (car preds)))))
                                  (let loop-merge ((rest (cdr preds)) (acc first))
                                    (if (null? rest)
                                        acc
                                        (loop-merge
                                         (cdr rest)
                                         (set-intersection
                                          acc
                                          (edge-facts (list-ref cfg (car rest)) i
                                                      (vector-ref out-facts (car rest))))))))))
                   (new-out (transfer-block new-in block)))
              (unless (cfg-set-equal? (vector-ref in-facts i) new-in)
                (vector-set! in-facts i new-in)
                (set! any-changed #t))
              (unless (cfg-set-equal? (vector-ref out-facts i) new-out)
                (vector-set! out-facts i new-out)
                (set! any-changed #t))
              (loop (+ i 1)))))
        (fixed-point any-changed))))

  (let loop ((i 0) (result '()))
    (if (= i block-count)
        (reverse result)
        (let* ((block (list-ref cfg i))
               (rewritten-instrs
                (let inner ((rest (basic-block-instructions block))
                            (facts (vector-ref in-facts i))
                            (acc '()))
                  (if (null? rest)
                      (reverse acc)
                      (let* ((instr      (car rest))
                             (new-instr  (rewrite-instr instr facts))
                             (next-facts (transfer-instr facts new-instr)))
                        (inner (cdr rest) next-facts (cons new-instr acc))))))
               (new-block (make-basic-block (basic-block-label block) rewritten-instrs)))
          (set-basic-block-successors! new-block (basic-block-successors block))
          (loop (+ i 1) (cons new-block result))))))

;;; --- Pass 5.5: Unsafe car/cdr ---

(define (optimize-unsafe-car-cdr-cfg cfg)
  (define (transfer-instr facts instr)
    (if (not (and (pair? instr) (eq? (car instr) 'assign)))
        facts
        (let ((dst (cadr instr)) (rhs (caddr instr)))
          (cond
           ((and (pair? rhs) (eq? (car rhs) 'primop) (eq? (cadr rhs) 'cons))
            (set-add facts dst))
           ((symbol? rhs)
            (if (memq rhs facts) (set-add facts dst) (set-remove facts dst)))
           (else
            (set-remove facts dst))))))

  (define (pair-test-subject block)
    (let ((instrs (basic-block-instructions block)))
      (and (>= (length instrs) 2)
           (let* ((term (list-ref instrs (- (length instrs) 1)))
                  (pre  (list-ref instrs (- (length instrs) 2))))
             (and (pair? term) (eq? (car term) 'if)
                  (pair? pre)  (eq? (car pre)  'assign)
                  (eq? (cadr pre) (cadr term))
                  (pair? (caddr pre)) (eq? (car (caddr pre)) 'primop)
                  (eq? (cadr (caddr pre)) 'pair?)
                  (symbol? (caddr (caddr pre)))
                  (caddr (caddr pre)))))))

  (define (edge-facts pred-block succ-index pred-out)
    (let ((successors   (basic-block-successors pred-block))
          (then-subject (pair-test-subject pred-block)))
      (if (and then-subject (pair? successors) (eqv? (car successors) succ-index))
          (set-add pred-out then-subject)
          pred-out)))

  (define (rewrite-instr instr facts)
    (if (and (pair? instr)         (eq? (car instr) 'assign)
             (pair? (caddr instr)) (eq? (car (caddr instr)) 'primop)
             (memq (cadr (caddr instr)) '(car cdr))
             (symbol? (caddr (caddr instr)))
             (memq (caddr (caddr instr)) facts))
        (let* ((dst (cadr instr)) (rhs (caddr instr))
               (op  (cadr rhs))  (arg (caddr rhs)))
          `(assign ,dst (primop ,(if (eq? op 'car) 'unsafe-car 'unsafe-cdr) ,arg)))
        instr))

  (rewrite-cfg-with-must-analysis cfg transfer-instr edge-facts rewrite-instr))

;;; --- Pass 5.5b: Unsafe arithmetic ---

(define (optimize-unsafe-arith-cfg cfg)
  (define (arith-result-op? op) (memq op '(+ - * safe-+ safe-- safe-*)))

  (define (transfer-instr facts instr)
    (if (not (and (pair? instr) (eq? (car instr) 'assign)))
        facts
        (let ((dst (cadr instr)) (rhs (caddr instr)))
          (cond
           ((number? rhs)
            (set-add facts dst))
           ((symbol? rhs)
            (if (memq rhs facts) (set-add facts dst) (set-remove facts dst)))
           ((and (pair? rhs) (eq? (car rhs) 'primop) (arith-result-op? (cadr rhs)))
            (set-add facts dst))
           (else
            (set-remove facts dst))))))

  (define (safe->unsafe op)
    (case op
      ((safe-+) '+) ((safe--) '-) ((safe-*) '*)
      ((safe-=) '=) ((safe-<) '<) ((safe->) '>)
      (else #f)))

  (define (fixnum-operand? v facts) (or (number? v) (and (symbol? v) (memq v facts))))

  (define (rewrite-instr instr facts)
    (if (and (pair? instr)         (eq? (car instr) 'assign)
             (pair? (caddr instr)) (eq? (car (caddr instr)) 'primop)
             (safe->unsafe (cadr (caddr instr))))
        (let* ((dst       (cadr instr))
               (rhs       (caddr instr))
               (op        (cadr rhs))
               (a         (caddr rhs))
               (b         (cadddr rhs))
               (unsafe-op (safe->unsafe op)))
          (if (and (fixnum-operand? a facts) (fixnum-operand? b facts))
              `(assign ,dst (primop ,unsafe-op ,a ,b))
              instr))
        instr))

  (define (no-edge-facts pred-block succ-index pred-out) pred-out)

  (rewrite-cfg-with-must-analysis cfg transfer-instr no-edge-facts rewrite-instr))

;;; --- Pass 5.6: Constant Folding ---

(define (constant-fold-cfg cfg)
  (define block-count (length cfg))

  (define (facts-lookup facts var)
    (let ((entry (assq var facts)))
      (if entry (list (cdr entry)) #f)))

  (define (facts-bind facts var val)
    (cons (cons var val)
          (let loop ((rest facts) (acc '()))
            (cond ((null? rest)           (reverse acc))
                  ((eq? (caar rest) var)  (loop (cdr rest) acc))
                  (else                   (loop (cdr rest) (cons (car rest) acc)))))))

  (define (facts-unbind facts var)
    (let loop ((rest facts) (acc '()))
      (cond ((null? rest)           (reverse acc))
            ((eq? (caar rest) var)  (loop (cdr rest) acc))
            (else                   (loop (cdr rest) (cons (car rest) acc))))))

  (define (facts-intersect f1 f2)
    (let loop ((rest f1) (acc '()))
      (if (null? rest)
          (reverse acc)
          (let* ((entry  (car rest))
                 (var    (car entry))
                 (val    (cdr entry))
                 (f2-e   (assq var f2)))
            (loop (cdr rest)
                  (if (and f2-e (equal? (cdr f2-e) val))
                      (cons entry acc)
                      acc))))))

  (define (facts-equal? f1 f2)
    (and (= (length f1) (length f2))
         (let loop ((rest f1))
           (or (null? rest)
               (let* ((entry (car rest))
                      (var   (car entry))
                      (val   (cdr entry))
                      (f2-e  (assq var f2)))
                 (and f2-e
                      (equal? (cdr f2-e) val)
                      (loop (cdr rest))))))))

  (define (fold-primop op arg-vals)
    (define (fold2 pred? op2)
      (and (= (length arg-vals) 2)
           (pred? (car arg-vals))
           (pred? (cadr arg-vals))
           (list (op2 (car arg-vals) (cadr arg-vals)))))
    (define (fold1 op1)
      (and (= (length arg-vals) 1)
           (list (op1 (car arg-vals)))))
    (case op
      ((+)     (fold2 number? +))
      ((-)     (fold2 number? -))
      ((*)     (fold2 number? *))
      ((=)     (fold2 number? =))
      ((<)     (fold2 number? <))
      ((>)     (fold2 number? >))
      ((null?) (fold1 null?))
      ((pair?) (fold1 pair?))
      (else #f)))

  (define (lookup-arg facts v)
    (if (literal-expr? v) (list v) (facts-lookup facts v)))

  (define (transfer-instr facts instr)
    (if (not (and (pair? instr) (eq? (car instr) 'assign)))
        facts
        (let ((dst (cadr instr))
              (rhs (caddr instr)))
          (cond
           ((literal-expr? rhs)
            (facts-bind facts dst rhs))
           ((symbol? rhs)
            (let ((vb (facts-lookup facts rhs)))
              (if vb
                  (facts-bind facts dst (car vb))
                  (facts-unbind facts dst))))
           ((and (pair? rhs) (eq? (car rhs) 'primop))
            (let* ((op        (cadr rhs))
                   (arg-boxes (map (lambda (v) (lookup-arg facts v)) (cddr rhs))))
              (if (all (lambda (b) b) arg-boxes)
                  (let ((folded (fold-primop op (map car arg-boxes))))
                    (if folded
                        (facts-bind facts dst (car folded))
                        (facts-unbind facts dst)))
                  (facts-unbind facts dst))))
           (else
            (facts-unbind facts dst))))))

  (define (transfer-block in-facts block)
    (let loop ((rest (basic-block-instructions block)) (facts in-facts))
      (if (null? rest)
          facts
          (loop (cdr rest) (transfer-instr facts (car rest))))))

  (define predecessors (make-vector block-count '()))
  (let build-preds ((i 0))
    (when (< i block-count)
      (for-each
       (lambda (succ)
         (vector-set! predecessors succ (cons i (vector-ref predecessors succ))))
       (basic-block-successors (list-ref cfg i)))
      (build-preds (+ i 1))))

  (define in-facts  (make-vector block-count '()))
  (define out-facts (make-vector block-count '()))

  (let fixed-point ((changed #t))
    (if (not changed)
        'done
        (let ((any-changed #f))
          (do ((i 0 (+ i 1)))
              ((= i block-count))
            (let* ((preds   (vector-ref predecessors i))
                   (new-in
                    (if (= i 0)
                        '()
                        (if (null? preds)
                            '()
                            (let ((first-out (vector-ref out-facts (car preds))))
                              (let merge ((rest (cdr preds)) (acc first-out))
                                (if (null? rest)
                                    acc
                                    (merge (cdr rest)
                                           (facts-intersect
                                            acc
                                            (vector-ref out-facts (car rest))))))))))
                   (new-out (transfer-block new-in (list-ref cfg i))))
              (unless (facts-equal? new-in (vector-ref in-facts i))
                (vector-set! in-facts i new-in)
                (set! any-changed #t))
              (unless (facts-equal? new-out (vector-ref out-facts i))
                (vector-set! out-facts i new-out)
                (set! any-changed #t))))
          (fixed-point any-changed))))

  (define (rewrite-block block initial-facts)
    (let loop ((rest       (basic-block-instructions block))
               (facts      initial-facts)
               (result     '())
               (new-succs  (basic-block-successors block)))
      (if (null? rest)
          (let ((rewritten (make-basic-block (basic-block-label block)
                                             (reverse result))))
            (set-basic-block-successors! rewritten new-succs)
            rewritten)
          (let* ((instr (car rest))
                 (rw
                  (cond
                   ((and (pair? instr)
                         (eq? (car instr) 'assign)
                         (pair? (caddr instr))
                         (eq? (car (caddr instr)) 'primop))
                    (let* ((dst       (cadr instr))
                           (rhs       (caddr instr))
                           (op        (cadr rhs))
                           (arg-boxes (map (lambda (v) (lookup-arg facts v))
                                           (cddr rhs))))
                      (if (all (lambda (b) b) arg-boxes)
                          (let ((folded (fold-primop op (map car arg-boxes))))
                            (if folded
                                (list `(assign ,dst ,(car folded)) new-succs)
                                (list instr new-succs)))
                          (list instr new-succs))))
                   ((and (pair? instr)
                         (eq? (car instr) 'assign)
                         (symbol? (caddr instr)))
                    (let ((vb (facts-lookup facts (caddr instr))))
                      (if vb
                          (list `(assign ,(cadr instr) ,(car vb)) new-succs)
                          (list instr new-succs))))
                   ((and (pair? instr) (eq? (car instr) 'if))
                    (let* ((cond-expr (cadr instr))
                           (val-box   (if (literal-expr? cond-expr)
                                          (list cond-expr)
                                          (facts-lookup facts cond-expr))))
                      (if val-box
                          (let ((cond-val   (car val-box))
                                (then-succ  (car new-succs))
                                (else-succ  (cadr new-succs))
                                (then-label (caddr instr))
                                (else-label (cadddr instr)))
                            (if cond-val
                                (list `(goto ,then-label) (list then-succ))
                                (list `(goto ,else-label) (list else-succ))))
                          (list instr new-succs))))
                   (else
                    (list instr new-succs))))
                 (new-instr     (car rw))
                 (updated-succs (cadr rw))
                 (next-facts    (transfer-instr facts new-instr)))
            (loop (cdr rest)
                  next-facts
                  (cons new-instr result)
                  updated-succs)))))

  (let rewrite-loop ((i 0) (result '()))
    (if (= i block-count)
        (reverse result)
        (rewrite-loop (+ i 1)
                      (cons (rewrite-block (list-ref cfg i)
                                           (vector-ref in-facts i))
                            result)))))

;;; --- Pass 5.7: Dead Write Elimination ---

(define (eliminate-dead-writes-cfg cfg)
  (define block-count (length cfg))

  (define (sym-list lst)
    (let loop ((rest lst) (acc '()))
      (if (null? rest)
          (reverse acc)
          (loop (cdr rest)
                (if (symbol? (car rest)) (cons (car rest) acc) acc)))))

  (define (tac-rhs-uses rhs)
    (cond
     ((literal-expr? rhs)  '())
     ((symbol? rhs)        (list rhs))
     ((and (pair? rhs) (eq? (car rhs) 'primop))
      (sym-list (cddr rhs)))
     ((and (pair? rhs) (memq (car rhs) '(cons box unbox car cdr pair? null? make-vector vector-length vector-ref vector-set! vector?)))
      (sym-list (cdr rhs)))
     ((and (pair? rhs) (eq? (car rhs) 'global))
      '())
     ((and (pair? rhs) (eq? (car rhs) 'closure-env-ref))
      (if (symbol? (cadr rhs)) (list (cadr rhs)) '()))
     ((and (pair? rhs) (eq? (car rhs) 'make-closure))
      (sym-list (cddr rhs)))
     ((and (pair? rhs) (memq (car rhs) '(closure-call direct-call)))
      (sym-list (cdr rhs)))
     (else '())))

  (define (tac-instr-uses instr)
    (cond
     ((and (pair? instr) (eq? (car instr) 'assign))
      (tac-rhs-uses (caddr instr)))
     ((and (pair? instr) (eq? (car instr) 'if))
      (if (symbol? (cadr instr)) (list (cadr instr)) '()))
     ((and (pair? instr) (eq? (car instr) 'return))
      (if (symbol? (cadr instr)) (list (cadr instr)) '()))
     ((and (pair? instr) (eq? (car instr) 'tail-call))
      (sym-list (cdr instr)))
     ((and (pair? instr) (eq? (car instr) 'direct-tail-call))
      (sym-list (cddr instr)))
     ((and (pair? instr) (eq? (car instr) 'set-box!))
      (sym-list (cdr instr)))
     ((and (pair? instr) (eq? (car instr) 'set-global!))
      (if (symbol? (caddr instr)) (list (caddr instr)) '()))
     (else '())))

  (define (tac-instr-defs instr)
    (if (and (pair? instr) (eq? (car instr) 'assign))
        (list (cadr instr))
        '()))

  (define (tac-rhs-pure? rhs)
    (cond
     ((literal-expr? rhs) #t)
     ((symbol? rhs)       #t)
     ((and (pair? rhs) (eq? (car rhs) 'primop))
      (and (memq (cadr rhs) '(+ - * = < > null? pair? vector? unsafe-car unsafe-cdr))
           #t))
     ((and (pair? rhs) (eq? (car rhs) 'global))          #t)
     ((and (pair? rhs) (eq? (car rhs) 'closure-env-ref)) #t)
     ((and (pair? rhs) (eq? (car rhs) 'unbox))           #t)
     (else #f)))

  (define (tac-block-use block)
    (let loop ((instrs (basic-block-instructions block))
               (defs   '())
               (uses   '()))
      (if (null? instrs)
          uses
          (let* ((instr      (car instrs))
                 (instr-uses (set-difference (tac-instr-uses instr) defs))
                 (instr-defs (tac-instr-defs instr)))
            (loop (cdr instrs)
                  (set-union defs instr-defs)
                  (set-union uses instr-uses))))))

  (define (tac-block-def block)
    (let loop ((instrs (basic-block-instructions block)) (defs '()))
      (if (null? instrs)
          defs
          (loop (cdr instrs)
                (set-union defs (tac-instr-defs (car instrs)))))))

  (let* ((use-vec (list->vector (map tac-block-use cfg)))
         (def-vec (list->vector (map tac-block-def cfg)))
         (in-vec  (make-vector block-count '()))
         (out-vec (make-vector block-count '())))

    (let fixed-point ()
      (let ((changed #f))
        (do ((i (- block-count 1) (- i 1)))
            ((< i 0))
          (let* ((block   (list-ref cfg i))
                 (succs   (basic-block-successors block))
                 (new-out (let s-loop ((rest succs) (acc '()))
                            (if (null? rest)
                                acc
                                (s-loop (cdr rest)
                                        (set-union acc
                                                   (vector-ref in-vec (car rest)))))))
                 (new-in  (set-union (vector-ref use-vec i)
                                     (set-difference new-out
                                                     (vector-ref def-vec i)))))
            (when (not (set-equal? new-out (vector-ref out-vec i)))
              (vector-set! out-vec i new-out)
              (set! changed #t))
            (when (not (set-equal? new-in (vector-ref in-vec i)))
              (vector-set! in-vec i new-in)
              (set! changed #t))))
        (when changed (fixed-point))))

    (define (rewrite-block block out-live)
      (let loop ((instrs  (reverse (basic-block-instructions block)))
                 (live    out-live)
                 (result  '()))
        (if (null? instrs)
            (let ((rewritten (make-basic-block (basic-block-label block)
                                               result)))
              (set-basic-block-successors! rewritten (basic-block-successors block))
              rewritten)
            (let* ((instr   (car instrs))
                   (dead?   (and (pair? instr)
                                 (eq? (car instr) 'assign)
                                 (not (memq (cadr instr) live))
                                 (tac-rhs-pure? (caddr instr))))
                   (new-live
                    (if dead?
                        live
                        (set-union (set-difference live (tac-instr-defs instr))
                                   (tac-instr-uses instr)))))
              (loop (cdr instrs)
                    new-live
                    (if dead? result (cons instr result)))))))

    (let rewrite-loop ((i 0) (result '()))
      (if (= i block-count)
          (reverse result)
          (rewrite-loop (+ i 1)
                        (cons (rewrite-block (list-ref cfg i)
                                             (vector-ref out-vec i))
                              result))))))

)) ; end define-library
