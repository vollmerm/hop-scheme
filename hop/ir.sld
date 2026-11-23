(define-library (hop ir)
  ;;; Instruction grammars and the operations that follow from them.
  ;;;
  ;;; An instruction is a list (opcode field ...). An instruction set gives
  ;;; each opcode a shape: one operand kind per field, and optionally a kind
  ;;; after a dot that covers any number of remaining fields.
  ;;;
  ;;;   def    a variable the instruction writes
  ;;;   use    an operand the instruction reads: a variable, or a literal
  ;;;   label  a block label
  ;;;   datum  anything else, passed through untouched (an operator name, a
  ;;;          procedure label, an arity, a slot index)
  ;;;   expr   a variable, a literal, or a compound expression of the set's
  ;;;          expression set, whose own operands are read
  ;;;
  ;;; From the shapes, map-operands rebuilds an instruction with its operands
  ;;; replaced, and instruction-uses and instruction-defs list them, so no
  ;;; pass needs to know where an opcode keeps its operands.
  ;;;
  ;;; define-instruction-set checks every kind when it is expanded:
  ;;;
  ;;;   (define-instruction-set name
  ;;;     (expressions expression-set)     ; optional, for expr fields
  ;;;     (instruction opcode kind ...)    ; any instruction
  ;;;     (terminator opcode kind ...)     ; one that ends a basic block
  ;;;     ...)
  (export define-instruction-set
          instruction-set?
          instruction-shape
          terminator-instruction?
          map-operands
          map-uses
          instruction-uses
          instruction-defs
          tac-expression
          tac-instruction
          map-instr-uses
          instr-uses
          instr-def
          terminator?)
  (cond-expand
   (chicken
    ;; Chicken warns about every macro an exported macro expands into unless
    ;; that one is exported too.
    (export instruction-shape-literal check-instruction-shape terminator-opcodes
            unknown-operand-kind unknown-instruction-role))
   (else))
  (import (scheme base)
          (hop match))
  (begin

(define-record-type <instruction-set>
  (make-instruction-set name expressions shape-of terminator-opcode?)
  instruction-set?
  (name instruction-set-name)
  ;; the instruction set of expr fields' compound expressions, or #f
  (expressions instruction-set-expressions)
  ;; opcode -> shape, or #f for an opcode the set does not have
  (shape-of instruction-set-shape-of)
  (terminator-opcode? instruction-set-terminator-opcode?))

;; Checks the kinds of a shape when it is expanded, and quotes it.
(define-syntax instruction-shape-literal
  (syntax-rules ()
    ((_ shape) (check-instruction-shape shape shape))))

(define-syntax check-instruction-shape
  (syntax-rules (def use label datum expr)
    ((_ () shape) 'shape)
    ((_ (def . rest) shape) (check-instruction-shape rest shape))
    ((_ (use . rest) shape) (check-instruction-shape rest shape))
    ((_ (label . rest) shape) (check-instruction-shape rest shape))
    ((_ (datum . rest) shape) (check-instruction-shape rest shape))
    ((_ (expr . rest) shape) (check-instruction-shape rest shape))
    ((_ def shape) 'shape)
    ((_ use shape) 'shape)
    ((_ label shape) 'shape)
    ((_ datum shape) 'shape)
    ((_ expr shape) 'shape)
    ((_ (kind . rest) shape) (unknown-operand-kind kind shape))
    ((_ kind shape) (unknown-operand-kind kind shape))))

;; Has no rules, so a use stops expansion with an error that shows the kind.
(define-syntax unknown-operand-kind
  (syntax-rules ()))

(define-syntax define-instruction-set
  (syntax-rules (expressions instruction terminator)
    ((_ name (expressions set) (role opcode . shape) ...)
     (define name
       (make-instruction-set
        'name
        set
        (lambda (op)
          (case op
            ((opcode) (instruction-shape-literal shape))
            ...
            (else #f)))
        (lambda (op)
          (and (memq op (terminator-opcodes () (role opcode) ...)) #t)))))
    ((_ name (role opcode . shape) ...)
     (define-instruction-set name (expressions #f) (role opcode . shape) ...))))

;; The opcodes marked terminator, as a quoted list.
(define-syntax terminator-opcodes
  (syntax-rules (instruction terminator)
    ((_ (found ...)) '(found ...))
    ((_ (found ...) (terminator opcode) . rest)
     (terminator-opcodes (found ... opcode) . rest))
    ((_ (found ...) (instruction opcode) . rest)
     (terminator-opcodes (found ...) . rest))
    ((_ (found ...) (role opcode) . rest)
     (unknown-instruction-role role opcode))))

;; Has no rules, so a use stops expansion with an error that shows the role.
(define-syntax unknown-instruction-role
  (syntax-rules ()))

(define (instruction-shape set instr)
  (match instr
    ((opcode . _)
     (or ((instruction-set-shape-of set) opcode)
         (error "unknown instruction" (instruction-set-name set) instr)))
    (_ (error "not an instruction" (instruction-set-name set) instr))))

(define (terminator-instruction? set instr)
  (match instr
    ((opcode . _) ((instruction-set-terminator-opcode? set) opcode))
    (_ #f)))

;; Rebuilds instr, replacing each variable it writes by (on-def v), each
;; variable it reads by (on-use v), and each block label by (on-label l).
;; Fields are visited left to right.
(define (map-operands set instr on-def on-use on-label)
  (define (field kind value)
    (case kind
      ((def) (on-def value))
      ((use) (if (symbol? value) (on-use value) value))
      ((label) (on-label value))
      ((datum) value)
      ((expr)
       (cond
        ((symbol? value) (on-use value))
        ((pair? value)
         (map-operands (instruction-set-expressions set) value on-def on-use on-label))
        (else value)))))
  (match instr
    ((opcode . fields)
     (cons opcode
           (let walk ((shape (instruction-shape set instr)) (fields fields))
             (match (list shape fields)
               ((() ()) '())
               (((? symbol?) ()) '())
               (((kind . kinds) (value . values))
                (let ((first (field kind value)))
                  (cons first (walk kinds values))))
               (((? symbol? kind) (value . values))
                (let ((first (field kind value)))
                  (cons first (walk kind values))))
               (_ (error "instruction does not fit its shape" instr))))))))

(define (map-uses set f instr)
  (map-operands set instr (lambda (v) v) f (lambda (l) l)))

(define (instruction-uses set instr)
  (let ((uses '()))
    (map-uses set (lambda (v) (set! uses (cons v uses)) v) instr)
    (reverse uses)))

(define (instruction-defs set instr)
  (let ((defs '()))
    (map-operands set instr
                  (lambda (v) (set! defs (cons v defs)) v)
                  (lambda (v) v)
                  (lambda (l) l))
    (reverse defs)))

;;; --- Three-address code ---
;;;
;;; The right-hand side of an assign is an expr: a variable, a literal
;;; (a number, a boolean, '(), or (quote sym)), or one of these.

(define-instruction-set tac-expression
  (instruction quote datum)
  (instruction global datum)
  (instruction primop datum . use)
  (instruction cons use use)
  (instruction box use)
  (instruction unbox use)
  (instruction car use)
  (instruction cdr use)
  (instruction pair? use)
  (instruction null? use)
  (instruction closure-env-ref use datum)
  (instruction make-closure datum datum . use)
  (instruction make-variadic-closure datum datum . use)
  (instruction closure-call use . use)
  (instruction apply-call use use use)
  (instruction callcc-call use)
  (instruction direct-call datum . use)
  ;; refinements, present only while a procedure is in SSA form
  (instruction pi datum use)
  (instruction pi-field datum use use))

(define-instruction-set tac-instruction
  (expressions tac-expression)
  (instruction assign def expr)
  (instruction label label)
  (instruction set-box! use use)
  (instruction set-global! datum use)
  (terminator if use label label)
  (terminator goto label)
  (terminator return use)
  (terminator tail-call use . use)
  (terminator tail-apply-call use use use)
  (terminator tail-callcc-call use)
  (terminator direct-tail-call datum . use))

;; Rebuilds a TAC instruction with f applied to each variable it reads.
(define (map-instr-uses f instr)
  (map-uses tac-instruction f instr))

;; The variables a TAC instruction reads, in order.
(define (instr-uses instr)
  (instruction-uses tac-instruction instr))

;; The variable a TAC instruction writes, or #f.
(define (instr-def instr)
  (match instr
    (('assign dst _) dst)
    (_ #f)))

(define (terminator? instr)
  (terminator-instruction? tac-instruction instr))

)) ; end define-library
