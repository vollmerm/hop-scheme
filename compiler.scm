;;; A small Scheme-to-AArch64 compiler.
;;;
;;; The file is organized as a sequence of explicit compilation passes so that
;;; each stage has a single, teachable job:
;;;
;;;   source program
;;;     -> program lowering
;;;     -> uniquify
;;;     -> letrec desugaring
;;;     -> closure conversion
;;;     -> three-address code (TAC)
;;;     -> control-flow graph (CFG)
;;;     -> machine-like backend IR
;;;     -> register allocation / calling-convention lowering
;;;     -> AArch64 assembly
;;;
;;; The source language supported here is intentionally small: arithmetic,
;;; booleans, null, pairs, conditionals, boxes, lambdas, applications,
;;; lambda-only letrec, and top-level variable define in multi-form programs.

(import (scheme base)
        (scheme read)
        (scheme write))

;;; ============================================================================
;;; Shared Helpers
;;; Small utilities used across many passes. These helpers are deliberately
;;; simple so the interesting compiler logic below can read directly.
;;; ============================================================================

(define (body->expr body-exprs)
  (cond
    ((null? body-exprs)
     (error "Empty body is not supported"))
    ((null? (cdr body-exprs))
     (car body-exprs))
    (else
     `(begin ,@body-exprs))))

(define (append-map proc lst)
  (let loop ((rest lst) (result '()))
    (if (null? rest)
        result
        (append result (proc (car rest)) (loop (cdr rest) '())))))

(define (dedupe-symbols lst)
  (let loop ((rest lst) (seen '()) (result '()))
    (cond
      ((null? rest) (reverse result))
      ((memq (car rest) seen)
       (loop (cdr rest) seen result))
      (else
       (loop (cdr rest)
             (cons (car rest) seen)
             (cons (car rest) result))))))

(define (remove-shadowed-bindings env names)
  (let loop ((rest env) (result '()))
    (cond
      ((null? rest) (reverse result))
      ((memq (caar rest) names)
       (loop (cdr rest) result))
      (else
       (loop (cdr rest) (cons (car rest) result))))))

(define (all predicate lst)
  (cond
    ((null? lst) #t)
    ((predicate (car lst)) (all predicate (cdr lst)))
    (else #f)))

(define (single-binding? binding)
  (and (pair? binding)
       (pair? (cdr binding))
       (null? (cddr binding))))

(define (lambda-expr? expr)
  (and (pair? expr) (eq? (car expr) 'lambda)))

(define (literal-expr? expr)
  (or (number? expr) (boolean? expr) (null? expr)))

(define (nest-let-bindings bindings body-exprs)
  (if (null? bindings)
      (body->expr body-exprs)
      `(let (,(car bindings))
         ,(nest-let-bindings (cdr bindings) body-exprs))))

;;; ============================================================================
;;; Pass 0: Program Lowering
;;; Accept either a single expression or an explicit `(program ...)` wrapper,
;;; flatten top-level `begin`, assign compiler-known global slots, and rewrite
;;; top-level define into explicit global initialization.
;;;
;;; INPUT GRAMMAR (Source)
;;;
;;;   Source  ::= (program Form*)   ; multi-form top level
;;;             | Expr              ; bare expression
;;;
;;;   Form    ::= (define Var Expr) ; top-level variable definition
;;;             | (begin Form*)     ; spliced form group
;;;             | Expr
;;;
;;;   Expr    ::= Var               ; variable reference
;;;             | Literal           ; integer, boolean, or ()
;;;             | (begin Expr+)
;;;             | (if Expr Expr Expr)
;;;             | (let ((Var Expr)) Expr+)
;;;             | (letrec ((Var Expr)+) Expr+)  ; lambda bindings only
;;;             | (lambda (Var*) Expr+)
;;;             | (primop PrimOp Expr*)
;;;             | (app Expr Expr*)
;;;             | (cons Expr Expr)
;;;             | (car Expr)
;;;             | (cdr Expr)
;;;             | (pair? Expr)
;;;             | (null? Expr)
;;;             | (box Expr)
;;;             | (unbox Expr)
;;;             | (set-box! Expr Expr)
;;;             | (make-vector Expr Expr)
;;;             | (vector-length Expr)
;;;             | (vector-ref Expr Expr)
;;;             | (vector-set! Expr Expr Expr)
;;;
;;;   PrimOp  ::= + | - | * | = | <
;;;   Literal ::= Integer | #t | #f | ()
;;;
;;; OUTPUT GRAMMAR (Lowered)
;;;
;;;   Expr    ::= Var
;;;             | Literal
;;;             | (global N)            ; read from global slot N (integer)
;;;             | (set-global! N Expr)  ; write to global slot N
;;;             | (begin Expr+)
;;;             | (if Expr Expr Expr)
;;;             | (let ((Var Expr)) Expr+)
;;;             | (letrec ((Var Expr)+) Expr+)
;;;             | (lambda (Var*) Expr+)
;;;             | (primop PrimOp Expr*)
;;;             | (app Expr Expr*)
;;;             | (cons Expr Expr)
;;;             | (car Expr)
;;;             | (cdr Expr)
;;;             | (pair? Expr)
;;;             | (null? Expr)
;;;             | (box Expr)
;;;             | (unbox Expr)
;;;             | (set-box! Expr Expr)
;;;             | (make-vector Expr Expr)
;;;             | (vector-length Expr)
;;;             | (vector-ref Expr Expr)
;;;             | (vector-set! Expr Expr Expr)
;;;
;;; Changes: top-level `(define Var E)` → `(set-global! N E)`;
;;;          free references to defined names → `(global N)`.
;;;          The program is collapsed to a single Expr (possibly a `begin`).
;;; ============================================================================

(define (program-source? source)
  (and (pair? source) (eq? (car source) 'program)))

(define (source->forms source)
  (if (program-source? source)
      (cdr source)
      (list source)))

(define (top-level-define-form? form)
  (and (pair? form)
       (eq? (car form) 'define)
       (pair? (cdr form))
       (symbol? (cadr form))
       (pair? (cddr form))
       (null? (cdddr form))))

(define (flatten-top-level-forms forms)
  (define (flatten-form form)
    (if (and (pair? form) (eq? (car form) 'begin))
        (flatten-top-level-forms (cdr form))
        (list form)))
  (append-map flatten-form forms))

(define (collect-top-level-global-env forms)
  (let loop ((rest forms) (next-slot 0) (env '()))
    (if (null? rest)
        env
        (let ((form (car rest)))
          (if (top-level-define-form? form)
              (let ((name (cadr form)))
                (if (assoc name env)
                    (loop (cdr rest) next-slot env)
                    (loop (cdr rest)
                          (+ next-slot 1)
                          (cons (list name next-slot) env))))
              (loop (cdr rest) next-slot env))))))

(define (global-slot name global-env)
  (let ((binding (assoc name global-env)))
    (if binding
        (cadr binding)
        (error "Unknown global binding" name))))

(define (resolve-globals expr local-env global-env)
  (cond
    ((symbol? expr)
     (if (memq expr local-env)
         expr
         (let ((binding (assoc expr global-env)))
           (if binding
               `(global ,(cadr binding))
               expr))))
    ((literal-expr? expr) expr)
    ((pair? expr)
     (case (car expr)
       ((begin)
        `(begin ,@(map (lambda (e) (resolve-globals e local-env global-env))
                       (cdr expr))))
       ((primop)
        `(primop ,(cadr expr)
                 ,@(map (lambda (e) (resolve-globals e local-env global-env))
                        (cddr expr))))
       ((if)
        `(if ,(resolve-globals (cadr expr) local-env global-env)
             ,(resolve-globals (caddr expr) local-env global-env)
             ,(resolve-globals (cadddr expr) local-env global-env)))
       ((let)
        (let* ((binding (caadr expr))
               (var (car binding))
               (val-expr (cadr binding))
               (body-exprs (cddr expr)))
          `(let ((,var ,(resolve-globals val-expr local-env global-env)))
             ,@(map (lambda (body-expr)
                      (resolve-globals body-expr
                                       (cons var local-env)
                                       global-env))
                    body-exprs))))
       ((lambda)
        (let ((params (cadr expr)))
          `(lambda ,params
             ,@(map (lambda (body-expr)
                      (resolve-globals body-expr
                                       (append params local-env)
                                       global-env))
                    (cddr expr)))))
       ((letrec)
        (let* ((bindings (cadr expr))
               (names (map car bindings))
               (rec-env (append names local-env)))
          `(letrec
             ,(map (lambda (binding)
                     (list (car binding)
                           (resolve-globals (cadr binding) rec-env global-env)))
                   bindings)
             ,@(map (lambda (body-expr)
                      (resolve-globals body-expr rec-env global-env))
                    (cddr expr)))))
       ((app)
        `(app ,(resolve-globals (cadr expr) local-env global-env)
              ,@(map (lambda (e) (resolve-globals e local-env global-env))
                     (cddr expr))))
        ((cons make-vector vector-ref)
         `(,(car expr) ,(resolve-globals (cadr expr) local-env global-env)
                       ,(resolve-globals (caddr expr) local-env global-env)))
        ((+ - * = < >)
         `(,(car expr) ,(resolve-globals (cadr expr) local-env global-env)
                       ,(resolve-globals (caddr expr) local-env global-env)))
        ((box unbox car cdr pair? null? vector-length vector?)
         `(,(car expr) ,(resolve-globals (cadr expr) local-env global-env)))
        ((set-box!)
         `(set-box! ,(resolve-globals (cadr expr) local-env global-env)
                    ,(resolve-globals (caddr expr) local-env global-env)))
        ((vector-set!)
         `(vector-set! ,(resolve-globals (cadr expr) local-env global-env)
                       ,(resolve-globals (caddr expr) local-env global-env)
                       ,(resolve-globals (cadddr expr) local-env global-env)))
       ((define)
        (error "Internal define is not supported" expr))
       (else
        (error "Unknown expression during global resolution" (car expr)))))
    (else
     (error "Invalid expression during global resolution" expr))))

(define (lower-source-program source)
  (let* ((forms (flatten-top-level-forms (source->forms source)))
         (global-env (collect-top-level-global-env forms)))
    (if (null? forms)
        (error "Program requires at least one top-level form")
        (values
         (body->expr
          (map (lambda (form)
                 (if (top-level-define-form? form)
                     ;; Top-level define is not a local binder after this point;
                     ;; it is an ordered write into a compiler-assigned slot.
                     `(set-global! ,(global-slot (cadr form) global-env)
                                    ,(resolve-globals (caddr form) '() global-env))
                     (resolve-globals form '() global-env)))
               forms))
         (length global-env)))))

;;; ============================================================================
;;; Pass 1: Uniquify
;;; Renames every binder so that each variable name is globally unique.
;;; After this pass, later stages no longer need to reason about shadowing by
;;; name; they can treat identifiers as stable handles for bindings.
;;;
;;; GRAMMAR: unchanged from the Lowered grammar (Pass 0 output).
;;; This pass is structure-preserving; only the *names* of binders and their
;;; references change.  Every Var bound by `let`, `letrec`, or `lambda` is
;;; replaced by a fresh symbol of the form `original.N`.  Free variables
;;; (globals, primitives) are left unchanged.
;;; ============================================================================

(define (uniquify expr)
  (define counter 0)
  
  (define (fresh-name name)
    (set! counter (+ counter 1))
    (string->symbol 
     (string-append (symbol->string name) 
                    "." 
                    (number->string counter))))
  
  (define (uniquify-expr expr env)
    (cond
      ((symbol? expr)
       ;; Variable reference
       (let ((binding (assoc expr env)))
         (if binding
             (cadr binding)  ; Return the unique name
             expr)))         ; Keep global/primitive names as-is
      
      ((literal-expr? expr) expr)
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(map (lambda (e) (uniquify-expr e env)) (cdr expr))))
         
          ((primop)
           `(primop ,(cadr expr) 
                    ,@(map (lambda (e) (uniquify-expr e env)) (cddr expr))))
         
         ((if)
          `(if ,(uniquify-expr (cadr expr) env)
               ,(uniquify-expr (caddr expr) env)
               ,(uniquify-expr (cadddr expr) env)))
         
          ((let)
           (let* ((binding (caadr expr))
                  (var (car binding))
                  (val-expr (cadr binding))
                  (body-exprs (cddr expr))
                  (unique-var (fresh-name var))
                  (new-env (cons (list var unique-var) env))
                  (val-expr-unique (uniquify-expr val-expr env))
                  (body-unique
                   (map (lambda (body-expr)
                          (uniquify-expr body-expr new-env))
                        body-exprs)))
             `(let ((,unique-var ,val-expr-unique)) ,@body-unique)))
          
          ((lambda)
           (let* ((params (cadr expr))
                  (body-exprs (cddr expr))
                  (unique-params (map fresh-name params))
                  (new-env (append (map (lambda (old new) (list old new)) 
                                        params unique-params)
                                   env))
                  (body-unique
                   (map (lambda (body-expr)
                          (uniquify-expr body-expr new-env))
                        body-exprs)))
             `(lambda ,unique-params ,@body-unique)))
          
          ((letrec)
           (let* ((bindings (cadr expr))
                  (vars (map car bindings))
                  (unique-vars (map fresh-name vars))
                  (rec-bindings (map (lambda (old new) (list old new))
                                     vars unique-vars))
                  (new-env (append rec-bindings env))
                  (unique-bindings
                   (map (lambda (binding unique-var)
                          (let ((value-expr (cadr binding)))
                            (if (not (lambda-expr? value-expr))
                                (error "letrec requires lambda bindings" value-expr)
                                (list unique-var
                                      (uniquify-expr value-expr new-env)))))
                        bindings
                        unique-vars))
                  (body-unique
                   (map (lambda (body-expr)
                          (uniquify-expr body-expr new-env))
                        (cddr expr))))
             `(letrec ,unique-bindings ,@body-unique)))
          
          ((app)
           `(app ,(uniquify-expr (cadr expr) env)
                 ,@(map (lambda (e) (uniquify-expr e env)) (cddr expr))))

          ((cons make-vector vector-ref)
           `(,(car expr) ,(uniquify-expr (cadr expr) env)
                         ,(uniquify-expr (caddr expr) env)))
          ((+ - * = < >)
           `(,(car expr) ,(uniquify-expr (cadr expr) env)
                         ,(uniquify-expr (caddr expr) env)))
          ((box unbox car cdr pair? null? vector-length vector?)
           `(,(car expr) ,(uniquify-expr (cadr expr) env)))
          ((set-box!)
           `(set-box! ,(uniquify-expr (cadr expr) env) 
                      ,(uniquify-expr (caddr expr) env)))
          ((vector-set!)
           `(vector-set! ,(uniquify-expr (cadr expr) env)
                         ,(uniquify-expr (caddr expr) env)
                         ,(uniquify-expr (cadddr expr) env)))

          ((+ - * = < >)
           `(,(car expr) ,(uniquify-expr (cadr expr) env)
                         ,(uniquify-expr (caddr expr) env)))
          
          ((box unbox car cdr pair? null?)
           `(,(car expr) ,(uniquify-expr (cadr expr) env)))
          
          ((set-box!)
           `(set-box! ,(uniquify-expr (cadr expr) env) 
                      ,(uniquify-expr (caddr expr) env)))
          
          ((global)
           expr)

          ((set-global!)
           `(set-global! ,(cadr expr)
                         ,(uniquify-expr (caddr expr) env)))
          
          (else (error "Unknown expression type" (car expr)))))
      
      (else (error "Invalid expression" expr))))
  
  (uniquify-expr expr '()))

;;; ============================================================================
;;; Pass 1.5: Builtin Canonicalization
;;; Rewrites user-facing list and vector primitives (car, cdr, cons, pair?,
;;; null?, make-vector, vector-length, vector-ref, vector-set!) into uniform
;;; (primop op ...) form. Runs immediately after uniquify, which means bound
;;; identifiers are already renamed to name.N form, so builtin-head detection
;;; is purely syntactic with no scope tracking needed.
;;;
;;; A bare builtin name in value position (e.g. passed as a first-class
;;; argument) is wrapped as a fresh lambda so it remains a legal value.
;;;
;;; box/unbox/set-box! are intentionally excluded: they are internal compiler
;;; forms produced by desugar-letrec and must remain as special syntax.
;;; Arithmetic primops (+, -, *, =, <) already appear as (primop op ...) in
;;; source and are left unchanged.
;;;
;;; INPUT GRAMMAR:  Uniquified (Pass 1 output).
;;; OUTPUT GRAMMAR: Same, except car/cdr/cons/pair?/null?/make-vector/
;;;                 vector-length/vector-ref/vector-set! as operation heads
;;;                 are replaced by (primop op ...) and bare builtin symbols
;;;                 in value position become lambda wrappers.
;;; ============================================================================

(define builtin-primop-arities
  '((car . 1)
    (cdr . 1)
    (unsafe-car . 1)
    (unsafe-cdr . 1)
    (pair? . 1)
    (null? . 1)
    (vector? . 1)
    (cons . 2)
    (make-vector . 2)
    (vector-length . 1)
    (vector-ref . 2)
    (vector-set! . 3)
    (+ . 2)
    (- . 2)
    (* . 2)
    (= . 2)
    (< . 2)
    (> . 2)))

(define (builtin-primop? name)
  (assq name builtin-primop-arities))

(define (builtin-primop-arity name)
  (cdr (assq name builtin-primop-arities)))

;; Source-level arithmetic operators canonicalize to safe-checked primop forms.
;; The safe-OP runtime helpers verify that both operands are fixnums before
;; performing the operation, mirroring how (car x) → (primop car x) → possibly
;; (primop unsafe-car x) after the pair analysis proves x is definitely a pair.
(define builtin-safe-arith-rename
  '((+ . safe-+) (- . safe--) (* . safe-*) (= . safe-=) (< . safe-<) (> . safe->)))

(define (builtin-primop-canonical-name name)
  (let ((entry (assq name builtin-safe-arith-rename)))
    (if entry (cdr entry) name)))

(define (canonicalize-builtins expr)
  (define wrap-counter 0)
  (define (fresh-wrap-name)
    (set! wrap-counter (+ wrap-counter 1))
    (string->symbol (string-append "wrap." (number->string wrap-counter))))
  (define (make-wrap-lambda name arity)
    (let loop ((i 0) (params '()))
      (if (= i arity)
          (let ((ps (reverse params)))
            `(lambda ,ps (primop ,(builtin-primop-canonical-name name) ,@ps)))
          (loop (+ i 1) (cons (fresh-wrap-name) params)))))
  (define (canon expr)
    (cond
      ((symbol? expr)
       (if (builtin-primop? expr)
           (make-wrap-lambda expr (builtin-primop-arity expr))
           expr))
      ((literal-expr? expr) expr)
      ((pair? expr)
       (let ((entry (and (symbol? (car expr)) (builtin-primop? (car expr)))))
         (if entry
             `(primop ,(builtin-primop-canonical-name (car expr)) ,@(map canon (cdr expr)))
             (case (car expr)
               ((begin)    `(begin ,@(map canon (cdr expr))))
               ((primop)   `(primop ,(cadr expr) ,@(map canon (cddr expr))))
               ((if)       `(if ,(canon (cadr expr))
                                ,(canon (caddr expr))
                                ,(canon (cadddr expr))))
               ((let)
                (let* ((binding (caadr expr))
                       (var (car binding))
                       (val (cadr binding)))
                  `(let ((,var ,(canon val))) ,@(map canon (cddr expr)))))
               ((lambda)   `(lambda ,(cadr expr) ,@(map canon (cddr expr))))
               ((letrec)
                `(letrec ,(map (lambda (b) `(,(car b) ,(canon (cadr b)))) (cadr expr))
                   ,@(map canon (cddr expr))))
               ((app)      `(app ,(canon (cadr expr)) ,@(map canon (cddr expr))))
               ((box)      `(box ,(canon (cadr expr))))
               ((unbox)    `(unbox ,(canon (cadr expr))))
               ((set-box!) `(set-box! ,(canon (cadr expr)) ,(canon (caddr expr))))
               ((global)   expr)
               ((set-global!) `(set-global! ,(cadr expr) ,(canon (caddr expr))))
               (else (error "Unknown expression in canonicalize-builtins" (car expr)))))))
      (else (error "Invalid expression in canonicalize-builtins" expr))))
  (canon expr))

;;; ============================================================================
;;; Pass 2: Letrec Desugaring
;;; Rewrites lambda-only letrec groups into explicit allocation and
;;; initialization. Recursive bindings become boxes containing closures.
;;;
;;; This pass also preserves direct tail recursion by rewriting eligible calls
;;; to explicit self/group tail-call markers, which later stages can lower into
;;; jumps instead of ordinary calls.
;;;
;;; INPUT GRAMMAR: Uniquified (same structure as the Lowered grammar).
;;;
;;; OUTPUT GRAMMAR (Desugared)
;;;
;;;   Expr    ::= Var
;;;             | Literal
;;;             | (global N)
;;;             | (set-global! N Expr)
;;;             | (begin Expr+)
;;;             | (if Expr Expr Expr)
;;;             | (let ((Var Expr)) Expr+)
;;;             ; `letrec` is gone; replaced by let/box/set-box! sequences
;;;             | (lambda (Var*) Expr+)
;;;             | (primop PrimOp Expr*)
;;;             | (app Expr Expr*)          ; non-tail or non-recursive call
;;;             | (self-tail-call Expr*)    ; direct self tail recursion
;;;             | (group-tail-call Var Expr*) ; tail call to another group member
;;;             | (cons Expr Expr)
;;;             | (car Expr)
;;;             | (cdr Expr)
;;;             | (pair? Expr)
;;;             | (null? Expr)
;;;             | (box Expr)
;;;             | (unbox Expr)             ; also used for reading recursive bindings
;;;             | (set-box! Expr Expr)
;;;
;;; Changes: `letrec` is eliminated. Each binding name becomes a `let`-bound
;;;          box, set with `set-box!` after all closures are built. References
;;;          to recursive names become `(unbox Var)`. Direct self/mutual tail
;;;          calls at eligible sites become `self-tail-call` / `group-tail-call`
;;;          instead of `app`.
;;; ============================================================================

(define (desugar-letrec expr)
  ;; Mutual tail-call lowering only works when every member can share one
  ;; calling convention. This arity check is part of that contract.
  (define (all-same-arity? bindings)
    (or (null? bindings)
        (let ((arity (length (cadr (cadar bindings)))))
          (all (lambda (binding)
                 (= (length (cadr (cadr binding))) arity))
                bindings))))

  (define (tail-recursion-safe? expr group-names tail?)
    ;; We only rewrite recursive calls into explicit tail-call markers when the
    ;; recursive binding is used in positions that later passes can preserve as
    ;; jumps. This predicate rejects shapes that would require reifying a
    ;; closure or value from the recursive variable mid-expression.
    (cond
      ((symbol? expr)
       (not (memq expr group-names)))
      
      ((literal-expr? expr) #t)
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          (let loop ((rest (cdr expr)))
            (cond
              ((null? rest) #t)
              ((null? (cdr rest))
               (tail-recursion-safe? (car rest) group-names tail?))
              (else
               (and (tail-recursion-safe? (car rest) group-names #f)
                    (loop (cdr rest)))))))
         
         ((primop)
          (all (lambda (e) (tail-recursion-safe? e group-names #f))
               (cddr expr)))
         
         ((if)
          (and (tail-recursion-safe? (cadr expr) group-names #f)
               (tail-recursion-safe? (caddr expr) group-names tail?)
               (tail-recursion-safe? (cadddr expr) group-names tail?)))
         
         ((let)
          (and (tail-recursion-safe? (cadr (caadr expr)) group-names #f)
               (let loop ((rest (cddr expr)))
                 (cond
                   ((null? rest) #t)
                   ((null? (cdr rest))
                    (tail-recursion-safe? (car rest) group-names tail?))
                   (else
                    (and (tail-recursion-safe? (car rest) group-names #f)
                         (loop (cdr rest))))))))
         
         ((lambda)
          (tail-recursion-safe? (body->expr (cddr expr)) group-names #f))
         
         ((letrec)
          (and (all (lambda (binding)
                      (tail-recursion-safe? (cadr binding) group-names #f))
                    (cadr expr))
               (tail-recursion-safe? (body->expr (cddr expr)) group-names tail?)))
         
         ((app)
          (let ((rator (cadr expr))
                (args (cddr expr)))
            (if (and (symbol? rator) (memq rator group-names))
                (and tail?
                     (all (lambda (arg)
                            (tail-recursion-safe? arg group-names #f))
                          args))
                (and (tail-recursion-safe? rator group-names #f)
                     (all (lambda (arg)
                            (tail-recursion-safe? arg group-names #f))
                          args)))))
         
          ((cons set-box!)
           (and (tail-recursion-safe? (cadr expr) group-names #f)
                (tail-recursion-safe? (caddr expr) group-names #f)))

           ((box unbox car cdr pair? null?)
            (tail-recursion-safe? (cadr expr) group-names #f))

           ((global)
            #t)

           ((set-global!)
            (tail-recursion-safe? (caddr expr) group-names #f))
           
           (else #f)))
      
      (else #f)))

  (define (free-vars-outside-group expr bound group-names)
    (define (collect expr bound)
      (cond
        ((symbol? expr)
         (if (or (memq expr bound) (memq expr group-names))
             '()
             (list expr)))
        
        ((literal-expr? expr) '())
        
        ((pair? expr)
         (case (car expr)
           ((begin)
            (append-map (lambda (e) (collect e bound)) (cdr expr)))
           
           ((primop)
            (append-map (lambda (e) (collect e bound)) (cddr expr)))
           
           ((if)
            (append (collect (cadr expr) bound)
                    (collect (caddr expr) bound)
                    (collect (cadddr expr) bound)))
           
           ((let)
            (let* ((binding (caadr expr))
                   (var (car binding))
                   (val (cadr binding))
                   (body (body->expr (cddr expr))))
              (append (collect val bound)
                      (collect body (cons var bound)))))
           
           ((lambda)
            (collect (body->expr (cddr expr))
                     (append (cadr expr) bound)))
           
           ((letrec)
            (let* ((bindings (cadr expr))
                   (names (map car bindings))
                   (new-bound (append names bound)))
              (append (append-map (lambda (binding)
                                    (collect (cadr binding) new-bound))
                                  bindings)
                      (append-map (lambda (body-expr)
                                    (collect body-expr new-bound))
                                  (cddr expr)))))
           
           ((app)
            (append-map (lambda (e) (collect e bound)) (cdr expr)))
           
           ((set-box!)
            (append (collect (cadr expr) bound)
                    (collect (caddr expr) bound)))

            ((box unbox)
             (collect (cadr expr) bound))

            ((primop)
             (append-map (lambda (e) (collect e bound)) (cddr expr)))

            ((global)
             '())

            ((set-global!)
             (collect (caddr expr) bound))
             
             (else '())))
        
        (else '())))
    
    (dedupe-symbols (collect expr bound)))

  (define (tail-call-targets expr group-names tail?)
    (cond
      ((or (symbol? expr) (literal-expr? expr)) '())
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          (let loop ((rest (cdr expr)))
            (cond
              ((null? rest) '())
              ((null? (cdr rest))
               (tail-call-targets (car rest) group-names tail?))
              (else
               (append (tail-call-targets (car rest) group-names #f)
                       (loop (cdr rest)))))))
         
         ((primop)
          (append-map (lambda (e) (tail-call-targets e group-names #f))
                      (cddr expr)))
         
         ((if)
          (append (tail-call-targets (cadr expr) group-names #f)
                  (tail-call-targets (caddr expr) group-names tail?)
                  (tail-call-targets (cadddr expr) group-names tail?)))
         
         ((let)
          (append (tail-call-targets (cadr (caadr expr)) group-names #f)
                  (let loop ((rest (cddr expr)))
                    (cond
                      ((null? rest) '())
                      ((null? (cdr rest))
                       (tail-call-targets (car rest) group-names tail?))
                      (else
                       (append (tail-call-targets (car rest) group-names #f)
                               (loop (cdr rest))))))))
         
         ((lambda)
          (tail-call-targets (body->expr (cddr expr)) group-names #f))
         
         ((letrec)
          (append (append-map (lambda (binding)
                                (tail-call-targets (cadr binding) group-names #f))
                              (cadr expr))
                  (append-map (lambda (body-expr)
                                (tail-call-targets body-expr group-names tail?))
                              (cddr expr))))
         
         ((app)
          (let ((rator (cadr expr))
                (args (cddr expr)))
            (append (if (and tail? (symbol? rator) (memq rator group-names))
                        (list rator)
                        (tail-call-targets rator group-names #f))
                    (append-map (lambda (arg)
                                  (tail-call-targets arg group-names #f))
                                args))))
         
          ((set-box!)
           (append (tail-call-targets (cadr expr) group-names #f)
                   (tail-call-targets (caddr expr) group-names #f)))

           ((box unbox)
            (tail-call-targets (cadr expr) group-names #f))

           ((global)
            '())

           ((set-global!)
            (tail-call-targets (caddr expr) group-names #f))
           
           (else '())))
      
      (else '())))

  (define (mutually-tail-recursive? bindings)
    (let* ((group-names (map car bindings))
           (graph
            (map (lambda (binding)
                   (let* ((lambda-expr (cadr binding))
                          (body (body->expr (cddr lambda-expr))))
                     (list (car binding)
                           (dedupe-symbols
                            (tail-call-targets body group-names #t)))))
                 bindings)))
      (define (neighbors name)
        (let ((entry (assoc name graph)))
          (if entry (cadr entry) '())))
      (define (reachable? start target visited)
        (cond
          ((eq? start target) #t)
          ((memq start visited) #f)
          (else
           (let loop ((rest (neighbors start)))
             (cond
               ((null? rest) #f)
               ((reachable? (car rest) target (cons start visited)) #t)
               (else (loop (cdr rest))))))))
      (and (all (lambda (name)
                  (not (null? (neighbors name))))
                group-names)
           (all (lambda (name)
                  (all (lambda (other)
                         (reachable? name other '()))
                       group-names))
                group-names))))

  (define (eligible-mutual-tail-group? bindings)
    (let ((group-names (map car bindings)))
      (and (> (length bindings) 1)
           (all-same-arity? bindings)
           (mutually-tail-recursive? bindings)
           (all (lambda (binding)
                  (let* ((lambda-expr (cadr binding))
                         (body (body->expr (cddr lambda-expr))))
                    (tail-recursion-safe? body group-names #t)))
                bindings))))

  (define (group-entry-safe? expr group-names)
    (cond
      ((symbol? expr) (not (memq expr group-names)))
      ((literal-expr? expr) #t)
      ((pair? expr)
       (case (car expr)
         ((begin)
          (all (lambda (e) (group-entry-safe? e group-names)) (cdr expr)))
         ((primop)
          (all (lambda (e) (group-entry-safe? e group-names)) (cddr expr)))
         ((if)
          (and (group-entry-safe? (cadr expr) group-names)
               (group-entry-safe? (caddr expr) group-names)
               (group-entry-safe? (cadddr expr) group-names)))
         ((let)
          (and (group-entry-safe? (cadr (caadr expr)) group-names)
               (all (lambda (e) (group-entry-safe? e group-names)) (cddr expr))))
         ((lambda)
          #f)
         ((app)
          (let ((rator (cadr expr))
                (args (cddr expr)))
            (and (if (and (symbol? rator) (memq rator group-names))
                     #t
                     (group-entry-safe? rator group-names))
                 (all (lambda (arg) (group-entry-safe? arg group-names)) args))))
         ((set-box!)
          (and (group-entry-safe? (cadr expr) group-names)
               (group-entry-safe? (caddr expr) group-names)))
         ((box unbox)
          (group-entry-safe? (cadr expr) group-names))
          ((global)
           #t)
          ((set-global!)
           (group-entry-safe? (caddr expr) group-names))
          (else #f)))
      (else #f)))

  (define (rewrite-sequence exprs env current-group tail?)
    (let loop ((rest exprs) (result '()))
      (cond
        ((null? rest) (reverse result))
        ((null? (cdr rest))
         (reverse (cons (rewrite (car rest) env current-group tail?) result)))
        (else
         (loop (cdr rest)
               (cons (rewrite (car rest) env current-group #f) result))))))

  (define (rewrite-lambda expr env current-group)
    (let* ((params (cadr expr))
           (body-env (remove-shadowed-bindings env params))
           (body-exprs (rewrite-sequence (cddr expr) body-env current-group #t)))
      `(lambda ,params ,@body-exprs)))

  (define (rewrite expr env current-group tail?)
    (cond
      ((symbol? expr)
       ;; After desugaring, recursive bindings are represented as boxes that
       ;; hold closures. Reading such a variable therefore becomes an unbox.
       (let ((binding (assoc expr env)))
          (if binding
              `(unbox ,(cadr binding))
              expr)))
      
      ((literal-expr? expr) expr)
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(rewrite-sequence (cdr expr) env current-group tail?)))
         
         ((primop)
          `(primop ,(cadr expr)
                   ,@(map (lambda (e) (rewrite e env current-group #f)) (cddr expr))))
         
         ((if)
          `(if ,(rewrite (cadr expr) env current-group #f)
               ,(rewrite (caddr expr) env current-group tail?)
               ,(rewrite (cadddr expr) env current-group tail?)))
         
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val-expr (rewrite (cadr binding) env current-group #f))
                 (body-env (remove-shadowed-bindings env (list var)))
                 (body-exprs (rewrite-sequence (cddr expr) body-env current-group tail?)))
            `(let ((,var ,val-expr)) ,@body-exprs)))
         
         ((lambda)
          (rewrite-lambda expr env #f))
         
          ((letrec)
           (let* ((bindings (cadr expr))
                  (names (map car bindings))
                  (group-eligible?
                    (and (eligible-mutual-tail-group? bindings)
                         (group-entry-safe? (body->expr (cddr expr)) names))))
              (if (not (all (lambda (binding)
                              (and (single-binding? binding)
                                   (lambda-expr? (cadr binding))))
                           bindings))
                 (error "letrec requires lambda bindings" expr)
                 (let* ((base-env (remove-shadowed-bindings env names))
                        (rec-env (append (map (lambda (name) (list name name)) names)
                                         base-env))
                        ;; Each letrec name gets a box first so every lambda in
                        ;; the group can refer to the whole recursive knot while
                        ;; the closures are still being constructed.
                        (box-bindings
                         (map (lambda (name) (list name '(box #f))) names))
                        (init-exprs
                         (map (lambda (binding)
                                `(set-box! ,(car binding)
                                          ,(rewrite-lambda (cadr binding)
                                                           rec-env
                                                           (if group-eligible?
                                                               names
                                                               (list (car binding))))))
                             bindings))
                       (body-exprs
                        (append init-exprs
                                (rewrite-sequence (cddr expr)
                                                  rec-env
                                                  current-group
                                                  tail?))))
                  (nest-let-bindings box-bindings body-exprs)))))
         
          ((app)
           (let ((rator (cadr expr))
                 (args (cddr expr)))
             ;; The source language still says "app", but by this point we have
             ;; enough information to distinguish ordinary calls from
             ;; self/group tail recursion. Later passes can then lower the
             ;; explicit markers to jumps.
             (if (and tail?
                      current-group
                      (symbol? rator)
                      (memq rator current-group))
                (if (> (length current-group) 1)
                    `(group-tail-call ,rator
                                      ,@(map (lambda (e) (rewrite e env current-group #f)) args))
                    `(self-tail-call
                      ,@(map (lambda (e) (rewrite e env current-group #f)) args)))
                 `(app ,(rewrite rator env current-group #f)
                       ,@(map (lambda (e) (rewrite e env current-group #f)) args)))))

          ((cons)
           (error "cons in desugar-letrec: should have been canonicalized" expr))
          
          ((box)
           `(box ,(rewrite (cadr expr) env current-group #f)))
          
          ((unbox)
           `(unbox ,(rewrite (cadr expr) env current-group #f)))

          ((car)
           (error "car in desugar-letrec: should have been canonicalized" expr))

          ((cdr)
           (error "cdr in desugar-letrec: should have been canonicalized" expr))

          ((pair?)
           (error "pair? in desugar-letrec: should have been canonicalized" expr))

          ((null?)
           (error "null? in desugar-letrec: should have been canonicalized" expr))
          ((make-vector)
           (error "make-vector in desugar-letrec: should have been canonicalized" expr))
          ((vector-length)
           (error "vector-length in desugar-letrec: should have been canonicalized" expr))
          ((vector-ref)
           (error "vector-ref in desugar-letrec: should have been canonicalized" expr))
          ((vector-set!)
           (error "vector-set! in desugar-letrec: should have been canonicalized" expr))
           
           ((set-box!)
            (let ((target (cadr expr)))
             (when (and (symbol? target) (assoc target env))
               (error "Cannot mutate letrec function binding" target))
             `(set-box! ,(rewrite target env current-group #f)
                        ,(rewrite (caddr expr) env current-group #f))))

           ((global)
            expr)

           ((set-global!)
            `(set-global! ,(cadr expr)
                          ,(rewrite (caddr expr) env current-group #f)))
          
          (else (error "Unknown expression type in letrec desugaring" (car expr)))))
      
      (else (error "Invalid expression in letrec desugaring" expr))))
  
  (rewrite expr '() #f #t))

;;; ============================================================================
;;; Pass 3: Closure Conversion
;;; Turns lambdas into explicit closure values.
;;;
;;; After this pass, a function is represented as:
;;;   1. code plus an explicit environment interface,
;;;   2. an explicit environment payload for captured values, and
;;;   3. closure-call / make-closure forms instead of source-level application.
;;;
;;; INPUT GRAMMAR: Desugared (Pass 2 output).
;;;
;;; OUTPUT GRAMMAR (Closure-Converted)
;;;
;;;   Expr    ::= SimpleExpr
;;;             | (begin Expr+)
;;;             | (if Expr Expr Expr)
;;;             | (let ((Var Expr)) Expr)
;;;             | (make-closure (lambda (Var*) Expr) CaptureExpr*)
;;;             ;   ^ lambda is only legal nested here; `(global N)` appears
;;;             ;     as a capture but not as a standalone Expr arm
;;;             | (closure-call Expr Expr*)    ; generic indirect call
;;;             | (self-tail-call Expr*)        ; direct self tail recursion
;;;             | (group-tail-call Var Expr*)   ; mutual tail call
;;;             | (group-closures MemberSpec* CaptureSpec*)
;;;             ;   ^ mutually tail-recursive cluster emitted as a unit
;;;             | (cons Expr Expr)
;;;             | (car Expr)
;;;             | (cdr Expr)
;;;             | (pair? Expr)
;;;             | (null? Expr)
;;;             | (box Expr)
;;;             | (unbox Expr)
;;;             | (set-box! Expr Expr)
;;;             | (set-global! N Expr)
;;;             | (primop PrimOp Expr*)
;;;
;;;   SimpleExpr ::= Var               ; local variable (after cc, usually (local Var))
;;;               | Literal
;;;               | (local Var)        ; value available directly as a local
;;;               | (closure Var)      ; value accessed from the closure environment
;;;               | (global N)         ; value from a global slot
;;;
;;;   CaptureExpr ::= SimpleExpr
;;;
;;;   MemberSpec  ::= (BoxVar MemberName Params Body)
;;;   CaptureSpec ::= (EnvVar SimpleExpr)
;;;
;;; Changes: `lambda` / `app` are gone as top-level Expr forms. `lambda`
;;;          appears only inside `make-closure`. Variable references gain
;;;          `(local ...)` / `(closure ...)` wrappers. `app` → `closure-call`.
;;;          Mutually tail-recursive letrec clusters become `group-closures`.
;;; ============================================================================

(define (free-vars expr bound)
  ;; Return list of free variables in expr, given bound variables
  (define (collect expr bound)
    (cond
      ((symbol? expr)
       (if (memq expr bound) '() (list expr)))
      
      ((literal-expr? expr) '())
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          (append-map (lambda (e) (collect e bound)) (cdr expr)))
         
         ((primop)
          (append-map (lambda (e) (collect e bound)) (cddr expr)))
         
         ((if)
          (append (collect (cadr expr) bound)
                  (collect (caddr expr) bound)
                  (collect (cadddr expr) bound)))
         
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (cadr binding))
                 (body (body->expr (cddr expr))))
            (append (collect val bound)
                    (collect body (cons var bound)))))
         
         ((lambda)
          (let* ((params (cadr expr))
                 (body (body->expr (cddr expr))))
            (collect body (append params bound))))
         
          ((app)
           (append-map (lambda (e) (collect e bound)) (cdr expr)))

          ((self-tail-call)
           (append-map (lambda (e) (collect e bound)) (cdr expr)))

          ((group-tail-call)
           (append-map (lambda (e) (collect e bound)) (cddr expr)))
           
           ((box unbox)
            (collect (cadr expr) bound))

           ((global)
            '())

           ((set-global!)
            (collect (caddr expr) bound))

           ((set-box!)
            (append (collect (cadr expr) bound)
                    (collect (caddr expr) bound)))
          
          (else (error "Unknown expression in free-vars" (car expr)))))
      
      (else '())))
  
  (dedupe-symbols (collect expr bound)))

(define (closure-convert expr)
  ;; This pass makes environments first-class. Every variable reference is
  ;; reinterpreted as either:
  ;;   - (local x): available directly as a procedure/local binding, or
  ;;   - (closure env.k): represented by one of the synthetic environment
  ;;     parameters introduced for captured values.
  (define (any predicate lst)
    (cond
      ((null? lst) #f)
      ((predicate (car lst)) #t)
      (else (any predicate (cdr lst)))))

  (define (make-env-vars prefix count)
    (let loop ((i 0) (result '()))
      (if (= i count)
          (reverse result)
          (loop (+ i 1)
                (cons (string->symbol
                       (string-append prefix (number->string i)))
                      result)))))

  (define (local-repr-name repr)
    (and (pair? repr)
         (eq? (car repr) 'local)
         (pair? (cdr repr))
         (symbol? (cadr repr))
         (cadr repr)))

  (define (lookup-repr name env)
    (let ((binding (assoc name env)))
      (if binding
          (cadr binding)
          name)))

  (define (collect-group-tail-targets expr)
    (cond
      ((or (symbol? expr) (literal-expr? expr)) '())
      ((pair? expr)
       (case (car expr)
         ((group-tail-call)
          (cons (cadr expr)
                (append-map collect-group-tail-targets (cddr expr))))
         ((begin app set-box!)
          (append-map collect-group-tail-targets (cdr expr)))
         ((primop)
          (append-map collect-group-tail-targets (cddr expr)))
         ((if)
          (append (collect-group-tail-targets (cadr expr))
                  (collect-group-tail-targets (caddr expr))
                  (collect-group-tail-targets (cadddr expr))))
         ((let)
          (append (collect-group-tail-targets (cadr (caadr expr)))
                  (append-map collect-group-tail-targets (cddr expr))))
         ((lambda)
          (collect-group-tail-targets (body->expr (cddr expr))))
         ((box unbox)
           (collect-group-tail-targets (cadr expr)))
         ((global)
          '())
         ((set-global!)
          (collect-group-tail-targets (caddr expr)))
         (else '())))
      (else '())))

  (define (mentions-box-var? expr box-vars)
    (cond
      ((symbol? expr) (memq expr box-vars))
      ((literal-expr? expr) #f)
      ((pair? expr)
       (case (car expr)
         ((begin app primop set-box!)
          (any (lambda (e) (mentions-box-var? e box-vars)) (cdr expr)))
         ((if)
          (or (mentions-box-var? (cadr expr) box-vars)
              (mentions-box-var? (caddr expr) box-vars)
              (mentions-box-var? (cadddr expr) box-vars)))
         ((let)
          (or (mentions-box-var? (cadr (caadr expr)) box-vars)
              (any (lambda (e) (mentions-box-var? e box-vars)) (cddr expr))))
         ((lambda)
          (mentions-box-var? (body->expr (cddr expr)) box-vars))
          ((box unbox)
            (mentions-box-var? (cadr expr) box-vars))
          ((global)
           #f)
          ((set-global!)
           (mentions-box-var? (caddr expr) box-vars))
          (else #f)))
      (else #f)))

  (define (safe-group-body? expr box-vars)
    (cond
      ((symbol? expr) (not (memq expr box-vars)))
      ((literal-expr? expr) #t)
      ((pair? expr)
       (case (car expr)
         ((begin)
          (all (lambda (e) (safe-group-body? e box-vars)) (cdr expr)))
         ((primop)
          (all (lambda (e) (safe-group-body? e box-vars)) (cddr expr)))
         ((if)
          (and (safe-group-body? (cadr expr) box-vars)
               (safe-group-body? (caddr expr) box-vars)
               (safe-group-body? (cadddr expr) box-vars)))
         ((let)
          (and (safe-group-body? (cadr (caadr expr)) box-vars)
               (all (lambda (e) (safe-group-body? e box-vars)) (cddr expr))))
         ((lambda)
          (not (mentions-box-var? (body->expr (cddr expr)) box-vars)))
         ((app)
          (let ((rator (cadr expr))
                (args (cddr expr)))
            (if (and (pair? rator)
                     (eq? (car rator) 'unbox)
                     (symbol? (cadr rator))
                     (memq (cadr rator) box-vars))
                (all (lambda (arg) (safe-group-body? arg box-vars)) args)
                (and (safe-group-body? rator box-vars)
                     (all (lambda (arg) (safe-group-body? arg box-vars)) args)))))
          ((cons make-vector vector-length vector-ref vector-set! vector?)
           (error "vector or list op in safe-group-body?: should have been canonicalized" expr))
         ((box)
           (safe-group-body? (cadr expr) box-vars))
         ((unbox)
           (let ((target (cadr expr)))
             (if (and (symbol? target) (memq target box-vars))
                 #f
                 (safe-group-body? target box-vars))))
          ((set-box!)
           (and (not (and (symbol? (cadr expr)) (memq (cadr expr) box-vars)))
                (safe-group-body? (cadr expr) box-vars)
                (safe-group-body? (caddr expr) box-vars)))
          ((global)
           #t)
          ((set-global!)
           (safe-group-body? (caddr expr) box-vars))
          (else #f)))
      (else #f)))

  (define (extract-group-prefix exprs env)
    (define (links-other-member? member names)
      (let ((name (cadr member))
            (targets (collect-group-tail-targets (cadddr member))))
        (let loop ((rest-targets targets))
          (cond
            ((null? rest-targets) #f)
            ((and (memq (car rest-targets) names)
                  (not (eq? (car rest-targets) name)))
             #t)
            (else
             (loop (cdr rest-targets)))))))

    (define (finish members rest)
      (let ((names (map cadr members))
            (box-vars (map cadr members)))
        (if (and (> (length members) 1)
                 (safe-group-body? (body->expr rest) box-vars)
                 (any (lambda (member)
                        (links-other-member? member names))
                      members))
            (cons members rest)
            #f)))

    (let loop ((rest exprs) (members '()))
      (if (null? rest)
          (finish members '())
          (let ((expr (car rest)))
            (if (and (pair? expr)
                     (eq? (car expr) 'set-box!)
                     (symbol? (cadr expr))
                     (pair? (caddr expr))
                     (eq? (car (caddr expr)) 'lambda))
                (let* ((box-name (cadr expr))
                       (box-repr (lookup-repr box-name env))
                       (local-box (local-repr-name box-repr))
                       (lambda-expr (caddr expr)))
                  (if local-box
                      (loop (cdr rest)
                            (append members
                                    (list (list local-box
                                                box-name
                                                (cadr lambda-expr)
                                                (body->expr (cddr lambda-expr))))))
                      (finish members rest)))
                (finish members rest))))))

  (define (convert-group-prefix exprs env self-tail-prefix)
    (let ((prefix (extract-group-prefix exprs env)))
      (and prefix
            (let* ((members (car prefix))
                   (remaining (cdr prefix))
                   (member-names (map cadr members))
                    ;; All closures in a mutually tail-recursive cluster share
                    ;; one environment payload. That keeps inter-member tail
                    ;; calls cheap and gives later lowering passes a clear path
                    ;; to jump among entry labels without rebuilding closures.
                    (shared-captures
                    (dedupe-symbols
                     (append-map
                      (lambda (member)
                        (free-vars (cadddr member)
                                  (append (caddr member) member-names)))
                     members)))
                  (capture-params
                   (make-env-vars "group.env." (length shared-captures)))
                  (capture-bindings
                   (map (lambda (fv capture-param)
                          (list fv `(local ,capture-param)))
                        shared-captures
                        capture-params))
                  (group-env (append capture-bindings env))
                  (converted-members
                   (map (lambda (member)
                          (let* ((box-var (car member))
                                 (member-name (cadr member))
                                 (params (caddr member))
                                 (body (cadddr member))
                                 (param-bindings
                                  (map (lambda (param)
                                         (list param `(local ,param)))
                                       params))
                             (body-env (append param-bindings group-env)))
                             (list box-var
                                   member-name
                                   params
                                   (convert body body-env '()))))
                         members))
                   (capture-values
                    (map (lambda (fv capture-param)
                           (list capture-param (lookup-repr fv env)))
                         shared-captures
                         capture-params)))
              (cons (cons `(group-closures ,converted-members ,capture-values)
                          (map (lambda (e) (convert e env self-tail-prefix)) remaining))
                    #t)))))

  (define (convert-sequence exprs env self-tail-prefix)
    (let ((group-result (convert-group-prefix exprs env self-tail-prefix)))
      (if group-result
          (car group-result)
          (map (lambda (e) (convert e env self-tail-prefix)) exprs))))

  (define (convert expr env self-tail-prefix)
    ;; env maps source names to their runtime representation. Reading a source
    ;; variable after closure conversion is no longer uniform: locals stay as
    ;; locals, while captured variables become explicit closure payload reads.
    
    (cond
      ((symbol? expr)
       (let ((binding (assoc expr env)))
         (if binding
             (cadr binding)  ; Return the representation
             expr)))         ; Global/primitive
      
      ((literal-expr? expr)
       expr)
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(convert-sequence (cdr expr) env self-tail-prefix)))
         ((primop)
          `(primop ,(cadr expr)
                   ,@(map (lambda (e) (convert e env self-tail-prefix)) (cddr expr))))
         ((if)
          `(if ,(convert (cadr expr) env self-tail-prefix)
               ,(convert (caddr expr) env self-tail-prefix)
               ,(convert (cadddr expr) env self-tail-prefix)))
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (cadr binding))
                 (body (body->expr (cddr expr)))
                 (val-converted (convert val env self-tail-prefix))
                 (new-env (cons (list var `(local ,var)) env))
                 (body-converted (convert body new-env self-tail-prefix)))
            `(let ((,var ,val-converted)) ,body-converted)))
         ((lambda)
          (let* ((params (cadr expr))
                 (body (body->expr (cddr expr)))
                 (fvs (free-vars body params))
                 ;; These synthetic parameters stand for the closure payload
                 ;; that will be prepended to the user-visible parameters.
                 (env-vars (make-env-vars "env." (length fvs)))
                 (param-bindings (map (lambda (p) (list p `(local ,p))) params))
                 (env-bindings (map (lambda (fv env-var)
                                      (list fv `(closure ,env-var)))
                                    fvs env-vars))
                 (new-env (append param-bindings env-bindings env))
                 (self-tail-env (map (lambda (env-var) `(local ,env-var)) env-vars))
                 (body-converted (convert body new-env self-tail-env)))
            ;; The output lambda now expects its environment explicitly, and
            ;; make-closure packages the current values of the free variables
            ;; beside that code pointer.
            `(make-closure
              (lambda ,(append env-vars params) ,body-converted)
              ,@(map (lambda (fv)
                       (let ((binding (assoc fv env)))
                         (if binding
                             (cadr binding)
                             fv)))  ; Global/primitive
                     fvs))))
         ((app)
          (let ((rator (cadr expr))
                (rands (cddr expr)))
            `(closure-call ,(convert rator env self-tail-prefix)
                           ,@(map (lambda (e) (convert e env self-tail-prefix)) rands))))
         ((cons)
          (error "cons in closure-convert: should have been canonicalized" expr))
         ((self-tail-call)
          `(self-tail-call
            ,@self-tail-prefix
            ,@(map (lambda (e) (convert e env self-tail-prefix)) (cdr expr))))
         ((group-tail-call)
          `(group-tail-call
            ,(cadr expr)
            ,@(map (lambda (e) (convert e env self-tail-prefix)) (cddr expr))))
         ((group-closures global)
          expr)
         ((box)
          `(box ,(convert (cadr expr) env self-tail-prefix)))
         ((unbox)
          `(unbox ,(convert (cadr expr) env self-tail-prefix)))
         ((car)
          (error "car in closure-convert: should have been canonicalized" expr))
         ((cdr)
          (error "cdr in closure-convert: should have been canonicalized" expr))
         ((pair?)
          (error "pair? in closure-convert: should have been canonicalized" expr))
          ((null?)
           (error "null? in closure-convert: should have been canonicalized" expr))
          ((make-vector)
           (error "make-vector in closure-convert: should have been canonicalized" expr))
          ((vector-length)
           (error "vector-length in closure-convert: should have been canonicalized" expr))
          ((vector-ref)
           (error "vector-ref in closure-convert: should have been canonicalized" expr))
          ((vector-set!)
           (error "vector-set! in closure-convert: should have been canonicalized" expr))
          ((set-box!)
          `(set-box! ,(convert (cadr expr) env self-tail-prefix)
                     ,(convert (caddr expr) env self-tail-prefix)))
         ((set-global!)
          `(set-global! ,(cadr expr)
                        ,(convert (caddr expr) env self-tail-prefix)))
         (else
          (error "Unknown expression in closure-convert" (car expr)))))
       
      (else (error "Invalid expression in closure-convert" expr))))
  
  (convert expr '() '()))

;;; ============================================================================
;;; Pass 3.5: Normalize for 0CFA and rewrite monomorphic closure calls
;;; The normalization here is intentionally lightweight: it gives every
;;; make-closure a stable procedure name and ensures closure-call operators and
;;; arguments are explicit simple names. That keeps the analysis small while
;;; preserving the source-shaped structure of the program.
;;;
;;; INPUT GRAMMAR: Closure-Converted (Pass 3 output).
;;;
;;; OUTPUT GRAMMAR (CFA-Normalized)
;;;
;;;   Expr    ::= SimpleExpr
;;;             | (begin Expr+)
;;;             | (if Expr Expr Expr)
;;;             | (let ((Var Expr)) Expr+)
;;;             | (make-closure ProcName (lambda (Var*) Expr) SimpleExpr*)
;;;             ;   ^ same as before but now carries a stable synthetic name
;;;             | (closure-call SimpleExpr SimpleExpr*)  ; rator+rands all simple
;;;             | (self-tail-call SimpleExpr*)
;;;             | (group-tail-call Var SimpleExpr*)
;;;             | (group-closures MemberSpec* CaptureSpec*)
;;;             | (cons Expr Expr)
;;;             | (car Expr)
;;;             | (cdr Expr)
;;;             | (pair? Expr)
;;;             | (null? Expr)
;;;             | (box Expr)
;;;             | (unbox Expr)
;;;             | (set-box! Expr Expr)
;;;             | (set-global! N Expr)
;;;             | (primop PrimOp Expr*)
;;;
;;;   SimpleExpr ::= Var | Literal
;;;               | (local Var) | (closure Var) | (global N)
;;;
;;; Changes from Pass 3 output:
;;;   - `make-closure` gains an explicit `ProcName` symbol before the lambda.
;;;   - The operator and all arguments of `closure-call`, `self-tail-call`,
;;;     `group-tail-call`, and the captured values of `make-closure` are all
;;;     `SimpleExpr`. Complex subexpressions are hoisted into fresh `let`
;;;     bindings introduced by this pass.
;;; ============================================================================

(define (cfa-simple-expr? expr)
  (or (symbol? expr)
      (literal-expr? expr)
      (and (pair? expr) (memq (car expr) '(local closure global)))))

(define (wrap-let-bindings bindings body)
  (let loop ((rest (reverse bindings)) (result body))
    (if (null? rest)
        result
        `(let (,(car rest)) ,(loop (cdr rest) result)))))

(define (normalize-for-cfa expr)
  (define temp-counter 0)
  (define proc-counter 0)

  (define (fresh-cfa-temp)
    (set! temp-counter (+ temp-counter 1))
    (string->symbol (string-append "cfa.tmp." (number->string temp-counter))))

  (define (fresh-cfa-proc)
    (set! proc-counter (+ proc-counter 1))
    (string->symbol (string-append "cfa.proc." (number->string proc-counter))))

  (define (normalize-simple expr)
    ;; 0CFA is easier to teach and implement over names than over arbitrary
    ;; nested expressions. This helper hoists a complex subexpression into a
    ;; temporary let-binding whenever needed.
    (let ((normalized (normalize expr)))
      (if (cfa-simple-expr? normalized)
          (values '() normalized)
          (let ((tmp (fresh-cfa-temp)))
            (values (list (list tmp normalized)) tmp)))))

  (define (normalize-simple-list exprs)
    (let loop ((rest exprs) (bindings '()) (result '()))
      (if (null? rest)
          (values bindings (reverse result))
          (let-values (((new-bindings simple-expr)
                        (normalize-simple (car rest))))
            (loop (cdr rest)
                  (append bindings new-bindings)
                  (cons simple-expr result))))))

  (define (normalize-sequence exprs)
    (map normalize exprs))

  (define (normalize expr)
    (cond
      ((or (symbol? expr) (literal-expr? expr)) expr)
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(normalize-sequence (cdr expr))))
         ((primop)
          `(primop ,(cadr expr)
                   ,@(normalize-sequence (cddr expr))))
         ((if)
          `(if ,(normalize (cadr expr))
               ,(normalize (caddr expr))
               ,(normalize (cadddr expr))))
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (normalize (cadr binding)))
                 (body-exprs (normalize-sequence (cddr expr))))
            `(let ((,var ,val)) ,@body-exprs)))
         ((lambda)
          `(lambda ,(cadr expr) ,@(normalize-sequence (cddr expr))))
          ((make-closure)
           (let* ((lambda-expr (cadr expr))
                  (captures (cddr expr)))
             (let-values (((capture-bindings simple-captures)
                           (normalize-simple-list captures)))
               ;; Every closure allocation gets a stable synthetic procedure
               ;; name so the analysis can talk about "which procedure flows
               ;; here?" without comparing lambda syntax trees.
               (let ((proc-name (fresh-cfa-proc)))
                 (wrap-let-bindings
                  capture-bindings
                  `(make-closure ,proc-name
                                 ,(normalize lambda-expr)
                                 ,@simple-captures))))))
          ((closure-call)
           (let-values (((op-bindings simple-op)
                         (normalize-simple (cadr expr)))
                        ((arg-bindings simple-args)
                         (normalize-simple-list (cddr expr))))
             ;; Calls are normalized to "simple operator, simple arguments" so
             ;; the analysis logic can focus on flow propagation instead of
             ;; recursively re-lowering nested source expressions.
             (wrap-let-bindings
              (append op-bindings arg-bindings)
              `(closure-call ,simple-op ,@simple-args))))
         ((self-tail-call)
          (let-values (((arg-bindings simple-args)
                        (normalize-simple-list (cdr expr))))
            (wrap-let-bindings arg-bindings `(self-tail-call ,@simple-args))))
         ((group-tail-call)
          (let-values (((arg-bindings simple-args)
                        (normalize-simple-list (cddr expr))))
            (wrap-let-bindings
             arg-bindings
             `(group-tail-call ,(cadr expr) ,@simple-args))))
         ((group-closures)
          `(group-closures
            ,(map (lambda (member)
                    (list (car member)
                          (cadr member)
                          (caddr member)
                          (normalize (cadddr member))))
                  (cadr expr))
            ,(map (lambda (capture-spec)
                    (list (car capture-spec)
                          (normalize (cadr capture-spec))))
                  (caddr expr))))
          ((cons)
            (error "cons in normalize-for-cfa: should have been canonicalized" expr))
          ((make-vector)
            (error "make-vector in normalize-for-cfa: should have been canonicalized" expr))
          ((vector-length)
            (error "vector-length in normalize-for-cfa: should have been canonicalized" expr))
          ((vector-ref)
            (error "vector-ref in normalize-for-cfa: should have been canonicalized" expr))
          ((vector-set!)
            (error "vector-set! in normalize-for-cfa: should have been canonicalized" expr))
           ((set-box!)
           `(set-box! ,(normalize (cadr expr)) ,(normalize (caddr expr))))
          ((box unbox)
           `(,(car expr) ,(normalize (cadr expr))))
          ((set-global!)
           `(set-global! ,(cadr expr) ,(normalize (caddr expr))))
         ((local closure global)
           expr)
         (else
          (error "Unknown expression in CFA normalization" (car expr)))))
      (else
       (error "Invalid expression in CFA normalization" expr))))

  (normalize expr))

;;; ============================================================================
;;; Pass 3.6: 0CFA Analysis and Known-Call Rewriting
;;; run-0cfa computes a whole-program 0th-order control-flow analysis over the
;;; CFA-normalized IR. rewrite-known-calls then uses that result to replace
;;; generic `closure-call` sites with `known-call` wherever exactly one
;;; procedure can flow to the operator.
;;;
;;; INPUT GRAMMAR: CFA-Normalized (Pass 3.5 output).
;;;
;;; OUTPUT GRAMMAR (CFA-Rewritten)
;;;
;;;   Expr    ::= SimpleExpr
;;;             | (begin Expr+)
;;;             | (if Expr Expr Expr)
;;;             | (let ((Var Expr)) Expr+)
;;;             | (make-closure ProcName (lambda (Var*) Expr) SimpleExpr*)
;;;             | (closure-call SimpleExpr SimpleExpr*)  ; polymorphic call site
;;;             | (known-call ProcName CaptureCount SimpleExpr SimpleExpr*)
;;;             ;   ^ monomorphic call site: ProcName is the unique callee,
;;;             ;     CaptureCount is how many env slots precede the user args,
;;;             ;     SimpleExpr is the closure value (carries the environment)
;;;             | (self-tail-call SimpleExpr*)
;;;             | (group-tail-call Var SimpleExpr*)
;;;             | (group-closures MemberSpec* CaptureSpec*)
;;;             | (cons Expr Expr)
;;;             | (car Expr)
;;;             | (cdr Expr)
;;;             | (pair? Expr)
;;;             | (null? Expr)
;;;             | (box Expr)
;;;             | (unbox Expr)
;;;             | (set-box! Expr Expr)
;;;             | (set-global! N Expr)
;;;             | (primop PrimOp Expr*)
;;;
;;;   SimpleExpr ::= Var | Literal
;;;               | (local Var) | (closure Var) | (global N)
;;;
;;; Changes: some `closure-call` sites become `known-call`; everything else
;;; is structurally unchanged.
;;; ============================================================================

(define (run-0cfa expr)
  ;; The analysis tracks five related facts:
  ;;   - procedures: metadata for every closure-allocated procedure,
  ;;   - var-flow: which procedures may flow to each variable-like name,
  ;;   - box-flow: which procedures may be stored in each box,
  ;;   - global-flow: which procedures may be stored in each global slot,
  ;;   - proc-results: which procedures may be returned by each procedure.
  (define procedures (make-hash-table))
  (define var-flow (make-hash-table))
  (define box-flow (make-hash-table))
  (define global-flow (make-hash-table))
  (define proc-results (make-hash-table))
  (define changed #f)

  (define (table-keys table)
    (map car (cdr table)))

  (define (flow-ref table key)
    (let ((value (hash-ref table key)))
      (if value value '())))

  (define (add-flow! table key values)
    (if (or (not key) (null? values))
        #f
        (let* ((current (flow-ref table key))
               (updated (dedupe-symbols (append current values))))
          (if (set-equal? current updated)
              #f
              (begin
                (hash-set! table key updated)
                (set! changed #t)
                #t)))))

  (define (repr-name expr)
    (cond
      ((symbol? expr) expr)
      ((and (pair? expr) (memq (car expr) '(local closure))) (cadr expr))
      (else #f)))

  (define (box-key expr)
    (repr-name expr))

  (define (collect-procedures expr)
    ;; First pass over the normalized tree: assign stable metadata to each
    ;; make-closure site so the dataflow phase can refer to procedures by name.
    (cond
      ((or (symbol? expr) (literal-expr? expr)) 'done)
      ((pair? expr)
       (case (car expr)
         ((begin)
          (for-each collect-procedures (cdr expr)))
         ((primop cons set-box!)
          (for-each collect-procedures (cdr expr)))
         ((if)
          (collect-procedures (cadr expr))
          (collect-procedures (caddr expr))
          (collect-procedures (cadddr expr)))
         ((let)
          (collect-procedures (cadr (caadr expr)))
          (for-each collect-procedures (cddr expr)))
         ((lambda)
          (for-each collect-procedures (cddr expr)))
         ((make-closure)
          (let ((proc-name (cadr expr))
                (lambda-expr (caddr expr))
                (captures (cdddr expr)))
            (hash-set! procedures
                       proc-name
                       (list (length captures)
                             (cadr lambda-expr)
                             (body->expr (cddr lambda-expr))))
            (collect-procedures (body->expr (cddr lambda-expr)))
            (for-each collect-procedures captures)))
         ((closure-call known-call self-tail-call)
          (for-each collect-procedures (cdr expr)))
         ((group-tail-call)
          (for-each collect-procedures (cddr expr)))
         ((group-closures)
           (for-each (lambda (member)
                       (collect-procedures (cadddr member)))
                     (cadr expr))
           (for-each (lambda (capture-spec)
                       (collect-procedures (cadr capture-spec)))
                     (caddr expr)))
          ((box unbox)
           (collect-procedures (cadr expr)))
          ((set-global!)
           (collect-procedures (caddr expr)))
          ((local closure global) 'done)
          (else
           (error "Unknown expression while collecting CFA procedures" (car expr)))))
      (else
       (error "Invalid expression while collecting CFA procedures" expr))))

  (collect-procedures expr)

  (define (analyze-expr expr current-proc)
    (cond
      ((literal-expr? expr) '())
      ((symbol? expr) (flow-ref var-flow expr))
      ((pair? expr)
        (case (car expr)
          ((local closure)
           (flow-ref var-flow (cadr expr)))
          ((global)
           (flow-ref global-flow (cadr expr)))
          ((begin)
           (let loop ((rest (cdr expr)) (last '()))
             (if (null? rest)
                last
                (loop (cdr rest)
                      (analyze-expr (car rest) current-proc)))))
         ((primop)
          (begin
            (for-each (lambda (subexpr)
                        (analyze-expr subexpr current-proc))
                      (cdr expr))
            '()))
         ((if)
          (begin
            (analyze-expr (cadr expr) current-proc)
            (set-union (analyze-expr (caddr expr) current-proc)
                       (analyze-expr (cadddr expr) current-proc))))
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (value-set (analyze-expr (cadr binding) current-proc)))
            (add-flow! var-flow var value-set)
            (analyze-expr (body->expr (cddr expr)) current-proc)))
          ((make-closure)
           (let* ((proc-name (cadr expr))
                  (meta (hash-ref procedures proc-name))
                 (capture-count (car meta))
                 (params (cadr meta))
                 (captures (cdddr expr))
                 (env-params
                  (let loop ((rest params) (remaining capture-count) (result '()))
                    (if (= remaining 0)
                        (reverse result)
                        (loop (cdr rest)
                              (- remaining 1)
                              (cons (car rest) result))))))
             ;; Closing over a value means the abstract values flowing to that
             ;; capture now also flow to the synthetic environment parameter.
             (let loop ((env-rest env-params) (capture-rest captures))
               (if (or (null? env-rest) (null? capture-rest))
                   'done
                   (begin
                    (add-flow! var-flow
                               (car env-rest)
                               (analyze-expr (car capture-rest) current-proc))
                    (loop (cdr env-rest) (cdr capture-rest)))))
            (list proc-name)))
          ((closure-call)
           (let* ((proc-set (analyze-expr (cadr expr) current-proc))
                  (arg-sets (map (lambda (arg)
                                   (analyze-expr arg current-proc))
                                 (cddr expr))))
             ;; For every possible callee, push each argument's abstract values
             ;; into that callee's formal parameters, then union together the
             ;; abstract results that procedure may return.
             (for-each
              (lambda (proc-name)
                (let* ((meta (hash-ref procedures proc-name))
                      (capture-count (car meta))
                      (params (cadr meta))
                      (actual-params (list-tail params capture-count)))
                 (let loop ((param-rest actual-params) (arg-rest arg-sets))
                   (if (or (null? param-rest) (null? arg-rest))
                       'done
                       (begin
                         (add-flow! var-flow (car param-rest) (car arg-rest))
                         (loop (cdr param-rest) (cdr arg-rest)))))))
             proc-set)
            (let loop ((rest proc-set) (result '()))
              (if (null? rest)
                  result
                  (loop (cdr rest)
                        (set-union result
                                   (flow-ref proc-results (car rest))))))))
          ((self-tail-call)
           (let ((meta (and current-proc (hash-ref procedures current-proc))))
             (if (not meta)
                 '()
                 (let* ((capture-count (car meta))
                        (params (cadr meta))
                        (actual-params (list-tail params capture-count))
                        (actual-arg-sets
                         (map (lambda (arg)
                                (analyze-expr arg current-proc))
                              (list-tail (cdr expr) capture-count))))
                   (let loop ((param-rest actual-params) (arg-rest actual-arg-sets))
                     (if (or (null? param-rest) (null? arg-rest))
                         'done
                         (begin
                           (add-flow! var-flow (car param-rest) (car arg-rest))
                           (loop (cdr param-rest) (cdr arg-rest)))))
                   (flow-ref proc-results current-proc)))))
         ((group-tail-call)
          (begin
            (for-each (lambda (arg)
                        (analyze-expr arg current-proc))
                      (cddr expr))
            '()))
         ((group-closures)
          (begin
            (for-each (lambda (capture-spec)
                        (analyze-expr (cadr capture-spec) current-proc))
                      (caddr expr))
            '()))
         ((box)
          (begin
            (analyze-expr (cadr expr) current-proc)
            '()))
         ((unbox)
          (let ((key (box-key (cadr expr))))
            (analyze-expr (cadr expr) current-proc)
            (if key
                (flow-ref box-flow key)
                '())))
          ((set-box!)
           (let ((value-set (analyze-expr (caddr expr) current-proc))
                 (key (box-key (cadr expr))))
             (analyze-expr (cadr expr) current-proc)
             (add-flow! box-flow key value-set)
             value-set))
          ((set-global!)
           (let ((value-set (analyze-expr (caddr expr) current-proc)))
             (add-flow! global-flow (cadr expr) value-set)
             value-set))
          (else
           (error "Unknown expression in 0CFA" (car expr)))))
      (else
       (error "Invalid expression in 0CFA" expr))))

  (let loop ()
    (set! changed #f)

    ;; Re-run the program body and all procedure bodies until the abstract
    ;; environments and result sets stop growing.
    (analyze-expr expr #f)
    (for-each
     (lambda (proc-name)
       (let* ((meta (hash-ref procedures proc-name))
              (body (caddr meta))
              (result-set (analyze-expr body proc-name)))
         (add-flow! proc-results proc-name result-set)))
     (table-keys procedures))
     (if changed
         (loop)
         (list procedures var-flow box-flow global-flow proc-results))))

(define (rewrite-known-calls expr analysis)
  (let ((procedures (car analysis))
         (var-flow (cadr analysis))
         (box-flow (caddr analysis))
         (global-flow (cadddr analysis)))
    (define (flow-ref table key)
      (let ((value (hash-ref table key)))
        (if value value '())))

    (define (repr-name expr)
      (cond
        ((symbol? expr) expr)
        ((and (pair? expr) (memq (car expr) '(local closure))) (cadr expr))
        (else #f)))

    (define (box-key expr)
      (repr-name expr))

    (define (closure-set expr)
      (cond
        ((symbol? expr) (flow-ref var-flow expr))
        ((literal-expr? expr) '())
        ((pair? expr)
         (case (car expr)
           ((local closure)
            (flow-ref var-flow (cadr expr)))
            ((global)
             (flow-ref global-flow (cadr expr)))
            ((unbox)
             (let ((key (box-key (cadr expr))))
               (if key
                  (flow-ref box-flow key)
                  '())))
           ((make-closure)
            (list (cadr expr)))
            ((let)
             (closure-set (body->expr (cddr expr))))
           ((begin)
            (if (null? (cdr expr))
                '()
                (closure-set (car (reverse (cdr expr))))))
           ((if)
            (set-union (closure-set (caddr expr))
                       (closure-set (cadddr expr))))
           (else '())))
        (else '())))

    (define (rewrite expr)
      (cond
        ((or (symbol? expr) (literal-expr? expr)) expr)
        ((pair? expr)
         (case (car expr)
           ((begin)
            `(begin ,@(map rewrite (cdr expr))))
           ((primop)
            `(primop ,(cadr expr) ,@(map rewrite (cddr expr))))
           ((if)
            `(if ,(rewrite (cadr expr))
                 ,(rewrite (caddr expr))
                 ,(rewrite (cadddr expr))))
           ((let)
            `(let (,(list (car (caadr expr))
                          (rewrite (cadr (caadr expr)))))
               ,@(map rewrite (cddr expr))))
           ((lambda)
            `(lambda ,(cadr expr) ,@(map rewrite (cddr expr))))
           ((make-closure)
            `(make-closure ,(cadr expr)
                           ,(rewrite (caddr expr))
                           ,@(map rewrite (cdddr expr))))
            ((closure-call)
             (let* ((rator (rewrite (cadr expr)))
                    (args (map rewrite (cddr expr)))
                    (targets (closure-set rator)))
               ;; If 0CFA proves there is exactly one possible callee, keep the
               ;; closure value for its environment but replace the generic
               ;; indirect call with a direct known-call form.
               (if (and (= (length targets) 1)
                        (hash-ref procedures (car targets)))
                   (let* ((proc-name (car targets))
                          (meta (hash-ref procedures proc-name))
                          (capture-count (car meta)))
                    `(known-call ,proc-name ,capture-count ,rator ,@args))
                  `(closure-call ,rator ,@args))))
           ((known-call)
            `(known-call ,(cadr expr)
                         ,(caddr expr)
                         ,(rewrite (cadddr expr))
                         ,@(map rewrite (cddddr expr))))
           ((self-tail-call)
            `(self-tail-call ,@(map rewrite (cdr expr))))
           ((group-tail-call)
            `(group-tail-call ,(cadr expr) ,@(map rewrite (cddr expr))))
           ((group-closures)
            `(group-closures
              ,(map (lambda (member)
                      (list (car member)
                            (cadr member)
                            (caddr member)
                            (rewrite (cadddr member))))
                    (cadr expr))
              ,(map (lambda (capture-spec)
                      (list (car capture-spec)
                            (rewrite (cadr capture-spec))))
                    (caddr expr))))
            ((cons set-box! make-vector vector-ref vector-set!)
             `(,(car expr) ,(rewrite (cadr expr)) ,(rewrite (caddr expr))))
           ((set-global!)
            `(set-global! ,(cadr expr) ,(rewrite (caddr expr))))
             ((box unbox car cdr pair? null? vector-length vector? local closure global)
              `(,(car expr) ,(rewrite (cadr expr))))
            (else
             (error "Unknown expression in known-call rewrite" (car expr)))))
        (else
         (error "Invalid expression in known-call rewrite" expr))))

    (rewrite expr)))

;;; ============================================================================
;;; Pass 4: Convert to Three-Address Code (TAC)
;;; Lowers expression-oriented code into a flat, explicit instruction stream.
;;;
;;; TAC makes evaluation order, temporary values, branches, and returns
;;; concrete. This is the point where expression trees become something closer
;;; to an imperative program.
;;;
;;; INPUT GRAMMAR: CFA-Rewritten (Pass 3.6 output).
;;;
;;; OUTPUT
;;;
;;; The result is NOT an expression; it is a pair of:
;;;   - a flat list of TAC instructions (the entry-point body), and
;;;   - a list of <procedure> records, one per lifted lambda/make-closure site.
;;;
;;;   Instr   ::= (assign Var RHS)
;;;             | (label Label)
;;;             | (if Var Label Label)
;;;             | (goto Label)
;;;             | (return Var)
;;;             | (tail-call Var Var*)            ; indirect tail call
;;;             | (direct-tail-call ProcName Var*) ; direct tail call
;;;             | (set-box! Var Var)
;;;             | (set-global! N Var)
;;;
;;;   RHS     ::= Var | Literal
;;;             | (primop PrimOp Var*)
;;;             | (cons Var Var)
;;;             | (box Var)
;;;             | (unbox Var) | (car Var) | (cdr Var)
;;;             | (pair? Var) | (null? Var) | (vector? Var)
;;;             | (vector-length Var)
;;;             | (global N)
;;;             | (closure-env-ref Var N)     ; load env slot N from closure Var
;;;             | (make-closure ProcName Var*) ; allocate closure over free vars
;;;             | (closure-call Var Var*)      ; indirect call
;;;             | (direct-call ProcName Var*)  ; direct call
;;;
;;;   Label   ::= Symbol
;;;   Var     ::= Symbol
;;;
;;; Changes: expression nesting is gone. Every sub-expression result lands in a
;;; fresh temporary. Lambdas are lifted to top-level <procedure> records.
;;; `if` becomes a three-field branch instruction. `begin` sequences become
;;; consecutive instructions with labels at join points.
;;; ============================================================================

(define-record-type <procedure>
  (make-procedure name params instructions)
  procedure?
  (name procedure-name)
  (params procedure-params)
  (instructions procedure-instructions))

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

(define (expr->tac expr)
  ;; Convert expression-shaped IR into a linear, statement-shaped program.
  ;; The result splits into:
  ;;   - TAC instructions for the current body, and
  ;;   - lifted procedures created from nested lambdas/closures.
  
  (define temp-counter 0)
  (define (fresh-temp)
    (set! temp-counter (+ temp-counter 1))
    (string->symbol (string-append "t" (number->string temp-counter))))
  
  (define proc-counter 0)
  (define (fresh-proc)
    (set! proc-counter (+ proc-counter 1))
    (string->symbol (string-append "proc" (number->string proc-counter))))
  
  (define (simple? expr)
    ;; Check if expression is simple (doesn't need temporaries)
    (or (symbol? expr) (literal-expr? expr)
        (and (pair? expr) (memq (car expr) '(local closure)))))
  
  (define (simple-value expr)
    (if (and (pair? expr) (memq (car expr) '(local closure)))
        (cadr expr)
        expr))
  
  (define (convert-list exprs)
    (let loop ((rest exprs)
               (instrs '())
               (vars '())
               (procedures '()))
      (if (null? rest)
          (values instrs vars procedures)
          (let-values (((new-instrs new-var new-procedures)
                        (convert-value (car rest) #f)))
            (loop (cdr rest)
                  (append instrs new-instrs)
                  (append vars (list new-var))
                  (append procedures new-procedures))))))

  (define (convert-call closure-expr args)
    (let-values (((closure-instrs closure-var closure-procedures)
                  (convert-value closure-expr #f))
                 ((arg-instrs arg-vars arg-procedures)
                  (convert-list args)))
      (values (append closure-instrs arg-instrs)
              closure-var
              arg-vars
              (append closure-procedures arg-procedures))))

  (define (convert-known-call proc-name capture-count closure-expr args dest tail?)
    ;; known-call still starts from a closure value because that closure carries
    ;; captured variables. TAC makes those hidden environment arguments explicit
    ;; by loading each payload slot before emitting the direct call.
    (let-values (((closure-instrs closure-var closure-procedures)
                  (convert-value closure-expr #f))
                 ((arg-instrs arg-vars arg-procedures)
                  (convert-list args)))
      (let loop ((index 0) (env-instrs '()) (env-vars '()))
        (if (= index capture-count)
            (let ((all-args (append (reverse env-vars) arg-vars)))
              (if tail?
                  (values (append closure-instrs
                                  arg-instrs
                                  env-instrs
                                  (list `(direct-tail-call ,proc-name ,@all-args)))
                          (append closure-procedures arg-procedures))
                  (let ((result-var (or dest (fresh-temp))))
                    (values (append closure-instrs
                                    arg-instrs
                                    env-instrs
                                    (list `(assign ,result-var
                                                   (direct-call ,proc-name ,@all-args))))
                            result-var
                            (append closure-procedures arg-procedures)))))
            (let ((env-var (fresh-temp)))
              (loop (+ index 1)
                    (append env-instrs
                            (list `(assign ,env-var
                                           (closure-env-ref ,closure-var ,index))))
                    (cons env-var env-vars)))))))

  (define (local-name expr)
    (and (pair? expr)
         (eq? (car expr) 'local)
         (pair? (cdr expr))
         (symbol? (cadr expr))
         (cadr expr)))

  (define (match-cluster-init expr)
    (and (pair? expr)
         (eq? (car expr) 'set-box!)
         (let ((name (local-name (cadr expr)))
               (value (caddr expr)))
           (and name
                 (pair? value)
                 (eq? (car value) 'make-closure)
                 (let* ((named-closure?
                         (and (symbol? (cadr value))
                              (pair? (caddr value))
                              (eq? (car (caddr value)) 'lambda)))
                        (lambda-expr (if named-closure?
                                         (caddr value)
                                         (cadr value))))
                   (and (pair? lambda-expr)
                        (eq? (car lambda-expr) 'lambda)
                        (list name
                              (cadr lambda-expr)
                              (body->expr (cddr lambda-expr)))))))))

  (define (match-group-closures expr)
    (and (pair? expr)
         (eq? (car expr) 'group-closures)
         (pair? (cdr expr))
         (pair? (cddr expr))
         (null? (cdddr expr))
         (list (cadr expr) (caddr expr))))

  (define (cluster-body-compatible? expr names)
    (cond
      ((or (symbol? expr) (literal-expr? expr)) #t)
      ((pair? expr)
       (case (car expr)
         ((begin)
          (all (lambda (e) (cluster-body-compatible? e names)) (cdr expr)))
         ((primop)
          (all (lambda (e) (cluster-body-compatible? e names)) (cddr expr)))
         ((if)
          (and (cluster-body-compatible? (cadr expr) names)
               (cluster-body-compatible? (caddr expr) names)
               (cluster-body-compatible? (cadddr expr) names)))
         ((let)
          (and (cluster-body-compatible? (cadr (caadr expr)) names)
               (all (lambda (e) (cluster-body-compatible? e names))
                    (cddr expr))))
         ((lambda)
          (cluster-body-compatible? (body->expr (cddr expr)) names))
          ((group-tail-call)
           (and (symbol? (cadr expr))
                (memq (cadr expr) names)
                (all (lambda (e) (cluster-body-compatible? e names))
                     (cddr expr))))
          ((self-tail-call) #f)
           ((app closure-call known-call set-box! cons make-vector vector-ref vector-set!)
            (all (lambda (e) (cluster-body-compatible? e names)) (cdr expr)))
           ((box unbox car cdr pair? null? vector-length vector?)
             (cluster-body-compatible? (cadr expr) names))
          ((global local closure) #t)
          ((set-global!)
           (cluster-body-compatible? (caddr expr) names))
          (else #f)))
      (else #f)))

  (define (collect-group-tail-targets expr)
    (cond
      ((or (symbol? expr) (literal-expr? expr)) '())
      ((pair? expr)
       (case (car expr)
          ((group-tail-call)
           (cons (cadr expr)
                 (append-map collect-group-tail-targets (cddr expr))))
           ((begin app closure-call known-call set-box! cons make-vector vector-ref vector-set!)
            (append-map collect-group-tail-targets (cdr expr)))
         ((primop)
          (append-map collect-group-tail-targets (cddr expr)))
         ((if)
          (append (collect-group-tail-targets (cadr expr))
                  (collect-group-tail-targets (caddr expr))
                  (collect-group-tail-targets (cadddr expr))))
         ((let)
          (append (collect-group-tail-targets (cadr (caadr expr)))
                  (append-map collect-group-tail-targets (cddr expr))))
         ((lambda)
           (collect-group-tail-targets (body->expr (cddr expr))))
            ((box unbox car cdr pair? null? vector-length vector?)
             (collect-group-tail-targets (cadr expr)))
           ((global)
            '())
           ((set-global!)
            (collect-group-tail-targets (caddr expr)))
           (else '())))
      (else '())))

  (define (all-same-member-arity? members)
    (or (null? members)
        (let ((arity (length (cadr (car members)))))
          (all (lambda (member)
                 (= (length (cadr member)) arity))
               members))))

  (define (has-cross-group-tail-call? members names)
    (let loop ((rest members))
      (cond
        ((null? rest) #f)
        (else
         (let ((name (car (car rest)))
               (targets (collect-group-tail-targets (caddr (car rest)))))
           (if (let inner ((remaining-targets targets))
                 (cond
                   ((null? remaining-targets) #f)
                   ((and (memq (car remaining-targets) names)
                         (not (eq? (car remaining-targets) name)))
                    #t)
                   (else
                    (inner (cdr remaining-targets)))))
               #t
               (loop (cdr rest))))))))

  (define (extract-cluster-prefix exprs)
    (define (finish members rest)
      (let ((names (map car members)))
        (if (and (> (length members) 1)
                 (all-same-member-arity? members)
                 (all (lambda (member)
                        (cluster-body-compatible? (caddr member) names))
                      members)
                 (has-cross-group-tail-call? members names))
            (cons members rest)
            #f)))
    (let loop ((rest exprs) (members '()))
      (cond
        ((null? rest) (finish members '()))
        (else
         (let ((member (match-cluster-init (car rest))))
           (if member
               (loop (cdr rest) (append members (list member)))
               (finish members rest)))))))

  ;; Collect all names n such that (local n) appears anywhere in the expression tree.
  (define (local-refs-in-expr expr)
    (cond
      ((not (pair? expr)) '())
      ((and (eq? (car expr) 'local)
            (pair? (cdr expr))
            (null? (cddr expr))
            (symbol? (cadr expr)))
       (list (cadr expr)))
      (else
       (append-map local-refs-in-expr expr))))

  (define (build-dispatch-instructions entry-tag dispatch-label member-labels)
    (let loop ((rest member-labels)
               (index 0)
               (current-label dispatch-label)
               (instrs '()))
      (if (null? (cdr rest))
          (append instrs
                  (list `(label ,current-label)
                        `(goto ,(car rest))))
          (let ((next-label (fresh-temp))
                (cmp-var (fresh-temp)))
            (loop (cdr rest)
                  (+ index 1)
                  next-label
                  (append instrs
                          (list `(label ,current-label)
                                `(assign ,cmp-var (primop = ,entry-tag ,index))
                                `(if ,cmp-var ,(car rest) ,next-label))))))))

  (define (convert-cluster-prefix exprs)
    (define (lower-cluster members capture-specs remaining-exprs)
      (let* ((cluster-proc (fresh-proc))
             (shared-params (map (lambda (ignored) (fresh-temp))
                                 (caddr (car members))))
             (entry-tag (fresh-temp))
             (dispatch-label
              (string->symbol
               (string-append "dispatch." (symbol->string cluster-proc))))
             (member-labels
              (map (lambda (member)
                     (string->symbol
                      (string-append "entry."
                                     (symbol->string (cadr member)))))
                   members))
             (group-context
              (map (lambda (member label)
                     (list (cadr member) label))
                   members
                   member-labels))
              (capture-param-names (map car capture-specs))
              (capture-value-exprs (map cadr capture-specs)))
        (let-values (((capture-instrs capture-vars capture-procedures)
                      (convert-list capture-value-exprs)))
          ;; Determine which members are "external": their box-var appears in
          ;; remaining-exprs as a (local name) reference, meaning they are called
          ;; from outside the cluster.  Internal-only members skip closure
          ;; allocation and the dispatch; they are reachable only via a
          ;; group-tail-call goto from other members.
          (let* ((all-local-refs (append-map local-refs-in-expr remaining-exprs))
                 (box-vars (map car members))
                 (external-box-names (filter (lambda (n) (memq n box-vars)) all-local-refs))
                 (is-external?
                  ;; If no (local name) refs are found, fall back to treating all as external.
                  (if (null? external-box-names)
                      (lambda (m) #t)
                      (lambda (m) (memq (car m) external-box-names))))
                 (dispatch-member-labels
                  (let loop ((ms members) (ls member-labels) (result '()))
                    (if (null? ms)
                        (reverse result)
                        (loop (cdr ms) (cdr ls)
                              (if (is-external? (car ms))
                                  (cons (car ls) result)
                                  result))))))
          ;; A tail-recursive cluster becomes one procedure with an entry tag.
          ;; Entering the cluster chooses a member label; jumping between
          ;; members becomes a plain goto after rewriting the shared parameters.
          (let ((init-instrs
                 (let loop ((rest members) (index 0) (instrs capture-instrs))
                   (if (null? rest)
                       instrs
                       (let ((box-name (car (car rest))))
                         (if (is-external? (car rest))
                             (let ((closure-temp (fresh-temp)))
                               (loop (cdr rest)
                                     (+ index 1)
                                     (append instrs
                                             (list `(assign ,closure-temp
                                                            (make-closure ,cluster-proc ,index ,@capture-vars))
                                                   `(set-box! ,box-name ,closure-temp)))))
                             ;; Internal-only member: no closure allocation, no dispatch entry.
                             (loop (cdr rest) index instrs)))))))
            (let loop ((rest members)
                       (labels member-labels)
                       (instrs (build-dispatch-instructions entry-tag
                                                           dispatch-label
                                                           dispatch-member-labels))
                       (procedures capture-procedures))
              (if (null? rest)
                  (values init-instrs
                          (append procedures
                                  (list (make-procedure cluster-proc
                                                        (append (list entry-tag)
                                                                capture-param-names
                                                                shared-params)
                                                        instrs)))
                          remaining-exprs)
                  (let* ((member (car rest))
                         (params (caddr member))
                         (body (cadddr member))
                         (entry-label (car labels)))
                    (let-values (((body-instrs body-procedures)
                                  (convert-tail body
                                                params
                                                entry-label
                                                group-context
                                                shared-params)))
                      (loop (cdr rest)
                            (cdr labels)
                            (append instrs
                                    (list `(label ,entry-label))
                                    (map (lambda (param shared)
                                           `(assign ,param ,shared))
                                         params
                                         shared-params)
                                    body-instrs)
                            (append procedures body-procedures)))))))))))
    (let ((explicit (and (pair? exprs) (match-group-closures (car exprs)))))
      (if explicit
          (lower-cluster (car explicit) (cadr explicit) (cdr exprs))
          (let ((cluster (extract-cluster-prefix exprs)))
            (if (not cluster)
                (values '() '() exprs)
                (lower-cluster
                 (map (lambda (member)
                        (list (car member) (car member) (cadr member) (caddr member)))
                      (car cluster))
                 '()
                 (cdr cluster)))))))

  (define (convert-tail expr current-params current-entry-label group-context shared-params)
    (cond
      ((simple? expr)
       (values (list `(return ,(simple-value expr))) '()))
      
       ((pair? expr)
        (case (car expr)
          ((begin)
           (let ((body-exprs (cdr expr)))
            (let-values (((cluster-instrs cluster-procedures remaining-exprs)
                          (convert-cluster-prefix body-exprs)))
              (let loop ((rest remaining-exprs)
                         (instrs cluster-instrs)
                         (procedures cluster-procedures))
                (cond
                  ((null? rest)
                   (error "begin requires at least one expression"))
                  ((null? (cdr rest))
                   (let-values (((tail-instrs tail-procedures)
                                 (convert-tail (car rest)
                                               current-params
                                               current-entry-label
                                               group-context
                                               shared-params)))
                     (values (append instrs tail-instrs)
                             (append procedures tail-procedures))))
                  (else
                   (let-values (((new-instrs ignored-result new-procedures)
                                 (convert-value (car rest) #f)))
                     (loop (cdr rest)
                           (append instrs new-instrs)
                           (append procedures new-procedures)))))))))
         
          ((if)
           (let* ((then-label (fresh-temp))
                  (else-label (fresh-temp)))
             ;; Tail-position conditionals can branch directly to two tail
             ;; fragments because both branches end in a return or tail-call.
             (let-values (((test-instrs test-var test-procedures)
                           (convert-value (cadr expr) #f))
                         ((then-instrs then-procedures)
                          (convert-tail (caddr expr)
                                        current-params
                                        current-entry-label
                                        group-context
                                        shared-params))
                         ((else-instrs else-procedures)
                          (convert-tail (cadddr expr)
                                        current-params
                                        current-entry-label
                                        group-context
                                        shared-params)))
              (values
               (append test-instrs
                       (list `(if ,test-var ,then-label ,else-label))
                       (list `(label ,then-label))
                       then-instrs
                       (list `(label ,else-label))
                       else-instrs)
               (append test-procedures
                       then-procedures
                       else-procedures)))))
         
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (cadr binding))
                 (body (body->expr (cddr expr))))
            (let-values (((val-instrs val-result val-procedures)
                          (convert-value val #f))
                         ((body-instrs body-procedures)
                          (convert-tail body
                                        current-params
                                        current-entry-label
                                        group-context
                                        shared-params)))
              (values (append val-instrs
                              (list `(assign ,var ,val-result))
                              body-instrs)
                      (append val-procedures body-procedures)))))
         
          ((self-tail-call)
           (if (not current-entry-label)
               (error "self-tail-call outside of procedure" expr)
               (let ((args (cdr expr)))
                 (when (not (= (length args) (length current-params)))
                   (error "Arity mismatch in self-tail-call" expr))
                 (let-values (((arg-instrs arg-vars arg-procedures)
                               (convert-list args)))
                   ;; Rebind the current parameters and jump back to the
                   ;; procedure entry label. At TAC level, a self tail call is
                   ;; already just control flow, not a call instruction.
                   (values (append arg-instrs
                                   (map (lambda (param arg)
                                          `(assign ,param ,arg))
                                       current-params
                                       arg-vars)
                                  (list `(goto ,current-entry-label)))
                          arg-procedures)))))
         
         ((group-tail-call)
          (if (or (not group-context) (not shared-params))
              (error "group-tail-call outside of cluster" expr)
              (let* ((target (cadr expr))
                     (args (cddr expr))
                     (entry (assoc target group-context)))
                (when (not entry)
                  (error "Unknown group-tail-call target" target))
                (when (not (= (length args) (length shared-params)))
                  (error "Arity mismatch in group-tail-call" expr))
                (let-values (((arg-instrs arg-vars arg-procedures)
                              (convert-list args)))
                  (values (append arg-instrs
                                  (map (lambda (shared arg)
                                         `(assign ,shared ,arg))
                                       shared-params
                                       arg-vars)
                                  (list `(goto ,(cadr entry))))
                          arg-procedures)))))
         
          ((closure-call)
           (let ((closure-expr (cadr expr))
                 (args (cddr expr)))
             (let-values (((call-instrs closure-var arg-vars procedures)
                           (convert-call closure-expr args)))
               (values (append call-instrs
                               (list `(tail-call ,closure-var ,@arg-vars)))
                       procedures))))

          ((known-call)
           (convert-known-call (cadr expr)
                               (caddr expr)
                               (cadddr expr)
                               (cddddr expr)
                               #f
                               #t))
          
          (else
           (let-values (((instrs result-var procedures)
                         (convert-value expr #f)))
            (values (append instrs (list `(return ,result-var)))
                    procedures)))))
      
      (else
       (error "Invalid expression in tail position" expr))))
  
  (define (convert-value expr dest)
    ;; dest: optional destination variable
    ;; Returns: (values instructions result-var procedures)
    (define (convert-unary-value-op op arg-expr)
      (let-values (((instrs arg-var procedures)
                    (convert-value arg-expr #f)))
        (let ((result-var (or dest (fresh-temp))))
          (values (append instrs
                          (list `(assign ,result-var (,op ,arg-var))))
                  result-var
                  procedures))))

    (define (convert-binary-value-op op left-expr right-expr)
      (let-values (((left-instrs left-var left-procedures)
                    (convert-value left-expr #f))
                   ((right-instrs right-var right-procedures)
                    (convert-value right-expr #f)))
        (let ((result-var (or dest (fresh-temp))))
          (values (append left-instrs
                          right-instrs
                          (list `(assign ,result-var (,op ,left-var ,right-var))))
                  result-var
                  (append left-procedures right-procedures)))))

    (cond
      ((simple? expr)
       (let ((value (simple-value expr)))
         (if dest
             (if (eq? dest value)
                 (values '() dest '())
                 (values (list `(assign ,dest ,value)) dest '()))
             (values '() value '()))))
      
      ((pair? expr)
        (case (car expr)
          ((global)
           (let ((result-var (or dest (fresh-temp))))
             (values (list `(assign ,result-var ,expr))
                     result-var
                     '())))
          ((begin)
          (let ((body-exprs (cdr expr)))
            (let-values (((cluster-instrs cluster-procedures remaining-exprs)
                          (convert-cluster-prefix body-exprs)))
              (let loop ((rest remaining-exprs)
                         (instrs cluster-instrs)
                         (procedures cluster-procedures))
                (cond
                  ((null? rest)
                   (error "begin requires at least one expression"))
                  ((null? (cdr rest))
                   (let-values (((last-instrs last-result last-procedures)
                                 (convert-value (car rest) dest)))
                     (values (append instrs last-instrs)
                             last-result
                             (append procedures last-procedures))))
                  (else
                   (let-values (((new-instrs ignored-result new-procedures)
                                 (convert-value (car rest) #f)))
                     (loop (cdr rest)
                           (append instrs new-instrs)
                           (append procedures new-procedures)))))))))
         
          ((primop)
           (let ((op (cadr expr))
                 (args (cddr expr)))
             (let-values (((arg-instrs arg-vars arg-procedures)
                           (convert-list args)))
              (let ((result-var (or dest (fresh-temp))))
                (values (append arg-instrs
                                (list `(assign ,result-var
                                               (primop ,op ,@arg-vars))))
                        result-var
                        arg-procedures)))))
         
           ((cons)
            (error "cons in expr->tac: should have been canonicalized" expr))
          ((make-vector)
            (error "make-vector in expr->tac: should have been canonicalized" expr))
          ((vector-length)
            (error "vector-length in expr->tac: should have been canonicalized" expr))
          ((vector-ref)
            (error "vector-ref in expr->tac: should have been canonicalized" expr))
          ((vector-set!)
            (error "vector-set! in expr->tac: should have been canonicalized" expr))
          ((vector?)
            (error "vector? in expr->tac: should have been canonicalized" expr))

          ((box)
           (convert-unary-value-op 'box (cadr expr)))
           
          ((unbox)
           (convert-unary-value-op 'unbox (cadr expr)))

          ((car)
           (error "car in expr->tac: should have been canonicalized" expr))
          ((cdr)
           (error "cdr in expr->tac: should have been canonicalized" expr))
          ((pair?)
           (error "pair? in expr->tac: should have been canonicalized" expr))
          ((null?)
           (error "null? in expr->tac: should have been canonicalized" expr))
         
          ((if)
           (let* ((then-label (fresh-temp))
                  (else-label (fresh-temp))
                  (join-label (fresh-temp))
                  (result-var (or dest (fresh-temp))))
             ;; Value-position conditionals need an explicit join so both
             ;; branches assign into the same destination before control merges.
             (let-values (((test-instrs test-var test-procedures)
                           (convert-value (cadr expr) #f))
                         ((then-instrs then-result then-procedures)
                          (convert-value (caddr expr) result-var))
                         ((else-instrs else-result else-procedures)
                          (convert-value (cadddr expr) result-var)))
              (values
               (append test-instrs
                       (list `(if ,test-var ,then-label ,else-label))
                       (list `(label ,then-label))
                       then-instrs
                       (list `(goto ,join-label))
                       (list `(label ,else-label))
                       else-instrs
                       (list `(goto ,join-label))
                       (list `(label ,join-label)))
               result-var
               (append test-procedures
                       then-procedures
                       else-procedures)))))
         
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val (cadr binding))
                 (body (body->expr (cddr expr))))
            (let-values (((val-instrs val-result val-procedures)
                          (convert-value val #f)))
              (let ((assign-instr `(assign ,var ,val-result)))
                (let-values (((body-instrs body-result body-procedures)
                              (convert-value body dest)))
                  (values (append val-instrs (list assign-instr) body-instrs)
                          body-result
                          (append val-procedures body-procedures)))))))
         
          ((make-closure)
            (let* ((named-closure?
                    (and (symbol? (cadr expr))
                         (pair? (caddr expr))
                         (eq? (car (caddr expr)) 'lambda)))
                  (proc-name (if named-closure?
                                 (cadr expr)
                                 (fresh-proc)))
                  (lambda-expr (if named-closure?
                                   (caddr expr)
                                   (cadr expr)))
                  (free-vars (if named-closure?
                                 (cdddr expr)
                                 (cddr expr)))
                   (proc-params (cadr lambda-expr))
                   (proc-body (body->expr (cddr lambda-expr))))
              (let ((entry-label (fresh-temp)))
                ;; TAC lifts each lambda body into its own procedure and turns
                ;; the source-level lambda expression into data: a make-closure
                ;; instruction that points at the lifted procedure plus captures.
                (let-values (((body-instrs body-procedures)
                              (convert-tail proc-body
                                           proc-params
                                          entry-label
                                          #f
                                          #f))
                           ((fv-instrs fv-vars fv-procedures)
                            (convert-list free-vars)))
                (let ((result-var (or dest (fresh-temp)))
                      (procedure
                       (make-procedure proc-name
                                       proc-params
                                       (cons `(label ,entry-label) body-instrs))))
                  (values (append fv-instrs
                                  (list `(assign ,result-var
                                                 (make-closure ,proc-name
                                                               ,@fv-vars))))
                          result-var
                          (append body-procedures
                                   fv-procedures
                                   (list procedure))))))))

          ((known-call)
           (convert-known-call (cadr expr)
                               (caddr expr)
                               (cadddr expr)
                               (cddddr expr)
                               dest
                               #f))
          
          ((closure-call)
           (let* ((closure-expr (cadr expr))
                  (args (cddr expr)))
            (let-values (((call-instrs closure-var arg-vars procedures)
                          (convert-call closure-expr args)))
              (let ((result-var (or dest (fresh-temp))))
                (values (append call-instrs
                                (list `(assign ,result-var
                                               (closure-call ,closure-var
                                                             ,@arg-vars))))
                        result-var
                        procedures)))))
         
         ((group-tail-call)
          (error "group-tail-call is only valid in tail position" expr))
         
          ((set-box!)
           (let-values (((box-instrs box-var box-procedures)
                         (convert-value (cadr expr) #f))
                        ((val-instrs val-var val-procedures)
                         (convert-value (caddr expr) #f)))
             (let ((result-var (or dest val-var)))
              (values (append box-instrs
                              val-instrs
                              (list `(set-box! ,box-var ,val-var))
                              (if (eq? result-var val-var)
                                  '()
                                  (list `(assign ,result-var ,val-var))))
                       result-var
                       (append box-procedures val-procedures)))))

          ((set-global!)
           (let-values (((val-instrs val-var val-procedures)
                         (convert-value (caddr expr) #f)))
             (let ((result-var (or dest val-var)))
               (values (append val-instrs
                               (list `(set-global! ,(cadr expr) ,val-var))
                               (if (eq? result-var val-var)
                                   '()
                                   (list `(assign ,result-var ,val-var))))
                       result-var
                       val-procedures))))
          
          ((local closure)
           (values '() (cadr expr) '()))
         
         (else
          (error "Unknown expression in expr->tac" (car expr)))))
      
      (else
       (error "Invalid expression in expr->tac" expr))))
  
  (convert-tail expr '() #f #f #f))

;;; ============================================================================
;;; Data Structures for CFG
;;; ============================================================================

;; We need to define the record type differently for mutable fields
;; In standard Scheme, we can use a constructor with mutable fields
(define-record-type <basic-block>
  (make-basic-block label instructions)
  basic-block?
  (label basic-block-label)
  (instructions basic-block-instructions)
  (successors basic-block-successors set-basic-block-successors!))

;;; ============================================================================
;;; Pass 5: Build Control Flow Graph (CFG)
;;; Groups TAC instructions into basic blocks and records control-flow edges.
;;;
;;; The CFG is the boundary between the mostly source-shaped middle end and the
;;; backend. Once code is in CFG form, later stages can reason in terms of
;;; blocks, successors, liveness, and register allocation.
;;;
;;; INPUT: a flat list of TAC instructions (Pass 4 output).
;;;
;;; OUTPUT: a list of <basic-block> records.
;;;
;;;   BasicBlock ::= { label:      Label | #f
;;;                  , instrs:     Instr*   ; same TAC instructions as input
;;;                  , successors: BlockIndex* }
;;;
;;;   BlockIndex ::= Integer   ; 0-based index into the block list
;;;
;;; Block boundaries (leaders):
;;;   - index 0 (the first instruction is always a leader),
;;;   - any `(label L)` instruction,
;;;   - any instruction that immediately follows a terminator
;;;     (`if` / `goto` / `return` / `tail-call` / `direct-tail-call`).
;;;
;;; Successor edges come only from the terminator of each block:
;;;   `(if _ then else)`        → two successors (then-block, else-block)
;;;   `(goto L)`                → one successor (block labelled L)
;;;   `(return _)`              → no successors (function exit)
;;;   `(tail-call _ _*)`        → no successors (indirect tail transfer)
;;;   `(direct-tail-call N _*)` → no successors (direct tail transfer)
;;;   fall-through              → one successor (next block in list)
;;; ============================================================================

(define (build-cfg tac-instrs)
  ;; Convert linear TAC into basic blocks. Each block has one entry and exits
  ;; only through its final terminator or by falling through to the next block.
  
  (define (terminator? instr)
    (and (pair? instr)
         (memq (car instr) '(if goto return tail-call direct-tail-call))))

  (define (is-leader? index instrs)
    ;; Determine if instruction at index is a basic block leader
    (let ((instr (list-ref instrs index)))
      (or (= index 0)  ; First instruction is always a leader
          (and (pair? instr) (eq? (car instr) 'label))  ; Labels are leaders
          (and (> index 0)  ; Instruction after a terminator is a leader
               (terminator? (list-ref instrs (- index 1)))))))
  
  (define (split-into-blocks instrs)
    ;; Leaders mark block boundaries: the first instruction, every label, and
    ;; every instruction that follows a terminator.
    (let* ((len (length instrs))
           (leaders (make-vector len #f)))
      
      ;; Mark all leaders
      (do ((i 0 (+ i 1)))
          ((= i len))
        (vector-set! leaders i (is-leader? i instrs)))
      
      ;; Collect blocks
      (let loop ((i 0) (blocks '()) (current-block '()) (current-label #f))
        (cond
          ((= i len)
           ;; End of instructions - finish last block
           (if (null? current-block)
               (reverse blocks)
               (reverse (cons (make-basic-block current-label 
                                               (reverse current-block))
                             blocks))))
          
          ((vector-ref leaders i)
           ;; Start of a new block
           (if (null? current-block)
               ;; First block
               (let ((instr (list-ref instrs i)))
                 (loop (+ i 1)
                       blocks
                       (list instr)
                       (if (and (pair? instr) (eq? (car instr) 'label))
                           (cadr instr)
                           #f)))
               ;; Finish current block and start new one
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
           ;; Continue current block
           (loop (+ i 1)
                 blocks
                 (cons (list-ref instrs i) current-block)
                 current-label))))))
  
  (define (find-successors blocks)
    ;; Once blocks are formed, successor edges come only from the final
    ;; instruction of each block.
    (let ((label->block (make-hash-table)))
      
      ;; Build mapping from label to block index
      (do ((i 0 (+ i 1)) (block-list blocks (cdr block-list)))
          ((null? block-list))
        (let* ((block (car block-list))
               (label (basic-block-label block)))
          (when label
            (hash-set! label->block label i))))
      
      ;; Determine successors for each block
      (do ((i 0 (+ i 1)) (block-list blocks (cdr block-list)))
          ((null? block-list))
        (let* ((block (car block-list))
               (instrs (basic-block-instructions block))
               (last-instr (if (null? instrs) #f (car (reverse instrs)))))
          
          (cond
            ((not last-instr)
             ;; Empty block - no successors
             (set-basic-block-successors! block '()))
            
             ((and (pair? last-instr) (eq? (car last-instr) 'if))
              ;; Conditional branch
              (let ((then-label (caddr last-instr))
                    (else-label (cadddr last-instr)))
               (set-basic-block-successors! 
                block 
                (list (hash-ref label->block then-label)
                      (hash-ref label->block else-label)))))
            
             ((and (pair? last-instr) (eq? (car last-instr) 'goto))
              ;; Unconditional jump
              (let ((target-label (cadr last-instr)))
                (set-basic-block-successors! 
                 block 
                 (list (hash-ref label->block target-label)))))
             
              ((and (pair? last-instr) (memq (car last-instr) '(return tail-call direct-tail-call)))
               ;; Function/program exit
               (set-basic-block-successors! block '()))
             
             ((= i (- (length blocks) 1))
              ;; Last block with no jump - no successors
              (set-basic-block-successors! block '()))
            
            (else
             ;; Fall through to next block
             (set-basic-block-successors! block (list (+ i 1)))))))
      
      blocks))
  
  ;; Main CFG construction
  (let ((blocks (split-into-blocks tac-instrs)))
     (find-successors blocks)))

;;; ============================================================================
;;; Shared infrastructure for Passes 5.5 and 5.5b: Forward Must-Analysis
;;;
;;; A "must set" is an unordered list of variable symbols representing facts
;;; that hold on EVERY path to the current point (intersection join).
;;;
;;; Generic driver: `rewrite-cfg-with-must-analysis`
;;;   cfg           — list of basic-blocks
;;;   transfer-instr — (facts instr) → facts': update the must-set after instr
;;;   edge-facts     — (pred-block succ-index pred-out) → facts': optional
;;;                    conditional refinement on a CFG edge (e.g. then-branch
;;;                    of a type-test).  Pass the identity for no refinement.
;;;   rewrite-instr  — (instr facts) → instr': rewrite one instruction using
;;;                    the current must-set; return instr unchanged if no rewrite.
;;;
;;; Returns a new CFG list with rewrites applied.
;;; ============================================================================

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

  (define (set-equal? xs ys)
    (and (null? (set-difference xs ys)) (null? (set-difference ys xs))))

  (define (transfer-block facts block)
    (let loop ((rest (basic-block-instructions block)) (f facts))
      (if (null? rest) f (loop (cdr rest) (transfer-instr f (car rest))))))

  ;; Build predecessor map.
  (define predecessors (make-vector block-count '()))
  (let loop ((i 0))
    (when (< i block-count)
      (for-each (lambda (succ)
                  (vector-set! predecessors succ (cons i (vector-ref predecessors succ))))
                (basic-block-successors (list-ref cfg i)))
      (loop (+ i 1))))

  ;; Forward fixed-point iteration (intersection join = must semantics).
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
              (unless (set-equal? (vector-ref in-facts i) new-in)
                (vector-set! in-facts i new-in)
                (set! any-changed #t))
              (unless (set-equal? (vector-ref out-facts i) new-out)
                (vector-set! out-facts i new-out)
                (set! any-changed #t))
              (loop (+ i 1)))))
        (fixed-point any-changed))))

  ;; Rewrite each block using its computed entry facts.
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

;;; ============================================================================
;;; Pass 5.5: Pair Must-Analysis — unsafe car/cdr rewrite
;;; Facts: definitely-pair(var) — var holds a pair on every incoming path.
;;; Sources: (primop cons …), then-edge of (if (primop pair? x) …), copy of pair.
;;; Join: intersection.  Rewrites (primop car/cdr x) → unsafe-car/cdr when proven.
;;; ============================================================================

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
    ;; If block ends with  (assign t (primop pair? x)) / (if t …), return x.
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

;;; ============================================================================
;;; Pass 5.5b: Fixnum Must-Analysis — unsafe arithmetic rewrite
;;; Facts: definitely-fixnum(var) — var holds a fixnum on every incoming path.
;;; Sources: numeric literals, arithmetic primops (+/-/* and safe variants), copy.
;;; Comparison ops (= < >) yield booleans, not fixnums — excluded from sources.
;;; Join: intersection.  Rewrites (primop safe-OP a b) → (primop OP a b) when both
;;; operands are proven fixnums, eliminating the runtime type-check call.
;;; ============================================================================

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

;;; ============================================================================
;;; Pass 5.6: Constant Folding on CFG
;;; Runs a forward must-analysis to discover variables whose value is
;;; unconditionally a known compile-time constant (a literal: number, boolean,
;;; or null) on every path to a given program point.  Where a primop
;;; application can be evaluated at compile time (all argument variables carry
;;; known constant values), the assign is rewritten to a literal assignment.
;;; Conditional branches on known-constant conditions are rewritten to
;;; unconditional gotos and their block successor lists updated.
;;;
;;; Facts tracked:
;;;   definitely-constant(var, val): var holds the literal val on all
;;;   incoming paths.
;;;
;;; Sources of certainty:
;;;   - `(assign v lit)`             → v = lit.
;;;   - `(assign v u)`               → v = facts[u]  when u is known constant.
;;;   - `(assign v (primop op …))`   → v = fold(op, …) when all arg variables
;;;                                    carry known constants and the op folds.
;;;   - Inline literals in primop arg positions (TAC allows mixed Var/Lit args).
;;;
;;; Join uses intersection (must semantics): a variable is known constant at a
;;; join only if every predecessor path agrees on the same value.
;;; ============================================================================

(define (constant-fold-cfg cfg)
  (define block-count (length cfg))

  ;; --- facts-map helpers -------------------------------------------
  ;; A facts map is an association list  ((var . literal) …).
  ;; We wrap looked-up values as (list val) so that boolean #f is
  ;; distinguishable from "not found".

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
    ;; Keep only bindings present in both maps with identical values.
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

  ;; --- primop constant folding -------------------------------------
  ;; Returns (list result-literal) on success, #f if not foldable.
  ;; Wrapping avoids ambiguity when the result is boolean #f.

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

  ;; --- transfer function -------------------------------------------

  (define (lookup-arg facts v)
    ;; Return (list val) if v is a known constant (inline literal or
    ;; variable with a fact), else #f.
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

  ;; --- predecessor map ---------------------------------------------

  (define predecessors (make-vector block-count '()))
  (let build-preds ((i 0))
    (when (< i block-count)
      (for-each
       (lambda (succ)
         (vector-set! predecessors succ (cons i (vector-ref predecessors succ))))
       (basic-block-successors (list-ref cfg i)))
      (build-preds (+ i 1))))

  ;; --- forward fixed-point -----------------------------------------

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

  ;; --- rewrite pass ------------------------------------------------

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
                    ;; Fold a pure primop assignment when all args are constants.
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
                    ;; Copy propagation: replace a variable copy with its constant.
                    ((and (pair? instr)
                          (eq? (car instr) 'assign)
                          (symbol? (caddr instr)))
                     (let ((vb (facts-lookup facts (caddr instr))))
                       (if vb
                           (list `(assign ,(cadr instr) ,(car vb)) new-succs)
                           (list instr new-succs))))
                    ;; Constant branch: fold (if known-cond L1 L2) to a goto.
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

;;; ============================================================================
;;; Pass 5.7: Dead Write Elimination on CFG
;;; Runs a standard backward liveness analysis on the TAC CFG. An assignment
;;; `(assign v rhs)` is removed when v is not live after the instruction and
;;; rhs is pure (no observable side effects).
;;;
;;; Pure RHS forms (safe to discard):
;;;   literals, variable copies, (primop op …) for arithmetic /comparison /safe
;;;   predicates (+ - * = < > null? pair? unsafe-car unsafe-cdr),
;;;   (global N), (closure-env-ref v N), (unbox v).
;;;
;;; The vector-length, vector-ref, make-vector, vector-set! primops are
;;;   impure: they carry runtime checks (tag/dispatch) that may trap.
;;;   The vector? predicate is pure---it is an inline tag-only check.
;;;
;;; Non-pure RHS forms (never eliminated):
;;;   (cons …), (box …), (make-closure …), (make-vector …),
;;;   (closure-call …), (direct-call …),
;;;   (primop car …), (primop cdr …),
;;;   (primop vector-length …), (primop vector-ref …), (primop vector-set! …)
;;;   — these carry a type-check side effect or allocate.
;;; ============================================================================

(define (eliminate-dead-writes-cfg cfg)
  (define block-count (length cfg))

  ;; --- TAC variable use / def helpers ------------------------------

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
    ;; #t when evaluating rhs produces no observable side effects and may be
    ;; safely discarded if its result is never used.
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

  ;; --- block-level use / def for liveness --------------------------

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

  ;; --- backward fixed-point liveness -------------------------------

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

    ;; --- rewrite: remove dead pure assignments -------------------

    (define (rewrite-block block out-live)
      ;; Walk instructions backwards, maintaining the live set, and collect
      ;; the surviving instructions in forward order.
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
                        ;; Removed instruction: liveness is unchanged.
                        live
                        ;; Kept instruction: propagate liveness backwards.
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

;;; ============================================================================
;;; Backend: instruction selection and linear-scan allocation
;;; The backend proceeds in three conceptual steps:
;;;
;;;   1. instruction selection:
;;;      TAC operations become machine-like instructions with symbolic homes
;;;      (virtual registers / abstract operands),
;;;   2. analysis and allocation:
;;;      liveness is computed and linear scan assigns registers or stack slots,
;;;   3. finalization:
;;;      calling-convention details, prologue/epilogue code, and helper calls
;;;      are made explicit before assembly emission.
;;;
;;; ── Step 1: Instruction Selection ──────────────────────────────────────────
;;;
;;; INPUT: CFG of TAC instructions (Pass 5 output).
;;;
;;; OUTPUT: <machine-procedure> with <machine-block>* of abstract machine
;;;         instructions. Operands are still *symbolic* (Var or Literal); no
;;;         physical registers or stack offsets appear yet.
;;;
;;;   MachInstr ::= (move-in Var ArgLocation)   ; param arrives from calling conv
;;;               | (move Var Operand)
;;;               | (binop Op Var Operand Operand)
;;;               | (alloc-pair Var Operand Operand)
;;;               | (alloc-box Var Operand)
;;;               | (load-box Var Operand)
;;;               | (load-car Var Operand)
;;;               | (load-cdr Var Operand)
;;;               | (is-pair Var Operand)
;;;               | (is-null Var Operand)
;;;               | (load-closure-env Var Operand N)
;;;               | (load-global Var N)
;;;               | (alloc-closure Var ProcName Operand*)
;;;               | (store-box Operand Operand)
;;;               | (store-global N Operand)
;;;               | (call Var Operand Operand*)      ; indirect call, Var = result
;;;               | (call-known Var ProcName Operand*) ; direct call
;;;               | (tail-call Operand Operand*)     ; indirect tail call
;;;               | (tail-call-known ProcName Operand*) ; direct tail call
;;;               | (branch-if Operand Label Label)
;;;               | (jump Label)
;;;               | (ret Operand)
;;;
;;;   ArgLocation ::= (arg-register Reg) | (stack-arg N)
;;;   Operand     ::= Var | Literal | ArgLocation
;;;
;;; ── Step 2: Liveness Analysis + Linear-Scan Allocation ─────────────────────
;;;
;;; INPUT: <machine-procedure> with symbolic Var operands (step 1 output).
;;;
;;; OUTPUT: same instruction set with all Var operands replaced by homes:
;;;
;;;   Home ::= (register Reg)   ; callee-saved register
;;;          | (stack-slot N)   ; frame slot (spill or GC root shadow)
;;;          | (arg-register Reg)
;;;          | (stack-arg N)
;;;
;;; Additional GC root-sync instructions are inserted around safepoints
;;; (`alloc-box`, `alloc-pair`, `alloc-closure`, `call`, `call-known`):
;;;   - before: `(move (stack-slot N) (register Reg))` for each live root
;;;   - after:  `(move (register Reg) (stack-slot N))` reloads updated pointers
;;;
;;; ── Step 3: ABI Finalization ────────────────────────────────────────────────
;;;
;;; INPUT: allocated <machine-procedure> (step 2 output).
;;;
;;; OUTPUT: fully lowered instruction list ready for assembly emission.
;;;         The `call`, `tail-call`, `call-known`, `tail-call-known`, and `ret`
;;;         pseudo-instructions are expanded into ABI-concrete sequences.
;;;         Prologue and epilogue pseudo-instructions are made explicit.
;;;
;;;   Additional finalized instructions (not present in earlier steps):
;;;
;;;   (allocate-frame N)              ; stp x29,x30 + sub sp
;;;   (save-callee-saved Reg*)        ; store each used callee-saved reg
;;;   (init-frame-slots N)            ; zero out GC root slots
;;;   (gc-push-frame ProcName)        ; link frame into GC frame chain
;;;   (gc-pop-frame)                  ; unlink before tail/return
;;;   (restore-callee-saved Reg*)     ; reload callee-saved regs
;;;   (deallocate-frame N)            ; add sp + ldp x29,x30
;;;   (move-out Operand Operand)      ; place arg in calling-conv location
;;;   (call-indirect N)               ; branch-with-link via hop_call_N helper
;;;   (call-label ProcName)           ; branch-with-link to known label
;;;   (tail-call-indirect N)          ; branch via hop_tail_call_N helper
;;;   (tail-call-label ProcName)      ; branch to known label
;;;   (ret)                           ; return (no operand; result already in x0)
;;; ============================================================================

(define aarch64-arg-registers '(x0 x1 x2 x3 x4 x5 x6 x7))
(define aarch64-return-register 'x0)
;; These are the general-purpose registers this backend may keep hop_value
;; temporaries in between safepoints. They are callee-saved in the platform ABI,
;; so ordinary calls preserve them once we spill/restore them in the prologue.
(define aarch64-callee-saved '(x19 x20 x21 x22 x23 x24 x25 x26 x27 x28))
(define gc-frame-header-bytes 16)

(define (set-union xs ys)
  (dedupe-symbols (append xs ys)))

(define (set-difference xs ys)
  (let loop ((rest xs) (result '()))
    (cond
      ((null? rest) (reverse result))
      ((memq (car rest) ys)
       (loop (cdr rest) result))
      (else
       (loop (cdr rest) (cons (car rest) result))))))

(define (set-equal? xs ys)
  (and (null? (set-difference xs ys))
       (null? (set-difference ys xs))))

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
                       ;; Parameters arrive according to the calling convention.
                       ;; The backend IR makes that explicit with move-in pseudo
                       ;; instructions before ordinary instruction selection.
                       (map (lambda (binding)
                              `(move-in ,(car binding) ,(cadr binding)))
                            param-locations)
                       '()))
                 (selected-block
                  (select-machine-block (car blocks) initial-instrs)))
            (loop (cdr blocks)
                  #f
                  (cons selected-block result)))))))

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
  ;; A plain copy is the easiest place to recover a redundant move: if the
  ;; destination can reuse the source register, the emitted move disappears.
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
        ;; Standard backwards dataflow:
        ;;   out[B] = union of in[S] for successors S
        ;;   in[B]  = use[B] union (out[B] - def[B])
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
  ;; The block-level in/out sets tell us which variables are live at block
  ;; boundaries. Walk each block backwards to refine that into a per-instruction
  ;; live-before set. We use those fine-grained sets to decide exactly which
  ;; register-held values must be materialized into stack-visible root slots
  ;; before a GC safepoint.
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
  ;; Collapse liveness information into live intervals. Linear scan only needs
  ;; to know the first and last program point where each variable is live.
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
                     ;; This minimal allocator spills instead of splitting
                     ;; intervals: if no register is free, the value gets a
                     ;; stack slot for its whole live range.
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
  ;; Register-homed values still need a stack-visible root slot because GC only
  ;; walks frame slots. Each register home gets a dedicated shadow slot; we fill
  ;; those slots lazily at safepoints rather than after every definition.
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
  ;; After a safepoint, reload every live register-homed variable from its
  ;; root slot so that GC-updated pointers are visible to subsequent code.
  ;; We skip def-var because the safepoint instruction just wrote a fresh
  ;; new-space value into its register home; reloading from the root slot
  ;; (which was not updated by the pre-safepoint sync) would clobber it.
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
  ;; GC adds a small hidden frame header in addition to the ordinary frame
  ;; body. The header lives just above the saved x29/x30 pair and stores:
  ;;   [x29, #-16] previous GC frame
  ;;   [x29, # -8] pointer to this procedure's GC descriptor
  ;; The rest of the frame is the usual saved-register / root-slot /
  ;; outgoing-arg area. "frame slots" includes both true spills and the shadow
  ;; root slots that keep register-homed values visible to the collector.
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

(define (finalize-machine-instruction instr stack-size saved-registers)
  (case (car instr)
    ((move-in)
     (list `(move ,(cadr instr) ,(caddr instr))))
    ((call)
     (let ((dst (cadr instr))
           (closure (caddr instr))
            (args (cdddr instr)))
         ;; Finalization is where pseudo-instructions become ABI-aware code:
         ;; move arguments/results through the calling-convention locations and
         ;; make frame teardown explicit around tail calls and returns.
         ;;
         ;; GC note: ordinary calls keep the current frame live, so all roots
         ;; must already be materialized in GC-visible frame slots before
         ;; control transfers to a helper or callee that may allocate.
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
        ;; Tail calls are different: once we pop the GC frame, this procedure
        ;; stops contributing roots. That is why gc-pop-frame is sequenced
        ;; before deallocating the frame and branching away.
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
                              ;; The first block receives the procedure prologue.
                              ;; Epilogues are inserted instruction-by-instruction
                              ;; when returns and tail calls are finalized.
                              ;;
                              ;; GC note: init-frame-slots clears every GC-visible
                              ;; frame slot before the frame becomes visible to
                              ;; the collector. That covers both true spills and
                              ;; the shadow root slots used for register homes.
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
  ;; This helper is the whole backend pipeline for one procedure-sized CFG:
  ;; instruction selection -> liveness/allocation -> ABI finalization.
  (finalize-machine-procedure
   (allocate-machine-procedure
     (select-machine-procedure name params cfg))))

;;; ============================================================================
;;; Helper: Display results
;;; ============================================================================

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

;;; ============================================================================
;;; AArch64 assembly emission
;;; The emitter converts the allocated backend IR into textual Apple-style
;;; AArch64 assembly. By this point, the interesting compiler work is already
;;; done; emission is mostly a matter of printing each lowered instruction in
;;; the right concrete form.
;;;
;;; INPUT: a list of finalized <machine-procedure> records (Backend step 3
;;;        output). All homes are physical (register, stack-slot), all
;;;        calling-convention details are explicit, and prologue/epilogue
;;;        pseudo-instructions are present.
;;;
;;; OUTPUT: textual AArch64 assembly (string / port). No grammar
;;;         transformation occurs; this pass only renders IR as text.
;;;
;;; Notable target conventions:
;;;   - Apple-style symbol names (underscore-prefixed where required).
;;;   - Tagged `hop_value` integers passed/returned in x0.
;;;   - `scheme_entry` is the public entry point called by codegen_harness.c.
;;;   - Closure/allocation helpers (hop_call_N, hop_tail_call_N, hop_alloc_*)
;;;     are declared external and called via BL/B.
;;; ============================================================================

(define (procedure-saved-bytes proc)
  (* 8 (length (machine-procedure-used-registers proc))))

(define (procedure-outgoing-bytes proc)
  (* 8 (max-outgoing-stack-args (machine-procedure-blocks proc))))

;;; Outgoing stack args occupy the lowest part of the frame (sp+0 upward) so
;;; that at the moment of a call instruction sp already points at arg[0], which
;;; is what the AArch64 PCS requires for stack-passed arguments.
(define (procedure-outgoing-base proc)
  0)

(define (incoming-stack-arg-offset index)
  (+ 16 (* 8 index)))

;;; Root slots sit above the outgoing-arg area and the callee-saved-register
;;; save area.  Offsets are relative to sp (= x29 - stack_size).
(define (stack-slot-offset proc index)
  (+ (procedure-outgoing-bytes proc)
     (procedure-saved-bytes proc)
     (* 8 index)))

(define (saved-register-offset proc reg)
  ;; Callee-saved registers are stored just above the outgoing-arg area.
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
;; Toggle for unsafe pair loads:
;;   'fast         => unchecked field access
;;   'debug-assert => use checked runtime helper for easier debugging
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

(define (register-operand? operand)
  (and (pair? operand)
       (memq (car operand) '(register arg-register))))

(define (register-name operand)
  (symbol->string (cadr operand)))

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
      ;; Stack slots are the runtime-visible root homes. That includes ordinary
      ;; spills and the shadow slots that mirror register-homed values.
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
  ;; The calling convention here reflects the GC invariant:
  ;;   - load the argument from its home into x0
  ;;   - call the runtime helper
  ;;   - store the result back into a home
  ;;
  ;; The helper may allocate, but that is safe because every other live Scheme
  ;; value has already been mirrored into a GC-visible frame slot rather than
  ;; only existing in a machine register.
  (emit-load-operand port "x0" operand proc)
  (emit-asm-line port (string-append "    bl " helper))
  (emit-store-operand port "x0" dst proc))

(define (emit-safe-binop port op dst a b proc)
  ;; Safe arithmetic helpers are NOT GC safepoints (they don't allocate), so
  ;; live values in callee-saved registers survive the call unchanged.
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

(define (emit-alloc-closure port dst proc-name captures proc)
  (let ((count (length captures)))
    (if (<= count 3)
        ;; Fast path: pass up to 3 captures directly in x1..x3.
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
        ;; General path: store all captures to the outgoing-arg area at [sp,#8*i],
        ;; then call hop_alloc_closure_n(code, count, envs_ptr).
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
     ;; Zeroing keeps newly-published frames precise even before the procedure
     ;; has written all of its locals. xzr is not a tagged pointer value.
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
     ;; Publish the current frame to the collector. After this point, any
     ;; allocation helper can find this frame by following hop_gc_top_frame and
     ;; then use the descriptor to locate its root slots precisely.
     (emit-procedure-descriptor-address port "x9" (cadr instr))
     (emit-procedure-address port "x10" 'hop_gc_top_frame)
     (emit-asm-line port "    ldr x11, [x10]")
     (emit-asm-line port "    str x11, [x29, #-16]")
     (emit-asm-line port "    str x9, [x29, #-8]")
     (emit-asm-line port "    mov x11, x29")
     (emit-asm-line port "    str x11, [x10]"))
    ((gc-pop-frame)
     ;; Remove the frame from the collector's linked list before tail transfer
     ;; or return tears the frame down.
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
      ;; The pair helper may trigger GC. By the time we copy values into x0/x1,
      ;; the source operands already live in stack slots, so the runtime can
      ;; recover them precisely if it collects.
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
  ;; A descriptor is the runtime's compact summary of a frame layout.
  ;; For this collector we only need:
  ;;   - how many frame slots may hold Scheme values
  ;;   - how many bytes to step from x29 down to slot 0
  ;; The second field is NOT the total stack_size; it is the offset from x29
  ;; to the first root slot.  With the current frame layout:
  ;;   [sp]  outgoing-arg area
  ;;   [sp + outgoing_bytes]  callee-saved registers
  ;;   [sp + outgoing_bytes + saved_bytes + alignment_padding]  root slots  ← slot 0
  ;;   [x29 - gc_header_bytes]  GC header
  ;;   [x29]  saved x29/x30
  ;; x29 - slot_0_address = stack_size(aligned) - outgoing_bytes - saved_bytes.
  ;; This correctly accounts for any alignment padding inserted by stack-align.
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

;;; ============================================================================
;;; Simple hash table implementation 
;;; ============================================================================

(define (make-hash-table) (list 'hash-table))
(define (hash-set! ht key value)
  (let ((pair (assoc key (cdr ht))))
    (if pair
        (set-cdr! pair value)
        (set-cdr! ht (cons (cons key value) (cdr ht))))))
(define (hash-ref ht key)
  (let ((pair (assoc key (cdr ht))))
    (if pair (cdr pair) #f)))

;;; ============================================================================
;;; Main Compiler Driver
;;; These entry points stitch the passes together:
;;;
;;;   - compile-to-cfg: stop after the middle end
;;;   - compile-to-backend: run through allocation/finalization
;;;   - write-aarch64-program: emit assembly to a file
;;;   - write-aarch64-program-file: read forms from a source file first
;;;   - compile-program: educational debugging view of the intermediate stages
;;; ============================================================================

(define (compile-to-cfg expr)
  ;; Every public entry point goes through program lowering first, even the
  ;; original "single expression" path. That keeps the whole compiler talking
  ;; about one uniform internal program shape.
  (let-values (((lowered-program global-count) (lower-source-program expr)))
    (let* ((uniquified (uniquify lowered-program))
           (canonicalized (canonicalize-builtins uniquified))
           (desugared (desugar-letrec canonicalized))
           (closure-converted (closure-convert desugared))
           (cfa-normalized (normalize-for-cfa closure-converted))
           (cfa-analysis (run-0cfa cfa-normalized))
           (cfa-rewritten (rewrite-known-calls cfa-normalized cfa-analysis)))
      (let-values (((tac-instrs procedures) (expr->tac cfa-rewritten)))
          (let* ((entry-cfg (build-cfg tac-instrs))
                 (procedure-cfgs
            (map (lambda (procedure)
                   (cons procedure
                   (build-cfg (procedure-instructions procedure))))
                 procedures))
                 (optimized-entry-cfg
                   (eliminate-dead-writes-cfg
                     (constant-fold-cfg
                       (optimize-unsafe-arith-cfg
                         (optimize-unsafe-car-cdr-cfg entry-cfg)))))
                 (optimized-procedure-cfgs
            (map (lambda (procedure+cfg)
                   (cons (car procedure+cfg)
                   (eliminate-dead-writes-cfg
                     (constant-fold-cfg
                       (optimize-unsafe-arith-cfg
                         (optimize-unsafe-car-cdr-cfg (cdr procedure+cfg)))))))
                 procedure-cfgs)))
            (values lowered-program
              global-count
              uniquified
              canonicalized
              desugared
              closure-converted
              cfa-normalized
              cfa-rewritten
              optimized-entry-cfg
              optimized-procedure-cfgs))))))

(define (compile-to-backend expr)
  (let-values (((lowered-program global-count uniquified canonicalized desugared closure-converted cfa-normalized
                             cfa-rewritten entry-cfg procedures)
                 (compile-to-cfg expr)))
    (let ((entry-machine
           (cfg->allocated-machine-procedure 'scheme_entry '() entry-cfg))
          (procedure-machines
           (map (lambda (procedure+cfg)
                  (cfg->allocated-machine-procedure
                   (procedure-name (car procedure+cfg))
                   (procedure-params (car procedure+cfg))
                   (cdr procedure+cfg)))
                procedures)))
      (values lowered-program
              global-count
              uniquified
              canonicalized
              desugared
              closure-converted
              cfa-normalized
              cfa-rewritten
              entry-cfg
              procedures
              entry-machine
              procedure-machines))))

(define (write-aarch64-program expr path)
  (let-values (((lowered-program global-count uniquified canonicalized desugared closure-converted cfa-normalized
                              cfa-rewritten entry-cfg procedures
                               entry-machine procedure-machines)
                  (compile-to-backend expr)))
    (call-with-output-file path
      (lambda (port)
        (emit-aarch64-program port entry-machine procedure-machines global-count)))))

(define (write-aarch64-program-forms forms path)
  (write-aarch64-program (cons 'program forms) path))

(define (read-program-forms path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((forms '()))
        (let ((form (read port)))
          (if (eof-object? form)
              (reverse forms)
              (loop (cons form forms))))))))

(define (write-aarch64-program-file input-path output-path)
  (write-aarch64-program-forms (read-program-forms input-path) output-path))

(define (compile-program expr)
  ;; compile-program is intentionally pedagogical: it prints the major
  ;; representations in pipeline order so a reader can watch one source program
  ;; become lower-level at each pass boundary.
  (display "=== Source Program ===\n")
  (write expr) (newline)
  
  (display "\n=== After Program Lowering ===\n")
  (let-values (((lowered-program global-count uniquified canonicalized desugared closure-converted cfa-normalized
                              cfa-rewritten entry-cfg procedures
                               entry-machine procedure-machines)
                 (compile-to-backend expr)))
    (write lowered-program) (newline)
    (display "Global slots: ")
    (write global-count)
    (newline)
    
    (display "\n=== After Uniquify ===\n")
    (write uniquified) (newline)

    (display "\n=== After Builtin Canonicalization ===\n")
    (write canonicalized) (newline)

    (display "\n=== After letrec Desugaring ===\n")
    (write desugared) (newline)
    
    (display "\n=== After Closure Conversion ===\n")
    (write closure-converted) (newline)

    (display "\n=== After CFA Normalization ===\n")
    (write cfa-normalized) (newline)

    (display "\n=== After 0CFA Call Rewriting ===\n")
    (write cfa-rewritten) (newline)

    (display "\n=== After Pair-Proven Unsafe car/cdr Rewrite (CFG) ===\n")
    (display-cfg entry-cfg)
    (display "Entry CFG built with ")
    (display (length entry-cfg))
    (display " basic blocks\n")
    (display "\n=== Allocated Backend ===\n")
    (display-machine-procedure entry-machine)
    (for-each display-machine-procedure procedure-machines)
    
    (when (not (null? procedures))
      (display "\n=== Procedure CFGs ===\n")
      (for-each (lambda (procedure+cfg)
                  (display-procedure-cfg (car procedure+cfg) (cdr procedure+cfg)))
                procedures))
    
    (display "\n=== Compilation Complete ===\n")))

(define (compile-program-forms forms)
  (compile-program (cons 'program forms)))

;;; Test fixtures and demo helpers live in separate test-owned files so loading
;;; the compiler does not implicitly run or define the regression suite.
