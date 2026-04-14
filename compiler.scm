;;; Scheme Compiler - Initial Passes (Corrected)
;;; Supports: arithmetic, booleans, conditionals, boxes, lambda, letrec
;;; Passes: uniquify -> letrec-desugar -> closure-conversion -> TAC CFG

(import (scheme base)
        (scheme write))

;;; ============================================================================
;;; Shared Helpers
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

(define (nest-let-bindings bindings body-exprs)
  (if (null? bindings)
      (body->expr body-exprs)
      `(let (,(car bindings))
         ,(nest-let-bindings (cdr bindings) body-exprs))))

(define (desugar-letrec expr)
  (define (rewrite expr env)
    (cond
      ((symbol? expr)
       (let ((binding (assoc expr env)))
         (if binding
             `(unbox ,(cadr binding))
             expr)))
      
      ((or (number? expr) (boolean? expr)) expr)
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(map (lambda (e) (rewrite e env)) (cdr expr))))
         
         ((primop)
          `(primop ,(cadr expr)
                   ,@(map (lambda (e) (rewrite e env)) (cddr expr))))
         
         ((if)
          `(if ,(rewrite (cadr expr) env)
               ,(rewrite (caddr expr) env)
               ,(rewrite (cadddr expr) env)))
         
         ((let)
          (let* ((binding (caadr expr))
                 (var (car binding))
                 (val-expr (rewrite (cadr binding) env))
                 (body-env (remove-shadowed-bindings env (list var)))
                 (body-exprs (map (lambda (body-expr)
                                    (rewrite body-expr body-env))
                                  (cddr expr))))
            `(let ((,var ,val-expr)) ,@body-exprs)))
         
         ((lambda)
          (let* ((params (cadr expr))
                 (body-env (remove-shadowed-bindings env params))
                 (body-exprs (map (lambda (body-expr)
                                    (rewrite body-expr body-env))
                                  (cddr expr))))
            `(lambda ,params ,@body-exprs)))
         
          ((letrec)
           (let* ((bindings (cadr expr))
                  (names (map car bindings)))
             (if (not (all (lambda (binding)
                            (and (single-binding? binding)
                                  (lambda-expr? (cadr binding))))
                          bindings))
                 (error "letrec requires lambda bindings" expr)
                (let* ((base-env (remove-shadowed-bindings env names))
                       (rec-env (append (map (lambda (name) (list name name)) names)
                                        base-env))
                        (box-bindings
                         (map (lambda (name) (list name '(box #f))) names))
                        (init-exprs
                         (map (lambda (binding)
                                `(set-box! ,(car binding)
                                          ,(rewrite (cadr binding) rec-env)))
                             bindings))
                       (body-exprs
                        (append init-exprs
                                (map (lambda (body-expr)
                                       (rewrite body-expr rec-env))
                                     (cddr expr)))))
                  (nest-let-bindings box-bindings body-exprs)))))
         
         ((app)
          `(app ,(rewrite (cadr expr) env)
                ,@(map (lambda (e) (rewrite e env)) (cddr expr))))
         
         ((box)
          `(box ,(rewrite (cadr expr) env)))
         
         ((unbox)
          `(unbox ,(rewrite (cadr expr) env)))
         
         ((set-box!)
          (let ((target (cadr expr)))
            (when (and (symbol? target) (assoc target env))
              (error "Cannot mutate letrec function binding" target))
            `(set-box! ,(rewrite target env)
                       ,(rewrite (caddr expr) env))))
         
         (else (error "Unknown expression type in letrec desugaring" (car expr)))))
      
      (else (error "Invalid expression in letrec desugaring" expr))))
  
  (rewrite expr '()))

;;; ============================================================================
;;; Pass 1: Uniquify
;;; Renames all variables to unique names while respecting scope
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
      
      ((or (number? expr) (boolean? expr)) expr)
      
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
         
         ((box)
          `(box ,(uniquify-expr (cadr expr) env)))
         
         ((unbox)
          `(unbox ,(uniquify-expr (cadr expr) env)))
         
         ((set-box!)
          `(set-box! ,(uniquify-expr (cadr expr) env) 
                     ,(uniquify-expr (caddr expr) env)))
         
         (else (error "Unknown expression type" (car expr)))))
      
      (else (error "Invalid expression" expr))))
  
  (uniquify-expr expr '()))

;;; ============================================================================
;;; Pass 2: Closure Conversion
;;; ============================================================================

(define (free-vars expr bound)
  ;; Return list of free variables in expr, given bound variables
  (define (collect expr bound)
    (cond
      ((symbol? expr)
       (if (memq expr bound) '() (list expr)))
      
      ((or (number? expr) (boolean? expr)) '())
      
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
         
         ((box unbox)
          (collect (cadr expr) bound))
         
         ((set-box!)
          (append (collect (cadr expr) bound)
                  (collect (caddr expr) bound)))
         
         (else (error "Unknown expression in free-vars" (car expr)))))
      
      (else '())))
  
  (dedupe-symbols (collect expr bound)))

(define (closure-convert expr)
  (define (convert expr env)
    ;; env: association list mapping variable names to their representation
    ;; Either (local var) or (closure env-var) for captured variables.
    
    (cond
      ((symbol? expr)
       (let ((binding (assoc expr env)))
         (if binding
             (cadr binding)  ; Return the representation
             expr)))         ; Global/primitive
      
      ((or (number? expr) (boolean? expr))
       expr)
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          `(begin ,@(map (lambda (e) (convert e env)) (cdr expr))))
         
          ((primop)
           `(primop ,(cadr expr) 
                    ,@(map (lambda (e) (convert e env)) (cddr expr))))
         
         ((if)
          `(if ,(convert (cadr expr) env)
               ,(convert (caddr expr) env)
               ,(convert (cadddr expr) env)))
         
          ((let)
           (let* ((binding (caadr expr))
                  (var (car binding))
                  (val (cadr binding))
                  (body (body->expr (cddr expr)))
                  (val-converted (convert val env))
                  (new-env (cons (list var `(local ,var)) env))
                  (body-converted (convert body new-env)))
             `(let ((,var ,val-converted)) ,body-converted)))
          
          ((lambda)
           (let* ((params (cadr expr))
                  (body (body->expr (cddr expr)))
                  (fvs (free-vars body params))
                  
                  ;; Generate closure environment variables
                  (env-vars (let loop ((i 0) (fv-list fvs) (result '()))
                             (if (null? fv-list)
                                 (reverse result)
                                 (loop (+ i 1) 
                                       (cdr fv-list) 
                                       (cons (string->symbol 
                                              (string-append "env." 
                                                             (number->string i)))
                                             result)))))
                 
                 ;; Build new environment for lambda body
                 (param-bindings (map (lambda (p) (list p `(local ,p))) params))
                 (env-bindings (map (lambda (fv env-var)
                                      (list fv `(closure ,env-var)))
                                    fvs env-vars))
                 (new-env (append param-bindings env-bindings env))
                 
                 (body-converted (convert body new-env)))
            
            ;; Create closure structure
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
            `(closure-call ,(convert rator env)
                           ,@(map (lambda (e) (convert e env)) rands))))
         
         ((box)
          `(box ,(convert (cadr expr) env)))
         
         ((unbox)
          `(unbox ,(convert (cadr expr) env)))
         
         ((set-box!)
          `(set-box! ,(convert (cadr expr) env)
                     ,(convert (caddr expr) env)))
         
         (else (error "Unknown expression in closure-convert" (car expr)))))
      
      (else (error "Invalid expression in closure-convert" expr))))
  
  (convert expr '()))

;;; ============================================================================
;;; Pass 3: Convert to Three-Address Code (TAC)
;;; ============================================================================

(define-record-type <procedure>
  (make-procedure name params instructions)
  procedure?
  (name procedure-name)
  (params procedure-params)
  (instructions procedure-instructions))

(define (expr->tac expr)
  ;; Convert an expression to TAC form.
  ;; Returns: (values instructions procedures)
  
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
    (or (symbol? expr) (number? expr) (boolean? expr)
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
  
  (define (convert-tail expr)
    (cond
      ((simple? expr)
       (values (list `(return ,(simple-value expr))) '()))
      
      ((pair? expr)
       (case (car expr)
         ((begin)
          (let ((body-exprs (cdr expr)))
            (let loop ((rest body-exprs)
                       (instrs '())
                       (procedures '()))
              (cond
                ((null? rest)
                 (error "begin requires at least one expression"))
                ((null? (cdr rest))
                 (let-values (((tail-instrs tail-procedures)
                               (convert-tail (car rest))))
                   (values (append instrs tail-instrs)
                           (append procedures tail-procedures))))
                (else
                 (let-values (((new-instrs ignored-result new-procedures)
                               (convert-value (car rest) #f)))
                   (loop (cdr rest)
                         (append instrs new-instrs)
                         (append procedures new-procedures))))))))
         
         ((if)
          (let* ((then-label (fresh-temp))
                 (else-label (fresh-temp)))
            (let-values (((test-instrs test-var test-procedures)
                          (convert-value (cadr expr) #f))
                         ((then-instrs then-procedures)
                          (convert-tail (caddr expr)))
                         ((else-instrs else-procedures)
                          (convert-tail (cadddr expr))))
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
                          (convert-tail body)))
              (values (append val-instrs
                              (list `(assign ,var ,val-result))
                              body-instrs)
                      (append val-procedures body-procedures)))))
         
         ((closure-call)
          (let ((closure-expr (cadr expr))
                (args (cddr expr)))
            (let-values (((call-instrs closure-var arg-vars procedures)
                          (convert-call closure-expr args)))
              (values (append call-instrs
                              (list `(tail-call ,closure-var ,@arg-vars)))
                      procedures))))
         
         (else
          (let-values (((instrs result-var procedures)
                        (convert-value expr #f)))
            (values (append instrs (list `(return ,result-var)))
                    procedures)))))
      
      (else (error "Invalid expression in tail position" expr))))
  
  (define (convert-value expr dest)
    ;; dest: optional destination variable
    ;; Returns: (values instructions result-var procedures)
    
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
          ((begin)
           (let ((body-exprs (cdr expr)))
             (let loop ((rest body-exprs)
                        (instrs '())
                       (procedures '()))
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
                          (append procedures new-procedures))))))))
         
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
          
          ((box)
           (let-values (((instrs val-var procedures) (convert-value (cadr expr) #f)))
              (let ((result-var (or dest (fresh-temp))))
                (values (append instrs 
                                (list `(assign ,result-var (box ,val-var))))
                        result-var
                        procedures))))
          
          ((unbox)
           (let-values (((instrs box-var procedures) (convert-value (cadr expr) #f)))
             (let ((result-var (or dest (fresh-temp))))
               (values (append instrs
                               (list `(assign ,result-var (unbox ,box-var))))
                       result-var
                       procedures))))
          
          ((if)
           (let* ((then-label (fresh-temp))
                  (else-label (fresh-temp))
                  (join-label (fresh-temp))
                  (result-var (or dest (fresh-temp))))
             
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
              
             (let-values (((val-instrs val-result val-procedures) (convert-value val #f)))
                ;; Generate assignment for the let-bound variable
                 (let ((assign-instr `(assign ,var ,val-result)))
                   (let-values (((body-instrs body-result body-procedures)
                                 (convert-value body dest)))
                     (values (append val-instrs (list assign-instr) body-instrs) 
                            body-result
                            (append val-procedures body-procedures)))))))
          
          ((make-closure)
           ;; Convert closure creation
           (let* ((lambda-expr (cadr expr))
                  (free-vars (cddr expr))
                  (proc-name (fresh-proc))
                  (proc-params (cadr lambda-expr))
                  (proc-body (body->expr (cddr lambda-expr))))
             
             (let-values (((body-instrs body-procedures)
                            (convert-tail proc-body))
                           ((fv-instrs fv-vars fv-procedures)
                            (convert-list free-vars)))
                (let ((result-var (or dest (fresh-temp)))
                      (procedure
                      (make-procedure proc-name
                                      proc-params
                                      body-instrs)))
                  (values (append fv-instrs
                                  (list `(assign ,result-var 
                                                 (make-closure ,proc-name 
                                                              ,@fv-vars))))
                         result-var
                         (append body-procedures
                                 fv-procedures
                                 (list procedure)))))))
          
          ((closure-call)
           ;; Convert closure call
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
          
           ((set-box!)
           (let-values (((box-instrs box-var box-procedures) (convert-value (cadr expr) #f))
                         ((val-instrs val-var val-procedures) (convert-value (caddr expr) #f)))
              (let ((result-var (or dest val-var)))
                (values (append box-instrs
                                val-instrs
                               (list `(set-box! ,box-var ,val-var))
                               (if (eq? result-var val-var)
                                   '()
                                   (list `(assign ,result-var ,val-var))))
                       result-var
                       (append box-procedures val-procedures)))))
          
          ((local closure)
           ;; These should have been handled by the simple? check above
           (values '() (cadr expr) '()))
          
          (else (error "Unknown expression in expr->tac" (car expr)))))
      
       (else (error "Invalid expression in expr->tac" expr))))
  
  (convert-tail expr))

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
;;; Build Control Flow Graph (CFG)
;;; ============================================================================

(define (build-cfg tac-instrs)
  ;; Build proper control flow graph from TAC instructions
  ;; Returns list of basic blocks in order
  
  (define (terminator? instr)
    (and (pair? instr)
         (memq (car instr) '(if goto return tail-call))))

  (define (is-leader? index instrs)
    ;; Determine if instruction at index is a basic block leader
    (let ((instr (list-ref instrs index)))
      (or (= index 0)  ; First instruction is always a leader
          (and (pair? instr) (eq? (car instr) 'label))  ; Labels are leaders
          (and (> index 0)  ; Instruction after a terminator is a leader
               (terminator? (list-ref instrs (- index 1)))))))
  
  (define (split-into-blocks instrs)
    ;; Split instructions into basic blocks at leaders
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
    ;; Determine successors for each basic block
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
             
              ((and (pair? last-instr) (memq (car last-instr) '(return tail-call)))
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
;;; ============================================================================

(define (compile-to-cfg expr)
  (let* ((uniquified (uniquify expr))
         (desugared (desugar-letrec uniquified))
         (closure-converted (closure-convert desugared)))
    (let-values (((tac-instrs procedures) (expr->tac closure-converted)))
      (values uniquified
              desugared
              closure-converted
              (build-cfg tac-instrs)
              (map (lambda (procedure)
                     (cons procedure
                           (build-cfg (procedure-instructions procedure))))
                   procedures)))))

(define (compile-program expr)
  (display "=== Source Program ===\n")
  (write expr) (newline)
  
  (display "\n=== After Uniquify ===\n")
  (let-values (((uniquified desugared closure-converted entry-cfg procedures)
                (compile-to-cfg expr)))
    (write uniquified) (newline)
    
    (display "\n=== After letrec Desugaring ===\n")
    (write desugared) (newline)
    
    (display "\n=== After Closure Conversion ===\n")
    (write closure-converted) (newline)
    
    (display "\n=== Entry CFG ===\n")
    (display-cfg entry-cfg)
    (display "Entry CFG built with ")
    (display (length entry-cfg))
    (display " basic blocks\n")
    
    (when (not (null? procedures))
      (display "\n=== Procedure CFGs ===\n")
      (for-each (lambda (procedure+cfg)
                  (display-procedure-cfg (car procedure+cfg) (cdr procedure+cfg)))
                procedures))
    
    (display "\n=== Compilation Complete ===\n")))

;;; ============================================================================
;;; Test Programs
;;; ============================================================================

(define test1
  '(let ((x 5))
     (primop + x 1)))

(define test2
  '(let ((f (lambda (x) (primop + x 1))))
     (app f 5)))

(define test3
  '(let ((b (box 0)))
     (set-box! b (primop + (unbox b) 1))
     (unbox b)))

(define test4
  '(if (primop > x 0)
       (primop + x 1)
       (primop - x 1)))

(define test5
  '(let ((x 5))
     (let ((y 10))
       (primop + x y))))

(define test6
  '(if (primop > x 0)
       (let ((y (primop + x 1)))
         (primop * y 2))
       (primop - x 1)))

(define test7
  '(if (primop > x 0)
       (primop + x 1)
       (if (primop < x -5)
           (primop - x 2)
           (primop * x 3))))

(define test8
  '(let ((x 0))
     (if (primop < x 10)
          (let ((y (primop + x 1)))
            (primop * y 2))
          (primop - x 5))))

(define test9
  '(let ((x 5))
     (let ((f (lambda (y)
                (let ((b (box x)))
                  (set-box! b (primop + (unbox b) y))
                  (unbox b)))))
       (app f 3))))

(define test10
  '(let ((x 5))
     (let ((mk (lambda (y)
                 (lambda (z)
                   (primop + x (primop + y z))))))
       (let ((f (app mk 7)))
         (app f 3)))))

(define test11
  '(let ((x 2))
     (let ((f (lambda (y)
                (primop + y 1)
                (primop + x y))))
       (app f 4))))

(define test12
  '(let ((x (if #t 1 2)))
     (primop + x 10)))

(define test13
  '(letrec ((countdown
             (lambda (n)
               (if (primop = n 0)
                   0
                   (app countdown (primop - n 1))))))
     (app countdown 3)))

(define test14
  '(letrec ((even?
             (lambda (n)
               (if (primop = n 0)
                   #t
                   (app odd? (primop - n 1)))))
            (odd?
             (lambda (n)
               (if (primop = n 0)
                   #f
                   (app even? (primop - n 1))))))
     (app even? 4)))

(define test15
  '(letrec ((id
             (lambda (x)
               x)))
     (app id 1)
     (app id 2)))

;; Run tests
(display "\nTest 1: Simple arithmetic\n")
(compile-program test1)

(display "\n\nTest 2: Lambda application\n")
(compile-program test2)

(display "\n\nTest 3: Box operations\n")
(compile-program test3)

(display "\n\nTest 5: Nested lets\n")
(compile-program test5)

(display "\n\nTest 6: Conditional with let\n")
(compile-program test6)

(display "\n\nTest 7: Nested conditionals\n")
(compile-program test7)

(display "\n\nTest 8: Loop-like pattern (for testing CFG)\n")
(compile-program test8)

(display "\n\nTest 9: Closure capture with sequencing in lambda body\n")
(compile-program test9)

(display "\n\nTest 10: Nested closures\n")
(compile-program test10)

(display "\n\nTest 11: Direct sequencing in lambda body\n")
(compile-program test11)

(display "\n\nTest 12: Simple values in if branches\n")
(compile-program test12)

(display "\n\nTest 13: Self-recursive letrec\n")
(compile-program test13)

(display "\n\nTest 14: Mutually recursive letrec\n")
(compile-program test14)

(display "\n\nTest 15: Sequencing in letrec body\n")
(compile-program test15)
