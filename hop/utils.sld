(define-library (hop utils)
  (export body->expr
          append-map
          filter
          ash
          mangle-identifier
          dedupe-symbols
          remove-shadowed-bindings
          all
          single-binding?
          lambda-expr?
          literal-expr?
          quoted-symbol-expr?
          nest-let-bindings
          set-union
          set-difference
          set-equal?
          params-variadic?
          params-fixed
          params-rest
          params-names
          make-params)
  (import (scheme base)
          (scheme cxr))
  (begin

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

; Chicken 5's (scheme base) does not export filter despite R7RS requiring it.
(define (filter pred lst)
  (let loop ((rest lst) (result '()))
    (cond ((null? rest) (reverse result))
          ((pred (car rest)) (loop (cdr rest) (cons (car rest) result)))
          (else (loop (cdr rest) result)))))

(define (ash n count)
  (if (negative? count)
      (floor (/ n (expt 2 (- count))))
      (* n (expt 2 count))))

; Turns an arbitrary Scheme identifier into text that's safe to use as an
; assembler symbol label: ASCII letters/digits pass through unchanged, every
; other character (including '_' itself, so escape output never collides with
; a literal input underscore) becomes a hex escape. This only ever needs to be
; unambiguous going forward (name -> label), never decoded back, so it's a
; plain injective encoding rather than a reversible one.
(define (identifier-safe-char? code)
  (or (and (>= code 48) (<= code 57))    ; 0-9
      (and (>= code 65) (<= code 90))    ; A-Z
      (and (>= code 97) (<= code 122)))) ; a-z

(define (hex-digit-char n)
  (string-ref "0123456789abcdef" n))

(define (hex-byte-escape code)
  (string-append "_"
                 (string (hex-digit-char (quotient code 16)))
                 (string (hex-digit-char (remainder code 16)))))

(define (mangle-identifier name)
  (let ((str (if (symbol? name) (symbol->string name) name)))
    (apply string-append
           (map (lambda (ch)
                  (let ((code (char->integer ch)))
                    (cond
                     ((identifier-safe-char? code) (string ch))
                     ((< code 256) (hex-byte-escape code))
                     (else (string-append "_u" (number->string code 16) "_")))))
                (string->list str)))))

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

;; A lambda's parameter list is either a plain proper list of symbols
;; (ordinary fixed-arity lambda, unchanged from before variadic support) or
;; a tagged 3-element list (variadic (fixed-sym...) rest-sym) recording a
;; rest parameter. The tagged shape is itself a proper list, so it flows
;; safely through code that only ever forwards `params` opaquely; only code
;; that needs to actually split fixed-vs-rest, or collect every bound name,
;; needs the helpers below.
(define (params-variadic? params)
  (and (pair? params) (eq? (car params) 'variadic)))

(define (params-fixed params)
  (if (params-variadic? params) (cadr params) params))

(define (params-rest params)
  (if (params-variadic? params) (caddr params) #f))

;; Every name bound by this parameter list, fixed params first and the rest
;; parameter (if any) last -- the shape most callers actually want when they
;; just need "the set of names this lambda binds".
(define (params-names params)
  (if (params-variadic? params)
      (append (params-fixed params) (list (params-rest params)))
      params))

(define (make-params fixed rest)
  (if rest (list 'variadic fixed rest) fixed))

; A quoted symbol stays wrapped as (quote sym) all the way through the
; pipeline so that a bare symbol always means a variable reference. Every
; pass checks literal-expr? before dispatching on (car expr), which lets the
; wrapper flow through untouched until the backend encodes it as a tagged
; symbol immediate.
(define (quoted-symbol-expr? expr)
  (and (pair? expr)
       (eq? (car expr) 'quote)
       (pair? (cdr expr))
       (symbol? (cadr expr))
       (null? (cddr expr))))

(define (literal-expr? expr)
  (or (number? expr) (boolean? expr) (null? expr)
      (quoted-symbol-expr? expr)))

(define (nest-let-bindings bindings body-exprs)
  (if (null? bindings)
      (body->expr body-exprs)
      `(let (,(car bindings))
         ,(nest-let-bindings (cdr bindings) body-exprs))))

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

)) ; end define-library
