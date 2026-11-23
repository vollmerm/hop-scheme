;;; Alex Shinn's portable pattern matcher, written in syntax-rules.
;;;
;;; This code is by Alex Shinn and is in the public domain. It is the version
;;; distributed with Guile 3.0 (ice-9/match.upstream.scm), packaged here as an
;;; R7RS library so that Chicken and Guile run the same matcher. Changes from
;;; that copy: a failed match calls R7RS `error`, malformed patterns are
;;; reported with R7RS `syntax-error`, and record patterns ($ rec field ...)
;;; are rejected at expansion time, since R7RS records have no portable
;;; field-by-index access.
;;;
;;; Quick reference (see the upstream documentation for the full syntax):
;;;
;;;   (match expr (pattern body ...) ...)
;;;
;;;   x              binds x               _          matches anything
;;;   'datum         equal? to datum       (p ...)    a proper list of p
;;;   (p . q)        a pair                (p ..1)    one or more p
;;;   (? pred p ...) pred holds, and p     (= f p)    (f value) matches p
;;;   (and p ...)    (or p ...)            (not p)
;;;   number, boolean, string literals match by equal?.
(define-library (hop match)
  (export match
          match-lambda
          match-lambda*
          match-let
          match-let*
          match-letrec)
  ;; The macros above expand into these helpers. Chicken warns about every
  ;; helper a library does not export, and R7RS export lists cannot mark them
  ;; as internal, so Chicken gets them as ordinary exports.
  (cond-expand
   (chicken
    (export match-next match-one match-two match-quasiquote
            match-quasiquote-step match-drop-ids match-tuck-ids
            match-drop-first-arg match-gen-or match-gen-or-step
            match-gen-ellipsis match-verify-no-ellipsis match-gen-search
            match-vector match-vector-two match-vector-step
            match-gen-vector-ellipsis match-vector-tail match-vector-tail-two
            match-extract-vars match-extract-vars-step
            match-extract-quasiquote-vars match-extract-quasiquote-vars-step
            match-let/helper match-named-let match-check-ellipsis
            match-check-identifier match-bound-identifier-memv))
   (else))
  (import (scheme base))
  (begin

;; The basic interface.  MATCH just performs some basic syntax
;; validation, binds the match expression to a temporary variable `v',
;; and passes it on to MATCH-NEXT.  It's a constant throughout the
;; code below that the binding `v' is a direct variable reference, not
;; an expression.

(define-syntax match
  (syntax-rules ()
    ((match)
     (syntax-error "missing match expression"))
    ((match atom)
     (syntax-error "no match clauses"))
    ((match (app ...) (pat . body) ...)
     (let ((v (app ...)))
       (match-next v ((app ...) (set! (app ...))) (pat . body) ...)))
    ((match #(vec ...) (pat . body) ...)
     (let ((v #(vec ...)))
       (match-next v (v (set! v)) (pat . body) ...)))
    ((match atom (pat . body) ...)
     (let ((v atom))
       (match-next v (atom (set! atom)) (pat . body) ...)))
    ))

;; MATCH-NEXT passes each clause to MATCH-ONE in turn with its failure
;; thunk, which is expanded by recursing MATCH-NEXT on the remaining
;; clauses.  `g+s' is a list of two elements, the get! and set!
;; expressions respectively.

(define-syntax match-next
  (syntax-rules (=>)
    ;; no more clauses, the match failed
    ((match-next v g+s)
     ;; Here we call error in non-tail context, so that the backtrace
     ;; can show the source location of the failing match form.
     (begin
       (error "no matching pattern" v)
       #f))
    ;; named failure continuation
    ((match-next v g+s (pat (=> failure) . body) . rest)
     (let ((failure (lambda () (match-next v g+s . rest))))
       ;; match-one analyzes the pattern for us
       (match-one v pat g+s (match-drop-ids (begin . body)) (failure) ())))
    ;; anonymous failure continuation, give it a dummy name
    ((match-next v g+s (pat . body) . rest)
     (match-next v g+s (pat (=> failure) . body) . rest))))

;; MATCH-ONE first checks for ellipsis patterns, otherwise passes on to
;; MATCH-TWO.

(define-syntax match-one
  (syntax-rules ()
    ;; If it's a list of two or more values, check to see if the
    ;; second one is an ellipsis and handle accordingly, otherwise go
    ;; to MATCH-TWO.
    ((match-one v (p q . r) g+s sk fk i)
     (match-check-ellipsis
      q
      (match-extract-vars p (match-gen-ellipsis v p r  g+s sk fk i) i ())
      (match-two v (p q . r) g+s sk fk i)))
    ;; Go directly to MATCH-TWO.
    ((match-one . x)
     (match-two . x))))

;; This is the guts of the pattern matcher.  We are passed a lot of
;; information in the form:
;;
;;   (match-two var pattern getter setter success-k fail-k (ids ...))
;;
;; usually abbreviated
;;
;;   (match-two v p g+s sk fk i)
;;
;; where VAR is the symbol name of the current variable we are
;; matching, PATTERN is the current pattern, getter and setter are the
;; corresponding accessors (e.g. CAR and SET-CAR! of the pair holding
;; VAR), SUCCESS-K is the success continuation, FAIL-K is the failure
;; continuation (which is just a thunk call and is thus safe to expand
;; multiple times) and IDS are the list of identifiers bound in the
;; pattern so far.

(define-syntax match-two
  (syntax-rules (_ ___ ..1 *** quote quasiquote ? $ = and or not set! get!)
    ((match-two v () g+s (sk ...) fk i)
     (if (null? v) (sk ... i) fk))
    ((match-two v (quote p) g+s (sk ...) fk i)
     (if (equal? v 'p) (sk ... i) fk))
    ((match-two v (quasiquote p) . x)
     (match-quasiquote v p . x))
    ((match-two v (and) g+s (sk ...) fk i) (sk ... i))
    ((match-two v (and p q ...) g+s sk fk i)
     (match-one v p g+s (match-one v (and q ...) g+s sk fk) fk i))
    ((match-two v (or) g+s sk fk i) fk)
    ((match-two v (or p) . x)
     (match-one v p . x))
    ((match-two v (or p ...) g+s sk fk i)
     (match-extract-vars (or p ...) (match-gen-or v (p ...) g+s sk fk i) i ()))
    ((match-two v (not p) g+s (sk ...) fk i)
     (match-one v p g+s (match-drop-ids fk) (sk ... i) i))
    ((match-two v (get! getter) (g s) (sk ...) fk i)
     (let ((getter (lambda () g))) (sk ... i)))
    ((match-two v (set! setter) (g (s ...)) (sk ...) fk i)
     (let ((setter (lambda (x) (s ... x)))) (sk ... i)))
    ((match-two v (? pred . p) g+s sk fk i)
     (if (pred v) (match-one v (and . p) g+s sk fk i) fk))
    ((match-two v (= proc p) . x)
     (let ((w (proc v))) (match-one w p . x)))
    ((match-two v (p ___ . r) g+s sk fk i)
     (match-extract-vars p (match-gen-ellipsis v p r g+s sk fk i) i ()))
    ((match-two v (p) g+s sk fk i)
     (if (and (pair? v) (null? (cdr v)))
         (let ((w (car v)))
           (match-one w p ((car v) (set-car! v)) sk fk i))
         fk))
    ((match-two v (p *** q) g+s sk fk i)
     (match-extract-vars p (match-gen-search v p q g+s sk fk i) i ()))
    ((match-two v (p *** . q) g+s sk fk i)
     (syntax-error "invalid use of ***" (p *** . q)))
    ((match-two v (p ..1) g+s sk fk i)
     (if (pair? v)
         (match-one v (p ___) g+s sk fk i)
         fk))
    ((match-two v ($ rec p ...) g+s sk fk i)
     (syntax-error "record ($) patterns are not supported" ($ rec p ...)))
    ((match-two v (p . q) g+s sk fk i)
     (if (pair? v)
         (let ((w (car v)) (x (cdr v)))
           (match-one w p ((car v) (set-car! v))
                      (match-one x q ((cdr v) (set-cdr! v)) sk fk)
                      fk
                      i))
         fk))
    ((match-two v #(p ...) g+s . x)
     (match-vector v 0 () (p ...) . x))
    ((match-two v _ g+s (sk ...) fk i) (sk ... i))
    ;; Not a pair or vector or special literal, test to see if it's a
    ;; new symbol, in which case we just bind it, or if it's an
    ;; already bound symbol or some other literal, in which case we
    ;; compare it with EQUAL?.
    ((match-two v x g+s (sk ...) fk (id ...))
     (let-syntax
         ((new-sym?
           (syntax-rules (id ...)
             ((new-sym? x sk2 fk2) sk2)
             ((new-sym? y sk2 fk2) fk2))))
       (new-sym? random-sym-to-match
                 (let ((x v)) (sk ... (id ... x)))
                 (if (equal? v x) (sk ... (id ...)) fk))))
    ))

;; QUASIQUOTE patterns

(define-syntax match-quasiquote
  (syntax-rules (unquote unquote-splicing quasiquote)
    ((_ v (unquote p) g+s sk fk i)
     (match-one v p g+s sk fk i))
    ((_ v ((unquote-splicing p) . rest) g+s sk fk i)
     (if (pair? v)
       (match-one v
                  (p . tmp)
                  (match-quasiquote tmp rest g+s sk fk)
                  fk
                  i)
       fk))
    ((_ v (quasiquote p) g+s sk fk i . depth)
     (match-quasiquote v p g+s sk fk i #f . depth))
    ((_ v (unquote p) g+s sk fk i x . depth)
     (match-quasiquote v p g+s sk fk i . depth))
    ((_ v (unquote-splicing p) g+s sk fk i x . depth)
     (match-quasiquote v p g+s sk fk i . depth))
    ((_ v (p . q) g+s sk fk i . depth)
     (if (pair? v)
       (let ((w (car v)) (x (cdr v)))
         (match-quasiquote
          w p g+s
          (match-quasiquote-step x q g+s sk fk depth)
          fk i . depth))
       fk))
    ((_ v #(elt ...) g+s sk fk i . depth)
     (if (vector? v)
       (let ((ls (vector->list v)))
         (match-quasiquote ls (elt ...) g+s sk fk i . depth))
       fk))
    ((_ v x g+s sk fk i . depth)
     (match-one v 'x g+s sk fk i))))

(define-syntax match-quasiquote-step
  (syntax-rules ()
    ((match-quasiquote-step x q g+s sk fk depth i)
     (match-quasiquote x q g+s sk fk i . depth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities

;; Takes two values and just expands into the first.
(define-syntax match-drop-ids
  (syntax-rules ()
    ((_ expr ids ...) expr)))

(define-syntax match-tuck-ids
  (syntax-rules ()
    ((_ (letish args (expr ...)) ids ...)
     (letish args (expr ... ids ...)))))

(define-syntax match-drop-first-arg
  (syntax-rules ()
    ((_ arg expr) expr)))

;; To expand an OR group we try each clause in succession, passing the
;; first that succeeds to the success continuation.  On failure for
;; any clause, we just try the next clause, finally resorting to the
;; failure continuation fk if all clauses fail.  The only trick is
;; that we want to unify the identifiers, so that the success
;; continuation can refer to a variable from any of the OR clauses.

(define-syntax match-gen-or
  (syntax-rules ()
    ((_ v p g+s (sk ...) fk (i ...) ((id id-ls) ...))
     (let ((sk2 (lambda (id ...) (sk ... (i ... id ...)))))
       (match-gen-or-step v p g+s (match-drop-ids (sk2 id ...)) fk (i ...))))))

(define-syntax match-gen-or-step
  (syntax-rules ()
    ((_ v () g+s sk fk . x)
     ;; no OR clauses, call the failure continuation
     fk)
    ((_ v (p) . x)
     ;; last (or only) OR clause, just expand normally
     (match-one v p . x))
    ((_ v (p . q) g+s sk fk i)
     ;; match one and try the remaining on failure
     (let ((fk2 (lambda () (match-gen-or-step v q g+s sk fk i))))
       (match-one v p g+s sk (fk2) i)))
    ))

;; We match a pattern (p ...) by matching the pattern p in a loop on
;; each element of the variable, accumulating the bound ids into lists.

;; Look at the body of the simple case - it's just a named let loop,
;; matching each element in turn to the same pattern.  The only trick
;; is that we want to keep track of the lists of each extracted id, so
;; when the loop recurses we cons the ids onto their respective list
;; variables, and on success we bind the ids (what the user input and
;; expects to see in the success body) to the reversed accumulated
;; list IDs.

(define-syntax match-gen-ellipsis
  (syntax-rules ()
    ((_ v p () g+s (sk ...) fk i ((id id-ls) ...))
     (match-check-identifier p
       ;; simplest case equivalent to (p ...), just bind the list
       (let ((w v))
         (if (list? w)
             (match-one w p g+s (sk ...) fk i)
             fk))
       ;; simple case, match all elements of the list
       (let loop ((ls v) (id-ls '()) ...)
         (cond
           ((null? ls)
            (let ((id (reverse id-ls)) ...) (sk ... i)))
           ((pair? ls)
            (let ((w (car ls)))
              (match-one w p ((car ls) (set-car! ls))
                         (match-drop-ids (loop (cdr ls) (cons id id-ls) ...))
                         fk i)))
           (else
            fk)))))
    ((_ v p r g+s sk fk (i ...) ((id id-ls) ...))
     (match-verify-no-ellipsis
      r
      (match-bound-identifier-memv
       p
       (i ...)
       ;; p is bound, match the list up to the known length, then
       ;; match the trailing patterns
       (let loop ((ls v) (expect p))
         (cond
          ((null? expect)
           (match-one ls r (#f #f) sk fk (i ...)))
          ((pair? ls)
           (let ((w (car ls))
                 (e (car expect)))
             (if (equal? (car ls) (car expect))
                 (match-drop-ids (loop (cdr ls) (cdr expect)))
                 fk)))
          (else
           fk)))
       ;; general case, trailing patterns to match, keep track of the
       ;; remaining list length so we don't need any backtracking
       (let* ((tail-len (length 'r))
              (ls v)
              (len (and (list? ls) (length ls))))
         (if (or (not len) (< len tail-len))
             fk
             (let loop ((ls ls) (n len) (id-ls '()) ...)
               (cond
                ((= n tail-len)
                 (let ((id (reverse id-ls)) ...)
                   (match-one ls r (#f #f) sk fk (i ... id ...))))
                ((pair? ls)
                 (let ((w (car ls)))
                   (match-one w p ((car ls) (set-car! ls))
                              (match-drop-ids
                               (loop (cdr ls) (- n 1) (cons id id-ls) ...))
                              fk
                              (i ...))))
                (else
                 fk))))))))))

;; This is just a safety check.  Although unlike syntax-rules we allow
;; trailing patterns after an ellipsis, we explicitly disable multiple
;; ellipses at the same level.  This is because in the general case
;; such patterns are exponential in the number of ellipses, and we
;; don't want to make it easy to construct very expensive operations
;; with simple looking patterns.  For example, it would be O(n^2) for
;; patterns like (a ... b ...) because we must consider every trailing
;; element for every possible break for the leading "a ...".

(define-syntax match-verify-no-ellipsis
  (syntax-rules ()
    ((_ (x . y) sk)
     (match-check-ellipsis
      x
      (syntax-error
       "multiple ellipsis patterns not allowed at same level")
      (match-verify-no-ellipsis y sk)))
    ((_ () sk)
     sk)
    ((_ x sk)
     (syntax-error "dotted tail not allowed after ellipsis" x))))

;; To implement the tree search, we use two recursive procedures.  TRY
;; attempts to match Y once, and on success it calls the normal SK on
;; the accumulated list ids as in MATCH-GEN-ELLIPSIS.  On failure, we
;; call NEXT which first checks if the current value is a list
;; beginning with X, then calls TRY on each remaining element of the
;; list.  Since TRY will recursively call NEXT again on failure, this
;; effects a full depth-first search.
;;
;; The failure continuation throughout is a jump to the next step in
;; the tree search, initialized with the original failure continuation
;; FK.

(define-syntax match-gen-search
  (syntax-rules ()
    ((match-gen-search v p q g+s sk fk i ((id id-ls) ...))
     (letrec ((try (lambda (w fail id-ls ...)
                     (match-one w q g+s
                                (match-tuck-ids
                                 (let ((id (reverse id-ls)) ...)
                                   sk))
                                (next w fail id-ls ...) i)))
              (next (lambda (w fail id-ls ...)
                      (if (not (pair? w))
                          (fail)
                          (let ((u (car w)))
                            (match-one
                             u p ((car w) (set-car! w))
                             (match-drop-ids
                              ;; accumulate the head variables from
                              ;; the p pattern, and loop over the tail
                              (let ((id-ls (cons id id-ls)) ...)
                                (let lp ((ls (cdr w)))
                                  (if (pair? ls)
                                      (try (car ls)
                                           (lambda () (lp (cdr ls)))
                                           id-ls ...)
                                      (fail)))))
                             (fail) i))))))
       ;; the initial id-ls binding here is a dummy to get the right
       ;; number of '()s
       (let ((id-ls '()) ...)
         (try v (lambda () fk) id-ls ...))))))

;; Vector patterns are just more of the same, with the slight
;; exception that we pass around the current vector index being
;; matched.

(define-syntax match-vector
  (syntax-rules (___)
    ((_ v n pats (p q) . x)
     (match-check-ellipsis q
                          (match-gen-vector-ellipsis v n pats p . x)
                          (match-vector-two v n pats (p q) . x)))
    ((_ v n pats (p ___) sk fk i)
     (match-gen-vector-ellipsis v n pats p sk fk i))
    ((_ . x)
     (match-vector-two . x))))

;; Check the exact vector length, then check each element in turn.

(define-syntax match-vector-two
  (syntax-rules ()
    ((_ v n ((pat index) ...) () sk fk i)
     (if (vector? v)
         (let ((len (vector-length v)))
           (if (= len n)
               (match-vector-step v ((pat index) ...) sk fk i)
               fk))
         fk))
    ((_ v n (pats ...) (p . q) . x)
     (match-vector v (+ n 1) (pats ... (p n)) q . x))))

(define-syntax match-vector-step
  (syntax-rules ()
    ((_ v () (sk ...) fk i) (sk ... i))
    ((_ v ((pat index) . rest) sk fk i)
     (let ((w (vector-ref v index)))
       (match-one w pat ((vector-ref v index) (vector-set! v index))
                  (match-vector-step v rest sk fk)
                  fk i)))))

;; With a vector ellipsis pattern we first check to see if the vector
;; length is at least the required length.

(define-syntax match-gen-vector-ellipsis
  (syntax-rules ()
    ((_ v n ((pat index) ...) p sk fk i)
     (if (vector? v)
       (let ((len (vector-length v)))
         (if (>= len n)
           (match-vector-step v ((pat index) ...)
                              (match-vector-tail v p n len sk fk)
                              fk i)
           fk))
       fk))))

(define-syntax match-vector-tail
  (syntax-rules ()
    ((_ v p n len sk fk i)
     (match-extract-vars p (match-vector-tail-two v p n len sk fk i) i ()))))

(define-syntax match-vector-tail-two
  (syntax-rules ()
    ((_ v p n len (sk ...) fk i ((id id-ls) ...))
     (let loop ((j n) (id-ls '()) ...)
       (if (>= j len)
         (let ((id (reverse id-ls)) ...) (sk ... i))
         (let ((w (vector-ref v j)))
           (match-one w p ((vector-ref v j) (vector-set! v j))
                      (match-drop-ids (loop (+ j 1) (cons id id-ls) ...))
                      fk i)))))))

;; Extract all identifiers in a pattern.  A little more complicated
;; than just looking for symbols, we need to ignore special keywords
;; and non-pattern forms (such as the predicate expression in ?
;; patterns), and also ignore previously bound identifiers.
;;
;; Calls the continuation with all new vars as a list of the form
;; ((orig-var tmp-name) ...), where tmp-name can be used to uniquely
;; pair with the original variable (e.g. it's used in the ellipsis
;; generation for list variables).
;;
;; (match-extract-vars pattern continuation (ids ...) (new-vars ...))

(define-syntax match-extract-vars
  (syntax-rules (_ ___ ..1 *** ? $ = quote quasiquote and or not get! set!)
    ((match-extract-vars (? pred . p) . x)
     (match-extract-vars p . x))
    ((match-extract-vars ($ rec . p) . x)
     (match-extract-vars p . x))
    ((match-extract-vars (= proc p) . x)
     (match-extract-vars p . x))
    ((match-extract-vars (quote x) (k ...) i v)
     (k ... v))
    ((match-extract-vars (quasiquote x) k i v)
     (match-extract-quasiquote-vars x k i v (#t)))
    ((match-extract-vars (and . p) . x)
     (match-extract-vars p . x))
    ((match-extract-vars (or . p) . x)
     (match-extract-vars p . x))
    ((match-extract-vars (not . p) . x)
     (match-extract-vars p . x))
    ;; A non-keyword pair, expand the CAR with a continuation to
    ;; expand the CDR.
    ((match-extract-vars (p q . r) k i v)
     (match-check-ellipsis
      q
      (match-extract-vars (p . r) k i v)
      (match-extract-vars p (match-extract-vars-step (q . r) k i v) i ())))
    ((match-extract-vars (p . q) k i v)
     (match-extract-vars p (match-extract-vars-step q k i v) i ()))
    ((match-extract-vars #(p ...) . x)
     (match-extract-vars (p ...) . x))
    ((match-extract-vars _ (k ...) i v)    (k ... v))
    ((match-extract-vars ___ (k ...) i v)  (k ... v))
    ((match-extract-vars *** (k ...) i v)  (k ... v))
    ((match-extract-vars ..1 (k ...) i v)  (k ... v))
    ;; This is the main part, the only place where we might add a new
    ;; var if it's an unbound symbol.
    ((match-extract-vars p (k ...) (i ...) v)
     (let-syntax
         ((new-sym?
           (syntax-rules (i ...)
             ((new-sym? p sk fk) sk)
             ((new-sym? any sk fk) fk))))
       (new-sym? random-sym-to-match
                 (k ... ((p p-ls) . v))
                 (k ... v))))
    ))

;; Stepper used in the above so it can expand the CAR and CDR
;; separately.

(define-syntax match-extract-vars-step
  (syntax-rules ()
    ((_ p k i v ((v2 v2-ls) ...))
     (match-extract-vars p k (v2 ... . i) ((v2 v2-ls) ... . v)))
    ))

(define-syntax match-extract-quasiquote-vars
  (syntax-rules (quasiquote unquote unquote-splicing)
    ((match-extract-quasiquote-vars (quasiquote x) k i v d)
     (match-extract-quasiquote-vars x k i v (#t . d)))
    ((match-extract-quasiquote-vars (unquote-splicing x) k i v d)
     (match-extract-quasiquote-vars (unquote x) k i v d))
    ((match-extract-quasiquote-vars (unquote x) k i v (#t))
     (match-extract-vars x k i v))
    ((match-extract-quasiquote-vars (unquote x) k i v (#t . d))
     (match-extract-quasiquote-vars x k i v d))
    ((match-extract-quasiquote-vars (x . y) k i v d)
     (match-extract-quasiquote-vars
      x
      (match-extract-quasiquote-vars-step y k i v d) i () d))
    ((match-extract-quasiquote-vars #(x ...) k i v d)
     (match-extract-quasiquote-vars (x ...) k i v d))
    ((match-extract-quasiquote-vars x (k ...) i v d)
     (k ... v))
    ))

(define-syntax match-extract-quasiquote-vars-step
  (syntax-rules ()
    ((_ x k i v d ((v2 v2-ls) ...))
     (match-extract-quasiquote-vars x k (v2 ... . i) ((v2 v2-ls) ... . v) d))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Gimme some sugar baby.

(define-syntax match-lambda
  (syntax-rules ()
    ((_ (pattern . body) ...) (lambda (expr) (match expr (pattern . body) ...)))))

(define-syntax match-lambda*
  (syntax-rules ()
    ((_ (pattern . body) ...) (lambda expr (match expr (pattern . body) ...)))))

(define-syntax match-let
  (syntax-rules ()
    ((_ ((var value) ...) . body)
     (match-let/helper let () () ((var value) ...) . body))
    ((_ loop ((var init) ...) . body)
     (match-named-let loop () ((var init) ...) . body))))

(define-syntax match-letrec
  (syntax-rules ()
    ((_ ((var value) ...) . body)
     (match-let/helper letrec () () ((var value) ...) . body))))

(define-syntax match-let/helper
  (syntax-rules ()
    ((_ let ((var expr) ...) () () . body)
     (let ((var expr) ...) . body))
    ((_ let ((var expr) ...) ((pat tmp) ...) () . body)
     (let ((var expr) ...)
       (match-let* ((pat tmp) ...)
         . body)))
    ((_ let (v ...) (p ...) (((a . b) expr) . rest) . body)
     (match-let/helper
      let (v ... (tmp expr)) (p ... ((a . b) tmp)) rest . body))
    ((_ let (v ...) (p ...) ((#(a ...) expr) . rest) . body)
     (match-let/helper
      let (v ... (tmp expr)) (p ... (#(a ...) tmp)) rest . body))
    ((_ let (v ...) (p ...) ((a expr) . rest) . body)
     (match-let/helper let (v ... (a expr)) (p ...) rest . body))))

(define-syntax match-named-let
  (syntax-rules ()
    ((_ loop ((pat expr var) ...) () . body)
     (let loop ((var expr) ...)
       (match-let ((pat var) ...)
         . body)))
    ((_ loop (v ...) ((pat expr) . rest) . body)
     (match-named-let loop (v ... (pat expr tmp)) rest . body))))

(define-syntax match-let*
  (syntax-rules ()
    ((_ () . body)
     (let () . body))
    ((_ ((pat expr) . rest) . body)
     (match expr (pat (match-let* rest . body))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Otherwise COND-EXPANDed bits.

;; This *should* work, but doesn't :(
;;   (define-syntax match-check-ellipsis
;;     (syntax-rules (...)
;;       ((_ ... sk fk) sk)
;;       ((_ x sk fk) fk)))

;; This is a little more complicated, and introduces a new let-syntax,
;; but should work portably in any R[56]RS Scheme.  Taylor Campbell
;; originally came up with the idea.
(define-syntax match-check-ellipsis
  (syntax-rules ()
    ;; these two aren't necessary but provide fast-case failures
    ((match-check-ellipsis (a . b) success-k failure-k) failure-k)
    ((match-check-ellipsis #(a ...) success-k failure-k) failure-k)
    ;; matching an atom
    ((match-check-ellipsis id success-k failure-k)
     (let-syntax ((ellipsis? (syntax-rules ()
                               ;; iff `id' is `...' here then this will
                               ;; match a list of any length
                               ((ellipsis? (foo id) sk fk) sk)
                               ((ellipsis? other sk fk) fk))))
       ;; this list of three elements will only match the (foo id) list
       ;; above if `id' is `...'
       (ellipsis? (a b c) success-k failure-k)))))

;; This is portable but can be more efficient with non-portable
;; extensions.  This trick was originally discovered by Oleg Kiselyov.

(define-syntax match-check-identifier
  (syntax-rules ()
    ;; fast-case failures, lists and vectors are not identifiers
    ((_ (x . y) success-k failure-k) failure-k)
    ((_ #(x ...) success-k failure-k) failure-k)
    ;; x is an atom
    ((_ x success-k failure-k)
     (let-syntax
         ((sym?
           (syntax-rules ()
             ;; if the symbol `abracadabra' matches x, then x is a
             ;; symbol
             ((sym? x sk fk) sk)
             ;; otherwise x is a non-symbol datum
             ((sym? y sk fk) fk))))
       (sym? abracadabra success-k failure-k)))))

(define-syntax match-bound-identifier-memv
  (syntax-rules ()
    ((match-bound-identifier-memv a (id ...) sk fk)
     (match-check-identifier
      a
      (let-syntax
          ((memv?
            (syntax-rules (id ...)
              ((memv? a sk2 fk2) fk2)
              ((memv? anything-else sk2 fk2) sk2))))
        (memv? random-sym-to-match sk fk))
      fk))))

)) ; end define-library
