;;; The handful of non-R7RS-small primitives the compiler needs, with one
;;; implementation per supported host Scheme (Chicken or Guile). Everything
;;; else the compiler uses is R7RS-small or an SRFI (1, 69) both hosts provide.
(define-library (hop compat)
  (export sort
          bitwise-and
          bitwise-ior
          bitwise-not
          arithmetic-shift
          make-slots)
  (import (scheme base))
  (cond-expand
   (chicken
    (import (chicken bitwise)
            (chicken sort)
            (chicken type))
    ;; Chicken types (make-vector n x) as a vector whose elements are all of
    ;; x's type, and vector-set! never widens it. With csc -O3 (-specialize),
    ;; a vector made with #f and later filled with numbers then reads as
    ;; always #f, and the tests on it are folded away. The declared type
    ;; keeps the elements opaque.
    (begin
      (: make-slots (fixnum * --> (vector-of *)))
      (define (make-slots n fill) (make-vector n fill))))
   (guile
    (import (only (guile) sort logand logior lognot ash))
    (begin
      (define (bitwise-and . xs) (apply logand xs))
      (define (bitwise-ior . xs) (apply logior xs))
      (define (bitwise-not x) (lognot x))
      (define (arithmetic-shift n count) (ash n count))
      (define (make-slots n fill) (make-vector n fill))))))
