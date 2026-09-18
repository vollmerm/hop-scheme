;; A small library demonstrating separate compilation: add1 is the only
;; exported binding; bump-by is a private helper add1 delegates to, and
;; should never appear as a publicly visible symbol in the compiled output.
(define-library (vectors)
  (export add1)
  (begin
    (define (bump-by n step) (+ n step))
    (define (add1 n) (bump-by n 1))))
