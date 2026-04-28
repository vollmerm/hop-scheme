(import (scheme base)
        (scheme write))

;;; Load compiler.scm before this file so write-aarch64-program and
;;; compile-program are available in the current environment.

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

(define test16
  '(letrec ((sum-down
             (lambda (n acc)
               (if (primop = n 0)
                   acc
                   (app sum-down
                        (primop - n 1)
                        (primop + acc n))))))
     (app sum-down 3 0)))

(define test17
  '(letrec ((walk
             (lambda (n)
               (if (primop = n 0)
                   0
                   (app jump (primop - n 1) 1))))
            (jump
             (lambda (n extra)
               (if (primop = n 0)
                   extra
                   (app walk (primop - n 1))))))
     (app walk 3)))

(define test18
  '(let ((step 1))
     (letrec ((even?
               (lambda (n)
                 (if (primop = n 0)
                     #t
                     (app odd? (primop - n step)))))
              (odd?
               (lambda (n)
                 (if (primop = n 0)
                     #f
                     (app even? (primop - n step))))))
       (app even? 4))))

(define test19
  '(let ((step 1))
     (letrec ((even?
               (lambda (n)
                 (if (primop = n 0)
                     #t
                     (app odd? (primop - n step)))))
              (odd?
               (lambda (n)
                 (if (primop = n 0)
                     #f
                     (app even? (primop - n step))))))
       even?)))

(define test20
  '(car (cons 7 ())))

(define test21
  '(cdr (cons 7 ())))

(define test22
  '(pair? (cons 1 ())))

(define test23
  '(null? ()))

(define test24
  '(if ()
       1
       2))

(define test25
  '(letrec ((sum-list
             (lambda (xs acc)
               (if (null? xs)
                   acc
                   (app sum-list
                        (cdr xs)
                        (primop + acc (car xs)))))))
     (app sum-list
          (cons 1 (cons 2 (cons 3 ())))
          0)))

(define test26
  '(let ((make-adder
          (lambda (x)
            (lambda (y)
              (primop + x y)))))
     (let ((f (app make-adder 5)))
       (app f 1))))

(define test27
  '(let ((choose
          (lambda (flag)
            (if flag
                (lambda (x) (primop + x 1))
                (lambda (x) (primop + x 2))))))
     (let ((f (app choose #t)))
       (app f 5))))

(define test28
  '(let ((make-chain
          (lambda (x)
            (lambda (y)
              (lambda (z)
                (primop + x (primop + y z)))))))
     (let ((f (app (app make-chain 1) 2)))
       (app f 3))))

(define test29
  '(let ((step 2))
     (letrec ((walk
               (lambda (n acc)
                 (if (primop = n 0)
                     acc
                     (app jump
                          (primop - n 1)
                          (primop + acc step)))))
              (jump
               (lambda (n acc)
                 (if (primop = n 0)
                     acc
                     (app walk
                          (primop - n 1)
                          (primop + acc 1))))))
       (app walk 2 0))))

(define test30
  '(let ((b (box 1)))
     (if (pair? (cons 0 ()))
         (set-box! b 4)
         (set-box! b 9))
     (primop + (unbox b) 1)))

(define test31
  '(let ((xs (cons 1 (cons 2 ()))))
     (if (null? (cdr (cdr xs)))
         (car (cdr xs))
         9)))

(define test32
  '(if #f
       1
       2))

(define test33
  '(let ((pick
          (lambda (flag)
            (if flag
                (let ((delta 1))
                  (lambda (x) (primop + x delta)))
                (let ((delta 2))
                  (lambda (x) (primop + x delta)))))))
     (let ((f (app pick #f)))
       (app f 5))))

(define test34
  '(let ((step 2))
     (letrec ((build
               (lambda (n)
                 (if (primop = n 0)
                     (lambda (x) (primop + x step))
                     (app build (primop - n 1))))))
       (let ((f (app build 3)))
         (app f 4)))))

(define test35
  '(letrec ((build
             (lambda (n acc)
               (if (primop = n 0)
                   acc
                   (let ((junk (box n)))
                     (app build
                          (primop - n 1)
                          (cons n acc))))))
            (sum
             (lambda (xs acc)
               (if (null? xs)
                   acc
                   (app sum
                        (cdr xs)
                        (primop + acc (car xs)))))))
     (app sum (app build 60 ()) 0)))

(define test36
  '(letrec ((make
             (lambda (n)
               (if (primop = n 0)
                   (lambda (x) x)
                   (let ((prev (app make (primop - n 1)))
                         (junk (box n)))
                     (lambda (x)
                       (app prev (primop + x n))))))))
     (let ((f (app make 50)))
       (app f 0))))

(define test37
  '(program
     (define x 5)
     (define y (primop + x 2))
     (primop + y 1)))

(define test38
  '(program
     (define even?
       (lambda (n)
         (if (primop = n 0)
             #t
             (app odd? (primop - n 1)))))
     (define odd?
       (lambda (n)
         (if (primop = n 0)
             #f
             (app even? (primop - n 1)))))
     (app even? 4)))

(define test39
  '(program
     (begin
       (define x 1)
       (define y 2))
     (primop + x y)))

(define test40
  '(program
     (define offset 10)
     (define mk
       (lambda (x)
         (lambda (y)
           (primop + offset (primop + x y)))))
     (define f (app mk 5))
     (app f 1)))

(define test41
  '(program
     (define xs
       (letrec ((build
                 (lambda (n acc)
                   (if (primop = n 0)
                       acc
                       (let ((junk (box n)))
                         (app build
                              (primop - n 1)
                              (cons n acc)))))))
         (app build 60 ())))
     (letrec ((sum
                (lambda (ys acc)
                  (if (null? ys)
                      acc
                      (app sum
                           (cdr ys)
                           (primop + acc (car ys)))))))
        (app sum xs 0))))

(define test42
  '(let ((p (cons 7 ())))
     (letrec ((burn
               (lambda (n)
                 (if (primop = n 0)
                     0
                     (let ((junk (cons n ())))
                       (app burn (primop - n 1)))))))
       (app burn 60)
       (car p))))

(define test43
  '(let ((keep (cons 7 ())))
     (let ((worker
            (lambda (n)
              (letrec ((fill
                        (lambda (k acc)
                          (if (primop = k 0)
                              acc
                              (app fill
                                   (primop - k 1)
                                    (cons k acc))))))
                 (app fill n ())))))
        (app worker 40)
        (car keep))))

(define test44
  '(let ((keep (box 7)))
      (letrec ((burn
                (lambda (n)
                  (if (primop = n 0)
                      (unbox keep)
                      (let ((junk (cons n ())))
                        (app burn (primop - n 1)))))))
        (app burn 80))))

(define test45
  '(let ((sum8
          (lambda (a b c d e f g h)
            (primop + a
                     (primop + b
                              (primop + c
                                       (primop + d
                                                (primop + e
                                                         (primop + f
                                                                  (primop + g h))))))))))
     (app sum8 1 2 3 4 5 6 7 8)))

;; Regression test: car/cdr/cons/pair?/null? in application position after
;; builtin canonicalization. These should compile identically to their primop
;; equivalents. Expected result: 2
(define test46
  '(let ((xs (cons 2 (cons 3 ()))))
     (car xs)))

;; First-class test: car used as a first-class value passed to a
;; higher-order function. Expected result: 5
(define test47
  '(let ((apply-fn (lambda (f p) (app f p))))
     (app apply-fn car (cons 5 ()))))

;; Direct pair allocation should allow rewriting car to unsafe-car.
(define test48
  '(car (cons 11 ())))

;; pair? then-branch should establish pair-ness for guarded value.
(define test49
  '(let ((x (cons 6 ())))
     (if (pair? x)
         (car x)
         0)))

;; Join-point value remains conservative even if both branches build pairs.
(define test50
  '(let ((x (if (primop = 0 0)
                (cons 9 ())
                0)))
     (car x)))

;; Mutually recursive sum/step: step is internal-only (not referenced in the
;; letrec body), so its entry block has no dispatch predecessor.  Pair-facts
;; from sum's pair?-guarded then-branch propagate across the back-edge into
;; step's entry block, enabling unsafe-car and unsafe-cdr in step's body.
(define test51
  '(letrec ((sum (lambda (xs acc)
                   (if (pair? xs)
                       (app step xs acc)
                       acc)))
            (step (lambda (xs acc)
                    (app sum (cdr xs) (primop + acc (car xs))))))
     (app sum (cons 1 (cons 2 (cons 3 ()))) 0)))

;; Three-way mutual recursion (outer/A/B): outer is the only external member.
;; A and B are internal-only, so their entry blocks have no dispatch predecessor.
;; entry.A has TWO predecessors: outer's work block (which allocates a fresh cons
;; for the shared param) and entry.B (which also allocates a fresh cons).  In
;; iteration 1 entry.B has not been processed when entry.A is first visited, so
;; in[entry.A] = {} and car/cdr are left safe.  In iteration 2 both predecessors
;; carry pair evidence for the shared first param, giving in[entry.A] = {t4} and
;; enabling unsafe-car and unsafe-cdr in A.  B's own car is deliberately NOT
;; rewritten: the value B receives for item is the cdr of A's item, which is
;; known to be a pair only by the pair? edge-refinement (stored in a different
;; temp), so no pair evidence propagates into B's item param.
(define test52
  '(letrec ((outer (lambda (n acc)
                     (if (primop = n 0)
                         acc
                         (app A (cons n (cons (primop - n 1) ())) acc))))
            (A (lambda (item acc)
                 (let ((val (car item)))
                   (if (primop = val 0)
                       acc
                       (if (pair? (cdr item))
                           (app B (cdr item) (primop + acc val))
                           (app outer (primop - val 1) (primop + acc val)))))))
            (B (lambda (item acc)
                 (app A (cons (car item) ()) acc))))
     (app outer 3 0)))

;; test53: constant folding — let-bound constant, foldable primop application.
;; `(let ((x 3)) (* x x))` → after folding, the multiplication becomes the
;; literal 9 and the assignment to x becomes dead.  Assembly must not contain
;; a mul instruction.
(define test53
  '(let ((x 3))
     (primop * x x)))

;; test54: dead write elimination — pure computation whose result is unused.
;; The `dead` binding computes `(+ x 1)` but x is immediately returned;
;; dead write elimination removes the add because `dead` is never live.
(define test54
  '(let ((f (lambda (x) (let ((dead (primop + x 1))) x))))
     (app f 5)))

(define sample-tests
  (list (cons "Test 1: Simple arithmetic" test1)
        (cons "Test 2: Lambda application" test2)
        (cons "Test 3: Box operations" test3)
        (cons "Test 5: Nested lets" test5)
        (cons "Test 6: Conditional with let" test6)
        (cons "Test 7: Nested conditionals" test7)
        (cons "Test 8: Loop-like pattern (for testing CFG)" test8)
        (cons "Test 9: Closure capture with sequencing in lambda body" test9)
        (cons "Test 10: Nested closures" test10)
        (cons "Test 11: Direct sequencing in lambda body" test11)
        (cons "Test 12: Simple values in if branches" test12)
        (cons "Test 13: Self-recursive letrec" test13)
        (cons "Test 14: Mutually recursive letrec" test14)
        (cons "Test 15: Sequencing in letrec body" test15)
        (cons "Test 16: Self-recursive letrec with accumulator" test16)
        (cons "Test 17: Mutual letrec fallback with incompatible arities" test17)
        (cons "Test 18: Capturing mutual letrec cluster" test18)
        (cons "Test 19: Capturing mutual letrec escape fallback" test19)
        (cons "Test 20: car of a cons cell" test20)
        (cons "Test 21: cdr returns null" test21)
        (cons "Test 22: pair? recognizes pairs" test22)
        (cons "Test 23: null? recognizes the empty list" test23)
        (cons "Test 24: only #f is false" test24)
        (cons "Test 25: Recursive sum over a list" test25)
        (cons "Test 26: Monomorphic closure call for 0CFA" test26)
        (cons "Test 27: Polymorphic closure call fallback" test27)
        (cons "Test 28: Nested closure chain capture" test28)
        (cons "Test 29: Mutual letrec with captured outer state" test29)
        (cons "Test 30: Conditional side effects feed later code" test30)
        (cons "Test 31: Nested pair traversal" test31)
        (cons "Test 32: False selects else branch" test32)
        (cons "Test 33: Captured polymorphic closure fallback" test33)
        (cons "Test 34: Self-tail letrec returns captured closure" test34)
        (cons "Test 35: Pair GC stress with transient boxes" test35)
        (cons "Test 36: Closure GC stress with nested captures" test36)
        (cons "Test 37: Top-level define feeds later forms" test37)
        (cons "Test 38: Top-level globals support forward references" test38)
        (cons "Test 39: Top-level begin flattens into file scope" test39)
        (cons "Test 40: Nested lambdas read globals" test40)
        (cons "Test 41: Global roots survive GC" test41)
        (cons "Test 42: Caller roots survive allocating direct calls" test42)
        (cons "Test 43: Caller roots survive allocating closure calls" test43)
        (cons "Test 44: Forced GC cycle with transient allocations" test44)
        (cons "Test 45: Eight-parameter lambda application" test45)
        (cons "Test 46: car/cdr/cons after builtin canonicalization" test46)
        (cons "Test 47: car as first-class value" test47)
        (cons "Test 48: direct car rewrite to unsafe-car" test48)
        (cons "Test 49: pair?-guarded car rewrite" test49)
        (cons "Test 50: conservative join keeps safe car" test50)
        (cons "Test 51: internal-only step enables back-edge unsafe-car" test51)
        (cons "Test 52: three-way mutual recursion requires two analysis iterations" test52)
        (cons "Test 53: constant folding eliminates mul" test53)
        (cons "Test 54: dead write elimination removes unused add" test54)))

(define named-tests
  ;; These are runnable end-to-end regression cases. test6 and test7 stay as
  ;; sample-only compiler exercises because they reference a free x.
  (list (cons 'test1 test1)
        (cons 'test2 test2)
        (cons 'test3 test3)
        (cons 'test5 test5)
        (cons 'test8 test8)
        (cons 'test9 test9)
        (cons 'test10 test10)
        (cons 'test11 test11)
        (cons 'test12 test12)
        (cons 'test13 test13)
        (cons 'test14 test14)
        (cons 'test15 test15)
        (cons 'test16 test16)
        (cons 'test17 test17)
        (cons 'test18 test18)
        (cons 'test19 test19)
        (cons 'test20 test20)
        (cons 'test21 test21)
        (cons 'test22 test22)
        (cons 'test23 test23)
        (cons 'test24 test24)
        (cons 'test25 test25)
        (cons 'test26 test26)
        (cons 'test27 test27)
        (cons 'test28 test28)
        (cons 'test29 test29)
        (cons 'test30 test30)
        (cons 'test31 test31)
        (cons 'test32 test32)
         (cons 'test33 test33)
         (cons 'test34 test34)
         (cons 'test35 test35)
         (cons 'test36 test36)
         (cons 'test37 test37)
          (cons 'test38 test38)
         (cons 'test39 test39)
         (cons 'test40 test40)
         (cons 'test41 test41)
          (cons 'test42 test42)
          (cons 'test43 test43)
          (cons 'test44 test44)
          (cons 'test45 test45)
          (cons 'test46 test46)
          (cons 'test47 test47)
          (cons 'test48 test48)
          (cons 'test49 test49)
          (cons 'test50 test50)
          (cons 'test51 test51)
          (cons 'test52 test52)
          (cons 'test53 test53)
          (cons 'test54 test54)))

(define (lookup-named-test name)
  (let ((binding (assoc name named-tests)))
    (if binding
        (cdr binding)
        (error "Unknown test name" name))))

(define (write-named-aarch64-program name path)
  (write-aarch64-program (lookup-named-test name) path))

(define (run-sample-tests)
  (let loop ((rest sample-tests) (first? #t))
    (if (null? rest)
        'done
        (begin
          (display (if first? "\n" "\n\n"))
          (display (car (car rest)))
          (newline)
          (compile-program (cdr (car rest)))
          (loop (cdr rest) #f)))))
