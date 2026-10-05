;; Loaded by tools/scheme.sh before every Guile run (guile -l).
;;
;; Guile 3.0.11's loop-invariant code motion (licm) miscompiles loops whose
;; body guards a vector access with a loop-invariant test, e.g. (hop pass
;; sccp)'s
;;
;;   (do (...) (...) (... (if (and seed (< i (vector-length seed))) ...)))
;;
;; with seed #f: licm hoists the vector-length load above the `seed` test and
;; the VM segfaults reading it from #f. A ten-line program reproduces it
;; (guild compile it with and without -Ono-licm). Turn the pass off for the
;; modules Guile auto-compiles.
(set! %auto-compilation-options
      (append '(#:licm? #f) %auto-compilation-options))
