;; A program that imports (vectors) (see vectors_lib.scm) and uses its
;; exported add1 binding. Built together with build_program.sh:
;;   ./build_program.sh -o out/vectors_demo examples/vectors_lib.scm examples/vectors_demo.scm
(import (vectors))
(add1 41)
