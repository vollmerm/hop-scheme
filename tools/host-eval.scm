;;; Prints the value of a program's last form as computed by the host Scheme:
;;;   csi -R r7rs -I . -s tools/host-eval.scm FILE
(import (scheme base) (scheme write) (scheme file) (scheme read) (scheme eval)
        (scheme repl) (scheme process-context))

(define (read-forms path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((forms '()))
        (let ((form (read port)))
          (if (eof-object? form) (reverse forms) (loop (cons form forms))))))))

(let loop ((forms (read-forms (cadr (command-line)))) (value #f))
  (if (null? forms)
      (begin (write value) (newline))
      (loop (cdr forms) (eval (car forms) (interaction-environment)))))
