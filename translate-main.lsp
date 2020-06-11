(defun get-commandline-args ()
  (cdr (ext:command-args)))

(defun print-help ()
  (format t "~&translate <rules file> <plan>*~%")
  (quit)
  )

(defun translate-main ()
  (if (< (length (get-commandline-args)) 2) (print-help))
  (setq *rules* (read-file (first (get-commandline-args))))
  (dolist (planfile (rest (get-commandline-args)))
    (let ((contents (read-file planfile)))
      (parse-file planfile contents)))
  (dolist (plan *plans*)
    (format t "~&;; plan ~a:~%" (car plan))
    (dolist (step (translate-plan (cdr plan) *rules*))
      (dolist (act step)
	(format t "~&~s~%" act))))
  )

;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (translate-main))
(quit)
