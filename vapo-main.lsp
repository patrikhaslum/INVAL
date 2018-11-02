
(defun get-commandline-args ()
  (cdr (ext:command-args)))

(defvar *policy* nil)

(defun print-state-graph (sgraph)
  (format t "~&state graph~%")
  ;; print nodes
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (trans (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph))))
      (format t "~&~a state: ~a~%  goal? ~a~%  action: ~a~%  transitions: ~a~%"
	      index state is-goal action trans)
      )))

(defun print-DOT (sgraph)
  (format t "~&digraph policy {~%")
  ;; print nodes
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (trans (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph))))
      (cond
       (is-goal
	(format t "  S~a [shape=rectangle,peripheries=2,label=\"S~a: ~a\"];~%"
		index index action))
       (t
	(format t "  S~a [shape=rectangle,label=\"S~a: ~a\"];~%"
		index index action)))
      ))
  ;; print edges
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (translist (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph))))
      (dolist (trans translist)
	(format t "  S~a -> S~a [label=\"~a\"];~%"
		index (second trans) (first trans)))))
  (format t "~&}~%")
  )


(defun vapo-main ()
  ;; Process command line arguments and read input files.
  (if (endp (get-commandline-args)) (print-help))
  (do ((rem-arg-list (get-commandline-args) (cdr rem-arg-list)))
      ((endp rem-arg-list) t)
    (let ((arg (car rem-arg-list)))
      (cond ((equal arg "-v")
	     (setq *verbosity* (+ *verbosity* 1)))
	    ((equal arg "-q")
	     (setq *verbosity* 0))
	    ((= (length rem-arg-list) 1) ;; last arg is policy file
	     (format t "~&reading policy from ~a...~%" arg)
	     (let ((contents (read-file arg)))
	       (setq *policy* (parse-policy arg contents))))
	    (t
	     (format t "~&reading ~a...~%" arg)
	     (let ((contents (read-file arg)))
	       (parse-file arg contents))))))
  (when (null *policy*)
    (format t "~&a policy file (last argument) is required~%")
    (quit))
  (format t "~&validating policy ~a...~%" (car *policy*))
  (let ((result (validate-policy (cdr *policy*) *init* *goal*
				 *actions* *types* *objects*)))
    (when (not (first result))
      (format t "~&state graph construction failed~%")
      (quit))
    (print-state-graph (second result))
    (print-DOT (second result))
    ))

;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (vapo-main))
(quit)
