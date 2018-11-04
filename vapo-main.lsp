
(defun get-commandline-args ()
  (cdr (ext:command-args)))

(defvar *policy* nil)
(defvar *expand-goal-states* nil)
(defvar *exact-policy-match* nil)
(defvar *ignore-static-predicates* nil)

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

(defun print-DOT-state (index state action is-goal &key (state-dec nil))
  (format t "  S~a [shape=rectangle,peripheries=~a,label=\"S~a~a~a\"];~%"
	  index (if is-goal 2 1) index
	  (if state-dec ": " "")
	  (cond ((eq state-dec 'action) action)
		((eq state-dec 'state) state)
		(t ""))))
		 

(defun print-DOT (sgraph &key (state-dec nil))
  (format t "~&digraph policy {~%")
  ;; print nodes
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (trans (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph))))
      (print-DOT-state index state action is-goal :state-dec state-dec)
      ))
  ;; print edges
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (translist (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph))))
      (dolist (trans translist)
	(if (not (eql (first trans) 1))
	    (format t "  S~a -> S~a [label=\"~a\"];~%"
		    index (second trans) (first trans))
	  (format t "  S~a -> S~a;~%"
		  index (second trans)))
	)))
    (format t "~&}~%")
  )


(defun vapo-main ()
  ;; Process command line arguments and read input files.
  (if (endp (get-commandline-args)) (print-help))
  (let ((*policy* nil)
	(*expand-goal-states* nil)
	(*exact-policy-match* nil)
	(*ignore-static-predicates* nil)
	(*dot-state-decorate* nil)
	(*print-dot* nil)
	)
    ;; parse arguments
    (do ((rem-arg-list (get-commandline-args) (cdr rem-arg-list)))
	((endp rem-arg-list) t)
	(let ((arg (car rem-arg-list)))
	  (cond ((equal arg "-v")
		 (setq *verbosity* (+ *verbosity* 1)))
		((equal arg "-q")
		 (setq *verbosity* 0))
		((equal arg "-xgs")
		 (setq *expand-goal-states* t))
		((equal arg "-epm")
		 (setq *exact-policy-match* t))
		((equal arg "-isp")
		 (setq *ignore-static-predicates* t))
		((equal arg "-dot")
		 (setq *print-dot* t)
		 (format t "~&/*~%"))
		((equal arg "-dsd")
		 (when (null (cdr rem-arg-list))
		   (format t "~&-dsd requires an argument (action, state)~%")
		   (quit))
		 (setq *dot-state-decorate* (cadr rem-arg-list))
		 (setq rem-arg-list (cdr rem-arg-list)))
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
    ;; main
    (format t "~&validating policy ~a...~%" (car *policy*))
    (let ((result (validate-policy (cdr *policy*) *init* *goal*
				   *actions* *types* *objects*
				   :expand-goal-states *expand-goal-states*
				   :exact *exact-policy-match*
				   :predicates-to-ignore
				   (if *ignore-static-predicates*
				       (collect-static-predicates
					*predicates* *actions* *axioms*)
				     nil)
				   )))
      (when (not (first result))
	(format t "~&state graph construction failed~%"))
      (print-state-graph (second result))
      (when *print-dot*
	(format t "~&*/~%")
	(print-DOT (second result) :state-dec *dot-state-decorate*))
      )))

;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (vapo-main))
(quit)
