;;#!/usr/local/bin/ecl -shell

;; Note: load is only requried when used interactively or as a script.
;; (load "inval.lsp")
;; (load "vapo.lsp")
;; (load "simplify.lsp")

;; GCL version
;; (defun get-commandline-args ()
;;   (cdr si::*command-args*))

;; ECL version
(defun get-commandline-args ()
  (cdr (ext:command-args)))

;; Note: When running as a script with ECL, use:
;; (defun get-commandline-args ()
;;   ext:*unprocessed-ecl-command-args*)

(defun print-state-graph (sgraph)
  (format t "~&state graph~%")
  ;; print nodes
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (trans (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph)))
	  (value (fifth (nth index sgraph)))
	  )
      (format t "~&S~a state: ~a~%  goal? ~a~%  action: ~a~%  transitions: ~a~%  expected reward: ~a~%"
	      index state is-goal action trans value)
      )))

(defun print-DOT-state (index state action is-goal value &key (label-states t) (state-dec nil))
  (if label-states
      (format t "  S~a [shape=rectangle,peripheries=~a,label=\"S~a~a~a (~a)\"];~%"
	      index (if is-goal 2 1) index
	      (if state-dec ": " "")
	      (cond ((equal state-dec "action") action)
		    ((equal state-dec "state") state)
		    (t ""))
	      value)
    (format t "  S~a [shape=circle,peripheries=~a,label=\"\"];~%"
	    index (if is-goal 2 1))))
		 

(defun print-DOT (sgraph &key (dot-label t) (state-dec nil))
  (format t "~&digraph policy {~%")
  ;; print nodes
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (trans (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph)))
	  (value (fifth (nth index sgraph)))
	  )
      (print-DOT-state index state action is-goal value
		       :label-states dot-label :state-dec state-dec)
      ))
  ;; print edges
  (dotimes (index (length sgraph))
    (let ((state (first (nth index sgraph)))
	  (action (second (nth index sgraph)))
	  (translist (third (nth index sgraph)))
	  (is-goal (fourth (nth index sgraph))))
      (dolist (trans translist)
	(if (and (not (eql (first trans) 1)) dot-label)
	    (format t "  S~a -> S~a [label=\"~a\\n~a\"];~%"
		    index (second trans) (first trans) (third trans))
	  (format t "  S~a -> S~a [label=\"~a\"];~%"
		  index (second trans) (third trans)))
	)))
    (format t "~&}~%")
  )

(defun count-test-actions (sgel)
  (let ((action (second sgel)))
    (if action
	(if (and (> (length (symbol-name (car action))) 8)
		 (string-equal (subseq (symbol-name (car action)) 0 8) "DO_TEST_")) 1 0)
      0)))

(defun count-exp (sgraph index stack cfun)
  (let ((val (funcall cfun (elt sgraph index)))
	(child-val-list nil))
    (if (fourth (elt sgraph index)) 0
      (progn
	(dolist (pair (third (elt sgraph index)))
	  (when (not (find (second pair) stack))
	    (let ((chv (count-exp
			sgraph (second pair) (cons (second pair) stack) cfun)))
	      (when chv
		(setq child-val-list
		      (cons (list (first pair) chv)
			    child-val-list))))))
	;;(format t "~&S~a child values list: ~s~%" index child-val-list)
	(if child-val-list
	    (let ((tp (reduce #'+ (mapcar #'first child-val-list))))
	      (+ (reduce #'+ (mapcar #'(lambda (pair)
					 (* (/ (first pair) tp) (second pair)))
				     child-val-list))
		 val))
	  nil)))))

(defun vapo-main ()
  ;; Process command line arguments and read input files.
  (if (endp (get-commandline-args)) (print-help))
  (let ((*policy* nil)
	(*ambiguous-policy-resolver* nil)
	(*expand-goal-states* nil)
	(*exact-policy-match* nil)
	(*ignore-static-predicates* nil)
	(*print-state-graph* nil)
	(*dot-state-decorate* nil)
	(*dot-state-labels* t)
	(*print-dot* nil)
	(*count-test-actions* nil)
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
		((equal arg "-aok")
		 (setq *ambiguous-policy-resolver* #'first))
		((equal arg "-psg")
		 (setq *print-state-graph* t))
		((equal arg "-count-tests")
		 (setq *count-test-actions* t))
		((equal arg "-dot")
		 (setq *print-dot* t)
		 (format t "~&/*~%"))
		((equal arg "-dnl")
		 (setq *dot-state-labels* nil))
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
				   ;; reward exp
				   ;; '(- (reward) 1) - for Blai's "-C action"
				   '(reward) ;; unmodified
				   :ambiguous-policy-resolver *ambiguous-policy-resolver*
				   :expand-goal-states *expand-goal-states*
				   :exact *exact-policy-match*
				   :predicates-to-ignore
				   (if *ignore-static-predicates*
				       (append
					(collect-static-predicates
					 *predicates* *actions* *axioms*)
					(collect-static-functions
					 *functions* *actions*))
				     nil)
				   )))
      (format t "~&policy is ~a~%expected reward = ~a (~a)~%"
	      (if (first result) "executable and proper"
		"not valid or not proper")
	      (second result) (float (second result)))
      (when *print-state-graph*
	(print-state-graph (third result)))
      (when *count-test-actions*
	(let ((count (count-exp (third result) 0 nil #'count-test-actions)))
	  (format t "~&expected number of test actions: ~a~%" count)))
      (when *print-dot*
	(format t "~&*/~%")
	(print-DOT (third result)
		   :dot-label *dot-state-labels*
		   :state-dec *dot-state-decorate*))
      )))

;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (vapo-main))
(quit)
