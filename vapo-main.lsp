;;#!/usr/local/bin/ecl -shell

;; Note: load is only requried when used interactively or as a script.
;; (load "inval.lsp")
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
	  (is-goal (fourth (nth index sgraph))))
      (format t "~&~a state: ~a~%  goal? ~a~%  action: ~a~%  transitions: ~a~%"
	      index state is-goal action trans)
      )))

(defun print-DOT-state (index state action is-goal &key (state-dec nil))
  (format t "  S~a [shape=rectangle,peripheries=~a,label=\"S~a~a~a\"];~%"
	  index (if is-goal 2 1) index
	  (if state-dec ": " "")
	  (cond ((equal state-dec "action") action)
		((equal state-dec "state") state)
		(t "")
		)))
		 

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

(defun collect-arcs (sgraph)
  (let ((outgoing (make-sequence 'vector (length sgraph) :initial-element nil))
	(incoming (make-sequence 'vector (length sgraph) :initial-element nil)))
    (dotimes (index (length sgraph))
      (let ((translist (third (elt sgraph index))))
	(setf (elt outgoing index) (mapcar #'second translist))
	(dolist (trans translist)
	  (setf (elt incoming (second trans))
		(cons index (elt incoming (second trans)))))))
    (values outgoing incoming)))

(defun scc-dfs (index arcs visited node-list)
  (setf (elt visited index) t)
  (dolist (neigh (elt arcs index))
    (when (not (elt visited neigh))
      (setq node-list (scc-dfs neigh arcs visited node-list))))
  (cons index node-list))

(defun scc (sgraph)
  (multiple-value-bind
   (outgoing incoming) (collect-arcs sgraph)
   (let ((visited (make-sequence 'vector (length sgraph) :initial-element nil))
	 (post-order nil)
	 (components nil))
     (dotimes (k (length sgraph))
       (when (not (elt visited k))
	 (setq post-order (scc-dfs k outgoing visited post-order))))
     ;; (format t "~&order = ~a" post-order)
     (fill visited nil)
     (dolist (k post-order)
       (when (not (elt visited k))
	 (let ((comp (scc-dfs k incoming visited nil)))
	   (setq components (cons comp components)))))
     (let ((n-to-c (make-sequence 'vector (length sgraph) :initial-element nil))
	   (cout (make-sequence 'list (length components) :initial-element nil))
	   (cin (make-sequence 'list (length components) :initial-element nil)))
       (dotimes (cindex (length components))
	 (dolist (node (elt components cindex))
	   (setf (elt n-to-c node) cindex)))
       (dotimes (cindex (length components))
	 (dolist (node (elt components cindex))
	   (setf (elt cout cindex)
		 (union (elt cout cindex)
			(remove-duplicates
			 (mapcar #'(lambda (i) (elt n-to-c i))
				 (elt outgoing node)))))
	   (setf (elt cin cindex)
		 (union (elt cin cindex)
			(remove-duplicates
			 (mapcar #'(lambda (i) (elt n-to-c i))
				 (elt incoming node)))))
	   ))
       (mapcar #'list components cout cin))
     )))

(defun count-test-actions (sgel)
  (let ((action (second sgel)))
    (if action
	(if (string-equal (subseq (symbol-name (car action)) 0 5) "TEST_") 1 0)
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
	(*expand-goal-states* nil)
	(*exact-policy-match* nil)
	(*ignore-static-predicates* nil)
	(*dot-state-decorate* nil)
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
		((equal arg "-count-tests")
		 (setq *count-test-actions* t))
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
      (when *count-test-actions*
	(let ((count (count-exp (second result) 0 nil #'count-test-actions)))
	  (format t "~&expected number of test actions: ~a~%" count)))
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
