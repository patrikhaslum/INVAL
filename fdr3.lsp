
;; Name variables by fluent/atom name (instead of the usual "varNN"):
(defvar *name-FDR-variable-by-atom-name* t)

;; Force translator to output a problem with/without metric spec; if
;; neither option is in effect, the problem will be considered to be
;; metric iff there is an initialisation of the fluent (total-cost).
(defvar *force-metric* nil)
(defvar *force-non-metric* nil)

;; Filter out actions with inconsistent effects. Returns the reduced
;; list of actions.

(defun filter-sas-actions (actions)
  (remove-if #'(lambda (act)
		 (let ((prec (normalise-simple-formula
			      (assoc-val ':precondition (cdr act))))
		       (effs (normalise-simple-formula
			      (assoc-val ':effect (cdr act)))))
		   (or (not (consistent-assignment prec))
		       (not (consistent-assignment effs)))))
	     actions))

(defun consistent-assignment (alist)
  (cond ((endp alist) t)
	((eq (caar alist) 'when) (consistent-assignment (cdr alist)))
	((some #'(lambda (acond)
		   (and (not (eq (car acond) 'when))
			(equal (car acond) (caar alist))
			(not (equal (cdr acond) (cdar alist)))))
	       (cdr alist))
	 nil)
	(t (consistent-assignment (cdr alist)))
	))

;; Write a grounded and simplified problem in Fast Downward's FDR format
;; version 3 (i.e., the "output.sas" file).
;;  stream - output stream to write to;
;;  is-metric - t/nil;
;;  fluents - list of pairs (ground fluent . domain);
;;  atoms - list of ground atoms;
;;  stratified-dps - stratified list of derived predicate names, i.e.,
;;   second value returned by (stratify *axioms*);
;;  simple-actions - list of simplified ground actions;
;;  simple-axioms - list of simplified ground axioms.
;; For both fluents and atoms it is assumed that no fluents/atoms not
;; in the lists are mentioned in actions, axioms, init or goal.

(defun output-FDR-v3
  (stream fluents atoms stratified-dps simple-actions simple-axioms init goal)
  (let ((var-index (make-variable-index fluents atoms))
	(is-metric (cond (*force-metric* t)
			 (*force-non-metric* nil)
			 ((find-fluent-value '(total-cost) init) t)
			 (t nil))))
    (when (>= *verbosity* 2)
      (format t "variable index:~%")
      (dolist (var var-index)
	(format t " ~a~%" var)))
    ;; version section
    (format stream "begin_version~%~a~%end_version~%" 3)
    ;; metric section
    (format stream "begin_metric~%~a~%end_metric~%" (if is-metric 1 0))
    ;; variables section
    (format stream "~a~%" (length var-index))
    (dolist (var var-index)
      (let* ((var-name (caar var))
	     (var-num (cdr var))
	     (var-domain (cdar var))
	     (var-layer (find-stratum (car var-name) stratified-dps)))
	;; * The first line is "begin_variable". 
	(format stream "begin_variable~%")
	;; * The second line contains the name of the variable
	(cond (*name-FDR-variable-by-atom-name*
	       (format stream "~a" (car var-name))
	       (dolist (term (cdr var-name))
		 (format stream "_~a" term))
	       (format stream "~%"))
	      (t (format stream "var~a~%" var-num)))
	;; * The third line specifies the axiom layer of the variable. 
	(format stream "~a~%" var-layer)
	;; * The fourth line specifies variable's range
	(format stream "~a~%" (length var-domain))
	;; * The following range lines specify the symoblic names for
	;;   each of the range values, one at a time.
	(dolist (val var-domain)
	  (format stream "~a~%" (car val)))
	;; * The final line is "end_variable".
	(format stream "end_variable~%")
	))
    ;; mutex section (no additional information)
    (format stream "0~%")
    ;; init state section
    (format stream "begin_state~%")
    (dolist (var var-index)
      (format stream "~a~%"
	      (cond
	       ;; if the variable is a derived predicate, it's default
	       ;; value is 0 (false)
	       ((>= (find-stratum (caaar var) stratified-dps) 0) 0)
	       ;; if it is an object fluent, it's value should be
	       ;; defined in the initial state
	       ((find-fluent-value (caar var) init)
		(translate-value (find-fluent-value (caar var) init) var))
	       ;; else, it's a predicate: true if present in init:
	       ((find (caar var) init :test #'equal) 1)
	       ;; otherwise false (0):
	       (t 0))))
    (format stream "end_state~%")
    ;; goal section
    (let ((goal-list (normalise-simple-formula goal)))
      (format stream "begin_goal~%~a~%" (length goal-list))
      (dolist (atomic-goal goal-list)
	(multiple-value-call #'format stream "~a ~a~%"
			     (translate-atomic-condition
			      atomic-goal var-index)))
      (format stream "end_goal~%"))
    ;; operator section
    (format stream "~a~%" (length simple-actions))
    (dolist (act simple-actions)
      (when (>= *verbosity* 2)
	(format t "action: ~w~%" act))
      (output-FDR3-action stream act var-index is-metric init))
    ;; axiom section
    (format stream "~a~%" (length simple-axioms))
    (dolist (axiom simple-axioms)
      (when (>= *verbosity* 2)
	(format t "axiom: ~w~%" axiom))
      (format stream "begin_rule~%")
      (let ((head (cons (car (second axiom))
			(mapcar #'car (parse-typed-list
				       nil (cdr (second axiom)) 'object))))
	    (body (normalise-simple-formula (third axiom))))
	(format stream "~a~%" (length body))
	(dolist (acond body)
	  (multiple-value-bind (var val)
	      (translate-atomic-condition acond var-index)
	    (format stream "~a ~a~%" var val)))
	(format stream "~a 0 1~%" (translate-atom head var-index)))
      (format stream "end_rule~%"))
    ))

(defun output-FDR3-action (stream act var-index is-metric init)
  ;; * The first line is "begin_operator".
  ;; * The second line contains the name of the operator. 
  (format stream "begin_operator~%~a" (caar act))
  (dolist (arg (cdar act))
    (format stream " ~a" arg))
  (format stream "~%")
  (let* ((prec (normalise-simple-formula
		(assoc-val ':precondition (cdr act))))
	 (effs (normalise-simple-formula
		(assoc-val ':effect (cdr act))))
	 (prevail (remove-if
		   #'(lambda (acond)
		       (find (car acond) effs :key #'car :test #'equal))
		   prec)))
    ;; prevails
    (format stream "~a~%" (length prevail))
    (dolist (acond prevail)
      (multiple-value-bind (var val)
	  (translate-atomic-condition acond var-index)
	(format stream "~a ~a~%" var val)))
    ;; effects
    (format stream "~a~%" (length effs))
    (dolist (eff effs)
      (let* ((post-acond (if (eq (car eff) 'when) (third eff) eff))
	     (pre-val (find-value-in-condition (car post-acond) prec)))
	(cond ((eq (car eff) 'when)
	       (let ((econd (second eff)))
		 (format stream "~a" (length econd))
		 (dolist (acond econd)
		   (multiple-value-bind (var val)
		       (translate-atomic-condition acond var-index)
		     (format stream " ~a ~a" var val)))))
	      (t (format stream "0")))
	(multiple-value-bind (var val)
	    (translate-atomic-condition post-acond var-index)
	  (format stream " ~a ~a ~a~%"
		  var (if pre-val (multiple-value-bind (dummy val1)
				      (translate-atomic-condition
				       (cons (car post-acond) pre-val)
				       var-index) val1)
			-1) val))))
    ;; action cost
    (format stream "~a~%"
	    (cond (is-metric
		   (let ((cost (find-if
				#'(lambda (eff)
				    (and (listp eff)
					 (eq (car eff) 'increase)
					 (equal (cadr eff) '(total-cost))))
				(cdr (assoc ':effect (cdr act))))))
		     (cond (cost (static-eval (caddr cost) init)) (t 0))))
		  (t 1)))
    ) ; end of let
  (format stream "end_operator~%")
  )

(defun static-eval (exp init)
  (let ((val (eval-term exp nil init :report-errors nil)))
    (when (null (car val))
      (error "metric expression ~a is undefined" exp))
    (when (not (numberp (car val)))
      (error "metric expression ~a is not numeric (~a)" exp val))
    (car val)))


;; The variable index is a list of pairs (fd-pair . index), where fd-pair
;; is (variable-name . indexed-variable-domain), and indexed-variable-domain
;; is a list of pair (value-name . index).
(defun make-variable-index (fluents atoms)
  (number-list
   (mapcar #'(lambda (fd-pair)
	       (cons (car fd-pair) (number-list (cdr fd-pair) 0)))
	   (append fluents
		   (mapcar #'(lambda (atom) (cons atom '(false true)))
			   atoms)))
   0))

(defun find-stratum (predicate stratified-dps &optional (index 0))
  (cond ((endp stratified-dps) -1)
	((member predicate (car stratified-dps)) index)
	(t (find-stratum predicate (cdr stratified-dps) (+ index 1)))))

(defun normalise-simple-formula (form)
  (cond ((null form) nil)
	((eq (car form) 'when)
	 (when (not (= (length form) 3)) (error "ill-formed effect: ~a" form))
	 (let ((tr-econd (normalise-simple-formula (second form)))
	       (tr-eff (normalise-simple-formula (third form))))
	   (mapcar #'(lambda (single-eff) (list 'when tr-econd single-eff))
		   tr-eff)))
	((eq (car form) 'and)
	 (mapflat #'normalise-simple-formula (cdr form)))
	((member (car form) '(increase decrease < <= > >=)) nil)
	((member (car form) '(= assign))
	 (list (cons (second form) (third form))))
	((eq (car form) 'not)
	 (list (cons (second form) 'false)))
	(t (list (cons form 'true)))
	))

;; An "atomic condition" is a pair (fluent-name . fluent-value).
;; The fluent-name may be an atom (ground predicate), in which case
;; the value should be 'false or 'true.
;; The translation function looks up the variable and value in the
;; var-index, and returns the corresponding numbers by multiple-value.

(defun translate-atomic-condition (acond var-index)
  (let ((var (assoc (car acond) var-index :key #'car :test #'equal)))
    (when (null var) (error "error: undefined variable in ~s~%" acond))
    (let ((val (assoc (cdr acond) (cdar var) :test #'equal)))
      (when (null val) (error "error: undefined value in ~s~%" acond))
      (values (cdr var) (cdr val)))))

(defun translate-value (value-sym var)
  (let ((val (assoc value-sym (cdar var) :test #'equal)))
    (when (null val) (error "error: undefined value in ~s~%" acond))
    (cdr val)))

(defun translate-atom (atom var-index)
  (let ((var (assoc atom var-index :key #'car :test #'equal)))
    (if (null var) (error "error: undefined binary variable ~s~%" atom))
    (cdr var)))

;; var-name is a ground variable name; aclist is a list of atomic
;; conditions.
(defun find-value-in-condition (var-name aclist)
  (assoc-val var-name aclist :test #'equal))
