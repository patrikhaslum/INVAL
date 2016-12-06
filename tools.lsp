
;;;;
;; Interface to FD's translator. Used to generate lists of ground atoms,
;; actions, axioms and mutex groups.

(defvar *path-to-python* "python3")
(defvar *path-to-FD-dump.py* "dump.py")

(defun call-fd-dump (domain-path problem-path)
  (multiple-value-bind
      (stream code process)
      (si:run-program *path-to-python*
		      (list *path-to-FD-dump.py*
			    domain-path
			    problem-path
			    "fddump")
		      :wait t :input nil :output t)
    (when (not (eq code 0)) (error "~a running dump.py" code))
    (let ((content (read-file "fddump"))
	  (atoms nil)
	  (ground-action-names nil)
	  (ground-axioms nil)
	  (mutex-groups nil))
      (dolist (item content)
	(cond ((eq (car item) 'atoms)
	       (setq atoms (cdr item)))
	      ((eq (car item) 'actions)
	       (setq ground-action-names (cdr item)))
	      ((eq (car item) 'axioms)
	       (setq ground-axioms (cdr item)))
	      ((eq (car item) 'mutex-groups)
	       (setq mutex-groups (cdr item)))
	      ))
      (list atoms ground-action-names ground-axioms mutex-groups))))

(defun make-mutex-map (atoms mutex-groups)
  (let ((mmap (mapcar #'list atoms)))
    (dolist (group mutex-groups)
      (dolist (atom1 group)
	(dolist (atom2 group)
	  (when (not (equal atom1 atom2))
	    (setq mmap (add-to-set-map atom1 atom2 mmap :test #'equal))
	    ))))
    mmap))

;; Check if a list contains nil as an element.
;; (This function appears to be unused.)
;; (defun find-nil (lst)
;;   (cond ((endp lst) nil)
;; 	((eq (car lst) nil) t)
;; 	(t (find-nil (cdr lst)))))


;; Make an assoc list from 'lst', by associng elements with a series
;; of consecutive numbers, starting from 'num'.

(defun number-list (lst num)
  (cond ((endp lst) nil)
	(t (cons (cons (car lst) num)
		 (number-list (cdr lst) (+ num 1))))))

;;;;
;; Grounding tools.

;; A very basic implementation of grounding.
;; Returns (by multiple-value):
;; - list of ground fluents, on the form (fluent . domain);
;;   the domain includes the value 'undefined;
;; - list of ground atoms;
;; - list of simplified ground actions
;; - list of simplified (split) ground axioms.

(defun simple-ground
  (predicates functions actions axioms init goal types objects)
  (let* ((static-pred
	  (let ((tmp (collect-static-predicates predicates actions axioms
						:include-static-derived t)))
	    (when (>= *verbosity* 1)
	      (format t "~&static predicates: ~s~%" tmp))
	    tmp))
	 (init2 (apply-static-axioms init static-pred axioms types objects))
	 (static-fun
	  (collect-static-functions functions actions))
	 (state-pred
	  (remove-if #'(lambda (preddef)
			 (member (car preddef) static-pred))
		     predicates))
	 (state-fun
	  (remove-if #'(lambda (fundef)
			 (or (eq (cdr fundef) 'number)
			     (member (caar fundef) static-fun)))
		     functions))
	 (ground-actions
	  (mapflat #'(lambda (act)
		       (when (>= *verbosity* 1)
			 (format t "~&grounding ~a ~a...~%" (car act)
				 (assoc-val ':parameters (cdr act))))
		       (simplify-action act static-pred static-fun init2
					types objects
					:ground-all-parameters t :rename nil))
		   actions))
	 (ground-axioms
	  (mapflat #'(lambda (axiom)
		       (when (>= *verbosity* 1)
			 (format t "~&grounding ~a...~%" axiom))
		       (simplify-axiom axiom static-pred static-fun init2
				       types objects
				       :ground-all-parameters t))
		   (remove-if #'(lambda (axiom)
				  (axiom-predicate-in-list axiom static-pred))
			      axioms)))
	 (atoms
	  (mapflat #'(lambda (preddef)
		       (instantiate (cons (car preddef)
					  (mapcar #'car (cdr preddef)))
				    nil (cdr preddef) types objects
				    :insfun #'sublis))
		   state-pred))
	 (fluents
	  (mapflat #'(lambda (fundef)
		       (instantiate-object-fluent fundef types objects))
		   state-fun)))
    (values fluents atoms ground-actions ground-axioms)))

(defun apply-static-axioms (state static-pred axioms types objects)
  (let ((static-axioms
	 (remove-if #'(lambda (axiom)
			(not (axiom-predicate-in-list axiom static-pred)))
		    axioms)))
    (cond (static-axioms
	   (multiple-value-bind
	       (stratified-axioms stratified-dps) (stratify static-axioms)
	     (extend-state state stratified-axioms types objects)))
	  (t state))))

;; Generate all instances of an object-valued fluent, and return them
;; paired with the value domain. Returns nil if the value domain is
;; empty.

(defun instantiate-object-fluent (fun types objects)
  (let ((value-domain (objects-of-type (cdr fun) types objects)))
    (if value-domain
	(mapcar #'(lambda (gfun) (cons gfun (cons 'undefined value-domain)))
		(instantiate (cons (caar fun) (mapcar #'car (cdar fun)))
			     nil (cdar fun) *types* *objects*
			     :insfun #'sublis))
      nil)))

;; Instantiate variables in an expression, returning the list of instances
;; only where the guard formula evaluates to true (and well-defined) over
;; given facts.

(defun instantiate-with-guard
  (exp guard facts binds vars types objects
       &key (insfun #'instantiate-1) (insfun-returns-list nil))
  (instantiate
   exp binds vars types objects
   :insfun #'(lambda (binds exp)
	       (let* ((g-guard (instantiate-1 binds guard))
		      (val (eval-formula g-guard nil facts types objects)))
		 (if (and (car val) (cadr val))
		     (let ((g-exp (funcall insfun binds exp)))
		       (if insfun-returns-list g-exp (list g-exp)))
		   nil)))
   :insfun-returns-list t))

;; Ground an invariant (either set-constraint or formula).

(defun ground-invariant (inv facts types objects)
  (cond ((assoc-val ':set-constraint inv)
	 (instantiate-with-guard
	  (assoc-val ':set-constraint inv) (assoc-val ':context inv)
	  facts nil (parse-typed-list '() (assoc-val ':vars inv) 'object)
	  types objects
	  :insfun #'(lambda (binds sc)
		      (ground-set-constraint
		       binds sc facts types objects))))
	((assoc-val ':formula inv)
	 (instantiate-with-guard
	  (assoc-val ':formula inv) (assoc-val ':context inv)
	  facts nil (parse-typed-list '() (assoc-val ':vars inv) 'object)
	  types objects))
	(t (error "ill-formed invariant: ~a" inv))
	))

;; Internal function for grounding the elements of a set-constraint.

(defun ground-set-constraint (binds sc facts types objects)
  (cons (car sc)
	(cons (cadr sc)
	      (mapflat #'(lambda (sc-item)
			   (cond
			    ((not (listp sc-item))
			     (error "ill-formed set-constraint: ~a" sc))
			    ((eq (car sc-item) 'setof)
			     (ground-setof binds sc-item facts types objects))
			    (t (list (sublis binds sc-item)))))
		       (cddr sc)))))

(defun ground-setof (binds setof facts types objects)
  (let ((pso (parse-struct (cdr setof) :last ':atom)))
    (if (null (assoc-val ':atom pso))
	(error "ill-formed setof: ~a" setof)
      (instantiate-with-guard
       (assoc-val ':atom pso) (assoc-val ':context pso)
       facts binds (parse-typed-list nil (assoc-val ':vars pso) 'object)
       types objects))))

;;;;
;; Printing tools

(defun print-timed-plan (plan &key (stream t))
  (dolist (item (cdr plan))
    (let ((timestamp (car item))
	  (actions (cdr item)))
      (dolist (act actions)
	(format stream "~&~a : ~a~%" timestamp act)
	))))

(defun save-timed-plan (filename plan)
  (with-open-file
   (stream filename :direction :output)
   ;; (make-format-PDDL-friendly)
   (let ((*print-pretty* t))
     (print-timed-plan plan :stream stream))
   ;; (make-format-default)
   )
  nil)
