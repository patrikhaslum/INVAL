
;; Transform domain and problem to "simple ADL". Arguments:
;;  requirements: list of requirements for new domain definition.
;;  domain-name, problem-name: duh.
;;  predicates, functions, actions, axioms, init, goal, metric-type,
;;    metric, types, objects: problem definition (as in global variables).
;;  :declare-constants (t/nil): use :constants declaration in domain?
;;  :compile-disjunctive-goal (t/nil): compile away disjunctive goal?
;;    (by adding separate goal-achieving actions to the domain).
;;  :with-types (t/nil): passed to make-domain-definition and
;;    make-problem-definition.
;;  :ground-all-parameters (t/nil): fully ground the problem.
;; Returns two values, new-domain and new-problem:
;; new-domain is the simplified domain definition;
;; new-problem is the modified problem definition, or nil if no
;;  changes were made to the problem.

(defun simplify
  (domain-name problem-name requirements
	       predicates functions actions axioms init goal
	       metric-type metric types objects
	       &key (declare-constants t) (compile-disjunctive-goal nil)
	       (with-types nil) (ground-all-parameters nil))
  (let* ((static-pred
	  (collect-static-predicates predicates actions axioms))
	 (static-fun
	  (collect-static-functions functions actions))
	 (new-actions
	  (mapflat #'(lambda (act)
		       (simplify-action
			act static-pred static-fun init types objects
			:ground-all-parameters ground-all-parameters))
		   actions))
	 (new-axioms
	  (mapflat #'(lambda (axiom)
		       (simplify-axiom
			axiom static-pred static-fun init types objects
			:ground-all-parameters ground-all-parameters))
		   axioms))
	 (new-goal
	  (transform-to-dnf
	   (simplify-formula
	    (instantiate-quantifiers goal nil types objects)
	    static-pred nil init) nil))
	 (constants nil))
    (cond
     ((and (> (length new-goal) 1) compile-disjunctive-goal)
      (push '(goal-achieved) predicates)
      (dotimes (i (length new-goal))
	(push (make-action (symnumcat 'goal-disjunct- (+ i 1))
			   nil (nth i new-goal) '(goal-achieved))
	      actions))
      (setq new-goal '(goal-achieved)))
     ((> (length new-goal) 1)
      (setq new-goal (cons 'or new-goal)))
     ((equal *goal* (first new-goal))
      (setq new-goal nil))
     (t (setq new-goal (first new-goal)))
     )
    (when declare-constants
      (dolist (act new-actions)
	(dolist (cname (constants-in-expression
			(cdr (assoc ':precondition (cdr act)))))
	  (pushnew cname constants))
	(dolist (cname (constants-in-expression
			(cdr (assoc ':effect (cdr act)))))
	  (pushnew cname constants))))
    (values
     (make-domain-definition
      domain-name requirements types objects constants
      predicates functions new-axioms new-actions :with-types with-types)
     (cond (new-goal
	    (make-problem-definition
	     problem-name domain-name
	     (remove-if #'(lambda (od) (find (car od) constants)) objects)
	     init new-goal metric-type metric :with-types with-types))
	   (constants
	    (make-problem-definition
	     problem-name domain-name
	     (remove-if #'(lambda (od) (find (car od) constants)) objects)
	     init goal metric-type metric :with-types with-types))
	   (t nil)))
    ))

;; Replace current domain/problem definition with simplified result.
;; Note: This will discard all currently loaded plans.

(defun simplify-internal
  (requirements &key (declare-constants t) (compile-disjunctive-goal nil)
		(with-types nil) (ground-all-parameters nil))
  (multiple-value-bind (new-domain new-problem)
      (simplify *domain-name* *problem-name* '(:adl :typing :equality)
		*predicates* *functions* *actions* *axioms* *init* *goal*
		*metric-type* *metric* *types* *objects*
		:declare-constants declare-constants
		:compile-disjunctive-goal compile-disjunctive-goal
		:with-types with-types
		:ground-all-parameters ground-all-parameters)
    (when (null new-problem)
      (setq new-problem
	    (make-problem-definition *problem-name* *domain-name*
				     *objects* *init* *goal*
				     *metric-type* *metric*
				     :with-types *output-types*)))
    (clear-definitions)
    (parse-file "domain" (list domain))
    (parse-file "problem" (list problem))
    ))

;; Translate an action to "simple ADL", i.e., remove all ADL constructs
;; except conditional effects (typing and equality are also unaffected).
;; This may involve partially grounding the action.
;; act - the action (in parsed struct form, i.e., as in *actions*)
;; static-pred - list of static predicate names
;; static-fun - list of static (object-valued) function names
;; facts - list of facts (used to determine truth of static atoms/terms)
;; types - list of type declarations (as in *types*)
;; objects - list of object declarations (as in *objects*)
;; ground-all-parameters (t/nil) - if true, all action parameters are
;;  instantiated.
;; rename (t/nil) - if false, action names in the return list are
;;  (partially) instantiated actions (i.e., list of name plus arguments)
;;  rather than symbols.
;; Returns: List of partially grounded and simplified actions.

(defun simplify-action (act static-pred static-fun facts types objects
			    &key (ground-all-parameters nil) (rename t))
  (let* ((qf-prec (transform-to-nnf
		   (instantiate-quantifiers
		    (assoc-val ':precondition (cdr act)) nil types objects)
		   nil))
	 (qf-eff (transform-to-nnf
		  (instantiate-quantifiers
		   (assoc-val ':effect (cdr act)) nil types objects)
		  nil))
	 (svars (cond
		 (ground-all-parameters
		  (mapcar #'car (assoc-val ':parameters (cdr act))))
		 (t (union (find-formula-simplifiers
			    qf-prec static-pred static-fun)
			   (find-formula-simplifiers
			    qf-eff static-pred static-fun)))))
	 (gparam (mapcar #'(lambda (var)
			     (let ((vardecl
				    (assoc var (assoc-val
						':parameters (cdr act)))))
			       (when (null vardecl)
				 (error "variable ~a not declared in action ~a"
					var act))
			       vardecl))
			 svars))
	 (rparam (remove-if #'(lambda (p) (find (car p) svars))
			    (assoc-val ':parameters (cdr act)))))
    (flet ((make-pg-actions
	    (binds exp)
	    (let ((pg-prec (simplify-formula
			    (sublis binds qf-prec)
			    static-pred static-fun facts))
		  (pg-eff-list (simplify-effect
				(sublis binds qf-eff)
				static-pred static-fun facts))
		  (n-copies 0))
	      (cond
	       ((null pg-prec) nil)
	       ((null pg-eff-list) nil)
	       ((some #'null pg-eff-list) nil)
	       ((eq pg-prec t)
		(list
		 (make-action
		  (make-pg-action-name act binds nil rename)
		  rparam nil (cons 'and pg-eff-list))))
	       (t (mapcar #'(lambda (disjunct)
			      (make-action
			       (make-pg-action-name
				act binds (setq n-copies (+ n-copies 1))
				rename)
			       rparam disjunct (cons 'and pg-eff-list)))
			  (transform-to-dnf pg-prec nil)))
	       ))))
      (instantiate nil nil gparam types objects
		   :insfun #'make-pg-actions
		   :insfun-returns-list t)
      )))

(defun make-action (name param prec eff)
  (cons name
	(cond ((null prec)
	       (list (cons ':parameters param)
		     (cons ':effect eff)))
	      (t
	       (list (cons ':parameters param)
		     (cons ':precondition prec)
		     (cons ':effect eff)))
	      )))

(defun make-pg-action-name (act binds counter rename)
  (if rename
      (symnumcat (cons (car act) (append (make-name-suffix '- binds)
					 (if counter (list counter) nil))))
    (cons (car act)
	  (sublis binds (mapcar #'car (assoc-val ':parameters (cdr act)))))))

(defun make-name-suffix (sep binds)
  (cond ((endp binds) nil)
	(t (cons sep
		 (cons (cdr (car binds))
		       (make-name-suffix sep (cdr binds)))))))

;; Simplify an axiom. Simple axioms have bodies that are conjunctions
;; of literals (hence, simplifications may involve a transform to DNF).
;; axiom - the axiom.
;; static-pred, static-fun, facts - as req. by simplify-formula
;; types, objects - as in *types*, *objects*
;; ground-all-parameters (t/nil) - if true, the axiom is fully grounded.
;; Returns: List of (partially) grounded simple axioms.

(defun simplify-axiom (axiom static-pred static-fun facts types objects
			     &key (ground-all-parameters nil))
  (when (< (length axiom) 2) (error "ill-formed axiom: ~s" axiom))
  (let* ((axiom-head (second axiom))
	 (qf-axiom-body
	  (transform-to-nnf
	   (instantiate-quantifiers (third axiom) nil types objects) nil))
	 (aparam (axiom-parameters axiom types))
	 (gparam
	  (if ground-all-parameters aparam
	    (mapcar #'(lambda (var)
			(let ((vardecl (assoc var aparam)))
			  (when (null vardecl)
			    (error "variable ~a undeclared in axiom ~a"
				   var axiom))
			  vardecl))
		    (find-formula-simplifiers
		     qf-axiom-body static-pred static-fun)))))
    (flet ((make-pg-axioms
	    (binds exp)
	    (let ((pg-body (simplify-formula
			    (sublis binds qf-axiom-body)
			    static-pred static-fun facts)))
	      (cond
	       ((null pg-body) nil)
	       ((eq pg-body t)
		(list (list ':derived (sublis binds axiom-head))))
	       (t (when (>= *verbosity* 4)
		    (format t "~&simplified axiom body: ~a~%" pg-body))
		  (mapcar #'(lambda (disjunct)
			      (list ':derived (sublis binds axiom-head)
				    disjunct))
			  (transform-to-dnf pg-body nil)))
	       ))))
      (instantiate nil nil gparam types objects
		   :insfun #'make-pg-axioms
		   :insfun-returns-list t)
      )))


;; Instantiate quantifiers occurring in an expression, replacing them
;; with and/or. The function also flattens nested ands and ors.
;; exp - the expression
;; binds - assoc list of current variable bindings (initially empty)
;; types - assoc list of (type . supertype) pairs
;; objects - assoc list of (object . type) pairs
;; returns: the instantiated expression

(defun instantiate-quantifiers (exp binds types objects)
  (cond ((null exp) exp)
	;; if exp is a list...
	((listp exp)
	 ;; if exp is a quantified expression, call instantiate with
	 ;; the quantified variables and the the body (formula)
	 (cond
	  ((or (eq (car exp) 'forall) (eq (car exp) 'exists))
	   (if (not (= (length exp) 3))
	       (error "ill-formed quantified formula: ~s" exp))
	   (let ((qvars (parse-typed-list '() (second exp) 'object)))
	     (cons (cond ((eq (car exp) 'forall) 'and) (t 'or))
		   (instantiate (third exp)
				(remove-bindings qvars binds)
				qvars types objects
				:insfun #'(lambda (b e)
					    (instantiate-quantifiers
					     e b types objects))))))
	  ;; if the expression is of the form (and ...) or (or ...),
	  ;; then flatten ands/ors contained in it
	  ((eq (car exp) 'and)
	   (cons 'and
		 (mapflat #'(lambda (x)
			      (let ((ix (instantiate-quantifiers
					 x binds types objects)))
				(cond ((and (listp ix) (eq (car ix) 'and))
				       (cdr ix))
				      (t (list ix)))))
			  (cdr exp))))
	  ((eq (car exp) 'or)
	   (cons 'or
		 (mapflat #'(lambda (x)
			      (let ((ix (instantiate-quantifiers
					 x binds types objects)))
				(cond ((and (listp ix) (eq (car ix) 'or))
				       (cdr ix))
				      (t (list ix)))))
			  (cdr exp))))
	  ;; for any other list expression, recursively instantiate
	  ;; all elements
	  (t (mapcar #'(lambda (x) (instantiate-quantifiers
				    x binds types objects)) exp))
	  ))
	;; if exp is a symbol, look it up in bindings
	((symbolp exp)
	 (let ((val (assoc exp binds)))
	   ;; if it is found, return the value
	   (cond (val (cdr val))
		 ;; else return the exp itself
		 (t exp))))
	;; if exp is neither a list nor a symbol, just return it
	(t exp)
	))


;; Simplify a (partially grounded) formula, using static predicates
;; and true facts. An atomic formula whose predicate is static and
;; whose arguments are all ground (atomic) terms will be evaluated
;; wrt the set facts.
;; The function may return:
;; t - indicating a statically true formula;
;; nil - indicating a statically false formula;
;; or a simplified formula.

(defun simplify-formula (form static-pred static-fun facts)
  (cond ((null form) t)
	((eq form t) form)
	((eq (car form) 'and)
	 (let ((fs (remove t (mapcar
			      #'(lambda (f1)
				  (simplify-formula
				   f1 static-pred static-fun facts))
			      (cdr form)))))
	   (cond ((endp fs) t)
		 ((some #'null fs) nil)
		 ((= (length fs) 1) (first fs))
		 (t (cons 'and fs)))))
	((eq (car form) 'or)
	 (let ((fs (remove nil (mapcar
				#'(lambda (f1)
				    (simplify-formula
				     f1 static-pred static-fun facts))
				(cdr form)))))
	   (cond ((endp fs) nil)
		 ((find t fs) t)
		 ((= (length fs) 1) (first fs))
		 (t (cons 'or fs)))))
	((eq (car form) 'not)
	 (if (not (= (length form) 2)) (error "ill-formed formula: ~s~%" form))
	 (let ((f1 (simplify-formula
		    (second form) static-pred static-fun facts)))
	   (cond ((null f1) t)
		 ((eq f1 t) nil)
		 (t (list 'not f1)))))
	((eq (car form) '=)
	 (if (not (= (length form) 3)) (error "ill-formed formula: ~s~%" form))
	 (let ((v1 (simplify-term (second form) static-fun facts))
	       (v2 (simplify-term (third form) static-fun facts)))
	   (cond ((or (null v1) (null v2)) nil)
		 ((and (symbolp v1) v1 (not (variable-p v1))
		       (symbolp v2) v2 (not (variable-p v2)))
		  (cond ((eq v1 v2) t)
			(t nil)))
		 (t (list '= v1 v2)))))
	((member (car form) '(< <= > >=)) form)
	;; otherwise, it should be an atomic formula:
	(t (simplify-atomic-formula form static-pred static-fun facts))
	))

;; Simplify a (partially grounded) atomic formula, using static
;; predicates and true facts.
;; The function may return:
;; t - indicating a statically true formula;
;; nil - indicating a statically false formula;
;; or a simplified formula.
(defun simplify-atomic-formula (form static-pred static-fun facts)
  (let ((args ;; simplified argument terms
	 (mapcar #'(lambda (t1) (simplify-term t1 static-fun facts))
		 (cdr form))))
    (cond
     ;; if any argument term is undefined, return false:
     ((some #'(lambda (arg) (null arg)) args)
      nil)
     ;; if the predicate is static and all arguments are ground,
     ;; return the static value:
     ((and (member (car form) static-pred)
	   (every #'(lambda (arg) (and (symbolp arg) (not (variable-p arg))))
		  args))
      (cond ((find (cons (car form) args) facts :test #'equal) t)
	    (t nil)))
     ;; else, return the atom with simplified arguments
     (t (cons (car form) args))
     )))


;; Simplify a (partially grounded) term, using static functions and facts.
;; Static functions are evaluated by looking for atoms of the form
;; (= (f ..) v) in facts; if no such atom is found, the function term is
;; undefined.
;; The function may return:
;; nil - indicating a static but undefined term;
;; or a simplified term.

(defun simplify-term (term static-fun facts)
  (if (not (consp term)) term
    (let ((args (mapcar #'(lambda (t1)
			    (simplify-term t1 static-fun facts))
			(cdr term))))
      (cond
       ;; if any argument term is statically undefined, so is the
       ;; whole term:
       ((some #'null args) nil)
       ;; if the term is a built-in numeric function, we should
       ;; check if the arguments are all static, and if so evaluate
       ;; the function... but that's not implemented yet.
       ((assoc (car term) *builtin-numeric-functions*)
	(cons (car term) args))
       ;; if the function and all arguments are static, look up its value
       ((and (member (car term) static-fun)
	     (every #'(lambda (arg)
			(and (symbolp arg) (not (variable-p arg))))
		    args))
	(find-fluent-value (cons (car term) args) facts))
       ;; else, return the simplified term:
       (t (cons (car term) args))
       ))))


;; ;; Simplify conditions in an effect formula; this includes rewriting
;; ;; conditions to DNF and splitting them up into one condeff for each case.
;; ;; This function assumes that any quantifiers have already been removed.
;; ;; Returns: A list of simplified effects. The list is conjunctive, but
;; ;; will not have the 'and keyword at the start.
;; 
;; (defun simplify-effect-conditions (eff static-pred static-fun facts)
;;   (cond ((eq (car eff) 'and)
;; 	 (mapflat #'(lambda (e1)
;; 		      (simplify-effect-conditions
;; 		       e1 static-pred static-fun facts))
;; 		  (cdr eff)))
;; 	((eq (car eff) 'when)
;; 	 (let ((scond (simplify-formula
;; 		       (second eff) static-pred static-fun facts)))
;; 	   (cond ((null scond) nil)
;; 		 ((eq scond t)
;; 		  (cond ((eq (car (third eff)) 'and) (cdr (third eff)))
;; 			(t (list (third eff)))))
;; 		 (t (mapcar #'(lambda (disjunct)
;; 				(list 'when disjunct (third eff)))
;; 			    (transform-to-dnf scond nil)))
;; 		 )))
;; 	(t (list eff))
;; 	))

;; Simplify an effect formula: this includes rewriting conditions to DNF
;; and splitting them up into one condeff for each case, and simplifying
;; all static terms.
;; The function assumes that any quantifiers have already been removed.
;; Returns: A list of simplified effects. The list is conjunctive, but
;; will not have the 'and keyword at the start.
;; The returned list will contain NIL if some effect involves an undefined
;; static function term.

(defun simplify-effect (eff static-pred static-fun facts)
  (cond
   ((null eff) nil)
   ((eq (car eff) 'forall)
    (error "quantified formula in simplify-effect: ~a" eff))
   ((eq (car eff) 'and)
    (mapflat #'(lambda (e1)
		 (simplify-effect e1 static-pred static-fun facts))
	     (cdr eff)))
   ((eq (car eff) 'when)
    (when (not (= (length eff) 3))
      (error "ill-formed effect formula: ~s~%" eff))
    (let ((scond (simplify-formula (second eff) static-pred static-fun facts))
	  (seff (simplify-effect (third eff) static-pred static-fun facts)))
      (cond
       ((some #'null seff) (list nil))
       ((null scond) nil)
       ((eq scond t) seff)
       (t (mapcar #'(lambda (disjunct)
		      (list 'when disjunct
			    (if (> (length seff) 1) (cons 'and seff)
			      (car seff))))
		  (transform-to-dnf scond nil)))
       )))
   (t (let ((seff (simplify-atomic-effect eff static-fun facts)))
	(cond ((null seff) (list nil))
	      (t (list seff)))))
   ))

;; Simplify an atomic effect formula (literal). This involves only
;; simplifying static function terms.
;; Returns: The simplified effect, or NIL if the effect involves an
;; undefined static function term.

(defun simplify-atomic-effect (eff static-fun facts)
  (cond ((member (car eff) '(assign increase decrease))
	 (when (not (= (length eff) 3))
	   (error "ill-formed effect formula: ~s~%" eff))
	 (let ((args (mapcar #'(lambda (t1)
				 (simplify-term t1 static-fun facts))
			     (cdr (second eff))))
	       (val (simplify-term (third eff) static-fun facts)))
	   (cond
	    ((or (null val) (some #'null args)) nil)
	    (t (list (car eff) (cons (car (second eff)) args) val)))))
	((eq (car eff) 'not)
	 (when (not (= (length eff) 2))
	   (error "ill-formed effect formula: ~s~%" eff))
	 (list 'not (simplify-atomic-effect (second eff) static-fun facts)))
	(t
	 (let ((args (mapcar #'(lambda (t1)
				 (simplify-term t1 static-fun facts))
			     (cdr eff))))
	   (cond
	    ((some #'null args) nil)
	    (t (cons (car eff) args)))))
	))


;; Find free variables in a formula whose instantiation would allow
;; removal of disjunctions.

(defun find-formula-simplifiers (form static-pred static-fun)
  (cond ((null form) nil)
	((or (eq (car form) 'forall) (eq (car form) 'exists))
	 (error "find-formula-simplifiers: quantifiers must be removed"))
	((eq (car form) 'or)
	 (let ((vars nil)
	       (count 0))
	   (dolist (f1 (cdr form))
	     (cond ((is-static-formula f1 static-pred static-fun)
		    (setq vars (union (free-variables f1) vars))
		    (setq count (+ count 1)))))
	   (cond ((>= count (- (length (cdr form)) 1)) vars)
		 (t nil))))
	((eq (car form) 'when)
	 (find-formula-simplifiers (second form) static-pred static-fun))
	((eq (car form) 'imply)
	 (cond ((is-static-formula (second form) static-pred static-fun)
		(free-variables (second form)))
	       (t nil)))
	((eq (car form) 'and)
	 (reduce #'union
		 (mapcar #'(lambda (f1)
			     (find-formula-simplifiers
			      f1 static-pred static-fun))
			 (cdr form))))
	((eq (car form) 'not)
	 (find-formula-simplifiers (second form) static-pred static-fun))
	(t nil)))

(defun is-static-formula (form static-pred static-fun)
  (cond ((null form) t)
	((or (eq (car form) 'and) (eq (car form) 'or) (eq (car form) 'imply))
	 (every #'(lambda (f) (is-static-formula f static-pred static-fun))
		(cdr form)))
	((or (eq (car form) 'forall) (eq (car form) 'exists))
	 (is-static-formula (third form) static-pred static-fun))
	((eq (car form) 'not)
	 (is-static-formula (second form) static-pred static-fun))
	((eq (car form) '=)
	 (and (is-static-term (second form) static-fun)
	      (is-static-term (third form) static-fun)))
	((member (car form) static-pred)
	 (every #'(lambda (term) (is-static-term term static-fun))
		(cdr form)))
	(t nil)))

(defun is-static-term (term static-fun)
  (cond ((symbolp term) t)
	((member (car term) static-fun)
	 (every #'(lambda (t1) (is-static-term t1 static-fun))
		(cdr term)))
	(t nil)))

;; Find the set of static predicates.
;; These are predicates that appear in action effects, or are
;; defined by axioms that depend on some non-static predicate.

(defun collect-static-predicates
  (predicates actions axioms &key (include-static-derived nil))
  (let ((epred (collect-effect-predicates actions))
	(efuns (collect-effect-functions actions)))
    (set-difference
     (mapcar #'car predicates)
     (if include-static-derived
	 (collect-non-static-derived epred efuns axioms)
       (union epred (collect-derived-predicates axioms)))
     )))

(defun collect-non-static-derived (epred efuns axioms)
  (let ((new-epred nil)
	(rem-axioms nil))
    (dolist (axiom axioms)
      (cond ((non-static-formula (third axiom) epred efuns)
	     (setq new-epred (union new-epred (list (car (second axiom))))))
	    ((not (axiom-predicate-in-list axiom new-epred))
	     (push axiom rem-axioms))
	    ))
    (if (null new-epred) epred
      (collect-non-static-derived (union epred new-epred) efuns rem-axioms))))

(defun axiom-predicate-in-list (axiom predlist)
  (find (first (second axiom)) predlist))

;; this function cheats, by assuming that the names in preds can only
;; appear as predicates, i.e. first in a (sub-)list of the formula;
;; this assumption would be invalid if, for example, a name in preds is
;; also used as a function or connective.
(defun non-static-formula (form nspreds nsfuns)
  (cond ((null form) nil)
	((listp form)
	 (or (find (car form) nspreds)
	     (find (car form) nsfuns)
	     (some #'(lambda (f1) (non-static-formula f1 nspreds nsfuns))
		   (cdr form))))
	(t nil)))

;; Find the set of static (non-modified) functions.
;; ASSUMPTION: object functions cannot be derived.

(defun collect-static-functions (functions actions)
  (set-difference
   (mapcar #'caar functions) (collect-effect-functions actions)))

;; Collect the set of predicates occurring in preconditions and
;; effect conditions of a list of actions. (This function is
;; currently unused.)

(defun collect-condition-predicates (actions)
  (remove-duplicates
   (mapflat #'(lambda (act)
		(append (collect-predicates
			 (assoc-val ':precondition (cdr act)))
			(collect-effect-condition-predicates
			 (assoc-val ':effect (cdr act)))))
	    actions)))

;; Collect the set of predicates/functions occurring in the effect
;; of any action.

(defun collect-effect-predicates (actions)
  (remove-duplicates
   (mapflat #'(lambda (act)
		(collect-predicates (cdr (assoc ':effect (cdr act)))))
	    actions)))

(defun collect-effect-functions (actions)
  (remove-duplicates
   (mapflat #'(lambda (act)
		(collect-dynamic-functions
		 (assoc-val ':effect (cdr act))))
	    actions)))

;; Collect the set of predicates appearing in a formula.
;; Note: it is assumed that if the formula is an effect formula, then
;; we are interested in the predicates appearing as effects in the
;; formula. This means that in a formula of the form (when C E), only
;; predicates in E will be returned.

(defun collect-predicates (form)
  (cond ((null form) nil)
	((member (car form) '(increase decrease assign = < <= > >=)) nil)
	((or (eq (car form) 'and) (eq (car form) 'or) (eq (car form) 'imply))
	 (remove-duplicates
	  (mapflat #'collect-predicates (cdr form))))
	((or (eq (car form) 'forall) (eq (car form) 'exists))
	 (collect-predicates (third form)))
	((eq (car form) 'not)
	 (collect-predicates (second form)))
	((eq (car form) 'when)
	 (collect-predicates (third form)))
	(t (list (car form)))))


;; Collect the set of predicates appearing in effect conditions in
;; a formula. The argument is assumed to be an effect formula.

(defun collect-effect-condition-predicates (form)
  (cond ((null form) nil)
	((eq (car form) 'and)
	 (remove-duplicates
	  (mapflat #'collect-effect-condition-predicates (cdr form))))
	((eq (car form) 'forall)
	 (collect-effect-condition-predicates (third form)))
	((eq (car form) 'when)
	 (collect-predicates (second form)))
	(t nil)))

;; Collect the set of functions occurring in assign, increase or
;; decrease effects in a formula. The argument is assumed to be an
;; effect formula (or nil).

(defun collect-dynamic-functions (form)
  (cond ((null form) nil)
	((member (car form) '(assign increase decrease))
	 (list (car (second form))))
	((eq (car form) 'and)
	 (remove-duplicates
	  (mapflat #'collect-dynamic-functions (cdr form))))
	((eq (car form) 'forall)
	 (collect-dynamic-functions (third form)))
	((eq (car form) 'when)
	 (collect-dynamic-functions (third form)))
	(t nil)))


;; Detype a domain and problem. Input is taken from the global variables
;; holding current domain/problem, and returns an detyped domain and
;; problem definition. Arguments:
;;  requirements: list of requirements for new domain definition.
;;  :with-types ('force, 'strip or nil) is passed to make-domain/problem.

(defun detype (requirements &key (with-types nil))
  (let ((type-decl *types*)
	(type-pred (mapcar #'(lambda (td)
			       (cons (car td) (symnumcat 'type- (car td))))
			   *types*)))
    (values
     (make-domain-definition
      *domain-name*
      requirements
      nil ;; types
      *objects* ;; objects are only used here to find constant types
      nil ;; constants
      ;; predicates:
      (append (mapcar #'(lambda (pd)
			  (cons (car pd) (detype-typed-list (cdr pd))))
		      *predicates*)
	      (mapcar #'(lambda (tp) (list (cdr tp) (cons '?obj 'object)))
		      type-pred))
      ;; functions
      (mapcar #'(lambda (fd)
		  (cons (cons (caar fd) (detype-typed-list (cdar fd)))
			(if (eq (cdr fd) 'number) 'number 'object)))
	      *functions*)
      ;; axioms
      (mapcar #'(lambda (ax) (detype-axiom ax type-pred)) *axioms*)
      ;; actions
      (mapcar #'(lambda (act) (detype-action act type-pred)) *actions*)
      :with-types with-types)
     (make-problem-definition
      *problem-name*
      *domain-name*
      (detype-typed-list *objects*) ;; objects
      ;; init:
      (let ((new-init *init*))
	(dolist (od *objects*)
	  (dolist (ost (assoc-rec (cdr od) nil *types*) (cdr od))
	    (when (not (eq ost 'object))
	      (let ((ost-decl (assoc ost type-pred)))
		(when (null ost-decl)
		  (error "object ~a has undeclared supertype ~a" od ost))
		(push (list (cdr ost-decl) (car od)) new-init)))
	    ))
	new-init)
      ;; goal
      (detype-formula *goal* type-pred)
      *metric-type*
      *metric*
      :with-types with-types)
     )))

(defun detype-typed-list (typed-list)
  (mapcar #'(lambda (el)
	      (if (eq (cdr el) 'number) el (cons (car el) 'object)))
	  typed-list))

(defun detype-axiom (axiom tps)
  (let ((params (parse-typed-list nil (cdadr axiom) 'object)))
    (list ':derived
	  (cons (caadr axiom) (detype-typed-list params))
	  (merge-conjunctions
	   (types-to-formula params tps)
	   (detype-formula (caddr axiom) tps)))))

(defun detype-action (act tps)
  (let ((params (assoc-val ':parameters (cdr act)))
	(prec (assoc-val ':precondition (cdr act)))
	(eff (assoc-val ':effect (cdr act))))
    (cons (car act)
	  (reassoc ':parameters
		   (detype-typed-list params)
		   (reassoc ':precondition
			    (merge-conjunctions
			     (types-to-formula params tps)
			     (detype-formula prec tps))
			    (reassoc ':effect
				     (detype-effect-formula eff nil tps)
				     (cdr act)))))))

(defun detype-formula (form tps)
  (cond ((eq (car form) 'forall)
	 (when (not (= (length form) 3))
	   (error "ill-formed formula: ~s" form))
	 (let ((params (parse-typed-list nil (cadr form) 'object)))
	   (list (car form)
		 (detype-typed-list params)
		 (list 'imply
		       (types-to-formula params tps)
		       (detype-formula (caddr form) tps)))))
	((eq (car form) 'exists)
	 (when (not (= (length form) 3))
	   (error "ill-formed formula: ~s" form))
	 (let ((params (parse-typed-list nil (cadr form) 'object)))
	   (list (car form)
		 (detype-typed-list params)
		 (merge-conjunctions
		  (types-to-formula params tps)
		  (detype-formula (caddr form) tps)))))
	((member (car form) '(and or not imply))
	 (cons (car form)
	       (mapcar #'(lambda (f1) (detype-formula f1 tps))
		       (cdr form))))
	(t form)))

(defun detype-effect-formula (form carry tps)
  (cond ((eq (car form) 'and)
	 (cons 'and
	       (mapcar #'(lambda (f1) (detype-effect-formula f1 carry tps))
		       (cdr form))))
	((eq (car form) 'forall)
	 (when (not (= (length form) 3))
	   (error "ill-formed formula: ~s" form))
	 (let ((params (parse-typed-list nil (cadr form) 'object)))
	   (list (car form)
		 (detype-typed-list params)
		 (detype-effect-formula
		  (caddr form) (types-to-formula params tps) tps))))
	((eq (car form) 'when)
	 (when (not (= (length form) 3))
	   (error "ill-formed formula: ~s" form))
	 (list 'when
	       (merge-conjunctions
		carry
		(detype-formula (cadr form) tps))
	       (caddr form)))
	(carry (list 'when carry form))
	(t form)))

(defun types-to-formula (typed-list tps)
  (let ((res nil))
    (dolist (el typed-list)
      (when (not (eq (cdr el) 'object))
	(let ((type-decl (assoc (cdr el) tps)))
	  (when (null type-decl)
	    (error "element ~a has undeclared type" el))
	  (push (list (cdr type-decl) (car el)) res))))
    (cond ((> (length res) 1) (cons 'and res))
	  ((= (length res) 1) (car res))
	  (t res))))
