
;; What is RSK?
;;
;; RSK ("Reverse SKolemisation") compiles away PDDL3.1 object fluents.
;;
;; The fundamental operation in this compilation is to replace functions
;; (object fluents) with existentially quantified variables, which is
;; essentially Skolemisation in reverse. I'm sure there are other names
;; for this operation.
;;
;; RSK can peform the rewrite to a greater or lesser degree. This is
;; controlled by the :target keyword parameter:
;;
;; The default (:target nil) is to only "flattens" fluent terms, i.e.,
;; to remove nested complex terms.
;;
;; With :target 'sas, in addition, equalities and assignments are
;; rewritten so that the right-hand-side is always an atomic term.
;; This means that the result after grounding will contain only
;; conditions/effects of the form "variable=value". (Though note that
;; RSK does not implement grounding.)
;;
;; With :target 'strips, object fluents are completely replaced by
;; predicates.

;; How do I run RSK?
;;
;; As with INVAL, RSK can be compiled to a stand-alone executable (with
;; a suitable LISP compiler), run as a script (with a suitable LISP
;; interpreter), or used interactively.
;;
;; rsk-main.lsp contains a main procedure for running it compiled or
;; as a script. If you have ECL, running the script compile-with-ecl
;; should produce an executable, named "rsk". Run it without arguments
;; for some help.
;;
;; Note: There seems to be a bug in ECLs formatted printing. Sometimes
;; the output comes out slightly mangled (particularly at the start of
;; a line).
;;
;; To run interactively, the steps are:
;;
;; 1. Load inval.lsp and rsk.lsp;
;;
;; 2. Call
;;
;;  (load-files "my-domain.pddl" "my-problem.pddl")
;;
;; to load a domain/problem definition.
;;
;; 3. Call
;;
;;  (rsk-domain *domain-name* REQS *objects* *types* *predicates*
;;              *functions* *axioms* *actions* [:target TARGET])
;;
;; where REQS is a list of the keywords you want to appear in the
;; :requirements section of the domain (there is no smart code to figure
;; this out automatically) and TARGET is the formalism you want to
;; compile to ('sas or 'strips; to flatten only, the keyword parameter
;; can be left out). The function returns two values: the first is the
;; compiled domain, and the second is a list of constants that have been
;; declared in the domain. Only objects that appear in (compiled) actions
;; or axioms are declared as domain constants; this is necessary for the
;; compiled domain to pass VAL's syntax check. To disable the use of
;; domain constants (some planners are allergic to them), add the keyword
;; argument ":declare-constants nil". Note that the special constant
;; "undefined", defined as part of the PDDL3.1 syntax, should not appear
;; in the result of compiling to strips (if it does, it is probably
;; because it was used in an invalid way in the input domain).
;; An additional keyword parameter, :static-fun, can be used to provide
;; a list of names of functions that will not be rsk'd. The purpose of
;; this is to easy subsequent grounding by reducing the number of action
;; parameters and quantifiers; if the intent is to ground the transformed
;; domain, static function terms can be simplified to a constant after
;; parameters have been instantiated.
;;
;; 4. Call
;;
;;  (rsk-problem *problem-name* *domain-name* *objects* *types*
;;               *functions* *init* *goal* *metric-type* *metric*
;;               LIST-OF-CONSTS [:target TARGET])
;;
;; where LIST-OF-CONSTS is the list of names of constants already declared
;; in the domain (i.e., the second value returned by rsk-domain); this is
;; needed to avoid declaring them twice. The function returns the compiled
;; problem.

;;;;
;; Top-level functions (see above for details).

(defun rsk-domain
  (dname requirements objects types predicates functions axioms actions
	 &key (target nil) (declare-constants t) (static-fun nil))
  (let ((new-actions
	 (mapcar #'(lambda (act)
		     (cons (car act)
			   (rsk-action (cdr act) functions
				       :target target :static-fun static-fun)))
		 actions))
	(new-axioms
	 (mapcar #'(lambda (ax)
		     (rsk-axiom ax functions types
				:target target :static-fun static-fun))
		 axioms))
	(new-predicates
	 (cond ((eq target 'strips)
		(append predicates
			(make-rsk-predicates
			 (remove-if #'(lambda (fun)
					(member (caar fun) static-fun))
				    functions))))
	       (t predicates)))
	(new-functions
	 (cond ((eq target 'strips)
		(remove-if-not #'(lambda (fun)
				   (or (eq (cdr fun) 'number)
				       (member (caar fun) static-fun)))
			       functions))
	       (t functions)))
	(constants nil))
    (when declare-constants
      (dolist (act new-actions)
	(dolist (cname (constants-in-expression
			(cdr (assoc ':precondition (cdr act)))))
	  (pushnew cname constants))
	(dolist (cname (constants-in-expression
			(cdr (assoc ':effect (cdr act)))))
	  (pushnew cname constants)))
      (setq constants (remove 'undefined constants)))
    (values
     (make-domain-definition dname requirements types objects constants
			     new-predicates new-functions new-axioms
			     new-actions)
     constants)))

(defun rsk-problem
  (pname dname objects types functions init goal metric-type metric
	 declared-constants &key (target nil) (static-fun nil))
  (let ((new-init
	 (rsk-atom-list init functions :target target :static-fun static-fun))
	(new-goal
	 (rsk-closed-formula goal nil functions
			     :target target :static-fun static-fun))
	(new-metric
	 (cond (metric
		(let ((r1 (rsk-term metric nil functions
				    :static-fun static-fun)))
		  (cond ((null (second r1)) (first r1))
			(t (error "metric ~s cannot be rewritten" metric)))))
	       (t nil))))
    (make-problem-definition
     pname dname (remove-if #'(lambda (odef)
				(member (car odef) declared-constants))
			    objects)
     new-init new-goal metric-type new-metric)
    ))


;; Format elements of a domain into a valid PDDL domain definition.
;; Arguments:
;;  name: domain name (symbol).
;;  reqs: list of requirement keywords to appear in domain.
;;  types: typed list of types (internal format, as in *types*)
;;  objects: typed list of all declared objects; this is only used
;;           to identify the types of domain constants.
;;  constants: list of object names to be declared as :constants in
;;              domain.
;;  predicates: predicate list (internal format, as in *predicates*)
;;  functions: function list (internal format, as in *functions*)
;;  axioms: domain axioms (internal format, as in *axioms*)
;;  actions: domain actions (internal format, as in *actions*)
;;  keyword :with-types
;;    if eq 'force, type annotations are always included;
;;    if eq 'strip, all type annotations are removed
;;     (THIS OPTION IS NOT FULLY IMPLEMENTED).
;;    otherwise, types are kept except for function return types
;;    which are removed if eq 'number for all functions.
;; Returns: The domain definition.

(defun make-domain-definition
  (name reqs types objects constants predicates functions axioms actions
	&key (with-types nil))
  (append
   (list 'define (list 'domain name))
   (cond (reqs (list (cons ':requirements reqs)))
	 (t nil))
   (cond ((and types (not (eq with-types 'strip)))
	  (list (cons ':types (make-typed-list types with-types))))
	 (t nil))
   (cond (constants
	  (list (cons ':constants
		      (make-typed-list
		       (mapcar #'(lambda (cname)
				   (let ((cdef (assoc cname objects)))
				     (cond (cdef cdef)
					   (t (cons cname 'object)))))
			       constants)
		       with-types))))
	 (t nil))
   (list 
    (cons ':predicates
	  (mapcar #'(lambda (pred)
		      (cons (car pred)
			    (make-typed-list (cdr pred) with-types)))
		  predicates)))
   (cond ((null functions) nil)
	 ;; if we have only numeric functions, and :with-types is not 'force,
	 ;; we'll output them without return type (to conform with the
	 ;; PDDL2 standard).
	 ((and (not (eq with-types 'force))
	       (every #'(lambda (fun) (eq (cdr fun) 'number)) functions))
	  (list
	   (cons ':functions
		 (mapcar #'(lambda (fun)
			     (cons (caar fun)
				   (make-typed-list (cdar fun) with-types)))
			 functions))))
	 (t (list
	     (cons ':functions
		   (make-typed-list
		    (mapcar #'(lambda (fun)
				(cons (cons (caar fun)
					    (make-typed-list (cdar fun) with-types))
				      (cdr fun)))
			    functions)
		    with-types)))))
   axioms
   (mapcar #'(lambda (act)
	       (make-action-definition act :with-types with-types))
	   actions)
   ))

;; Make a PDDL action definition out of an action struct (internal
;; representation). This version formats :parameters, :precondition
;; and :effect in order, followed by any other fields.
(defun make-action-definition (action &key (with-types nil))
  (append
   (list ':action (car action)
	 ':parameters (make-typed-list
		       (assoc-val ':parameters (cdr action)) with-types))
   (if (assoc-val ':precondition (cdr action))
       (list ':precondition (assoc-val ':precondition (cdr action)))
     nil)
   (if (assoc-val ':effect (cdr action))
       (list ':effect (assoc-val ':effect (cdr action)))
     nil)
   (mapflat #'(lambda (elem)
		(if (member (car elem) '(:parameters :precondition :effect))
		    nil
		  (list (car elem) (cdr elem))))
	    (cdr action))
   ))

;; Format elements of a problem into a valid PDDL problem definition.
;; Arguments:
;;  name: problem name (symbol).
;;  domain-name: domain name (symbol).
;;  objects: typed list of objects.
;;  init: initial state (list of ground facts/fluent equalities).
;;  goal: goal formula.
;;  metric-type: metric type keyword ('minimize, 'maximize); can be
;;   nil if metric-exp is nil.
;;  metric-exp: metric expression.
;;  keyword :with-types as above.
;; Returns: The domain definition.

(defun make-problem-definition
  (name domain-name objects init goal metric-type metric-exp
	&key (with-types nil))
  (append
   (list 'define (list 'problem name)
	 (list ':domain domain-name)
	 (cons ':objects (make-typed-list objects with-types))
	 (cons ':init init)
	 (list ':goal goal))
   (cond (metric-exp
	  (list (list ':metric metric-type metric-exp)))
	 (t nil))
   ))

(defun make-typed-list (typed-list with-types)
  (cond ((eq with-types 'strip)
	 (mapcar #'car typed-list))
	(t (unparse-typed-list typed-list))
	))

;; Modify LISP's pretty-printer so that NIL is written as "()" for
;; PDDL output. For this to work, format must be called with pretty
;; printing enabled, i.e., *print-pretty* set to true.
(defun make-format-PDDL-friendly ()
  (set-pprint-dispatch 'null #'(lambda (strm obj) (format strm "()"))))

(defun make-format-default ()
  (setq *print-pprint-dispatch* (copy-pprint-dispatch nil)))

;; Write PDDL expressions to a file.
;; file-name is the name of file written to, remaining arguments are
;; expressions to be printed. The main purpose of this function is to
;; ensure empty lists are written as "()", not "nil".
(defun write-PDDL (file-name &rest exps)
  (with-open-file
   (stream file-name :direction :output)
   (make-format-PDDL-friendly)
   (let ((*print-pretty* t))
     (dolist (exp exps)
       (format stream "~&~w~%" exp)))
   (make-format-default))
  nil)
  

;; Perform RSK on the current domain and problem definition, and replace
;; it with the result. Note: This will discard all currently loaded plans.

(defun rsk-internal (&key (target nil) (static-fun nil))
  (multiple-value-bind (domain new-constants)
      (rsk-domain *domain-name* nil *objects* *types* *predicates*
		  *functions* *axioms* *actions*
		  :target target :static-fun static-fun)
    (let ((problem
	   (rsk-problem *problem-name* *domain-name* *objects* *types*
			*functions* *init* *goal* *metric-type* *metric*
			new-constants
			:target target :static-fun static-fun)))
      (clear-definitions)
      (parse-file "domain" (list domain))
      (parse-file "problem" (list problem))
      )))

;;;;
;; Core RSK functions.

;; Reverse Skolemise a formula.
;; The rewritten formula will have no complex terms as arguments to
;; predicates, with the possible exception of equality (depending on
;; the value of the :target parameter).
;; form - the formula.
;; terms - a list of already identified rsk terms; this is an assoc
;;   list of (term . var) pairs, where term is a flat function term
;;   and var the corresponding rsk variable.
;; functions - the list of domain functions (parsed).
;; returns: a list (new-form new-terms facts), where
;;  new-form is the rewritten formula, and
;;  new-terms is a list of new rsk terms.
;;  facts is a list of pairs (fterm . aterm), where fterm is a flat
;;  function term and aterm is an atomic term (constant or non-rsk
;;  variable, such that the formula implies (= (fterm) aterm). The
;;  list of facts is not complete, because the test for impliciation
;;  used is only that the fact appears (un-negated) in a top-level
;;  conjunction.

(defun rsk-formula (form terms functions &key (target nil) (static-fun nil))
  (cond
   ((null form) (list nil nil))
   ;; logical connectives (note: treats all connectives as n-ary)
   ((member (car form) '(and or not imply))
    (let ((new-terms nil)
	  (new-facts nil))
      (list
       (cons (car form)
	     (mapcar
	      #'(lambda (f1)
		  (let ((r1 (rsk-formula
			     f1 (append terms new-terms) functions
			     :target target :static-fun static-fun)))
		    (setq new-terms (append new-terms (second r1)))
		    (setq new-facts (append new-facts (third r1)))
		    (first r1)))
	      (cdr form)))
       new-terms
       new-facts)))
   ;; quantifiers
   ((member (car form) '(forall exists))
    (if (not (= (length form) 3))
	(error "ill-formed formula: ~s" form))
    (let* ((qvars (mapcar #'car (parse-typed-list nil (second form) 'objects)))
	   ;; independent terms are the terms not mentioning any variable
	   ;; shadowed by the quantifier; these are the terms only that can
	   ;; be reused inside the body of the quantified formula
	   (iterms (remove-if #'(lambda (term)
				  (some #'(lambda (arg) (member arg qvars))
					(cdar term)))
			      terms))
	   (r1 (rsk-formula (third form) iterms functions
			    :target target :static-fun static-fun))
	   ;; dependent terms are the terms found inside the body of the
	   ;; quantified formula that mention a quantified variable
	   (dterms (remove-if-not
		    #'(lambda (term)
			(some #'(lambda (arg) (member arg qvars))
			      (cdar term)))
		    (second r1)))
	   ;; new terms are the independent terms returned from the
	   ;; body of the quantifier
	   (nterms (remove-if
		    #'(lambda (term)
			(some #'(lambda (arg)
				  (member arg qvars)) (cdar term)))
		    (second r1))))
      ;; dependent terms have to be quantified inside the scope of this
      ;; quantifier; return the new independent terms
      (list (cond
	     ;; if the quantifier is existential, the new quantified
	     ;; variables bound by dependent terms can be merged into
	     ;; the quantifier
	     ((and dterms (eq (car form) 'exists))
	      (list (first form)
		    (append (type-complete (second form))
			    (make-rsk-parameters dterms functions))
		    (merge-conjunctions
		     (third form) (merge-conjunctions
				   (make-rsk-condition dterms :target target)
				   (first r1)))))
	     ;; otherwise, we have to place an existential quantifier
	     ;; inside the original quantifier
	     (dterms
	      (list (first form) (second form)
		    (list 'exists (make-rsk-parameters dterms functions)
			  (merge-conjunctions
			   (cons 'and (make-rsk-condition
				       dterms :target target))
			   (first r1)))))
	     ;; if we have no dependent terms, just return the original
	     ;; quantifier with the rewritten inner formula
	     (t (list (first form) (second form) (first r1))))
	    nterms ;; new terms
	    nil) ;; quantified formula returns no facts
      ))
   ;; equality
   ((eq (car form) '=)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (cond
     ;; both arguments are atomic: nothing to do
     ((and (not (listp (second form))) (not (listp (third form))))
      (list form nil nil))
     ;; second argument is atomic, first is not:
     ((not (listp (third form)))
      (let ((r1 (rsk-term-list (cdr (second form)) terms functions
			       :static-fun static-fun)))
	(list
	 (cond
	  ;; if target == strips, convert the equality to a predicate
	  ((eq target 'strips)
	   (cons (car (second form)) (append (first r1) (list (third form)))))
	  (t (list '= (cons (car (second form)) (first r1)) (third form))))
	 (second r1) ;; new terms
	 ;; return (rskd-first-arg . second-arg) as a fact
	 (list (cons (cons (car (second form)) (first r1)) (third form)))
	 )))
     ;; first argument is atomic, second is not:
     ((not (listp (second form)))
      (let ((r1 (rsk-term-list (cdr (third form)) terms functions
			       :static-fun static-fun)))
	(list
	 (cond
	  ;; if target == strips, convert the equality to a predicate
	  ((eq target 'strips)
	   (cons (car (third form)) (append (first r1) (list (second form)))))
	  (t (list '= (cons (car (third form)) (first r1)) (second form))))
	 (second r1) ;; new terms
	 ;; return (rskd-second-arg . first-arg) as a fact
	 (list (cons (cons (car (third form)) (first r1)) (second form)))
	 )))
     ;; otherwise, both arguments are complex:
     ;; if the target is sas or strips, we need to rsk one of the terms;
     ;; somewhat arbitrarily, we choose the second
     ((or (eq target 'sas) (eq target 'strips))
      (let* ((r1 (rsk-term-list (cdr (second form)) terms functions
				:static-fun static-fun))
	     (r2 (rsk-term (third form) (append terms (second r1)) functions
			   :static-fun static-fun)))
	(list
	 (cond
	  ((eq target 'strips)
	   (cons (car (second form)) (append (first r1) (list (first r2)))))
	  (t (list '= (cons (car (second form)) (first r1)) (first r2))))
	 (append (second r1) (second r2))
	 (list (cons (cons (car (third form)) (first r1)) (first r2)))
	 )))
     ;; if not, we need only to flatten out any nested terms
     (t (let* ((r1 (rsk-term-list (cdr (second form)) terms functions
				  :static-fun static-fun))
	       (r2 (rsk-term-list (cdr (third form))
				  (append terms (second r1)) functions
				  :static-fun static-fun)))
	  (list
	   (list '= (cons (car (second form)) (first r1))
		 (cons (car (third form)) (first r2)))
	   (append (second r1) (second r2))
	   nil ;; in this case, no new facts
	   )))
     ))
   ;; anything else, as far as we're concerned, is a predicate
   (t (let ((r1 (rsk-term-list (cdr form) terms functions
			       :static-fun static-fun)))
	(list (cons (car form) (first r1)) (second r1) nil)))
   ))

;; Reverse Skolemise a list of terms (args and return as above).

(defun rsk-term-list (tlist terms functions &key (static-fun nil))
  (let ((new-terms nil))
    (list
     (mapcar #'(lambda (term)
		 (let ((r1 (rsk-term term (append new-terms terms) functions
				     :static-fun static-fun)))
		   (setq new-terms (append new-terms (second r1)))
		   (first r1)))
	     tlist)
     new-terms)))

;; Reverse Skolemise a term (args and return as above).

(defun rsk-term (term terms functions &key (static-fun nil))
  (cond
   ;; a null term is an error
   ((null term) (error "null term!"))
   ;; if the term is a symbol (constant/variable) or number, return as is
   ((symbolp term) (list term nil))
   ((numberp term) (list term nil))
   ;; if the term matches one already found, return the corresponding
   ;; variable
   ((assoc term terms :test #'equal)
    (list (cdr (assoc term terms :test #'equal)) nil))
   ;; otherwise, it's a new function term; look up the function
   ;; to determine it's type: if it's a numeric function, or in the
   ;; list of static functions, it won't be rsk'd.
   (t (let ((fun (function-declaration (car term) functions))
	    (r1 (rsk-term-list (cdr term) terms functions
			       :static-fun static-fun)))
	(cond
	 ;; if it is a static function...
	 ((member (car term) static-fun)
	  (list (cons (car term) (first r1)) (second r1)))
	 ;; if it is a numeric function...
	 ((eq (cdr fun) 'number)
	  (list (cons (car term) (first r1)) (second r1)))
	 ;; does it correspond to a known rsk term?
	 ((assoc (cons (car term) (first r1)) terms :test #'equal)
	  (list
	   (cdr (assoc (cons (car term) (first r1)) terms :test #'equal))
	   nil))
	 ;; else, create a new rsk variable, bound to the term.
	 (t (let ((v (new-rsk-variable)))
	      (list v (cons (cons (cons (car term) (first r1)) v)
			    (second r1)))))
	 )))
   ))


;; Reverse Skolemise terms in an action effect formula.
;; effs - the formula.
;; terms - list of already identified rsk terms (as above).
;; facts - list of rsk term equalities known to hold in the context
;;  of the effect (i.e., implied by the action precondition or the
;;  effect condition, if inside a conditional effect); these are used
;;  to simplify the translation of object fluent assignment effects.
;; functions - the list of domain functions.
;; returns: a list (new-effs new-terms), where
;;  new-effs is a list of (rewritten) effect formulas, and
;;  new-terms is a list of new rsk terms.

(defun rsk-effects (effs terms facts functions
			 &key (target nil) (static-fun nil))
  (if (not (listp effs)) (error "ill-formed effect: ~s" effs))
  (let ((res nil)
	(new-terms nil))
    (dolist (e1 (if (eq (car effs) 'and) (cdr effs) (list effs)))
      (cond
       ((eq (car e1) 'forall)
	(if (not (= (length e1) 3))
	    (error "ill-formed quantified effect: ~s" e1))
	(let ((r1 (rsk-quantified-effects
		   (second e1) (third e1) (append terms new-terms)
		   facts functions :target target :static-fun static-fun)))
	  (setq res (append res (first r1)))
	  (setq new-terms (append new-terms (second r1)))))
       ((eq (car e1) 'when)
	(let ((r1 (rsk-conditional-effect
		   e1 (append terms new-terms) facts functions
		   :target target :static-fun static-fun)))
	  (setq res (append res (first r1)))
	  (setq new-terms (append new-terms (second r1)))))
       (t (let ((r1 (rsk-atomic-effect
		     e1 (append terms new-terms) facts functions
		     :target target :static-fun static-fun)))
	    (setq res (append res (first r1)))
	    (setq new-terms (append new-terms (second r1)))))
       ))
    (list res new-terms)))

(defun rsk-quantified-effects
  (qlist qeffs terms facts functions &key (target nil) (static-fun nil))
  (let ((qvars (mapcar #'car (parse-typed-list nil qlist 'object)))
	(res nil)
	(new-terms nil))
    (dolist (e1 (if (eq (car qeffs) 'and) (cdr qeffs) (list qeffs)))
      (let ((r1 (cond
		 ((eq (car e1) 'forall)
		  (error "nested quantified effect: ~s" qeffs))
		 ((eq (car e1) 'when)
		  (rsk-conditional-effect
		   e1 (append terms new-terms) facts functions
		   :target target :static-fun static-fun))
		 (t (rsk-atomic-effects
		     e1 (append terms new-terms) facts functions
		     :target target :static-fun static-fun)))))
	(let ((dterms (remove-if-not
		       #'(lambda (term)
			   (some #'(lambda (arg) (member arg qvars))
				 (cdar term)))
		       (second r1)))
	      (nterms (remove-if
		       #'(lambda (term)
			   (some #'(lambda (arg)
				     (member arg qvars)) (cdar term)))
		       (second r1))))
	  (let ((res1
		 (cond
		  (dterms
		   (let ((dtvars (make-rsk-parameters dterms functions))
			 (dtcond (make-rsk-condition dterms :target target)))
		     (mapcar
		      #'(lambda (qe1)
			  (cond
			   ((eq (car qe1) 'forall)
			    (cond
			     ((eq (car (third qe1)) 'when)
			      (list 'forall (append (type-complete qlist)
						    dtvars (second qe1))
				    (list 'when (merge-conjunctions
						 (second (third qe1)) dtcond)
					  (third (third qe1)))))
			     (t (list 'forall (append (type-complete qlist)
						      dtvars (second qe1))
				      (list 'when dtcond (third qe1))))))
			   ((eq (car qe1) 'when)
			    (list 'forall (append (type-complete qlist)
						  dtvars)
				  (list 'when (merge-conjunctions
					       (second qe1) dtcond)
					(third qe1))))
			   (t (list 'forall (append (type-complete qlist)
						    dtvars)
				    (list 'when dtcond qe1)))))
		      (first r1))))
		  (t (mapcar
		      #'(lambda (qe1)
			  (cond
			   ((eq (car qe1) 'forall)
			    (list 'forall (append qlist (second qe1))
				  (third qe1)))
			   (t (list 'forall qlist qe1))))
		      (first r1))))))
	    (setq res (append res res1))
	    (setq new-terms (append new-terms nterms))
	    ))))
    (list res new-terms)))

(defun rsk-conditional-effect (ceff terms facts functions
				    &key (target nil) (static-fun nil))
  (if (not (= (length ceff) 3)) (error "ill-formed effect: ~s" ceff))
  (let* ((r1 (rsk-formula (second ceff) terms functions
			  :target target :static-fun static-fun))
	 (r2 (rsk-atomic-effects
	      (third ceff) (append terms (second r1))
	      ;; facts implied by the effect condition can be used in
	      ;; rewriting the effect:
	      (append facts (third r1)) functions
	      :target target :static-fun static-fun)))
    (list (mapcar
	   #'(lambda (ce1)
	       (cond
		((eq (car ce1) 'forall)
		 (cond
		  ((eq (car (third ce1)) 'when)
		   (list 'forall (second ce1)
			 (list 'when (merge-conjunctions
				      (first r1) (second (third ce1)))
			       (third (third ce1)))))
		  (t (list 'forall (second ce1)
			   (list 'when (first r1) (third ce1))))))
		(t (list 'when (first r1) ce1))))
	   (first r2))
	  (append (second r1) (second r2)))))

(defun rsk-atomic-effects (effs terms facts functions
				&key (target nil) (static-fun nil))
  (if (not (listp effs)) (error "ill-formed effect: ~s" effs))
  (let ((res nil)
	(new-terms nil))
    (dolist (e1 (if (eq (car effs) 'and) (cdr effs) (list effs)))
      (let ((r1 (rsk-atomic-effect
		 e1 (append terms new-terms) facts functions
		 :target target :static-fun static-fun)))
	(setq res (append res (first r1)))
	(setq new-terms (append new-terms (second r1)))
	))
    (list res new-terms)))

(defun rsk-atomic-effect (eff terms facts functions
			      &key (target nil) (static-fun nil))
  (cond
   ((eq (car eff) 'assign)
    (if (not (= (length eff) 3)) (error "ill-formed atomic effect: ~s" eff))
    (let* ((fname (car (second eff)))
	   (fun (function-declaration (car (second eff)) functions))
	   (r1 (rsk-term-list (cdr (second eff)) terms functions
			      :static-fun static-fun))
	   (r2 (cond
		((eq (third eff) 'undefined)
		 (list 'undefined nil))
		;; if the rhs is complex, and target == sas/strips, we
		;; need to rsk the whole term
		((and (listp (third eff))
		      (or (eq target 'sas) (eq target 'strips)))
		 (rsk-term (third eff) (append terms (second r1)) functions
			   :static-fun static-fun))
		;; otherwise, we need only to flatten its arguments
		((listp (third eff))
		 (let ((r3 (rsk-term-list (cdr (third eff))
					  (append terms (second r1))
					  functions
					  :static-fun static-fun)))
		   (list (cons (car (third eff)) (first r3)) (second r3))))
		;; if the rhs is atomic, no need to do anything
		(t (list (third eff) nil)))))
      (cond
       ;; if target == strips, and the function is non-numeric, we need
       ;; to do a more complex rewrite, replacing assignment by adds and
       ;; deletes
       ((and (eq target 'strips) (not (eq (cdr fun) 'number)))
	(let* ((pre-val
		  (find-fluent-term
		   (cons (car (second eff)) (first r1)) facts))
		 (pos-part
		  (cond
		   ((eq (first r2) 'undefined) nil)
		   (t (cons fname (append (first r1) (list (first r2)))))))
		 (neg-part
		  (cond
		   (pre-val
		    (list 'not (append (car pre-val) (list (cdr pre-val)))))
		   (pos-part
		    (list 'forall (list '?delval '- (cdr fun))
			  (list 'when (list 'not (list '= '?delval (first r2)))
				(list 'not (cons fname (append (first r1)
							       '(?delval)))))))
		   (t (list 'forall (list '?delval '- (cdr fun))
			    (list 'not (cons fname (append (first r1)
							   '(?delval)))))))))
	    (list (append (list neg-part)
			  (cond (pos-part (list pos-part)) (t nil)))
		  (append (second r1) (second r2)))))
       ;; otherwise, we just return an assignment
       (t (list
	   (list (list 'assign (cons fname (first r1)) (first r2)))
	   (append (second r1) (second r2))))
       )))
   ((member (car eff) '(increase decrease))
    (if (not (= (length eff) 3)) (error "ill-formed atomic effect: ~s" eff))
    (let* ((fname (car (second eff)))
	   (r1 (rsk-term-list (cdr (second eff)) terms functions
			      :static-fun static-fun))
	   (r2 (rsk-term (third eff) (append terms (second r1)) functions
			 :static-fun static-fun)))
      (list
       (list (list (car eff) (cons fname (first r1)) (first r2)))
       (append (second r1) (second r2)))))
   ((eq (car eff) 'not)
    (if (not (= (length eff) 2)) (error "ill-formed atomic effect: ~s" eff))
    (let ((pname (car (second eff)))
	  (r1 (rsk-term-list (cdr (second eff)) terms functions
			     :static-fun static-fun)))
      (list (list (list 'not (cons pname (first r1)))) (second r1))))
   (t (let ((pname (car eff))
	    (r1 (rsk-term-list (cdr eff) terms functions
			       :static-fun static-fun)))
	(list (list (cons pname (first r1))) (second r1))))
   ))


;; Reverse Skolemise a formula, returning a new formula with all new
;; rsk variables existentially quantified. (Note that this function
;; returns the new formula only, without the new-terms and new-facts
;; lists.)

(defun rsk-closed-formula (form terms functions
				&key (target nil) (static-fun nil))
  (let ((r1 (rsk-formula form terms functions
			 :target target :static-fun static-fun)))
    (cond
     ((second r1)
      (list 'exists (make-rsk-parameters (second r1) functions)
	    (merge-conjunctions
	     (make-rsk-condition (second r1) :target target) (first r1))))
     (t (first r1))
     )))

;; Reverse Skolemise an action definition.
;; actdef - the action definition, in parsed-struct form, without
;;  the leading action name.
;; functions - list of domain functions.
;; returns: the rewritten action definition.

(defun rsk-action (actdef functions &key (target nil) (static-fun nil))
  (setq *rsk-counter* 0)
  (let* ((params (cdr (assoc ':parameters actdef)))
	 (prec (rsk-formula
		(cdr (assoc ':precondition actdef)) nil functions
		:target target :static-fun static-fun))
	 (effs (cond
		;; if target == strips, rewrite of effect formula is done
		;; in two steps: the first is to sas form, and the second
		;; step rewrites the result of the first to strips form;
		;; this is so that rsk terms created in the first step can
		;; be used to simplify effects in the second.
		((eq target 'strips)
		 (let* ((effs1 (rsk-effects
				(cdr (assoc ':effect actdef))
				(second prec)
				(append (second prec) (third prec))
				functions
				:target 'sas :static-fun static-fun))
			(effs2 (rsk-effects
				(cond
				 ((> (length (first effs1)) 1)
				  (cons 'and (first effs1)))
				 (t (car (first effs1))))
				(append (second prec) (second effs1))
				(append (second prec) (third prec)
					(second effs1))
				functions
				:target 'strips :static-fun static-fun)))
		   (list
		    (first effs2)
		    (append (second effs1) (second effs2)))))
		(t (rsk-effects
		    (cdr (assoc ':effect actdef)) (second prec)
		    ;; all new rsk terms created when rewriting the
		    ;; precondition can be treated as facts when rewriting
		    ;; the effect, since they will be conjoined to the
		    ;; precondition of the rsk'd action:
		    (append (second prec) (third prec)) functions
		    :target target :static-fun static-fun)))))
    (reassoc ':parameters
	     (append params (make-parsed-rsk-parameters
			     (append (second prec) (second effs)) functions))
	     (reassoc ':precondition
		      (merge-conjunctions
		       (make-rsk-condition
			(append (second prec) (second effs))
			:target target)
		       (first prec))
		      (reassoc ':effect
			       (cond
				((> (length (first effs)) 1)
				 (cons 'and (first effs)))
				(t (car (first effs))))
			       actdef)))))

;; Reverse Skolemise an axiom.

(defun rsk-axiom (axiom functions types &key (target nil) (static-fun nil))
  (setq *rsk-counter* 0)
  (if (not (= (length axiom) 3)) (error "ill-formed axiom: ~s" axiom))
  (let ((r1 (rsk-formula (second axiom) nil functions
			 :target target :static-fun static-fun)))
    (list ':derived (first r1)
	  (merge-conjunctions
	   (make-rsk-condition (second r1) :target target)
	   (rsk-closed-formula (third axiom) (second r1) functions
			       :target target :static-fun static-fun)))
    ))


;; Reverse Skolemise a list of ground atoms (i.e., a state).

(defun rsk-atom-list (atoms functions &key (target nil) (static-fun nil))
  (mapcar #'(lambda (atom)
	      (cond
	       ((eq (car atom) '=)
		(if (not (= (length atom) 3))
		    (error "ill-formed (initial) atom: ~s" atom))
		(if (listp (third atom))
		    (error "ill-formed (initial) atom: ~s" atom))
		(let ((fun (function-declaration
			    (car (second atom)) functions)))
		  (cond ((null fun)
			 (error "undefined function: ~s" atom))
			((and (eq target 'strips)
			      (not (eq (cdr fun) 'number))
			      (not (member (car (second atom)) static-fun)))
			 (append (second atom) (list (third atom))))
			(t atom))))
	       (t atom)))
	  atoms))

;; Return a list of the new predicates created by compiling away
;; non-numeric functions.

(defun make-rsk-predicates (functions)
  (cond
   ((endp functions) nil)
   ((eq (cdr (car functions)) 'number)
    (make-rsk-predicates (cdr functions)))
   (t (cons (append (car (car functions))
		    (list (cons '?value (cdr (car functions)))))
	    (make-rsk-predicates (cdr functions))))))

;; Utility functions used in Reverse Skolemisation:

;; Take an unparsed list of variables/constants that may be fully typed,
;; partially typed, or not typed at all, and return the equivalent fully
;; typed list.

(defun type-complete (tlist)
  (unparse-typed-list (parse-typed-list nil tlist 'object)))

;; Find the declaration of function 'fname. Returns a pair (fun . type)
;; where fun is the functions declaration (name only, if it's a built-in
;; numeric function) and type the functions value type.

(defun function-declaration (fname functions)
  (let ((fun (cond ((assoc fname *builtin-numeric-functions*)
		    (cons fname 'number))
		   (t (assoc fname functions :key #'car)))))
    (if (null fun) (error "undefined function: ~s" fname))
    fun))

;; Search a list of rsk terms for one matching the given fluent.

(defun find-fluent-term (fterm terms)
  (assoc fterm terms :test #'equal))

;; Create a new rsk variable.

(defun new-rsk-variable ()
  (setq *rsk-counter* (+ *rsk-counter* 1))
  (symnumcat '?rsk *rsk-counter*))

(defvar *rsk-counter* 0)

;; Create a typed parameter list from an assoc list of rsk terms.

(defun make-rsk-parameters (terms functions)
  (mapflat #'(lambda (term)
	       (let ((fun (assoc (caar term) functions :key #'car)))
		 (if (null fun) (error "undefined function: ~s" term))
		 (list (cdr term) '- (cdr fun))))
	   terms))

;; Create a parsed-form parameter list (that is, a list of (var . type)
;; pairs) from an assoc list of rsk terms.

(defun make-parsed-rsk-parameters (terms functions)
  (mapcar #'(lambda (term)
	      (let ((fun (assoc (caar term) functions :key #'car)))
		(if (null fun) (error "undefined function: ~s" term))
		(cons (cdr term) (cdr fun))))
	  terms))

;; Create a (conjunctive) condition from an assoc list of rsk terms.

(defun make-rsk-condition (terms &key (target nil))
  (let ((clist (mapcar #'(lambda (term)
			   (cond ((eq target 'strips)
				  (append (car term) (list (cdr term))))
				 (t (list '= (car term) (cdr term)))))
		       terms)))
    (cond
     ((> (length clist) 1) (cons 'and clist))
     ((= (length clist) 1) (car clist))
     (t nil))))
