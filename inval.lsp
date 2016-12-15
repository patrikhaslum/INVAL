
;; What is INVAL?
;;
;; INVAL is the Independent PDDL Plan Validator.
;;
;; INVAL is a PDDL plan validator based on my understanding of the
;; PDDL semantics, as they are defined in:
;;
;; Fox & Long, "PDDL2.1: An Extension to PDDL for Expressing Temporal
;;  Planning Domains". Journal of AI Research, vol. 20, 2003.
;;
;; Thiebaux, Hoffman & Nebel, "In Defense of PDDL Axioms". Artificial
;;  Intelligence, vol. 168, 2005.
;;
;; http://ipc.informatik.uni-freiburg.de/PddlExtension.
;;
;; Gerevini, Haslum, Long, Saetti, Dimopoulos, "Deterministic planning
;;  in the 5th international planning competition: PDDL3 and experimental
;;  evaluation of the planners". Artificial Intelligence, vol. 173(5-6),
;;  pp. 619-668, 2009.
;;
;; http://zeus.ing.unibs.it/ipc-5/bnf.pdf (PDDL3 syntax).

;; So if INVAL and VAL disagree, which is right?
;;
;; One of them. Or they could both be wrong.
;;
;; If you find an example where VAL and INVAL disagee on the validity,
;; or metric value, of a plan, this may indicate that one of the two
;; validators is incorrect, or that there is an area where the PDDL
;; semantics are less than crystal clear.
;;
;; First, check that the domain and problem are absolutely, perfectly
;; correct PDDL, and that they are really within the subset of PDDL
;; that INVAL can handle (see list of known bugs and limitations below).
;; Also check that your settings of the configuration options match VALs.
;;
;; If the discrepancy persists in spite of all the above checks, please
;; inform the developers of both validators.


;; How do I run INVAL?
;;
;; There are three ways to run INVAL:
;;
;; 1. Interactively.
;;
;; Load this file into your favourite Common LISP interpreter, and do
;; the following:
;;
;; i) To load domain and problem definitions, do
;;
;; (load-files "my-domain.pddl" "my-problem.pddl")
;;
;; ii) To load and validate a plan, do
;;
;; (setq my-plan (parse-plan "my plan" (read-file "my-problem.soln")))
;; (validate-plan (car my-plan) (cdr my-plan) *init* *goal* *constraints*
;;                *metric* *actions* (stratify *axioms*) *types* *objects*)
;;
;; (the seventh argument can be replaced with nil if the domain doesn't
;; use derived predicates).
;;
;; 2. As a script.
;;
;; Some CL interpreters (e.g., GCL, ECL) have a feature that allows them
;; to be used as script executors (in the same way as, e.g., bash or
;; perl). To make this work, make sure the first line (#!/...) and the
;; load call in inval-main.lsp are uncommented (you may also need to
;; edit the paths, and select/write an appropriate version of the
;; get-commandline-args function, which differs between interpreters),
;; and make the file executable. It should then be runnable like any
;; other script:
;;
;; inval-main.lsp <domain file> <problem file> <plan file>+
;;
;; See GCL documentation (-f option) / ECL documentation (-shell option)
;; for more information.
;;
;; 3. Compiling a stand-alone executable.
;;
;; I've got this to work with ECL. If you have ECL, just running the
;; script compile-with-ecl should produce an executable, named "inval".
;; It is invoked with the same arguments as in script form.


;; What are the known bugs and limitations?
;;
;; * INVAL does not handle temporal planning problems or temporal plans.
;;  It does work with parallel plans (i.e., the kind that graphplan,
;;  satplan and the like generate). See configuration options below for
;;  settings that affect the handling of parallel plans.
;;
;; * INVAL does not (normally) check that the domain/problem is correct,
;;  either syntactically, wrt types, or in any other way. If your input
;;  is not 100% correct PDDL, all bets are off.
;;
;;  A type-checking mechanism is implemented, but not used by the main
;;  validation function. To invoke it, load files (as above) and do
;;
;;  (type-check)
;;
;;  It returns nil if any problem was detected, t otherwise. Syntactic
;;  errors may cause the function to exit with an error. The "main"
;;  function (in inval-main.lsp) will run the type-checker if given
;;  the commandline option "-c".
;;
;; * There are a number of syntactic restrictions on input (mainly due
;;  to the fact that the first level of parsing is done by the standard
;;  LISP reader):
;;
;; - The symbol 'end-of-file is used internally to indicate end-of-file,
;;  so if the domain/problem contains a constant with that name, expect
;;  errors.
;;
;; - Similarly, if the domain/problem contains a constant (or predicate,
;;  or function, or anyting) named 'colon' or 'nil', strangeness will
;;  result.
;;
;; * The scale-up and scale-down numeric effect operators are not
;;  implemented.
;;
;; * Last but not least, INVAL is not efficient. On problems with complex
;;  action preconditions and/or effects, and particularly problems with
;;  derived predicates (axioms), it can be very slow. Be patient.

;; TODO's
;; * Should type-check-axiom check for conflicting parameter type
;;   declarations?
;; * type checking formulas and terms should use list of built-in
;;   numeric predicates/functions.
;; * violations of anonymous preferences are not added to metric value.
;; * remove polymorphic-actions support and other dead code.
;; * make type check return list of implied requirements (and check it
;;   against declared requirements).
;; * make printing at higher *verbosity* levels (3+) more consistent
;;   across different parts.

;;;;
;; Configuration options
;;
;; The behaviour of INVAL can be changed (slightly) by setting the
;; following variables.

;;;
;; Semantic options.
;;
;; These options modify how INVAL interprets PDDL and/or defines
;; plan validity.

;; Should two concurrent actions one of which adds an atom appearing
;; in the precondition (or an effect condition) of the other be
;; considered a conflict?
;;
;; The PDDL 2.1 spec very clearly answers yes (Definition 12, p. 93,
;; Fox & Long 2003). However, this form of concurrency is rampant in
;; graphplan/satplan-style plans, so we provide an option for allowing
;; it: set *add-read-are-mutex* to t to enforce the strict definition
;; (as per the PDDL spec) and to nil to allow concurrent add/reads.
(defvar *add-read-are-mutex* nil)

;; Are the parameter types given in an action definition to be regarded
;; as part of the actions precondition? (i.e., if a plan contains an
;; action instance with a non-type-matching argument, will that cause a
;; plan execution failure?)
;;
;; Although it does not appear to be formally stated in any of the PDDL
;; specifications, I believe the common view is that the answer should
;; be yes. However, allowing the possibility to relax this requirement
;; may be useful in some cases (e.g., to validate plans against action
;; definitions that take non-object arguments). Note that even if
;; *action-parameter-types-are-preconditions* is set to nil, the number
;; of arguments to each action must still match the number of parameters
;; (unless the *ignore-excess-arguments* option is true, cf. below).
(defvar *action-parameter-types-are-preconditions* t)

;; Can a type name be used as a (static) unary predicate in formulas?
;;
;; The PDDL 1.0 spec clearly says yes (McDermott et al. 1998, page 6).
;; VAL, however, says no. According to Derek, that's intentional: this
;; feature was ruled out from PDDL 2.1 and on. Some domains (e.g.,
;; freecell) declare predicates with the same names as types, which
;; would shadow type names used as predicates. VAL accepts domains in
;; which the same symbol is used both as a type and predicate name,
;; but assumes no association between the two.
;; If this option is set to true (t), type names implicitly define
;; static unary predicates, and these shadow any explicitly defined
;; unary predicate of the same name. If it is false, type names cannot
;; be used as predicates. (This option applies both to plan validation
;; and to domain/problem type checking.)
(defvar *type-names-are-predicates* nil)

;; Can a objects and types have multiple (super-)type declarations?
;;
;; There seems to be no indication for or against in any PDDL spec,
;; but VAL's answer is apparently "yes".
(defvar *multityping* t)

;; Are "(either ...)" types in declarations (type or object) conjunctive?
;;
;; The PDDL 1.0 and 1.2 specs say that "(either t1 .. tk) is the union
;; of types t1 to tk." (McDermott et al. 1998, page 6; Bacchus 2000,
;; page 4), which seems to imply the answer is "no". But VAL's answer
;; appears to be "yes".
(defvar *either-in-declarations-means-and* t)

;;;
;; Implementation options.
;;
;; These options only modify how some parts of validation is performed
;; (typically switching between alternative implementations) and their
;; setting should not affect whether a plan is considered valid or not.

;; Level of detail to print during plan validation (number, 0..)
;;  0 = print nothing
;;  1 = error and warning messages, final plan status and value
;;  2 = next happening, preference violations
;;  3 = states between happenings, action effects, axiom stratification
;;  4, 5 = more (and more) details about axiom evaluation.
(defvar *verbosity* 1)

;; Two alternative procedures for axiom stratification are implemented;
;; which one is used depends on the value of the configuration variable
;; *stratify-axioms-maximally*.
;;
;; If *stratify-axioms-maximally* is false, it uses the function
;; stratify-minimally, which implements the algorithm by Thiebaux,
;; Hoffmann & Nebel (2005). It outputs a stratification that is
;; "minimal", in the sense that it separates axioms into different
;; strata only when its strictly necessary for correctness (i.e.,
;; axioms in the higher stratum depend negatively on predicates defined
;; by axioms in the lower stratum).
;;
;; If *stratify-axioms-maximally* is true, it uses the function
;; stratify-maximally, which, in contrast, outputs a stratification
;; that is "maximal", in the sense that it places axioms together in
;; the same statum only when that is strictly necessary (i.e., when
;; the axioms are positively mutually dependent). Stratifying maximally
;; should lead to faster axiom evaluation (sometimes), since that
;; computes a fixpoint over application of all axioms in each stratum.
(defvar *stratify-axioms-maximally* nil)

;; Use alternative ("fast") implementation to compute axiom fixpoint.
;;
;; The basic implementation of axiom fixpoint computation (function
;; apply-axioms) is very simple. The alternative implementation
;; (function apply-axioms-2) is (hopefully) faster, but it is also way
;; more complicated (and thus more likely to be buggy) and has some
;; limitations. Currently, it does not support for numeric fluents in
;; any use. It does support object fluents, but only in "SAS form",
;; i.e., fluents can appear only in atomic formulas of the form
;; (= (f arg ... arg) val), where all arguments and the value are
;; atomic.
(defvar *fast-axiom-fixpoint* nil)

;;;
;; Non-standard options.
;;
;; These options enable various extensions/modifications to PDDL
;; semantics and/or the validation process, some of which are not
;; within the PDDL specification. They exist because I use INVAL
;; as platform for experimental language modification, and sometimes
;; as a component in other algorithms.

;; Are multiple action definitions with the same name allowed? If
;; polymorphic actions are enabled, the validator will choose the
;; action definition to use for each action in the plan among those
;; whose parameters match the given arguments; if there is more than
;; one matching action, it will then choose the one with the most
;; specific parameter types. If this is not enough to resolve the
;; ambiguity (i.e., there are two or more matching action definitions
;; of incomparable specificity), the validator considers it a plan
;; execution error.
(defvar *polymorphic-actions* nil)

;; Should excess arguments to an action be ignored (t), or treated as
;; an error (nil)? (This is sometimes useful to validate plans generated
;; with a compiled domain against the original domain definition.)
(defvar *ignore-excess-arguments* nil)

;; Should undefined actions be ignored (t), or treated as an error (nil)?
;; Note: If action polymorphism is enabled, ambiguous actions are still
;; treated as an error even if this option is set to true.
(defvar *ignore-undefined-actions* nil)

;; List of built-in numeric functions and predicates.
;;
;; Each item in the list is a list (name min-args max-args fun). The
;; minimum and maximum argument limits will only be checked if they
;; are numeric (so that a non-numeric constant, e.g., nil, can be
;; used to indicate n-ary functions/predicates). The function or predicate
;; element (fun) will be funcall'd with a single argument, which is the
;; list of argument values, when an expression is evaluated.
(defvar *builtin-numeric-functions*
  (list (list '+ 2 nil #'(lambda (args) (reduce #'+ args)))
	(list '* 2 nil #'(lambda (args) (reduce #'* args)))
	(list '- 1 2 #'(lambda (args)
			 (if (= (length args) 1) (- (first args))
			   (- (first args) (second args)))))
	(list '/ 2 2 #'(lambda (args) (/ (first args) (second args))))
	(list ':min 2 nil #'(lambda (args) (reduce #'min args)))
	(list ':max 2 nil #'(lambda (args) (reduce #'max args)))
	))

(defvar *builtin-numeric-predicates*
  (list (list '< 2 2 #'(lambda (args) (< (first args) (second args))))
	(list '<= 2 2 #'(lambda (args) (<= (first args) (second args))))
	(list '> 2 2 #'(lambda (args) (> (first args) (second args))))
	(list '>= 2 2 #'(lambda (args) (>= (first args) (second args))))
	))

;; List of predicate names that will be treated specially: when they
;; appear (positively) in the effects of an action, their arguments
;; will not be evaluated.
(defvar *quoted-argument-predicates* nil)

;; List of predicate names that will be treated specially: When they
;; are added, they will be added even if already present in the current
;; state (i.e., there will be duplicates). When deleted, all copies are
;; deleted.
(defvar *duplicated-predicates* nil)


;;;;
;; Plan validation

;; Validate a plan:
;; plan-name - the plan name (for trace printing)
;; plan - list of happenings; each happening is a list of action
;;   instances
;; state - starting state: list of (true) ground atoms and ground
;;   fluent equalities (same format as :init section of a PDDL problem
;;   definition)
;; goal - the goal formula (only the formula, i.e., without :goal keyword)
;; constraints - a PDDL3 constraint formula (again, only the formula; it
;;   may be nil, which is interpreted as true)
;; metric - the metric expression (the expression only, i.e., without
;;   :metric and minimize/maximize); should be nil if there is no metric.
;;   the metric can also be a function: this function will be called with
;;   the final state to produce the "value" of the plan (which can be any
;;   kind of value, not only a number).
;; actions - list of domain action schemas
;;   this is an assoc list of (name . definition) pairs, where the
;;   action definition is also an assoc list of (keyword . expresion)
;;   pairs, for keywords :parameters, :precondition, :effect, etc.
;;   note: this function (and those it calls) expects that the action
;;   parameters list is parsed into the internal format (an assoc list
;;   of (name . type) pairs); however, the parameter lists of quantifiers
;;   (in formulas and effects) and axiom heads are expected to be
;;   *unparsed* (i.e., in the PDDL 'name - type' form).
;; stratified-axioms - stratified list of domain axioms; this is a list
;;   of strata, where each stratum is a list of axioms
;; types - list of domain types
;;   this is an assoc list of (type . supertype) pairs
;; objects - list of domain/problem objects
;;   this is an assoc list of (object . type) pairs; note that all
;;   objects must be typed (with type 'object' if nothing else)
;; :visualisation - if not nil, a function of two arguments; will be
;;   called with the plan and the state sequence produced by executing
;;   the plan; if the plan is successful, the length of the state
;;   sequence will be the length of the plan +1; if the plan fails to
;;   execute, the state sequence will include only states up to the
;;   happening that fails.
;; returns:
;;   a list (success value vresult), where success (t/nil) indicates the
;;   plan is valid (executable and achieves the goal), value is the
;;   metric value of the plan (nil if no metric specified), and vresult
;;   is the result of calling the visualisation function, or nil if no
;;   visualisation function was specified.

(defun validate-plan (plan-name plan state goal constraint metric actions
				stratified-axioms types objects
				&key (visualisation nil))
  (if (>= *verbosity* 1)
      (format t "~&validating plan ~s~%" plan-name))
  (let* ((rss ;; are we getting a state sequence?
	  (or visualisation constraint))
	 (result ;; result of executing the plan
	  (execute-plan plan state actions stratified-axioms types objects
			:return-state-sequence rss))
	 (vres ;; visualisation result
	  (if visualisation (funcall visualisation plan (cdr result)) nil))
	 (final-state ;; final state (nil if plan failed to execute)
	  (cond ((car result)
		 (if (>= *verbosity* 1)
		     (format t "~&plan executed successfully~%"))
		 (if rss (car (last (cdr result))) (cdr result)))))
	 (goal-val ;; result of evaluating the goal (nil if exec fail)
	  (cond ((car result)
		 (if (>= *verbosity* 3)
		     (format t "~&(extended) final state:~%~s~%" final-state))
		 (eval-formula goal nil final-state types objects
			       :accept-preferences t))))
	 (con-val ;; result of evaluating constraint formula
	  (cond ((car result)
		 (eval-constraint-formula constraint (cdr result) types
					  objects :accept-preferences t))))
	 ) ; end of let* list
    (cond
     ;; plan failed to execute
     ((not (car result))
      (format t "~&plan failed to execute")
      (list nil nil vres))
     ;; goal undefined
     ((not (cadr goal-val))
      (if (>= *verbosity* 1)
	  (format t "~&error: goal ~s is undefined~%" goal))
      (list nil nil vres))
     ;; goal defined but not true in final state
     ((not (car goal-val))
      (if (>= *verbosity* 1)
	  (format t "~&error: goal ~s is false~%" goal))
      (list nil nil vres))
     ;; constraints undefined
     ((not (cadr con-val))
      (if (>= *verbosity* 1)
	  (format t "~&error: constraint ~s is undefined~%" constraint))
      (list nil nil vres))
     ;; constraints not satisfied
     ((not (car con-val))
      (if (>= *verbosity* 1)
	  (format t "~&error: constraint ~s not satisfied~%" constraint))
      (list nil nil vres))
     ;; ok, the plan is valid:
     ;; if there is a metric, we extend the final state with built-in
     ;; fluents (is-violated, total-time), so that we can evaluate the
     ;; metric expression
     (metric
      (let* ((pnames
	      (collect-preference-names metric nil))
	     (combined-vios
	      (multiset-add (caddr con-val)
			    (multiset-add (cadddr goal-val)
					  (mapcar #'(lambda (n) (cons n 0))
						  pnames))))
	     (metric-state
	      ;; we assign the fluent (total-time) the length of the plan,
	      ;; so that the metric is defined it includes this term; of
	      ;; course, this is somewhat pointless, since we don't consider
	      ;; action durations; but it is in accordance with the PDDL
	      ;; semantics of non-temporal (but possibly parallel) plans.
	      (apply-assign-effects
	       (list (list 'assign '(total-time) (length plan)))
	       ;; if we have preference terms in the metric, we have to
	       ;; define them in the final state; they are set to zero,
	       ;; plus any violations from the goal or constraint formulas.
	       (if pnames
		   (update-preference-violations combined-vios final-state)
		 final-state)))
	     (metric-val
	      (if (functionp metric) (list (funcall metric final-state) nil)
		(eval-term metric nil metric-state))))
	(cond ;; print violation counts if *verbosity* >= 2
	 ((and (>= *verbosity* 2) pnames)
	  (format t "~&preference violations: ~%")
	  (dolist (atom metric-state)
	    (if (and (eq (car atom) '=)
		     (= (length (second atom)) 2)
		     (eq (car (second atom)) 'is-violated))
		(format t " ~a~%" atom)))))
	(cond
	 ;; if the metric is a term (PDDL expression), but did not eval to
	 ;; a number, this is validation error:
	 ((and (not (functionp metric)) (not (numberp (first metric-val))))
	  (if (>= *verbosity* 1)
	      (format t "~&error: undefined/non-numeric value ~s of metric ~s~%"
		      metric-val metric))
	  (list nil nil vres))
	 ;; otherwise, everything is fine!!
	 (t (if (>= *verbosity* 1)
		(format t "~&plan valid!~%metric value: ~a~%" (car metric-val)))
	    (list t (car metric-val) vres))
	 )))
     ;; no metric defined, so just return success and vres
     (t (if (>= *verbosity* 1)
	    (format t "~&plan valid!~%"))
	(list t nil vres))
     )))

;; Util function to collect all symbols appearing in an (is-violated ..)
;; term in a (metric) expresssion (used by validate-plan to ensure all
;; is-violated terms are defined before metric is evaluated).

(defun collect-preference-names (exp names)
  (cond ((not (listp exp)) names)
	((endp exp) names)
	((eq (car exp) 'is-violated)
	 (if (not (= (length exp) 2))
	     (error "wrong number of arguments in ~s" exp))
	 (if (or (not (symbolp (cadr exp))) (null (cadr exp)))
	     (error "~a is not a valid preference name in ~s" (cadr exp) exp))
	 (if (find (cadr exp) names) names
	   (cons (cadr exp) names)))
	(t (collect-preference-names
	    (cdr exp) (collect-preference-names (car exp) names)))
	))


;; Run validate-plan on all plans, using the global variables for domain/
;; problem and plan info. The function doesn't return anything, but
;; validation results are printed according to the *verbosity* setting.

(defun validate-all-plans (&key (visualisation nil))
  (dolist (plan *plans*)
    (validate-plan (car plan) (cdr plan) *init* *goal* *constraints* *metric*
		   *actions* (stratify *axioms*) *types* *objects*
		   :visualisation visualisation)
    ))

;; Execute a plan:
;; plan - list of happenings (as above)
;; state - starting state (as above)
;; actions - list of domain action schemas (as above)
;; stratified-axioms - stratified list of axioms (as above)
;; types - list of domain types (as above)
;; objects - list of domain/problem objects (as above)
;; returns: a pair (success . result), where success (t/nil)
;;  indicates there was no error, and result is either the
;;  resulting state (same format as the input state), if
;;  return-state-sequence is nil, or the resulting state sequence.

(defun execute-plan (plan state actions stratified-axioms types objects
			  &key (return-state-sequence nil))
  (let ((sseq nil))
    (loop
     (let ((ext-state
	    (cond (stratified-axioms
		   (extend-state state stratified-axioms types objects))
		  (t state))))
       (if return-state-sequence
	   (setq sseq (append sseq (list ext-state))))
       ;; empty plan: return success with current state/sequence
       (if (endp plan)
	   (return
	    (cons t (if return-state-sequence sseq ext-state))))
       (if (>= *verbosity* 2)
	   (format t "~&next happening:~%~s~%" (first plan)))
       (if (and stratified-axioms (> (length (first plan)) 1))
	   (error "sematics of axioms are undefined for non-sequential plans"))
       ;; let result = result of executing first happening in state
       (if (>= *verbosity* 3)
	   (format t "~&(extended) current state:~%~s~%" ext-state))
       (let ((result (execute-happening
		      (first plan) ext-state actions types objects)))
	 ;; if this was not successful, return the failure
	 (if (not (car result))
	     (return (cons nil (if return-state-sequence sseq ext-state))))
	 ;; else, update state and plan and proceed to next iteration
	 (setq state (cdr result))
	 (setq plan (rest plan))
	 ))
     )))

;; Recursive version of execute-plan. This should be tail-recursive,
;; and thus not subject to stack overflows, but they happen anyway,
;; for long plans and/or large problems. Perhaps because GCL is isn't
;; clever enough to optimise? Indeed, that seems to be the case: it
;; works with ECL.
;;
;; (defun execute-plan (plan state actions stratified-axioms types objects)
;;   (cond
;;    ;; empty plan: return success with current state
;;    ((endp plan) (cons t state))
;;    (t (if (>= *verbosity* 1)
;; 	  (format t "~&next happening:~%~s~%" (first plan)))
;;       (if (and stratified-axioms (> (length (first plan)) 1))
;; 	  (error "sematics of axioms are undefined for non-sequential plans"))
;;       ;; let result = result of executing first happening in state
;;       (let ((ext-state (cond (stratified-axioms
;; 			      (extend-state state stratified-axioms
;; 					    types objects))
;; 			     (t state))))
;; 	(if (>= *verbosity* 2)
;; 	    (format t "~&(extended) current state:~%~s~%" ext-state))
;; 	(let ((result (execute-happening (first plan) ext-state
;; 					 actions types objects)))
;; 	  (cond ((car result) ;; if this was successful,
;; 		 ;; execute the rest of the plan in the resulting state
;; 		 (execute-plan (rest plan) (cdr result)
;; 			       actions stratified-axioms types objects))
;; 		;; else return the failure
;; 		(t result)))))
;;    ))

;; Execute a single happening:
;; happening - list of action instances (each a list of action name
;;   and arguments)
;; state - current state (as above)
;; actions - list of domain action schemas (as above)
;; types - list of domain types (as above)
;; objects - list of domain/problem objects (as above)
;; returns: a pair (success . next-state), where success (t/nil)
;;  indicates there was no error, and next-state is the resulting
;;  state (same format as the input state)

(defun execute-happening (happening state actions types objects)
  ;; for each action in the happening, check that
  ;; - there is such an action, and it has the right number of arguments
  ;; - its precondition holds in the state
  ;; and construct lists of
  ;; - atoms/fluents "read" by the precondition
  ;; - atoms added by the actions effects
  ;; - atoms deleted by the actions effects
  ;; - fluents (numeric and object) assigned by the actions effects
  ;; - fluents (numeric only) increased/decreased by the actions effects
  (let ((eas (mapcar
	      #'(lambda (a)
		  (cons a (check-action a state actions types objects)))
	      happening)))
    ;; success is true if every action was successfully checked
    ;; and there are no read/write or write/write conflicts
    (cons (and (every #'cadr eas) (check-conflicts eas))
	  ;; the resulting state is obtained by applying effects of
	  ;; each action
	  (apply-effects eas state))
    ))

(defun check-happening (happening state actions types objects)
  (mapcar #'(lambda (a)
	      (cons a (check-action a state actions types objects)))
	  happening))

;; Check an actions precondition and collect its read/write sets:
;; act - the action instance (a list of name and args)
;; state - the current state (as above)
;; actions - list of domain action schemas (as above)
;; types - list of domain types (as above)
;; objects - list of domain/problem objects (as above)
;; returns: a list (ok read add del abs rel), where
;;  ok: t if the action exists, has the right number of arguments,
;;    and is applicable in the state (precondition holds and all
;;    fluents in its precondition and effects are defined)
;;  read: list of atoms/fluents read by the precondition
;;  add: list of atoms added
;;  del: list of atoms deleted
;;  ass: list of fluents on which the action has an assign effect
;;  rel: list of fluents on which the action a relative (inc/dec) effect
;;  vios: multiset of preference violations in the action's precondition.

(defun check-action (act state actions types objects)
  (let* ((deflist (assoc-all (car act) actions))
	 (def (cond
	       ((null deflist) nil)
	       (*polymorphic-actions*
		(choose-action-definition act deflist types objects))
	       ((> (length deflist) 1)
		(if (>= *verbosity* 1)
		    (format t "~&error: action ~s multiply defined~%"
			    (car act)))
		nil)
	       (t (car deflist)))))
    (cond
     ((and (null deflist) *ignore-undefined-actions*)
      (if (>= *verbosity* 1)
	  (format t "~&note: skipping undefined action ~a~%" (car act)))
      (list t nil nil nil nil nil nil))
     ((null deflist)
      (if (>= *verbosity* 1)
	  (format t "~&error: no action matching ~a~%" act))
      (list nil nil nil nil nil nil nil))
     ((null def)
      (if (>= *verbosity* 1)
	  (format t "~&error: action ~s is ambiguous~%" act))
      (list nil nil nil nil nil nil nil))
     (t (let ((param (cdr (assoc ':parameters def))))
	  (cond
	   ;; if the given arguments do not match the action definitions
	   ;; parameters (in number and/or type), it's an error (options
	   ;; *ignore-excess-arguments* and
	   ;; *action-parameter-types-are-preconditions* are checked in
	   ;; the arguments-match-parameters function).
	   ((not (arguments-match-parameters (cdr act) param types objects))
	    (if (>= *verbosity* 1)
		(format t "~&arguments of ~a do not match parameters ~a~%"
			act (cons (car act) param)))
	    (list nil nil nil nil nil nil nil))
	   (t
	    ;; if there are more arguments than parameters, but the
	    ;; ignore-excess-arguments option is true, print an info
	    ;; message (unless we're being really quiet).
	    (if (and (< (length param) (length (cdr act)))
		     *ignore-excess-arguments*
		     (>= *verbosity* 1))
		(format t "note: ignoring excess arguments ~a for ~a~%"
			(nthcdr (length param) (cdr act)) (car act)))
	    (let* ((binds (make-binding param (cdr act)))
		   (pre
		    (instantiate-1 binds (cdr (assoc ':precondition def))))
		   (eff
		    (instantiate-1 binds (cdr (assoc ':effect def))))
		   (ok-def-read (eval-formula pre nil state types objects
					      :accept-preferences t)))
	      (cond
	       ((or (not (car ok-def-read))
		    (not (cadr ok-def-read)))
		(if (>= *verbosity* 1)
		    (format t "~&precondition ~s~%of action ~s is false/undefined~%(~s)~%"
			    pre act ok-def-read))
		(list nil nil nil nil nil nil nil))
	       (t (let ((col-eff (collect-effects eff t (caddr ok-def-read)
						  nil nil nil nil
						  state types objects)))
		    (cond ((not (car col-eff))
			   (if (>= *verbosity* 1)
			       (format t "~&effect ~s~%of action~%~s~%is undefined"
				       eff act))
			   (list nil nil nil nil nil nil nil))
			  (t (if (>= *verbosity* 3)
				 (format t "~&effects of ~s:~% add: ~s~% del: ~s~% assign: ~s~% +/-: ~s~%violations: ~s~%"
					 act (third col-eff) (fourth col-eff)
					 (fifth col-eff) (sixth col-eff)
					 (cadddr ok-def-read)))
			     (cons t (econs (cdr col-eff)
					    (cadddr ok-def-read)))))))
	       )))
	   )))
     )))

;; Check if a list of arguments is a valid instantiation of a list of
;; parameters. Note: This function encapsulates two of the options that
;; modify how action instances are matched against action definitions.
;; args - the argument list.
;; params - the parameters (an assoc list of (var . type) pairs).
;; types - list of domain types.
;; objects - list of domain objects.
;; returns: t if arguments are valid, nil otherwise.

(defun arguments-match-parameters (args params types objects)
  (cond
   ;; if we're at the end of the parameter list, it's a match if
   ;; either the argument list is also empty, or the
   ;; ignore-excess-arguments option is true.
   ((endp params) (or (endp args) *ignore-excess-arguments*))
   ;; if the parameter list is non-emtpy but the argument list
   ;; is not, it's a non-match.
   ((endp args) nil)
   ;; if the next argument is undeclared, we call this a non-match,
   ;; unless we're ignoring parameter types
   ((and *action-parameter-types-are-preconditions*
	 (null (assoc (first args) objects)))
    nil)
   ;; if the next argument does not type-match the next parameter,
   ;; it's a non-match, unless we are ignoring types
   ((and *action-parameter-types-are-preconditions*
	 (not (object-can-substitute-for-type
	       (first args) (cdr (first params)) types objects nil)))
    nil)
   (t (arguments-match-parameters (rest args) (rest params) types objects))
   ))

;; Choose the most specific matching action definition from a list
;; of candidates. This function will be called only if polymorphic
;; actions are enabled.
;; act - an action instance (list of action name and args)
;; cands - list of candidated domain actions; these should match on
;;  action name.
;; types - list of domain types (as above)
;; objects - list of domain objects (as above)
;; returns: the list of matching action definitions

(defun choose-action-definition (act cands types objects)
  (let*
      ;; remove candidates that don't match the given arguments
      ((mcands (remove-if-not
		#'(lambda (actdef)
		    (arguments-match-parameters
		     (cdr act) (cdr (assoc ':parameters actdef))
		     types objects))
		cands))
       ;; remove candidates if there exists a distinct more specific
       (mscands (remove-if
		 #'(lambda (actdef)
		     (some #'(lambda (msad)
			       (and (not (equal msad actdef))
				    (parameters-match-parameters
				     (cdr (assoc ':parameters msad))
				     (cdr (assoc ':parameters actdef))
				     types objects)))
			   mcands))
		 mcands)))
    ;; if there is exactly one remaining candicate, return it; if
    ;; there is none or more than one, it is an error.
    (cond
     ((>= *verbosity* 3)
      (format t "~&action definitions matching ~s:~%" act)
      (dolist (cand mcands)
	(format t " ~s ~s~%" (car act) (cdr (assoc ':parameters cand))))
      (format t "~&most specific definitions:~%")
      (dolist (cand mscands)
	(format t " ~s ~s~%" (car act) (cdr (assoc ':parameters cand))))
      ))
    (cond
     ((null mscands) nil)
     ((> (length mscands) 1) nil)
     (t (car mscands))
     )))

;; Check if a list of parameters can substitute for another parameter
;; list. This function is only used by choose-action-definition to
;; determine if one action definition is more specific than another.

(defun parameters-match-parameters (params1 params2 types objects)
  (cond
   ;; if both lists are at an end, they match
   ((endp params1) (endp params2))
   ((endp params2) nil)
   ;; otherwise, check if the first parameter in list 1 can substitute
   ;; for the first in list 2; if not, it's a non-match
   ((not (type-can-substitute-for-type (cdr (first params1))
				       (cdr (first params2))
				       types nil))
    nil)
   ;; else, check rest of the lists
   (t (parameters-match-parameters
       (rest params1) (rest params2) types objects))
   ))

;; Check a happening for read/write and write/write conflicts:
;; ealist - list of "expanded actions": each entry is a list with
;;   1. the action instance (for error reporting)
;;   2. the ok flag from check-action (should be t)
;;   3. the reads list from check-action
;;   4. the add list from check-action
;;   5. the del list from check-action
;;   6. the ass list from check-action
;;   7. the rel list from check-action
;; returns: t iff there are no conflicts; nil otherwise

(defun check-conflicts (ealist)
  (cond
   ;; empty list: all is good
   ((endp ealist) t)
   ;; check first action for self-conflicts, first action against
   ;; remaining actions, and then remaining actions
   (t (and (check-fluent-assignments (first (first ealist))
				     (sixth (first ealist))
				     (seventh (first ealist)))
	   (check-conflicts-2 (first ealist) (rest ealist))
	   (check-conflicts (rest ealist))))
   ))

;; Check fluent effects of action 'act' for self-consistency, i.e., that
;; no fluent appears twice in assignment, or in both an assignment and
;; an inc/dec effect.

(defun check-fluent-assignments (act ass rel)
  (cond ((endp ass) t)
	(t (let ((c1 (check-occurs (second (first ass)) (rest ass)))
		 (c2 (check-occurs (second (first ass)) rel)))
	     (cond ((or c1 c2)
		    (if (>= *verbosity* 1)
			(format t "~&error: action ~s has conflicting effects on ~s"
				act (second (first ass))))
		    nil)
		   (t (check-fluent-assignments act (rest ass) rel))
		   )))
	))

;; Check (expanded) action 'ea' against (expanded) actions in 'ealist'
;; for conflicts (Definition 12, p. 93, Fox & Long 2003).

(defun check-conflicts-2 (ea ealist)
  (every
   #'(lambda (oa) ;; the Other Action
       ;; check that action 'ea'...
       ;;       - does not add any atom read by oa
       (let ((c1 (check-common (fourth ea) (third oa)))
	     ;; - does not delete any atom read by oa
	     (c2 (check-common (fifth ea) (third oa)))
	     ;; - does not read any atom added by oa
	     (c3 (check-common (third ea) (fourth oa)))
	     ;; - does not read any atom deleted by oa
	     (c4 (check-common (third ea) (fifth oa)))
	     ;; - does not add any atom deleted by oa
	     (c5 (check-common (fourth ea) (fifth oa)))
	     ;; - does not delete any atom added by oa
	     (c6 (check-common (fifth ea) (fourth oa)))
	     ;; - does not assign any fluent read by oa
	     (c7 (check-common (sixth ea) (third oa)))
	     ;; - does not inc/dec any fluent read by oa
	     (c8 (check-common (seventh ea) (third oa)))
	     ;; - does not assign any fluent assigned by oa
	     (c9 (check-common (sixth ea) (sixth oa)))
	     ;; - does not assign any fluent inc'd/dec'd by oa
	     (c10 (check-common (sixth ea) (sixth oa)))
	     ;; - does not inc/dec any fluent assigned by oa
	     (c11 (check-common (seventh ea) (sixth oa)))
	     ;; - does not read any fluent assigned by oa
	     (c12 (check-common (third ea) (sixth oa)))
	     ;; - does not read any fluent inc'd/dec'd by oa
	     (c13 (check-common (third ea) (seventh oa))))
	 (cond ((or c2 c4)
		(if (>= *verbosity* 1)
		    (format t "~&error: atom read/write conflict:~%    ~s~%and ~s:~%~s ~s~%"
			    (first ea) (first oa) c2 c4))
		nil)
	       ((and *add-read-are-mutex* (or c1 c3))
		(if (>= *verbosity* 1)
		    (format t "~&error: atom read/write conflict:~%    ~s~%and ~s:~%~s ~s~%"
			    (first ea) (first oa) c1 c3))
		nil)
	       ((or c5 c6)
		(if (>= *verbosity* 1)
		    (format t "~&error: atom write/write conflict:~%    ~s~%and ~s:~%~s ~s~%"
			    (first ea) (first oa) c5 c6))
		nil)
	       ((or c7 c8 c12 c13)
		(if (>= *verbosity* 1)
		    (format t "~&error: fluent read/write conflict:~%    ~s~%and ~s:~%~s ~s ~s ~s~%"
			    (first ea) (first oa) c7 c8 c12 c13))
		nil)
	       ((or c9 c10 c11)
		(if (>= *verbosity* 1)
		    (format t "~&error: fluent write/write conflict:~%    ~s~%and ~s:~%~s ~s ~s~%"
			    (first ea) (first oa) c9 c10 c11))
		nil)
	       (t t)
	       )))
   ealist))

;; Check if (ground) fluent/atom 'atom' occurs in 'alist': alist is a
;; list of either (ground) fluents/atoms, or (ground) fluent effect
;; expressions (assign/increase/decrease <f> <v>).

(defun check-occurs (atom alist)
  (cond ((endp alist) nil)
	((member (first (first alist)) '(assign increase decrease))
	 (cond ((equal atom (second (first alist))) t)
	       (t (check-occurs atom (rest alist)))))
	(t (cond ((equal atom (first alist)) t)
		 (t (check-occurs atom (rest alist)))))
	))

;; Return the list of atoms/fluents from alist1 occurring in alist2;
;; both alist1 and alist2 are lists of either (ground) fluents/atoms,
;; or (ground) fluent effect expresssions (as above).

(defun check-common (alist1 alist2)
  (cond ((endp alist1) nil)
	((member (first (first alist1)) '(assign increase decrease))
	 (cond ((check-occurs (second (first alist1)) alist2)
		(cons (second (first alist1))
		      (check-common (rest alist1) alist2)))
	       (t (check-common (rest alist1) alist2))))
	((check-occurs (first alist1) alist2)
	 (cons (first alist1) (check-common (rest alist1) alist2)))
	(t (check-common (rest alist1) alist2))
	))


;; Evaluate a logical formula in a state, and find the atoms/fluents read:
;; form - the (PDDL) formula.
;; note: the parameter lists of quantifiers in the formula are assumed to
;;   be unparsed, i.e., in the PDDL (var - type ..) form.
;; reads - list of atoms/fluents read so far
;; state - the state (list of atoms/fluents as above)
;; types - list of domain types (as above)
;; objects - list of domain/problem objects (as above)
;; returns: a list (val def f-reads vios), where
;;   - 'val' is the formula's value (t or nil),
;;   - 'def' denotes if the formula's value is well-defined (t or nil),
;;     i.e., if all fluent expressions appearing in it were defined,
;;   - f-reads is the input reads list extended with any atom/fluent
;;     read by the formula, and
;;   - vios is the multiset of violated preferences, represented as an
;;     assoc list from preference name to number; anonymous preferences
;;     are counted under the name 'nil.

(defun eval-formula (form reads state types objects
		       &key (report-errors t) (accept-preferences nil))
  (cond
   ;; special case: treat an empty list as a true condition
   ((null form) (list t t reads nil))
   ;; logical connectives (note: handles n-ary and/or)
   ;; note: we must evaluate all the con-/disjuncts (sequentially)
   ;; to collect the set of read atoms/fluents and check definedness
   ((eq (car form) 'and)
    ;; Iterative evaluation of 'and:
    (let ((ok t)
	  (val t)
	  (vios nil))
      (dolist (f1 (cdr form))
	(let ((v1 (eval-formula f1 reads state types objects
				:report-errors report-errors
				:accept-preferences accept-preferences)))
	  (setq val (and val (car v1)))
	  (setq ok (and ok (cadr v1)))
	  (setq vios (multiset-add vios (cadddr v1)))
	  (setq reads (caddr v1))))
      (list val ok reads vios)))
   ((eq (car form) 'or)
    ;; Iterative evaluation of 'or:
    (let ((ok t)
	  (val nil))
      (dolist (f1 (cdr form))
	(let ((v1 (eval-formula f1 reads state types objects
				:report-errors report-errors
				:accept-preferences nil)))
	  (setq val (or val (car v1)))
	  (setq ok (and ok (cadr v1)))
	  (setq reads (caddr v1))))
      (list val ok reads nil)))
   ((eq (car form) 'not)
    (if (not (= (length form) 2)) (error "ill-formed formula: ~s" form))
    (let ((v1 (eval-formula (cadr form) reads state types objects
			    :report-errors report-errors
			    :accept-preferences nil)))
      (list (not (car v1)) (cadr v1) (caddr v1) nil)))
   ((eq (car form) 'imply)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let* ((v1 (eval-formula (cadr form) reads state types objects
			     :report-errors report-errors
			     :accept-preferences nil))
	   (v2 (eval-formula (caddr form) (caddr v1) state types objects
			     :report-errors report-errors
			     :accept-preferences nil)))
      (list (or (not (car v1)) (car v2))
	    (and (cadr v1) (cadr v2))
	    (caddr v2)
	    nil)))
   ;; quantifiers are handled by instantiating them as and/or lists
   ((eq (car form) 'forall)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let ((vars (parse-typed-list '() (cadr form) 'object)))
      (cond ((endp vars)
	     (eval-formula (caddr form) reads state types objects
			   :report-errors report-errors
			   :accept-preferences accept-preferences))
	    (t (eval-formula
		(cons 'and (instantiate (caddr form) nil vars types objects))
		reads state types objects
		:report-errors report-errors
		:accept-preferences accept-preferences)))))
   ((eq (car form) 'exists)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let ((vars (parse-typed-list '() (cadr form) 'object)))
      (cond ((endp vars)
	     (eval-formula (caddr form) reads state types objects
			   :report-errors report-errors
			   :accept-preferences nil))
	    (t (eval-formula
		(cons 'or (instantiate (caddr form) nil vars types objects))
		reads state types objects
		:report-errors report-errors
		:accept-preferences nil)))))
   ;; preference
   ((eq (car form) 'preference)
    (if (not accept-preferences)
	(error "preference ~a not allowed in this context" form))
    (if (or (< (length form) 2) (> (length form) 3))
	(error "ill-formed formula: ~s" form))
    (let ((pname (if (= (length form) 3) (second form) nil))
	  (pform (if (= (length form) 3) (third form) (second form))))
      (let ((v1 (eval-formula pform reads state types objects
			      :report-errors report-errors
			      :accept-preferences nil)))
	(cond ((null (cadr v1)) ;; result not defined
	       (list nil nil (caddr v1) nil))
	      ((null (car v1)) ;; result defined, preference false
	       (if (>= *verbosity* 2)
		   (format t "~&preference ~a ~a violated~%" pname pform))
	       (list t t (caddr v1) (list (cons pname 1))))
	      (t (list t t (cadr v1) nil))))))
   ;; equality
   ((eq (car form) '=)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let* ((v1 (eval-term (cadr form) reads state
			  :report-errors report-errors))
	   (v2 (eval-term (caddr form) (cadr v1) state
			  :report-errors report-errors)))
      (list (equal (car v1) (car v2)) (and (car v1) (car v2)) (cadr v2) nil)))
   ;; numeric predicates
   ((assoc (car form) *builtin-numeric-predicates*)
    (let ((pdef (assoc (car form) *builtin-numeric-predicates*))
	  (vlist (eval-term-list (cdr form) reads state
				 :report-errors report-errors)))
      (cond
       ;; too few arguments?
       ((and (numberp (second pdef))
	     (< (length (cdr form)) (second pdef)))
	(if report-errors
	    (format t "~&error: too few arguments to ~s in ~s (~s required)~%"
		    (first pdef) form (second pdef)))
	(list nil nil (cadr vlist) nil))
       ;; too many arguments?
       ((and (numberp (third pdef))
	     (> (length (cdr form)) (third pdef)))
	(if report-errors
	    (format t "~&error: too many arguments to ~s in ~s (~s allowed)~%"
		    (first pdef) form (third pdef)))
	(list nil nil (cadr vlist) nil))
       ;; non-numeric arguments?
       ((not (every #'numberp (car vlist)))
	(if report-errors
	    (format t "~&error: non-numeric arguments ~s in ~s"
		    (car vlist) form))
	(list nil nil (cadr vlist) nil))
       ;; all ok, apply the function
       (t (list (funcall (fourth pdef) (car vlist)) t (cadr vlist) nil))
       )))
   ;; type name used as unary predicate (if enabled)
   ((and *type-names-are-predicates*
	 (or (assoc (car form) types) (rassoc (car form) types))
	 (= (length (cdr form)) 1))
    (let ((vlist (eval-term-list (cdr form) reads state
				 :report-errors report-errors)))
      (cond ((object-can-substitute-for-type
	      (caar vlist) (car form) types objects nil)
	     (list t (not (some #'null (car vlist))) (cadr vlist) nil))
	    (t (list nil (not (some #'null (car vlist))) (cadr vlist) nil))
	    )))
   ;; finally, an atom: but the atom may have complex terms
   (t (let* ((vlist (eval-term-list (cdr form) reads state
				    :report-errors report-errors))
	     (ground-atom (cons (car form) (car vlist))))
	(cond ((find ground-atom state :test #'equal)
	       (list t (not (some #'null (car vlist)))
		     (cons ground-atom (cadr vlist)) nil))
	      (t (list nil (not (some #'null (car vlist)))
		       (cons ground-atom (cadr vlist)) nil)))))
   ))

;; Add two multisets, represented by assoc lists. Key equality is eq,
;; and the function is non-destructive.

(defun multiset-add (ms1 ms2)
  (if (endp ms2) ms1
    (let ((n (assoc (caar ms2) ms1)))
      (if n (multiset-add (reassoc (car n) (+ (cdr n) (cdar ms2)) ms1)
			  (cdr ms2))
	(multiset-add (cons (car ms2) ms1) (cdr ms2))))))

;; Evaluate a fluent expression in a state, and find the atoms/fluents read:
;; e - the (PDDL) expression; this may be either an object or numeric exp
;; reads - list of atoms/fluents read so far
;; state - the state (list of atoms/fluents as above)
;; returns: a list (val e-reads), where 'val' is the expression value
;;   (a number or an object name) and e-reads is the input reads list
;;   extended with any fluents read by e; note: val will be nil iff the
;;   fluent value is undefined in the state

(defun eval-term (e reads state &key (report-errors t))
  (cond
   ((not (listp e)) (list e reads))
   ((null e) (error "invalid term: ~s" e))
   ;; numeric functions
   ((assoc (car e) *builtin-numeric-functions*)
    (let ((fundef (assoc (car e) *builtin-numeric-functions*))
	  (vlist (eval-term-list (cdr e) reads state
				 :report-errors report-errors)))
      (cond
       ;; too few arguments?
       ((and (numberp (second fundef))
	     (< (length (cdr e)) (second fundef)))
	(if report-errors
	    (format t "~&error: too few arguments to ~s in ~s (~s required)~%"
		    (first fundef) e (second fundef)))
	(list nil (cadr vlist)))
       ;; too many arguments?
       ((and (numberp (third fundef))
	     (> (length (cdr e)) (third fundef)))
	(if report-errors
	    (format t "~&error: too many arguments to ~s in ~s (~s allowed)~%"
		    (first fundef) e (third fundef)))
	(list nil (cadr vlist)))
       ;; non-numeric arguments?
       ((not (every #'numberp (car vlist)))
	(if report-errors
	    (format t "~&error: non-numeric arguments ~s in ~s" (car vlist) e))
	(list nil (cadr vlist)))
       ;; all ok, apply the function
       (t (list (funcall (fourth fundef) (car vlist))
		(cadr vlist)))
       )))
   ;; anything else is a fluent expression
   (t (let* ((vlist (eval-term-list (cdr e) reads state
				    :report-errors report-errors))
	     (ground-fluent (cons (car e) (car vlist))))
	(cond ((not (some #'null (car vlist)))
	       (let ((val (find-fluent-value ground-fluent state)))
		 (cond ((null val)
			(if report-errors
			    (format t "~&error: fluent ~s is undefined"
				    ground-fluent))
			(list nil (cadr vlist)))
		       (t (list val (cadr vlist))))))
	      (t (if report-errors
		     (format t "~&error: undefined argument ~s~%in ~s"
			     (car vlist) e))
		 (list nil (cadr vlist))))))
   ))


(defun find-fluent-value (ground-fluent state)
  (let ((res (find-if
	      #'(lambda (a) (and (eq (first a) '=)
				 (equal (second a) ground-fluent)))
	      state)))
    (cond (res (third res))
	  (t nil))))


;; Evaluate a list of fluent expressions:
;; elist - the list of (PDDL) expressions
;; reads - list of atoms/fluents read so far
;; state - the state (list of atoms/fluents as above)
;; returns: a list (vals e-reads), where 'vals' is the corresponding
;;   list of expression values (number, object name or nil for undefined),
;;   and e-reads is the input reads list extended with any fluents read
;;   by any expression.

(defun eval-term-list (elist reads state &key (report-errors t))
  (cond ((endp elist) (list nil reads))
	(t (let* ((v1 (eval-term (car elist) reads state
				 :report-errors report-errors))
		  (vlist (eval-term-list (cdr elist) (cadr v1) state
					 :report-errors report-errors)))
	     (list (cons (car v1) (car vlist)) (cadr vlist))))
	))


;; Instantiate variables in an expression with all possible values:
;; exp - the expression
;; binds - assoc list of current variable bindings
;; vars - list of unbound variables
;; types - assoc list of (type . supertype) pairs
;; objects - assoc list of (object . type) pairs
;; :insfun - a function that will be called with the bindings and the
;;   expression, for each complete set of bindings of the variables;
;;   defaults to function instantiate-1 (see below), but note that
;;   the arguments also match those of sublis (which is a lot faster,
;;   but doesn't work for expressions with shadowing variables).
;; :insfun-returns-list - does the insfun return the instantiated
;;   expression wrapped in a list? (t/nil). Defaults to nil, which
;;   is the case for typical functions (e.g., instantiate-1 and sublis).
;; returns: a list of expressions

(defun instantiate
  (exp binds vars types objects &key (insfun #'instantiate-1)
       (insfun-returns-list nil))
  ;; if there is no unbound variable, instantiate the expression
  ;; with current bindings and return it wrapped in a list
  (cond ((endp vars)
	 (let ((ins-exp (funcall insfun binds exp)))
	   (cond (insfun-returns-list ins-exp)
		 (t (list ins-exp)))))
	;; if there are remaining variables, bind the first variable to
	;; each possible value and recursively call instantiate; each
	;; call will return a list of expressions, which are merged into
	;; a single list
	(t (mapflat
	    #'(lambda (x)
		(instantiate exp (extend-binding (caar vars) x binds)
			     (cdr vars) types objects
			     :insfun insfun
			     :insfun-returns-list insfun-returns-list))
	    (objects-of-type (cdar vars) types objects)))
	))

;; Alternative implementations of instantiate - neither one better
;; than the the simple one above!
;;
;; (defun instantiate
;;   (exp binds vars types objects &key (insfun #'instantiate-1))
;;   (let ((res nil))
;;     (labels
;;      ((instantiate-rec
;;        (binds vars)
;;        (if (endp vars)
;; 	   (push (funcall insfun binds exp) res)
;; 	 (dolist (obj (objects-of-type (cdar vars) types objects))
;; 	   (instantiate-rec (extend-binding (caar vars) obj binds)
;; 			    (cdr vars))))))
;;      (instantiate-rec binds vars))
;;     res))
;;
;; (defun instantiate
;;   (exp binds vars types objects &key (insfun #'instantiate-1) (res '(nil)))
;;   (if (endp vars)
;;       (rplaca res (cons (funcall insfun binds exp) (car res)))
;;     (dolist (obj (objects-of-type (cdar vars) types objects))
;;       (instantiate exp (extend-binding (caar vars) obj binds)
;; 		   (cdr vars) types objects :insfun insfun :res res)))
;;   (car res))


;; Instantiate an expression with a set of variable bindings. Bound
;; variables that are shadowed by quantifiers in the expression are
;; left untouched inside the quantifier body.
;; exp - the expression
;; binds - assoc list of current variable bindings
;; returns: the expression with values substituted for bound variables

(defun instantiate-1 (binds exp)
  ;; shortcut: if the bindings are empty, we'll return the same exp
  ;; eventually, so we may as well return it straight away.
  (cond ((endp binds) exp)
	((null exp) exp)
	;; if exp is a list...
	((listp exp)
	 ;; if exp is a quantified expression, unbind the
	 ;; quantified variables and then substitute bindings in
	 ;; the body (the quantified formula)
	 (cond
	  ((or (eq (car exp) 'forall) (eq (car exp) 'exists))
	   (if (not (= (length exp) 3))
	       (error "ill-formed quantified formula: ~s" exp))
	   (let ((qvars (parse-typed-list '() (second exp) 'object)))
	     (list (first exp) (second exp)
		   (instantiate-1 (remove-bindings qvars binds) (third exp)))))
	  ;; if the expression is an axiom, the axiom head is an
	  ;; atom schema, which must be handled specially
	  ((eq (car exp) ':derived)
	   (if (< (length exp) 2)
	       (error "ill-formed axiom: ~s" exp))
	   (list ':derived (instantiate-atom-schema (second exp) binds)
		 (instantiate-1 binds (third exp))))
	  ;; if this is a cons-pair, we cannot apply mapcar:
	  ((not (listp (cdr exp)))
	   (cons (instantiate-1 binds (car exp))
		 (instantiate-1 binds (cdr exp))))
	  ;; for any other list expression, recursively instantiate
	  ;; all elements
	  (t (mapcar #'(lambda (exp1) (instantiate-1 binds exp1)) exp))
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


;; Variant of instantiate-1 that also instantiates quantifiers within
;; the expression. Thus, if all free variables in the expression are
;; bound by the input binding, the returned expression will be fully
;; ground.
;; exp - the expression
;; binds - assoc list of current variable bindings
;; returns: the grounded expression

(defun ground-1 (binds exp types objects)
  (cond ((null exp) exp)
	((listp exp)
	 ;; if exp is a quantified expression, unbind the quantified
	 ;; variables and call instantiate with them and the body.
	 (cond
	  ((eq (car exp) 'forall)
	   (if (not (= (length exp) 3))
	       (error "ill-formed quantified formula: ~s" exp))
	   (let ((qvars (parse-typed-list '() (second exp) 'object)))
	     (cons 'and (instantiate
			 (third exp) (remove-bindings qvars binds)
			 qvars types objects
			 :insfun #'(lambda (b e)
				     (ground-1 b e types objects))))))
	  ((eq (car exp) 'exists)
	   (if (not (= (length exp) 3))
	       (error "ill-formed quantified formula: ~s" exp))
	   (let ((qvars (parse-typed-list '() (second exp) 'object)))
	     (cons 'or (instantiate
			(third exp) (remove-bindings qvars binds)
			qvars types objects
			:insfun #'(lambda (b e)
				    (ground-1 b e types objects))))))
	  ;; if the expression is an axiom, the axiom head is an
	  ;; atom schema, which must be handled specially
	  ((eq (car exp) ':derived)
	   (if (< (length exp) 2)
	       (error "ill-formed axiom: ~s" exp))
	   (list ':derived (instantiate-atom-schema (second exp) binds)
		 (ground-1 binds (third exp) types objects)))
	  ;; for any other list expression, recursively instantiate
	  ;; all elements
	  (t (mapcar #'(lambda (exp1) (ground-1 binds exp1 types objects))
		     exp))
	  ))
	;; if exp is a symbol, look it up in bindings
	((symbolp exp)
	 (let ((val (assoc exp binds)))
	   (cond (val (cdr val))
		 (t exp))))
	;; if exp is neither a list nor a symbol, just return it
	(t exp)
	))


;; Instantiate an atom schema, that is, an expression of the form
;; (pred-name arg*), where each argument may be a constant or variable,
;; and variables may have associated types (individually or several
;; with the same type declaration).

(defun instantiate-atom-schema (schema binds)
  (let ((args (parse-typed-list '() (rest schema) 'object)))
    (cons (first schema)
	  (mapcar #'(lambda (arg)
		      (let ((val (assoc (car arg) binds)))
			(cond (val (cdr val))
			      (t (car arg)))))
		  args))))

(defun instantiate-predicate (predicate types objects)
  (instantiate (cons (car predicate) (mapcar #'car (cdr predicate)))
	       nil (cdr predicate) types objects))

;; Functions for handling variable-value bindings:

(defun make-binding (params args)
  (cond ((endp params) nil)
	((endp args) (error "too few arguments for ~s" params))
	(t (cons (cons (caar params) (car args))
		 (make-binding (cdr params) (cdr args))))
	))

(defun extend-binding (var val binds)
  (cons (cons var val) binds))

(defun extend-binding-with-binding (binds new-binds)
  (cond ((endp new-binds) binds)
	((assoc (caar new-binds) binds)
	 (extend-binding-with-binding binds (cdr new-binds)))
	(t (cons (car new-binds)
		 (extend-binding-with-binding binds (cdr new-binds))))
	))

;; note: argument vars of remove-bindings can be a list of variable
;; names only, or a list of (var . type) cons pairs.

(defun remove-bindings (vars binds)
  (remove-if #'(lambda (b)
		 (find-if #'(lambda (v)
			      (cond ((consp v) (eq (car b) (car v)))
				    (t (eq (car b) v))))
			  vars))
	     binds))

;; unbind a single variable ('var') destructively from binds
(defun unbind-destructive (var binds)
  (cond ((endp binds) nil)
	((eq (car (car binds)) var) (cdr binds))
	(t (rplacd binds (unbind-destructive var (cdr binds))))))


;; Find all objects of a given type:
;; type - a type expression: either a type name, or (either type+ ...).
;;
;;   As a spectial case, if type is nil the variable is considered to
;;   be untyped and the list of all objects is returned. This is an
;;   exception and applies only in this function.
;;   
;; types - assoc list of (type . supertype) pairs
;; objects - assoc list of (object . type) pairs
;; return: list of objects (without types)

(defun objects-of-type (type types objects)
  (cond ((null type) (mapcar #'car objects))
	(t (let ((res nil))
	     (dolist (obj-type-def objects)
	       (cond ((and (not (member (car obj-type-def) res))
			   (object-can-substitute-for-type
			    (car obj-type-def) type types objects
			    (list 'objects-of-type type)))
		      (push (car obj-type-def) res))))
	     res))
	))


;; Split action effects into different categories:
;; eff - the effect formula
;; ok - is the effect formula well-defined so far (t/nil)
;; reads: input list of atoms/fluents read
;; add: input list of atoms added
;; del: input list of atoms deleted
;; ass: input list of fluents on which the action has an assign effect
;; rel: input list of fluents on which the action a relative (inc/dec) effect
;; state - the current state (as above)
;; types - list of domain types (as above)
;; objects - list of domain/problem objects (as above)
;; returns: a list (ok read add del abs rel), where
;;  ok: t if (conditions and terms in) the effect exp are well-defined
;;  read: list of atoms/fluents read
;;  add: list of atoms added
;;  del: list of atoms deleted
;;  ass: list of assigned fluents (object or numeric)
;;  rel: list of inc'd/dec'd fluents

(defun collect-effects (eff ok reads add del ass rel state types objects)
  (cond
   ((not (listp eff)) (error "ill-formed effect formula: ~s" eff))
   ((endp eff) (list ok reads add del ass rel))
   ((eq (car eff) 'and)
    (cond ((endp (cdr eff)) (list t reads add del ass rel))
	  (t (let ((c1 (collect-effects (cadr eff) ok reads add del ass rel
					state types objects)))
	       (collect-effects (cons 'and (cddr eff))
				(first c1) (second c1) (third c1)
				(fourth c1) (fifth c1) (sixth c1)
				state types objects)))))
   ((eq (car eff) 'forall)
    (if (not (= (length eff) 3)) (error "ill-formed effect formula: ~s" eff))
    (let ((vars (parse-typed-list '() (cadr eff) 'object)))
      (cond ((endp vars)
	     (collect-effects
	      (caddr eff) ok reads add del ass rel state types objects))
	    (t (collect-effects
		(cons 'and (instantiate (caddr eff) nil vars types objects))
		ok reads add del ass rel state types objects)))))
   ((eq (car eff) 'when)
    (if (not (= (length (cdr eff)) 2))
	(error "ill-formed effect formula ~s" eff))
    (let ((v1 (eval-formula (second eff) reads state types objects)))
      (cond ((and (car v1) (cadr v1))
	     (collect-effects (third eff) ok (caddr v1) add del ass rel
			      state types objects))
	    (t (list (and ok (cadr v1)) (caddr v1) add del ass rel))
	    )))
   ((eq (car eff) 'not)
    (if (not (= (length (cdr eff)) 1))
	(error "ill-formed effect formula: ~s" eff))
    (if (not (listp (cadr eff)))
	(error "ill-formed effect formula: ~s" eff))
    (let ((vlist (eval-term-list (cdr (cadr eff)) reads state)))
      (list (and ok (not (some #'null (car vlist)))) (cadr vlist)
	    add (cons (cons (car (cadr eff)) (car vlist)) del) ass rel)))
   ((eq (car eff) 'assign)
    (if (not (= (length (cdr eff)) 2))
	(error "ill-formed effect formula: ~s" eff))
    (if (not (listp (cadr eff)))
	(error "ill-formed effect formula: ~s" eff))
    (let* ((vlist (eval-term-list (cdr (cadr eff)) reads state))
	   (v2 (eval-term  (caddr eff) (cadr vlist) state)))
      (list (and ok (not (some #'null (car vlist))) (not (null (car v2))))
	    (cadr v2) add del
	    (cons (list 'assign (cons (car (cadr eff)) (car vlist)) (car v2))
		  ass)
	    rel)))
   ((member (car eff) '(increase decrease))
    (if (not (= (length (cdr eff)) 2))
	(error "ill-formed effect formula: ~s" eff))
    (if (not (listp (cadr eff)))
	(error "ill-formed effect formula: ~s" eff))
    (let* ((vlist (eval-term-list (cdr (cadr eff)) reads state))
	   (v2 (eval-term  (caddr eff) (cadr vlist) state)))
      (list (and ok (not (some #'null (car vlist))) (not (null (car v2))))
	    (cadr v2) add del ass
	    (cons (list (car eff) (cons (car (cadr eff)) (car vlist)) (car v2))
		  rel))))
   ((member (car eff) *quoted-argument-predicates*)
    (list ok reads (cons eff add) del ass rel))
   (t
    (let ((vlist (eval-term-list (cdr eff) reads state)))
      (list (and ok (not (some #'null (car vlist)))) (cadr vlist)
	    (cons (cons (car eff) (car vlist)) add) del ass rel)))
   ))

;; Apply a conflict-free set of action effects to a state:
;; ealist - list of "expanded actions": each entry is a list with
;;   1. the action instance (for error reporting)
;;   2. the ok flag from check-action (should be t)
;;   3. the reads list from check-action
;;   4. the add list from check-action
;;   5. the del list from check-action
;;   6. the ass list from check-action
;;   7. the rel list from check-action
;;   8. the preference violations multiset from check-action
;; returns: the new state

(defun apply-effects (ealist state)
  (if (endp ealist) state
    (apply-effects (rest ealist)
		   (update-preference-violations
		    (eighth (first ealist))
		    (apply-assign-effects
		     (sixth (first ealist))
		     (apply-relative-effects
		      (seventh (first ealist))
		      (apply-add-effects
		       (fourth (first ealist))
		       (apply-delete-effects
			(fifth (first ealist))
			state))))))))

(defun apply-delete-effects (del state)
  (remove-if #'(lambda (a) (member a del :test #'equal)) state))

(defun apply-add-effects (add state)
  (append (remove-if #'(lambda (a)
			 (and (member a state :test #'equal)
			      (not (member (car a) *duplicated-predicates*))))
		     add)
	  state))

(defun apply-relative-effects (rel state)
  (if (endp rel) state
    (let ((total-change 0))
      ;; collect total change on the fluent of the first relative effect
      (dolist (eff rel)
	(cond ((equal (second eff) (second (first rel)))
	       (if (not (numberp (third eff)))
		   (error "applying ~s: ~s is not a number" eff (third eff)))
	       (cond ((eq (first eff) 'increase)
		      (setq total-change (+ total-change (third eff))))
		     ((eq (first eff) 'decrease)
		      (setq total-change (- total-change (third eff))))))))
      (let ((current (find (second (first rel)) state
			   :test #'equal :key #'second)))
	(cond ((null current)
	       (error "applying ~s: ~s is undefined"
		      rel (second (first rel))))
	      ((not (numberp (third current)))
	       (error "applying ~s: value ~s of ~s is not a number"
		      rel (third current) (second (first rel))))
	      (t ;; reassign this fluent to its current value +
	       ;; total-change, and tail recurse with the list of
	       ;; relative effects on other fluents
	       (apply-relative-effects
		(remove (second (first rel)) rel
			:test #'equal :key #'second)
		(cons (list '= (second (first rel))
			    (+ (third current) total-change))
		      (remove (second (first rel)) state
			      :test #'equal :key #'second))))
	      )))))

(defun apply-assign-effects (ass state)
  (append
   ;; replace 'assign' with '='
   (mapcar #'(lambda (a) (list '= (second a) (third a))) ass)
   ;; remove existing assignments for assigned fluents
   (remove-if #'(lambda (atom)
		  (cond ((not (eq (car atom) '=)) nil)
			(t (member (second atom) ass
				   :test #'equal :key #'second))))
	      state)))

(defun update-preference-violations (vios state)
  (if (endp vios) state
    (let ((current (find (list 'is-violated (car (first vios))) state
			 :test #'equal :key #'second)))
      (if (and current (not (numberp (third current))))
	  (error "updating preferences ~s: ~s is not numeric" vios current))
      (update-preference-violations
       (cdr vios)
       (cons
	;; add new fluent assignment...
	(list '= (list 'is-violated (car (first vios)))
	      (if current (+ (third current) (cdar vios)) (cdar vios)))
	;; to state with old assignment (if any) removed
	(if current (remove (second current) state :test #'equal :key #'second)
	  state))))))


;;;;
;; Axiom handling

;; Extend state with values of derived predicates:
;; state - the state (list of ground atoms/fluent equalities)
;; stratified-axioms - list of axiom strata; each stratum is a list
;;   of axioms (still including the :derived keyword)
;; returns: the extended state.

(defun extend-state (state stratified-axioms types objects)
  (let ((base-state (clear-derived-predicates state stratified-axioms)))
    (if (>= *verbosity* 4)
	(format t "~&base state:~%~s~%" base-state))
    (apply-stratified-axioms base-state stratified-axioms types objects)))


;; Remove all instances of derived predicates from state:

(defun clear-derived-predicates (state stratified-axioms)
  (remove-if #'(lambda (atom)
		 (some #'(lambda (stratum)
			   (find (car atom) stratum :key #'caadr :test #'eq))
		       stratified-axioms))
	     state))


;; Extend state by applying a stratified list of axioms:

(defun apply-stratified-axioms (state strata types objects)
  (cond ((endp strata) state)
	(*fast-axiom-fixpoint*
	 (apply-stratified-axioms
	  (apply-axioms-2 state (first strata) types objects)
	  (rest strata) types objects))
	(t (apply-stratified-axioms
	    (apply-axioms state (first strata) types objects)
	    (rest strata) types objects))))


;; Extend state by applying a flat list of axioms (i.e., a single stratum).
;; It is assumed that the current state contains no atoms that appear in
;; the head of axioms.

(defun apply-axioms (state axioms types objects)
  ;; rem: list of axioms that remain to (possibly) apply; variables in
  ;;   axiom heads are grounded.
  ;; new-atoms: new atoms generated in current iteration.
  (let ((rem (instantiate-axioms axioms types objects))
	(new-atoms nil))
    (if (>= *verbosity* 4)
	(format t "~&applying ~s axioms in current stratum~%" (length rem)))
    ;; axiom application is a fixpoint computation: this is the outer loop
    (loop
     ;; clear new atoms
     (setq new-atoms nil)
     ;; for each remaining axiom...
     (dolist (axiom rem)
       ;; if the body of the axiom evaluates to true, add the head
       ;; atom to new-atoms
       (let ((v (eval-formula (third axiom) nil state types objects
			      :report-errors nil)))
       	 (if (and (first v) (second v)) ;; true and well-defined
	     (if (not (find (second axiom) new-atoms :test #'equal))
		 (progn 
		   (if (>= *verbosity* 5) (format t "~&triggered ~s~%" axiom))
		   (push (second axiom) new-atoms)))))
       )
     ;; end of inner loop: if no new atoms were derived, we have reached
     ;; a fixpoint and return the state
     (if (endp new-atoms) (return state))
     ;; else, add new atoms to state
     (setq state (append state new-atoms))
     ;; and remove from the remaining axioms list all axioms whose head
     ;; is an already derived atom.
     (setq rem (remove-if
		#'(lambda (a)
		    (find (second a) new-atoms :test #'equal))
		rem))
     (if (>= *verbosity* 4)
	 (format t "~&end of loop: ~s new atoms and ~s axioms remain~%"
		 (length new-atoms) (length rem)))
     )))

;; Collect predicates appearing in axiom heads:
;; axioms - flat list of domain axioms
;; returns: list of predicate names (duplicate-free)

(defun collect-derived-predicates (axioms)
  (cond ((endp axioms) nil)
	(t (let ((axiom (first axioms))
		 (coll (collect-derived-predicates (rest axioms))))
	     (if (< (length axiom) 2)
		 (error "ill-formed axiom: ~s" axiom))
	     (if (not (listp (second axiom)))
		 (error "ill-formed axiom: ~s" axiom))
	     (if (endp (second axiom))
		 (error "ill-formed axiom: ~s" axiom))
	     (if (not (symbolp (first (second axiom))))
		 (error "ill-formed axiom: ~s" axiom))
	     (add-to-set (first (second axiom)) coll)))
	))


;; Instantiate a stratified list of axioms:

(defun instantiate-stratified-axioms (strata types objects)
  (mapcar #'(lambda (s) (instantiate-axioms s types objects))
	  strata))


;; Instantiate a flat list of axioms:

(defun instantiate-axioms (axioms types objects)
  (mapflat #'(lambda (a) (instantiate-axiom a types objects)) axioms))


;; Instantiate a single axiom:

(defun instantiate-axiom (axiom types objects)
  (instantiate axiom nil (axiom-parameters axiom types) types objects
	       ;; :insfun #'(lambda (b e) (ground-1 b e types objects))
	       ))


;; Find the parameters of an axiom: these are the variables in the atom
;; schema that is the axiom head, and any free variables in the body that
;; do not appear in the head; variables in the head may be typed, and
;; to futher complicate matters, the atom schema may also have non-variable
;; arguments.

(defun axiom-parameters (axiom types)
  (when (< (length axiom) 2) (error "ill-formed axiom: ~s" axiom))
  (let ((h-args (parse-typed-list '() (cdr (second axiom)) 'object))
	(b-free (free-variables (third axiom))))
    (remove-duplicate-variables
     (append (mapcar #'(lambda (x) (cons x 'object)) b-free)
	     (remove-if-not #'variable-p h-args :key #'car)) types)
    ))

;; Remove duplicate variable declarations from a (var . type) assoc list,
;; assigning the most specific type to each variable that has multiple
;; declarations. If a variable is declared with two different types that
;; are not in subtype-supertype relation, an error is raised.
;; pt-list - the declaration list
;; types - the (type . supertype) assoc list
;; returns: a new (var . type) assoc list.

;; FIXME: Is it really an error to have conflicting type declarations?
;; Or should that be treated as the variable having a "conjunctive"
;; compound type spec (say, :both, to complement :either). Where would
;; support for that need to be added?

(defun remove-duplicate-variables (pt-list types)
  (let ((new-pt-list nil))
    (dolist (decl pt-list)
      (let ((prev-decl (assoc (car decl) new-pt-list)))
	(cond (prev-decl
	       (let ((new-type
		      (most-specific-type (cdr prev-decl) (cdr decl) types)))
		 (if (null new-type)
		     (error "conflicting types for ~a: ~a and ~a"
			    (car decl) (cdr prev-decl) (cdr decl)))
		 (rplacd prev-decl new-type)))
	      (t (setq new-pt-list (cons decl new-pt-list)))
	      )))
    new-pt-list))


;; Stratify a set of axioms.
;; axioms - list of domain axioms
;; returns: a list of strata, each of which is a flat list of axioms.

(defun stratify (axioms)
  (cond (*stratify-axioms-maximally* (stratify-maximally axioms))
	(t (stratify-minimally axioms))))

(defun stratify-minimally (axioms)
  ;; R is the relation between derived predicates: R[i,j] > 0 iff
  ;; predicate i occurs in the body of an axiom defining predicate j,
  ;; and R[i,j] = 2 iff predicate i occurs negatively in the body of
  ;; an axiom defining predicate j
  (let* ((dps (collect-derived-predicates axioms))
	 (R (make-array (list (length dps) (length dps))
			:element-type 'integer :initial-element 0))
	 (dp-strata nil)
	 (axiom-strata nil))
    (dotimes (j (length dps))
      (dolist (axiom axioms)
	(if (eq (first (second axiom)) (nth j dps))
	    (stratify-minimally-mark-occurrences
	     dps (transform-to-nnf (third axiom) nil) j R))))
    (dotimes (k (length dps))
      (dotimes (i (length dps))
	(dotimes (j (length dps))
	  (if (> (min (aref R i k) (aref R k j)) 0)
	      (setf (aref R i j) (max (aref R i k) (aref R k j) (aref R i j))))
	  )))
    (dotimes (i (length dps))
      (if (> (aref R i i) 1) (error "axioms cannot be stratified")))
    (let ((rem-dps dps))
      (do ((dps-in-stratum nil nil) (stratum nil nil)) ((endp rem-dps))
	  (dolist (dp rem-dps)
	    (if (every #'(lambda (x)
			   (< (aref R (position x dps) (position dp dps)) 2))
		       rem-dps)
		(push dp dps-in-stratum)))
	  (if (>= *verbosity* 3)
	      (format t "~&next axiom stratum: ~s ~%" dps-in-stratum))
	  (if (null dps-in-stratum)
	      (error "failed to extract next stratum!"))
	  (setq rem-dps
		(remove-if #'(lambda (x) (find x dps-in-stratum)) rem-dps))
	  (dolist (axiom axioms)
	    (if (member (first (second axiom)) dps-in-stratum)
		(push (list ':derived
			    (second axiom)
			    (transform-to-nnf (third axiom) nil))
		      stratum)))
	  (setq dp-strata (append dp-strata (list dps-in-stratum)))
	  (setq axiom-strata (append axiom-strata (list stratum)))
	  ))
    (values axiom-strata dp-strata)))

(defun stratify-minimally-mark-occurrences (dps f j R)
  (cond ((or (null f) (not (listp f))) 0)
	((or (eq (first f) 'and) (eq (first f) 'or))
	 (dolist (f1 (rest f))
	   (stratify-minimally-mark-occurrences dps f1 j R)))
	((or (eq (first f) 'forall) (eq (first f) 'exists))
	 (stratify-minimally-mark-occurrences dps (third f) j R))
	((eq (first f) 'not)
	 (let* ((p (first (second f)))
		(i (position p dps)))
	   (cond (i (if (and (< (aref R i j) 2) (>= *verbosity* 3))
			(format t "~&~s occurs negatively in def of ~s~%"
				p (nth j dps)))
		    (setf (aref R i j) 2)))))
	(t (let* ((p (first f))
		  (i (position p dps)))
	     (cond (i (if (and (< (aref R i j) 1) (>= *verbosity* 3))
			  (format t "~&~s occurs in def of ~s~%"
				  p (nth j dps)))
		      (setf (aref R i j) (max (aref R i j) 1))))))
	))


(defun stratify-maximally (axioms)
  ;; here, R is a relation between axioms: R[i,j] > 0 iff the predicate
  ;; defined by axiom i occurs in the body of axiom j (i.e., axiom j
  ;; depends on axiom i), and R[i,j] = 2 iff the dependence is strict.
  ;; dp-axioms is an assoc list (name . list-of-indices), where name is
  ;; the name of a derived pred and the list contains the numbers
  ;; (indices into the axioms list) of the axioms that define it.
  (if (null axioms) nil
    (let* ((dp-axioms nil)
	   (R (make-array (list (length axioms) (length axioms))
			  :element-type 'integer :initial-element 0))
	   (axiom-strata nil))
      (cond ((>= *verbosity* 3)
	     (format t "~&stratifying axioms:~%")
	     (dotimes (k (length axioms))
	       (format t "~a. ~a~%" k (nth k axioms)))))
      ;; init the predicate->axioms map
      (dotimes (k (length axioms))
	(setq dp-axioms
	      (add-to-set-map (car (second (nth k axioms))) k dp-axioms)))
      (cond ((>= *verbosity* 3)
	     (format t "predicate->axioms map: ~a~%" dp-axioms)))
      ;; init R:
      (dotimes (j (length axioms))
	(stratify-maximally-mark-occurrences
	 dp-axioms (transform-to-nnf (third (nth j axioms)) nil) j R))
      ;; compute the transitive closure:
      (dotimes (k (length axioms))
	(dotimes (i (length axioms))
	  (dotimes (j (length axioms))
	    (if (> (min (aref R i k) (aref R k j)) 0)
		(setf (aref R i j)
		      (max (aref R i k) (aref R k j) (aref R i j))))
	    )))
      (cond ((>= *verbosity* 3)
	     (format t "final relation matrix:~%")
	     (dotimes (i (length axioms))
	       (format t "R[~a] = [" i)
	       (dotimes (j (length axioms)) (format t " ~a" (aref R i j)))
	       (format t "]~%"))))
      (dotimes (i (length axioms))
	(if (> (aref R i i) 1) (error "axioms cannot be stratified")))
      (let ((prec-adj-list nil)
	    (prec-rev-adj-list nil))
	(dotimes (i (length axioms))
	  (dotimes (j (length axioms))
	    (cond ((> (aref R i j) 0)
		   (setq prec-adj-list
			 (add-to-set-map i j prec-adj-list))
		   (setq prec-rev-adj-list
			 (add-to-set-map j i prec-rev-adj-list)))
		  )))
	(cond ((>= *verbosity* 3)
	       (format t "precedence graph adjacency list: ~a~%" prec-adj-list)
	       (format t "reverse adjacency list: ~a~%" prec-rev-adj-list)))
	(let ((strata-list
	       (top-sort-components
		(scc (length axioms) prec-adj-list prec-rev-adj-list)
		prec-adj-list)))
	  (if (>= *verbosity* 3) (format t "strata: ~a~%" strata-list))
	  (mapcar #'(lambda (stratum)
		      (mapcar #'(lambda (index) (nth index axioms)) stratum))
		  strata-list)))
      )))

(defun scc (nn adj-list rev-adj-list)
  (let ((visited (make-array (list nn)
			     :element-type 'boolean
			     :initial-element nil))
	(seq nil)
	(components nil))
    (dotimes (i nn)
      (if (not (aref visited i))
	  (setq seq (scc-first-dfs i adj-list visited seq))))
    (setq visited (make-array (list nn)
			      :element-type 'boolean
			      :initial-element nil))
    (dolist (node seq)
      (if (not (aref visited node))
	  (setq components
		(cons (scc-second-dfs node rev-adj-list visited nil)
		      components))))
    components))

(defun scc-first-dfs (node adj-list visited seq)
  (setf (aref visited node) t)
  (dolist (n (cdr (assoc node adj-list)))
    (if (not (aref visited n))
	(setq seq (scc-first-dfs n adj-list visited seq))))
  (cons node seq))

(defun scc-second-dfs (node rev-adj-list visited cset)
  (setf (aref visited node) t)
  (setq cset (cons node cset))
  (dolist (n (cdr (assoc node rev-adj-list)))
    (if (not (aref visited n))
	(setq cset (scc-second-dfs n rev-adj-list visited cset))))
  cset)

(defun top-sort-components (comps adj-list)
  (cond ((endp comps) nil)
	(t (let ((c (find-min-component comps adj-list)))
	     (if (null c)
		 (error "cannot top sort ~a with ~a" comps adj-list))
	     (cons c (top-sort-components
		      (remove c comps :test #'equal)
		      (remove-if #'(lambda (adj) (member (car adj) c))
				 adj-list)))))
	))

(defun find-min-component (comps adj-list)
  (cond ((endp comps) nil)
	((every #'(lambda (adj)
		    (or (member (car adj) (car comps))
			(null (intersection (car comps) (cdr adj)))))
		adj-list)
	 (car comps))
	(t (find-min-component (cdr comps) adj-list))))

(defun stratify-maximally-mark-occurrences (dp-axioms form j R)
  (cond ((or (null form) (not (listp form))) 0)
	((or (eq (first form) 'and) (eq (first form) 'or))
	 (dolist (f1 (rest form))
	   (stratify-maximally-mark-occurrences dp-axioms f1 j R)))
	((or (eq (first form) 'forall) (eq (first form) 'exists))
	 (stratify-maximally-mark-occurrences dp-axioms (third form) j R))
	((eq (first form) 'not)
	 (let* ((p (first (second form))) ;; predicate
		(i-list (cdr (assoc p dp-axioms))))
	   (dolist (i i-list)
	     (if (and (< (aref R i j) 2) (>= *verbosity* 3))
		 (format t "~&axiom ~a depends strictly on ~a (~a)~%" j i p))
	     (setf (aref R i j) 2))))
	(t (let* ((p (first form))
		  (i-list (cdr (assoc p dp-axioms))))
	     (dolist (i i-list)
	       (if (and (< (aref R i j) 1) (>= *verbosity* 3))
		   (format t "~&axiom ~a depends on ~a (~a)~%" j i p))
	       (setf (aref R i j) (max (aref R i j) 1)))))
	))

;;;;
;; PDDL3 constraint evaluation

;; Evaluate a PDDL3 constraint formula on a state sequence.
;; form - the formula
;; seq - the state sequence
;; types - list of type declarations (same as in eval-formula)
;; objects - list of object declarations (same as in eval-formula)
;; returns: a list (val def vios), where
;;   - val is the formula's value (t or nil),
;;   - def denotes if the formula's value is well-defined (t or nil), and
;;   - vios is the multiset of violated preferences, represented as an
;;     assoc list from preference name to number; anonymous preferences
;;     are counted under the name 'nil.

(defun eval-constraint-formula
  (form seq types objects &key (accept-preferences t))
  (cond
   ((not (listp form))
    (error "ill-formed constraint formula: ~s" form))
   ;; empty list is considered an empty conjunction, and therefore true
   ((null form) (list t t nil))
   ;; conjunction
   ((eq (car form) 'and)
    (let ((ok t)
	  (val t)
	  (vios nil))
      (dolist (f1 (cdr form))
	(let ((v1 (eval-constraint-formula
		   f1 seq types objects
		   :accept-preferences accept-preferences)))
	  (setq val (and val (car v1)))
	  (setq ok (and ok (cadr v1)))
	  (setq vios (multiset-add vios (caddr v1)))
	  ))
      (list val ok vios)))
   ;; universal quantifier
   ((eq (car form) 'forall)
    (if (not (= (length form) 3))
	(error "ill-formed constraint formula: ~s" form))
    (let ((vars (parse-typed-list '() (cadr form) 'object)))
      (eval-constraint-formula
       (cons 'and (instantiate (caddr form) nil vars types objects))
       seq types objects :accept-preferences accept-preferences)))
   ;; preference
   ((eq (car form) 'preference)
    (if (not accept-preferences)
	(error "preference ~s not allowed in this context" form))
    (if (or (< (length form) 2) (> (length form) 3))
	(error "ill-formed constraint formula: ~s" form))
    (let ((pname (if (= (length form) 3) (second form) nil))
	  (pform (if (= (length form) 3) (third form) (second form))))
      (let ((v1 (eval-constraint-formula
		 pform seq types objects :accept-preferences nil)))
	(cond ((null (cadr v1)) ;; result not defined
	       (list nil nil nil))
	      ((null (car v1)) ;; result defined, preference false
	       (if (>= *verbosity* 2)
		   (format t "~&preference ~a ~a violated~%" pname pform))
	       (list t t (list (cons pname 1))))
	      (t (list t t nil))))))
   ;; modal op sometime
   ((eq (car form) 'sometime)
    (if (not (= (length form) 2))
	(error "ill-formed constraint formula: ~s" form))
    (check-sometime-constraint (second form) seq types objects))
   ;; modal op always
   ((eq (car form) 'always)
    (if (not (= (length form) 2))
	(error "ill-formed constraint formula: ~s" form))
    (check-always-constraint (second form) seq types objects))
   ;; modal op at-most-once
   ((eq (car form) 'at-most-once)
    (if (not (= (length form) 2))
	(error "ill-formed constraint formula: ~s" form))
    (check-at-most-once-constraint (second form) seq types objects))
   ;; modal op sometime-before
   ((eq (car form) 'sometime-before)
    (if (not (= (length form) 3))
	(error "ill-formed constraint formula: ~s" form))
    (check-sometime-before-constraint
     (second form) (third form) seq types objects))
   ;; modal op sometime-after
   ((eq (car form) 'sometime-after)
    (if (not (= (length form) 3))
	(error "ill-formed constraint formula: ~s" form))
    (check-sometime-after-constraint
     (second form) (third form) seq types objects))
   ;; "at end"
   ((and (>= (length form) 2) (eq (car form) 'at) (eq (cadr form) 'end))
    (if (not (= (length form) 3))
	(error "ill-formed constraint formula: ~s" form))
    (let ((v1 (eval-formula (third form) nil (car (last seq)) types objects)))
      (list (car v1) (cadr v1) nil)))
   ;; unrecognised constraint
   (t (error "unrecognised constraint formula: ~s" form))
   ))

;; Evaluate a formula on each state in a sequence.
;; Returns a list (vals def), where
;; - vals is a list truth (t/nil) values (same length as the state sequence)
;; - def (t/nil) denotes whether the formula is defined on every state in
;;   the sequence.

(defun eval-formula-on-sequence (form seq types objects)
  (reduce #'(lambda (res1 resn)
	      (list (cons (car res1) (car resn))
		    (and (cadr res1) (cadr resn))))
	  (mapcar #'(lambda (state)
		      (eval-formula form nil state types objects))
		  seq)
	  :initial-value '(() t)
	  :from-end t))

;; Constraint-checking functions for each modal op.
;; These all return a list (val def), where val is the value of the
;; constraint (t/nil) and def is nil iff the constraint is undefined
;; (that is, if evaluation of a state formula within it returns an
;; undefined result on any state).

(defun check-sometime-constraint (form seq types objects)
  (when (>= *verbosity* 3)
    (format t "~&checking (sometime ~a)~%" form))
  (let ((res (eval-formula-on-sequence form seq types objects)))
    (when (>= *verbosity* 3)
      (format t "~a : ~a ~%" form (if (cadr res) (car res) "not defined")))
    (list (some #'identity (car res)) (cadr res))))

(defun check-always-constraint (form seq types objects)
  (when (>= *verbosity* 3)
    (format t "~&checking (always ~a)~%" form))
  (let ((res (eval-formula-on-sequence form seq types objects)))
    (when (>= *verbosity* 3)
      (format t "~a : ~a ~%" form (if (cadr res) (car res) "not defined")))
    (list (every #'identity (car res)) (cadr res))))

(defun check-at-most-once-constraint (form seq types objects)
  (when (>= *verbosity* 3)
    (format t "~&checking (at-most-once ~a)~%" form))
  (let ((res (eval-formula-on-sequence form seq types objects)))
    (when (>= *verbosity* 3)
      (format t "~a : ~a ~%" form (if (cadr res) (car res) "not defined")))
    (list (<= (count-transitions (car res)) 1) (cadr res))))

;; Count the number of times that the value changes from false (nil)
;; to true (non-nil) in the value sequence vals.
(defun count-transitions (vals)
  (if (null vals) 0
    (cdr (reduce #'(lambda (prev next)
		     (cons next (if (and (not (car prev)) next)
				    (+ (cdr prev) 1)
				  (cdr prev))))
		 vals
		 :initial-value (cons nil 0)))))

;; (sometime-before alpha beta) - alpha is the trigger, beta is the
;; condition! that is, if ever alpha, then we must have beta in some
;; (strictly) earlier state.
(defun check-sometime-before-constraint (alpha beta seq types objects)
  (when (>= *verbosity* 3)
    (format t "~&checking (sometime-before ~a ~a)~%" alpha beta))
  (let ((ares (eval-formula-on-sequence alpha seq types objects))
	(bres (eval-formula-on-sequence beta seq types objects)))
    (when (>= *verbosity* 3)
      (format t "~a : ~a ~%" alpha (if (cadr ares) (car ares) "not defined"))
      (format t "~a : ~a ~%" beta (if (cadr bres) (car bres) "not defined")))
    (list
     (do ((avals (car ares) (cdr avals))
	  (bvals (car bres) (cdr bvals))
	  (beta-was-true nil))
	 ;; if we get to the end of the trigger sequence without
	 ;; violating the constraint, then it is true
	 ((endp avals) t)
       ;; if alpha is true and beta has not previously been true,
       ;; the constraint is violated
       (if (and (car avals) (not beta-was-true)) (return nil))
       ;; remember if beta has ever been true
       (if (car bvals) (setq beta-was-true t)))
     (and (cadr ares) (cadr bres)))))

;; (sometime-after alpha beta) - alpha is the trigger, beta is the
;; condition; that is, whenever alpha, we must have beta in some
;; (non-strictly) later state.
(defun check-sometime-after-constraint (alpha beta seq types objects)
  (when (>= *verbosity* 3)
    (format t "~&checking (sometime-after ~a ~a)~%" alpha beta))
  (let ((ares (eval-formula-on-sequence alpha seq types objects))
	(bres (eval-formula-on-sequence beta seq types objects)))
    (when (>= *verbosity* 3)
      (format t "~a : ~a ~%" alpha (if (cadr ares) (car ares) "not defined"))
      (format t "~a : ~a ~%" beta (if (cadr bres) (car bres) "not defined")))
    (list 
     (do ((avals (car ares) (cdr avals))
	  (bvals (car bres) (cdr bvals))
	  (beta-must-be-true nil))
	 ;; at the end of the trigger sequence, the constraint is
	 ;; satisfied if we have no future beta obligation:
	 ((endp avals) (not beta-must-be-true))
       ;; if alpha is true, mark a future beta obligation
       (if (car avals) (setq beta-must-be-true t))
       ;; if beta is true, clear future obligation (note the order
       ;; of these two if-statements; if alpha and beta are both
       ;; true, there will be no outstanding obligation)
       (if (car bvals) (setq beta-must-be-true nil)))
     (and (cadr ares) (cadr bres)))))


;;;;
;; Formula rewrite utilities.

;; Transform a formula to NNF by pushing negations down:
;; f - the formula
;; push-neg - are we in the scope of a negation? (t/nil)
;; returns: the transformed formula

(defun transform-to-nnf (f push-neg)
  (cond
   ((not (listp f)) (error "ill-formed formula: ~s" f))
   ((null f) f)
   ((eq (car f) 'and)
    (let ((fs (mapflat #'(lambda (f1)
			   (let ((nf1 (transform-to-nnf f1 push-neg)))
			     (cond ((eq (car nf1) 'and) (cdr nf1))
				   (t (list nf1)))))
		       (rest f))))
      (cond (push-neg (cons 'or fs))
	    (t (cons 'and fs)))))
   ((eq (car f) 'or)
    (let ((fs (mapcar #'(lambda (f1) (transform-to-nnf f1 push-neg))
		      (rest f))))
      (cond (push-neg (cons 'and fs))
	    (t (cons 'or fs)))))
   ((eq (car f) 'not)
    (if (not (= (length f) 2)) (error "ill-formed formula: ~s" f))
    (transform-to-nnf (second f) (not push-neg)))
   ((eq (car f) 'imply)
    (if (not (= (length f) 3)) (error "ill-formed formula: ~s" f))
    (let ((f1 (transform-to-nnf (second f) (not push-neg)))
	  (f2 (transform-to-nnf (third f) push-neg)))
      (cond (push-neg (list 'and f1 f2))
	    (t (list 'or f1 f2)))))
   ((eq (car f) 'forall)
    (if (not (= (length f) 3)) (error "ill-formed formula: ~s" f))
    (let ((f1 (transform-to-nnf (third f) push-neg)))
      (cond (push-neg (list 'exists (second f) f1))
	    (t (list 'forall (second f) f1)))))
   ((eq (car f) 'exists)
    (if (not (= (length f) 3)) (error "ill-formed formula: ~s" f))
    (let ((f1 (transform-to-nnf (third f) push-neg)))
      (cond (push-neg (list 'forall (second f) f1))
	    (t (list 'exists (second f) f1)))))
   ((eq (car f) 'when)
    (when push-neg
      (error "transform-to-nnf: conditional effect under negation"))
    (list 'when (transform-to-nnf (second f) nil) (third f)))
   ;; anything else is an atomic formula
   (push-neg (list 'not f))
   (t f)))

;; Transform a formula to DNF.
;; f - the formula
;; push-neg - are we in the scope of a negation? (t/nil)
;; returns: the list of disjuncts (without leading 'or)

(defun transform-to-dnf (f push-neg)
  (cond
   ((or (null f) (not (listp f)))
    (error "ill-formed formula: ~s" f))
   ((eq (car f) 'and)
    (if (endp (cdr f)) (error "ill-formed formula: ~s" f))
    (let ((ds (mapcar #'(lambda (f1) (transform-to-dnf f1 push-neg))
		      (rest f))))
      (cond (push-neg (reduce #'append ds))
	    (t (multiply-out ds)))))
   ((eq (car f) 'or)
    (if (endp (cdr f)) (error "ill-formed formula: ~s" f))
    (let ((ds (mapcar #'(lambda (f1) (transform-to-dnf f1 push-neg))
		      (rest f))))
      (cond (push-neg (multiply-out ds))
	    (t (reduce #'append ds)))))
   ((eq (car f) 'not)
    (if (not (= (length f) 2)) (error "ill-formed formula: ~s" f))
    (transform-to-dnf (second f) (not push-neg)))
   ((eq (car f) 'imply)
    (if (not (= (length f) 3)) (error "ill-formed formula: ~s" f))
    (let ((d1 (transform-to-dnf (second f) (not push-neg)))
	  (d2 (transform-to-dnf (third f) push-neg)))
      (cond (push-neg (multiply-out (list d1 d2)))
	    (t (append d1 d2)))))
   ((eq (car f) 'forall)
    (error "cannot transform ~s to DNF" f))
   ((eq (car f) 'exists)
    (error "cannot transform ~s to DNF" f))
   ;; anything else is an atomic formula
   (push-neg (list (list 'not f)))
   (t (list f))))

;; Transform a conjunction of disjunctions to DNF by multiplying it out.

(defun multiply-out (ds)
  (cond ((endp (cdr ds)) (car ds))
	(t (mapflat
	    #'(lambda (c2)
		(mapcar #'(lambda (c1) (merge-conjunctions c1 c2))
			(car ds)))
	    (multiply-out (cdr ds))))))


;; Merge two conjunctions/disjunctions (one or both may be nil)
;; Note: An empty conjunction (nil) means "constant true"; constant
;; false is represented by the symbol :false. An empty disjunction,
;; on the other hand, means constant false, and constant true is
;; is represented by the symbol :true.

(defun merge-conjunctions (c1 c2)
  (cond	((or (eq c1 ':false) (eq c2 ':false)) ':false)
	((not (listp c1))
	 (error "ill-formed formula (conjunction) ~a" c1))
	((not (listp c2))
	 (error "ill-formed formula (conjunction) ~a" c2))
	((null c2) c1)
	((null c1) c2)
	((eq (car c1) 'and)
	 (cond ((eq (car c2) 'and)
		(cons 'and (append (cdr c1) (cdr c2))))
	       (t (cons 'and (append (cdr c1) (list c2))))))
	((eq (car c2) 'and)
	 (cons 'and (cons c1 (cdr c2))))
	(t (list 'and c1 c2))))

(defun merge-disjunctions (d1 d2)
  (cond ((or (eq d1 ':true) (eq d2 ':true)) ':true)
	((not (listp d1))
	 (error "ill-formed formula (disjunction) ~a" d1))
	((not (listp d2))
	 (error "ill-formed formula (disjunction) ~a" d2))
	((null d2) d1)
	((null d1) d2)
	((eq (car d1) 'or)
	 (cond ((eq (car d2) 'or)
		(cons 'or (append (cdr d1) (cdr d2))))
	       (t (cons 'or (append (cdr d1) (list d2))))))
	((eq (car d2) 'or)
	 (cons 'or (cons d1 (cdr d2))))
	(t (list 'or d1 d2))))

;; Find the free variables in a formula or term:

(defun free-variables (exp)
  (cond ((null exp) nil)
	;; if the expression is not a list, it's a variable or constant
	((not (listp exp))
	 (cond ((variable-p exp) (list exp))
	       (t nil)))
	;; quantifier: remove bound variables
	((or (eq (first exp) 'forall)
	     (eq (first exp) 'exists))
	 (if (not (= (length exp) 3)) (error "ill-formed formula: ~s" exp))
	 (let ((vars (parse-typed-list '() (second exp) 'object)))
	   (remove-if #'(lambda (x) (find x vars :key #'car)) 
		      (free-variables (third exp)))))
	;; anything else: skip first element (connective or predicate) and
	;; recursively collect free variables in all other elements
	(t (mapflat #'free-variables (rest exp)))
	))

;; Convert a STRIPS formula into lists of positive and negative atoms,
;; returning them by multiple-value (positive atoms list first). The
;; function works both on normal (precondition/goal) formulas and
;; effect formulas. If input is not a simple STRIPS formula, an error
;; is triggered.

(defun formula-to-split-lists (f)
  (cond ((null f) (values nil nil))
	((not (listp f)) (error "ill-formed formula: ~s" f))
	((member (car f) '(or imply forall exists when))
	 (error "not a STRIPS formula: ~s" f))
	((eq (car f) 'and)
	 (let ((poslist nil)
	       (neglist nil))
	   (dolist (f1 (cdr f))
	     (multiple-value-bind
	      (pos neg) (formula-to-split-lists f1)
	      (setq poslist (append poslist pos))
	      (setq neglist (append neglist neg))))
	   (values poslist neglist)))
	((eq (car f) 'not)
	 (values nil (cdr f)))
	(t (values (list f) nil))
	))

;;;;
;; Type checking
;;
;; Note: In all functions below, the 'where' argument is used only to
;; print more informative error messages.

;; Check if a given object can be passed where an object of type t2
;; is expected.

(defun object-can-substitute-for-type (o t2 types objects where)
  (let ((otl (assoc-all o objects)))
    (cond
     ((null otl)
      (format t "~&~s: undefined object name ~s~%" where o) nil)
     ;; if multityping is enabled, the object can have several type
     ;; declarations; it's a match if any of the declared types can
     ;; substitute for t2.
     (t (some #'(lambda (ot)
		  (type-can-substitute-for-type ot t2 types where))
	      otl))
     )))

;; Check if an object (constant or variable) of type t1 can be passed
;; where an object of type t2 is expected.

(defun type-can-substitute-for-type (t1 t2 types where)
  (cond
   ;; If t1 is a list, it must be of the form (either t1-1 t1-2 .. t1-n).
   ;; In this case, there are two interpretations:
   ;; - if *either-in-declarations-measn-and* is true, substitution holds
   ;;  iff some of types t1-1 .. t1-n can substitute for t2
   ;; - if *either-in-declarations-means-and* is false, substitution holds
   ;;  iff all of types t1-1 .. t1-n can substitute for t2
   ((listp t1)
    (cond
     ((not (eq (car t1) 'either))
      (format t "~&~s: ill-formed type ~s~%" where t1) nil)
     (*either-in-declarations-means-and*
      (some #'(lambda (tt) (type-can-substitute-for-type tt t2 types where))
	    (cdr t1)))
     (t (every #'(lambda (tt) (type-can-substitute-for-type tt t2 types where))
	       (cdr t1)))))
   ;; If t2 is a list, it must be of the form (either t1-1 t1-2 .. t1-n).
   ;; In this case, substitution holds if t1 can substitute for any of
   ;; the types t1-1 .. t1-n
   ((listp t2)
    (cond
     ((not (eq (car t2) 'either))
      (format t "~&~s: ill-formed type ~s~%" where t2) nil)
     (t (some #'(lambda (tt) (type-can-substitute-for-type t1 tt types where))
	      (cdr t2)))))
   ;; Both t1 and t2 are atomic.
   ;; Note: Types 'object' and 'number' are implicitly defined, and
   ;; do not have supertypes. Their implicit definitions cannot be
   ;; be overridden by explicit type definitions. A type name that
   ;; appears only "on the right" (i.e., as the supertype in a type
   ;; declaration) is implicitly defined as a subtype of 'object'.
   (t (let ((super-types-list
	     (cond
	      ((member t1 '(object number)) (list nil))
	      ((and (null (assoc t1 types)) (rassoc t1 types))
	       (list 'object))
	      (t (assoc-all t1 types)))))
	(cond
	 ((null super-types-list)
	  (format t "~&~s: undefined type name ~s~%" where t1) nil)
	 ;; If t1 equals t2, it can obviously substitute for t2
	 ((eq t1 t2) t)
	 ;; t1 can have multiple type declarations (if the *multityping*
	 ;; option is set to true), in which case t1 can substitute for
	 ;; t2 iff at least one of it's declared (super)types can.
	 (t (some #'(lambda (super-type)
		      ;; we can only proceed up the type hierarchy if
		      ;; t1 has a supertype
		      (cond (super-type
			     (type-can-substitute-for-type
			      super-type t2 types where))
			    (t nil)))
		  super-types-list))
	 )))
   ))

;; Return the most specific of two types, or nil if neither is a subtype
;; of the other.

(defun most-specific-type (t1 t2 types)
  (cond ((type-can-substitute-for-type t1 t2 types nil) t1)
	((type-can-substitute-for-type t2 t1 types nil) t2)
	(t nil)))

;; Check a list of argument types against a list of parameter types.
;; Excess arguments are ignored, but too few will cause the function to
;; return nil.
;; Returns: t if each argument type matches (i.e., can substitute for)
;; the corresponding parameter type, nil otherwise.

(defun type-check-arguments (args params types where)
  (let ((ok t))
    (dotimes (i (length params))
      (cond
       ((null (nth i args))
	(setq ok nil))
       ((not (type-can-substitute-for-type
	      (nth i args) (cdr (nth i params)) types where))
	(format t "~&~s: argument ~s is incorrectly typed for ~s"
		where (nth i args) (nth i params))
	(setq ok nil))))
    ok))

;; Check a term, and return the term's type.
;; term - the term.
;; context - an assoc list of (var . type) pairs for variables declared
;;   in the current context.
;; predicates - list of domain predicates.
;; functions - list of domain functions.
;; types - list of domain types.
;; objects - list of domain constants.
;; where - something that indicates the context in which the term appears
;;   (used only for printing error messages).
;; :is-metric (t/nil) - is this the :metric expression? The built-in
;;   function (is-violated <pref name>) can only be used in the metric.
;; returns: the type of the term, if the term itself is type correct;
;;   nil otherwise.

(defun type-check-term
  (term context predicates functions types objects where
	&key (is-metric nil))
  (cond
   ((numberp term) 'number)
   ((variable-p term)
    (let ((decl (assoc term context)))
      (cond
       ((null decl)
	(format t "~&~s: undefined variable ~s~%" where term)
	nil)
       (t (cdr decl)))))
   ((symbolp term)
    (let ((decl (assoc term objects)))
      (cond
       ((null decl)
	(format t "~&~s: undeclared constant ~s~%" where term))
       (t (cdr decl)))))
   ((not (listp term))
    (error "term ~s is not a number, symbol or list" term))
   ;; n-ary numeric operators
   ((member (first term) '(+ *))
    (if (not (>= (length term) 3))
	(format t "~&~s: too few arguments for ~s~%" where term))
    (let ((args (type-check-term-list
		 (rest term) context predicates functions types objects where
		 :is-metric is-metric)))
      (cond
       ((and (every #'(lambda (tt) tt) args)
	     (>= (length term) 3))
	'number)
       (t nil))))
   ;; binary numeric operators
   ((member (car term) '(- / :min :max))
    (if (not (= (length term) 3))
	(format t "~&~s: incorrect number of arguments for ~s~%" where term))
    (let ((args (type-check-term-list
		 (rest term) context predicates functions types objects where
		 :is-metric is-metric)))
      (cond
       ((and (every #'(lambda (tt) tt) args) (== (length term) 3)) 'number)
       (t nil))))
   ;; zero-ary function total-time is always defined
   ((eq (car term) 'total-time)
    (cond ((not (= (length (cdr term)) 0))
	   (format t "~&~s: incorrect number of arguments ~s for ~s~%"
		   where term fun) nil)
	  (t 'number)))
   ;; unary "is-violated" function is always defined (but can only appear
   ;; in the :metric)
   ((eq (car term) 'is-violated)
    (cond ((not is-metric)
	   (format t "~&~s: ~a not allowed in this context~%" where term)
	   nil)
	  ((not (= (length (cdr term)) 1))
	   (format t "~&~s: incorrect number of arguments ~s for ~s~%"
		   where term fun)
	   nil)
	  ((not (symbolp (cadr term)))
	   (format t "~&~s: invalid preference name ~a in ~a~%"
		   where (cadr term) term)
	   nil)
	  (t 'number)))
   ;; anything else is a fluent expression
   (t (let ((fun (assoc (first term) functions :key #'car))
	    (args (type-check-term-list
		   (rest term) context predicates functions types objects
		   where :is-metric is-metric)))
	(cond
	 ((null fun)
	  (format t "~&~s: undefined function ~s~%" where term) nil)
	 ((not (= (length (car fun)) (length term)))
	  (format t "~&~s: incorrect number of arguments ~s for ~s~%"
		  where term fun) nil)
	 ((type-check-arguments args (rest (car fun)) types (list where term))
	  (cdr fun))
	 (t nil)
	 )))
   ))

;; Check a list of terms and return the list of results (term type or nil).

(defun type-check-term-list
  (tlist context predicates functions types objects where
	 &key (is-metric nil))
  (mapcar #'(lambda (term)
	      (type-check-term
	       term context predicates functions types objects where
	       :is-metric is-metric))
	  tlist))

;; Check a formula.
;; f - the (PDDL) formula.
;; context - an assoc list of (var . type) pairs for variables declared
;;   in the current context.
;; predicates - list of domain predicates.
;; functions - list of domain functions.
;; types - list of domain types.
;; objects - list of domain constants.
;; where - something that indicates the context in which the term appears
;;   (used only for printing error messages).
;; :accept-preferences (t/nil) - is the (preference ..) construct allowed
;;   in the current context?
;; returns: t if the formula is type correct, nil otherwise.

(defun type-check-formula
  (f context predicates functions types objects where
     &key (accept-preferences nil))
  (cond
   ;; a formula cannot be a non-list (i.e. symbol or number)
   ((not (listp f))
    (format t "~&~s: ill-formed constraint ~a" where f)
    nil)
   ;; an empty list is accepted as a syntactically correct formula
   ((null f) t)
   ;; logical connectives (note: handles n-ary and/or)
   ((member (car f) '(and or))
    (type-check-formula-list
     (cdr f) context predicates functions types objects where
     :accept-preferences (and accept-preferences (eq (car f) 'and))))
   ((eq (car f) 'not)
    (if (not (= (length f) 2))
	(format t "~&~s: ill-formed formula: ~s~%" where f))
    (and (type-check-formula-list
	  (rest f) context predicates functions types objects where
	  :accept-preferences nil)
	 (= (length f) 2)))
   ((eq (car f) 'imply)
    (if (not (= (length f) 3))
	(format t "~&~s: ill-formed formula: ~s~%" where f))
    (and (type-check-formula-list
	  (rest f) context predicates functions types objects where
	  :accept-preferences nil)
	 (= (length f) 3)))
   ;; quantifiers
   ((member (car f) '(forall exists))
    (cond
     ((= (length f) 3)
      (let ((qcontext
	     (append (parse-typed-list '() (second f) 'object) context)))
	(type-check-formula
	 (third f) qcontext predicates functions types objects where
	 :accept-preferences (and accept-preferences (eq (car f) 'forall)))))
     (t (format t "~&~s: ill-formed formula ~s~%" where f) nil)
     ))
   ;; equality
   ((eq (car f) '=)
    (if (not (= (length f) 3))
	(format t "~&~s: ill-formed formula ~s~%" where f))
    (and
     (not (some #'null (type-check-term-list
			(rest f) context predicates functions types objects
			where)))
     (= (length f) 3)))
   ;; numeric comparisons
   ((member (car f) '(< > <= >=))
    (if (not (= (length f) 3))
	(format t "~&~s: ill-formed formula ~s~%" where f))
    (and
     (every #'(lambda (tt) (eq tt 'number))
	    (type-check-term-list (rest f) context predicates functions
				  types objects where))
     (= (length f) 3)))
   ;; preference
   ((eq (car f) 'preference)
    (cond ((not accept-preferences)
	   (format t "~&~s: ~a not accepted in this context~%" where f)
	   nil)
	  ((= (length f) 3)
	   (cond ((not (symbolp (second f)))
		  (format t "~&~s: invalid preference name ~a in ~a~%"
			  where (second f) f)
		  nil)
		 (t (type-check-formula (third f) context predicates
					functions types objects where
					:accept-preferences nil))))
	  ((= (length f) 2)
	   (type-check-formula (third f) context predicates
			       functions types objects where
			       :accept-preferences nil))
	  (t (format t "~s: ill-formed preference ~a" where f))))
   ;; typename used as a unary predicate
   ((and *type-names-are-predicates*
	 (or (assoc (first f) types)
	     (rassoc (first f) types))
	 (= (length (rest f)) 1))
    (cond ;; A typename-as-predicate accepts any argument, but we still
	  ;; have to check that the argument (which may be a complex
	  ;; term) is well-defined.
	  ((null (type-check-term (second f) context predicates functions
			     types objects where))
	   nil)
	  (t t)))
   ;; finally, an atom: but the atom may have complex argument terms
   (t (let ((pred (assoc (first f) predicates))
	    (args (type-check-term-list (rest f) context predicates functions
					types objects where)))
	(cond
	 ((null pred)
	  (format t "~&~s: undefined predicate ~s~%" where f) nil)
	 ((not (= (length pred) (length f)))
	  (format t "~&~s: incorrect number of arguments ~s for ~s~%"
		  where f pred) nil)
	 ((some #'null args) nil)
	 (t (type-check-arguments args (rest pred) types (list where f)))
	 )))
   ))

;; Check a list of formulas, returning t iff all of them are type correct.

(defun type-check-formula-list
  (flist context predicates functions types objects where
	 &key (accept-preferences nil))
  (let ((ok t))
    (dolist (f flist)
      (let ((ok1 (type-check-formula
		  f context predicates functions types objects where
		  :accept-preferences accept-preferences)))
	(setq ok (and ok ok1))))
    ok))

;; Check an effect formula.
;; eff - the effect formula.
;; context - an assoc list of (var . type) pairs for variables declared
;;   in the current context.
;; predicates - list of domain predicates.
;; functions - list of domain functions.
;; types - list of domain types.
;; objects - list of domain constants.
;; where - something that indicates the context in which the term appears
;;   (used only for printing error messages).
;; returns: t if the effect formula is type correct, nil otherwise.

(defun type-check-effect (eff context predicates functions types objects where)
  (cond
   ;; an effect must be a non-empty list
   ((or (null eff) (not (listp eff)))
    (format t "~&~s: ill-formed effect ~s~%" where eff)
    nil)
   ;; conjunction
   ((eq (first eff) 'and)
    (type-check-effect-list (rest eff) context predicates functions
		       types objects where))
   ;; quantified
   ((eq (car eff) 'forall)
    (cond
     ((= (length eff) 3)
      (let ((qcontext
	     (append (parse-typed-list '() (second eff) 'object) context)))
	;; note: this will allow forall nested within forall (or, indeed,
	;; within a conditional effect), which is not correct
	(type-check-effect (third eff) qcontext predicates functions
			   types objects where)))
     (t (format t "~&~s: ill-formed effect ~s~%" where eff) nil)
     ))
   ;; conditional
   ((eq (car eff) 'when)
    (cond
     ((= (length eff) 3)
      ;; note: this will allow nesting of when's, forall's and and's
      (and (type-check-formula
	    (second eff) context predicates functions types objects where
	    :accept-preferences nil)
	   (type-check-effect (third eff) context predicates functions
			      types objects where)))
     (t (format t "~&~s: ill-formed effect ~s~%" where eff) nil)
     ))
   ;; negated
   ((eq (car eff) 'not)
    (cond
     ((= (length eff) 2)
      (type-check-atomic-effect (second eff) context predicates functions
				types objects where))
     (t (format t "~&~s: ill-formed effect ~s~%" where eff) nil)
     ))
   ;; fluent modification
   ((member (first eff) '(assign increase decrease))
    (if (not (= (length eff) 3))
	(format t "~&~s: ill-formed fluent effect ~s~%" where eff))
    (let ((fun (assoc (first (second eff)) functions :key #'car))
	  (args (type-check-term-list (rest (second eff)) context
				      predicates functions types objects where))
	  (lval (cond
		 ((eq (third eff) 'undefined) 'undefined)
		 (t (type-check-term (third eff) context predicates functions
				     types objects where)))))
      (cond
       ((null fun)
	(format t "~&~s: undefined function ~s~%" where (second eff)) nil)
       ((not (= (length (rest (car fun))) (length args)))
	(format t "~&~s: incorrect number of arguments ~s for ~s~%"
		where eff fun)
	nil)
       ((not (type-check-arguments args (rest (car fun))
				   types (list where eff)))
	nil)
       ((null lval) nil)
       ((not (or (and (eq lval 'undefined) (not (eq (cdr fun) 'number)))
		 (type-can-substitute-for-type lval (cdr fun) types where)))
	(format t "~&~s: incorrectly typed assignment ~s to ~s in ~s"
		where lval fun eff)
	nil)
       (t t))))
   ;; if none of the above, it should be a positive atomic effect
   (t (type-check-atomic-effect eff context predicates functions
			   types objects where))
   ))

;; Subfunction of type-check-effect (used in two places within that function).

(defun type-check-atomic-effect
  (eff context predicates functions types objects where)
  (let ((pred (assoc (first eff) predicates))
	(args (type-check-term-list (rest eff) context predicates functions
				    types objects where)))
    (cond
     ((null pred)
      (format t "~&~s: undefined predicate ~s~%" where eff) nil)
     ((not (= (length pred) (length eff)))
      (format t "~&~s: incorrect number of arguments ~s for ~s~%"
	      where eff pred) nil)
     (t (type-check-arguments args (rest pred) types (list where eff)))
     )))

;; Check a list of effect formulas, returning t only if all are type correct.

(defun type-check-effect-list
  (elist context predicates functions types objects where)
  (let ((ok t))
    (dolist (e (cdr elist))
      (let ((ok1 (type-check-effect e context predicates functions
				    types objects where)))
	(setq ok (and ok ok1))))
    ok))

;; Check an action.
;; action - a pair (name . definition), where definition is a parsed
;;   struct (an assoc list of (keyword . value) pairs).
;; predicates - list of domain predicates.
;; functions - list of domain functions.
;; types - list of domain types.
;; objects - list of domain constants.
;; returns: t if the action is type correct, nil otherwise.

(defun type-check-action (action predicates functions types objects)
  (let ((params (cdr (assoc ':parameters (cdr action))))
	(prec (cdr (assoc ':precondition (cdr action))))
	(effs (cdr (assoc ':effect (cdr action)))))
    (and (type-check-formula prec params predicates functions types objects
			     (list ':precondition (car action))
			     :accept-preferences t)
	 (type-check-effect effs params predicates functions types objects
			    (list ':effect (car action))))
    ))

;; Check an axiom.
;; axiom - the PDDL axiom (unmodified).
;; predicates - list of domain predicates.
;; functions - list of domain functions.
;; types - list of domain types.
;; objects - list of domain constants.
;; returns: t if the axiom is type correct, nil otherwise.

(defun type-check-axiom (axiom predicates functions types objects)
  (cond
   ((< (length axiom) 2)
    (format t "~&ill-formed axiom: ~s~%" axiom) nil)
   (t (let ((pred (assoc (first (second axiom)) predicates))
	    (params (axiom-parameters axiom types))
	    (args (mapcar #'car (parse-typed-list
				 nil (rest (second axiom)) 'object))))
	(cond
	 ((null pred)
	  (format t "~&(:DERIVED ~s ...): undefined predicate in head~%"
		  (second axiom))
	  nil)
	 ((not (= (length (rest pred)) (length args)))
	  (format t "~&(:DERIVED ~s ...): incorrect number of arguments for ~s~%"
		  (second axiom) pred)
	  nil)
	 (t (and (type-check-arguments
		  (type-check-term-list args params
					predicates functions types objects
					(list ':derived (second axiom)))
		  (rest pred) types (list ':derived (second axiom)))
		 (type-check-formula (third axiom) params
				     predicates functions types objects
				     (list ':derived (second axiom))
				     :accept-preferences nil)))
	 )))
   ))


;; Check a PDDL3 constraint formula.

(defun type-check-constraint-formula
  (f context predicates functions types objects where
     &key (accept-preferences t))
  (cond ((not (listp f))
	 (format t "~&~s: ill-formed constraint ~s" where f)
	 nil)
	;; an empty list is accepted
	((null f) t)
	;; conjunction
	((eq (car f) 'and)
	 (let ((ok t))
	   (dolist (f1 (cdr f))
	     (let ((ok1 (type-check-constraint-formula
			 f1 context predicates functions types objects where)))
	       (setq ok (and ok ok1))))
	   ok))
	;; universal quantification
	((eq (car f) 'forall)
	 (cond
	  ((= (length f) 3)
	   (let ((qcontext
		  (append (parse-typed-list '() (second f) 'object) context)))
	     (type-check-constraint-formula
	      (third f) qcontext predicates functions types objects where)))
	  (t (format t "~&~s: ill-formed constraint ~s~%" where f)
	     nil)
	  ))
	;; unary modal operators
	((member (car f) '(sometime always at-most-once))
	 (cond ((= (length f) 2)
		(type-check-formula (second f) context predicates
				    functions types objects where
				    :accept-preferences nil))
	       (t (format t "~&~s: ill-formed constraint ~s~%" where f) nil)
	       ))
	;; binary modal operators
	((member (car f) '(sometime-before sometime-after))
	 (cond ((= (length f) 3)
		(and (type-check-formula (second f) context predicates
					 functions types objects where
					 :accept-preferences nil)
		     (type-check-formula (third f) context predicates
					 functions types objects where
					 :accept-preferences nil)))
	       (t (format t "~&~s: ill-formed constraint ~s~%" where f) nil)
	       ))
	;; "at end" modality
	((and (>= (length f) 2) (eq (car f) 'at) (eq (cadr f) 'end))
	 (cond ((= (length f) 3)
		(type-check-formula (third f) context predicates
				    functions types objects where
				    :accept-preferences nil))
	       (t (format t "~&~s: ill-formed constraint ~s~%" where f) nil)
	       ))
	;; preference
	((eq (car f) 'preference)
	 (cond ((not accept-preferences)
		(format t "~&~s: ~s not accepted in this context~%" where f)
		nil)
	       ((= (length f) 3)
		(cond ((not (symbolp (second f)))
		       (format t "~&~s: invalid preference name ~s in ~s~%"
			       where (second f) f)
		       nil)
		      (t (type-check-constraint-formula
			  (third f) context predicates functions types objects
			  where :accept-preferences nil))))
	       ((= (length f) 2)
		(type-check-constraint-formula
		 (third f) context predicates functions types objects where
		 :accept-preferences nil))
	       (t (format t "~s: ill-formed preference ~s" where f))))
	(t (format t "~&~s: unrecognised constraint formula: ~s~%(note that INVAL does not reconise the temporal modalities within and always-within)~%"
		   where f)
	   nil)
	))

;; Check all actions and axioms, the initial state, goal and metric spec
;; (if any) for type correctness.
;; returns: t if everything is type correct, nil otherwise.

(defun type-check ()
  (let ((ok t))
    (dolist (action *actions*)
      (if (not (type-check-action
		action *predicates* *functions* *types* *objects*))
	  (setq ok nil)))
    (dolist (axiom *axioms*)
      (if (not (type-check-axiom
		axiom *predicates* *functions* *types* *objects*))
	  (setq ok nil)))
    (if (not (type-check-formula-list
	      *init* nil *predicates* *functions* *types* *objects* ':init
	      :accept-preferences nil))
	(setq ok nil))
    (if (not (type-check-formula
	      *goal* nil *predicates* *functions* *types* *objects* ':goal
	      :accept-preferences t))
	(setq ok nil))
    (if (not (type-check-constraint-formula
	      *constraints* nil *predicates* *functions* *types* *objects*
	      ':constraints))
	(setq ok nil))
    (if *metric*
	(let ((mt (type-check-term
		   *metric* nil *predicates* *functions* *types* *objects*
		   ':metric :is-metric t)))
	  (cond ((null mt)
		 (setq ok nil))
		((not (eq mt 'number))
		 (format t "~&:metric type is ~s (should be number)~%" mt)
		 (setq ok nil)))))
    ok))

;; Return axiom with arguments in the header type-enhanced according to
;; parameters of the derived predicate. If the axiom is malformed, the
;; predicate undeclared, or type information conflicting, the axiom is
;; returned as is.
(defun type-enhance-axiom (axiom predicates types)
  (if (< (length axiom) 2) axiom
    (let ((pred (assoc (car (second axiom)) predicates))
	  (args (parse-typed-list nil (cdr (second axiom)) 'object)))
      (if (or (null pred) (not (= (length (cdr pred)) (length args)))) axiom
	(list ':derived
	      (cons (car (second axiom))
		    (unparse-typed-list
		     (mapcar #'(lambda (arg param)
				 (if (variable-p (car arg))
				     (let ((ms-type
					    (most-specific-type
					     (cdr arg) (cdr param) types)))
				       (if ms-type
					   (cons (car arg) ms-type)
					 arg))
				   arg))
			     args (cdr pred))))
	      (third axiom))))))

;;;;
;; PDDL/Plan Parser

;; Global variables that will hold the parse result:

(defvar *domain-name* nil)  ;; domain name symbol
(defvar *problem-name* nil) ;; problem name symbol
(defvar *requirements* nil) ;; requirements list (not used)
(defvar *types* nil)       ;; list of (type . supertype) pairs
                           ;; note: type "object" will not appear
(defvar *objects* nil)     ;; list of (object . type) pairs
(defvar *predicates* nil)  ;; list of domain predicates
(defvar *functions* nil)   ;; list of domain functions
(defvar *actions* nil)     ;; list of domain actions
(defvar *axioms* nil)      ;; list of domain axioms
(defvar *init* nil)        ;; list of init state atoms/function values
(defvar *goal* nil)        ;; the goal condition
(defvar *metric* nil)      ;; the metric expression
(defvar *metric-type* nil) ;; the metric type (minimize or maximize)
(defvar *constraints* nil) ;; PDDL3 constraints
(defvar *invariants* nil)  ;; list of DKEL invariants (sans :invariant kw)
(defvar *sets* nil)        ;; list of (unparsed!) sets (sans :set kw)
(defvar *plans* nil)       ;; list of plans: pairs (name . plan)

;; List of recognised PDDL keywords. This list does not have to be
;; complete, but any keyword not in it will loose its leading colon
;; when input is read.
(defvar *pddl-keywords*
  '((domain . :domain)
    (requirements . :requirements)
    (types . :types)
    (predicates . :predicates)
    (functions . :functions)
    (constants . :constants)
    (action . :action)
    (parameters . :parameters)
    (precondition . :precondition)
    (condition . :condition)
    (effect . :effect)
    (derived . :derived)
    (objects . :objects)
    (init . :init)
    (goal . :goal)
    (metric . :metric)
    (constraints . :constraints)
    ;; DKEL extensions
    (invariant . :invariant)
    (vars . :vars)
    (context . :context)
    (set-constraint . :set-constraint)
    (formula . :formula)
    ;; inval/pddlcat custom extensions
    (pddl-macro-expand . :pddl-macro-expand)
    (plan . :plan)
    (set . :set)
    (heuristic . :heuristic)
    (name . :name)
    (min . :min)
    (max . :max)))

(defun clear-definitions ()
  (setq *domain-name* nil)
  (setq *problem-name* nil)
  (setq *requirements* nil)
  (setq *types* nil)
  (setq *objects* nil)
  (setq *predicates* nil)
  (setq *functions* nil)
  (setq *actions* nil)
  (setq *axioms* nil)
  (setq *init* nil)
  (setq *goal* nil)
  (setq *metric-type* nil)
  (setq *metric* nil)
  (setq *constraints* nil)
  (setq *invariants* nil)
  (setq *sets* nil)
  (setq *plans* nil))

(defun print-definitions ()
  (format t "~&domain: ~s~%" *domain-name*)
  (format t "~&problem: ~s~%" *problem-name*)
  (format t "~&requirements: ~s~%" *requirements*)
  (format t "~&types: ~s~%" *types*)
  (format t "~&objects: ~s~%" *objects*)
  (format t "~&predicates: ~s~%" *predicates*)
  (format t "~&functions: ~s~%" *functions*)
  (format t "~&actions: ~s~%" *actions*)
  (format t "~&invariants: ~s~%" *invariants*)
  (format t "~&axioms: ~s~%" *axioms*)
  (format t "~&init: ~s~%" *init*)
  (format t "~&goal: ~s~%" *goal*)
  (format t "~&constraints: ~s~%" *constraints*)
  (format t "~&metric: ~s ~s~%" *metric-type* *metric*)
  (format t "~&sets: ~s~%" *sets*)
  (format t "~&plans: ~s~%" *plans*))

;; read all lisp expressions in a file and return them as a list

(defun read-file (filename)
  (with-open-file
   (*in-stream* filename :direction :input)
   (let ((contents nil)
	 (*readtable* *pddl-readtable*))
     (do ((next-item (read *in-stream* nil 'end-of-file)
		     (read *in-stream* nil 'end-of-file)))
	 ;;((eq next-item 'end-of-file) (restore-keywords contents))
	 ((eq next-item 'end-of-file) contents)
       (setq contents (append contents (list next-item)))
       ))
   ))

(defparameter *pddl-readtable*
  (let ((table (copy-readtable)))
    (set-macro-character #\:
                         #'(lambda (stream char)
			     (let ((next (read stream nil 'end-of-file)))
			       (if (symbolp next)
				   (let ((kw (assoc next *pddl-keywords*)))
				     (if kw (cdr kw) next))
				 next)))
                         ;; #'(lambda (stream char)
			 ;;    (declare (ignore stream char))
			 ;;    'colon)
                         nil table)
    table))

;; (defun restore-keywords (exp)
;;   (cond ((not (listp exp)) exp)
;; 	((endp exp) nil)
;; 	((eq (car exp) 'colon)
;; 	 (let ((kw (assoc (cadr exp) *pddl-keywords*)))
;; 	   (cond (kw (cons (cdr kw) (restore-keywords (cddr exp))))
;; 		 (t (restore-keywords (cdr exp))))))
;; 	(t (cons (restore-keywords (car exp))
;; 		 (restore-keywords (cdr exp))))
;; 	))

;; Clear current definitions and load one or more files.

(defun load-files (&rest files)
  (clear-definitions)
  (dolist (file files)
    (format t "~&loading ~a...~%" file)
    (parse-file file (read-file file))))


;; parse the contents of a file: contents is a list, as produced by read-file

(defun parse-file (filename contents)
  (cond ((endp contents)
	 (format t "~&warning: empty file ~w assumed to be a plan~%"
		 filename)
	 (setq *plans* (cons (cons filename nil) *plans*)))
	;; if the first element in contents is a list, this may
	;; be a definitions file (domain or problem), or list of plans
	;; in pddlcat format; to find out, look at the first item
	((listp (car contents))
	 (let ((first-item (car contents))
	       (plan-count 0))
	   (cond ((endp first-item)
		  (error "empty definition/action in ~s" filename))
		 ((or (eq (car first-item) 'define)
		      (eq (car first-item) ':plan))
		  ;; ok, it's a definitions/plan file; process each item
		  (dolist (item contents t)
		    (cond ((not (listp item))
			   (error "non-definition ~s in ~s" item filename))
			  ((eq (car item) 'define)
			   (parse-definition filename item))
			  ;; handle pddlcat plan format
			  ((eq (car item) ':plan)
			   (setq plan-count (+ plan-count 1))
			   (setq *plans*
				 (cons (parse-plan
					(concatenate 'string
						     filename " #"
						     (prin1-to-string
						      plan-count))
					(cdr item))
				       *plans*)))
			  ;; ignore heuristic definitions
			  ((eq (car item) ':heuristic) t)
			  (t (error "unparseable thing ~s in ~s"
				    item filename))
			  )))
		 ;; if the first element of the list is neither 'define
		 ;; nor ':plan, it may be an untimed plan file
		 (t (setq *plans*
			  (cons (parse-plan filename contents) *plans*)))
		 )))
	;; otherwise, we assume this is a (timed) plan file
	(t (setq *plans* (cons (parse-plan filename contents) *plans*)))
	))

(defun parse-definition (filename content)
  (cond ((< (length content) 2)
	 (error "bad define: ~s in ~s" content filename))
	((not (listp (second content)))
	 (error "bad define: (define ~s ... in ~s"
		(second content) filename))
	((null (second content))
	 (error "bad define: (define ~s ... in ~s"
		(second content) filename))
	((member (first (second content)) '(domain situation problem))
	 (if (eq (first (second content)) 'domain)
	     (setq *domain-name* (second (second content))))
	 (if (eq (first (second content)) 'problem)
	     (setq *problem-name* (second (second content))))
	 (dolist (element (nthcdr 2 content) t)
	   (parse-definition-element filename (pddl-macro-expand element))))
	(t (error "unrecognised definition ~s in ~s"
		  (second content) filename))
	))

(defun parse-definition-element (filename element)
  (cond ((not (listp element))
	 (error "non-list element ~s in definition in ~s" element filename))
	((endp element)
	 (error "empty element ~s in definition in ~s" element filename))
	((eq (first element) ':domain)
	 (if (not (= (length element) 2))
	     (error "ill-formed declaration ~s" element))
	 (if (and *domain-name* (not (eq (cadr element) *domain-name*)))
	     (format t "~&warning: request for ~w but defined domain is ~w~%"
		     element *domain-name*)))
	((eq (first element) ':requirements)
	 (setq *requirements* (union *requirements* (rest element))))
	((eq (first element) ':types)
	 (setq *types*
	       (define-typed-things *types*
		 (parse-typed-list '() (rest element) 'object))))
	((eq (first element) ':predicates)
	 (setq *predicates*
	       (append *predicates*
		       (mapcar
			#'(lambda (pd)
			    (cons (car pd)
				  (parse-typed-list nil (cdr pd) 'object)))
			(rest element)))))
	((eq (first element) ':functions)
	 (setq *functions*
	       (append *functions*
		       (mapcar
			#'(lambda (tfd)
			    (cons
			     (cons (caar tfd)
				   (parse-typed-list nil (cdar tfd) 'object))
			     (cdr tfd)))
			(parse-typed-list nil (rest element) 'number)))))
	((eq (first element) ':action)
	 (setq *objects*
	       (define-typed-things *objects*
		 (remove 'undefined (constants-in-action element) :key #'car)))
	 (let* ((parsed-action-def (parse-struct (cddr element)))
		(action-params
		 (parse-typed-list
		  nil (cdr (assoc ':parameters parsed-action-def)) 'object))
		(intern-action-def (cond
				    (action-params (reassoc
						    ':parameters
						    action-params
						    parsed-action-def))
				    (t parsed-action-def))))
	   (setq *actions*
		 (append *actions*
			 (list (cons (cadr element) intern-action-def))))))
	((eq (first element) ':derived)
	 (setq *axioms* (cons element *axioms*)))
	((eq (first element) ':constants)
	 (setq *objects*
	       (define-typed-things *objects*
		 (parse-typed-list '() (rest element) 'object))))
	((eq (first element) ':objects)
	 (setq *objects*
	       (define-typed-things *objects*
		 (parse-typed-list '() (rest element) 'object))))
	((eq (first element) ':init)
	 (setq *init*
	       (append *init* (rest element))))
	((eq (first element) ':goal)
	 (cond ((null *goal*)
		(setq *goal* (second element)))
	       (t (setq *goal* (list 'and *goal* (second element))))))
	((eq (first element) ':constraints)
	 (setq *constraints*
	       (merge-conjunctions *constraints* (second element))))
	((eq (first element) ':metric)
	 (if *metric* (error "multiple :metric definitions in ~s" filename))
	 (if (< (length (rest element)) 2)
	     (error "malformed :metric ~s" element))
	 (setq *metric-type* (first (rest element)))
	 (setq *metric* (second (rest element))))
	;; Recognise some custom pddlcat extensions: invariants and sets:
	((eq (first element) ':invariant)
	 (setq *invariants*
	       (append *invariants*
		       (list (parse-struct (cdr element))))))
	((eq (first element) ':set)
	 (setq *sets* (append *sets* (list (cdr element)))))
	;; print a warning about unrecognised stuff
	(t (format t "~&warning: ~w in definition not recognised in ~w~%"
		   (first element) filename))
	))

(defun define-typed-things (typed-things list-of-new-defs)
  (dolist (def list-of-new-defs typed-things)
    (let ((prev-def (assoc (car def) typed-things)))
      (cond (prev-def
	     (cond ((eq (cdr prev-def) 'object)
		    (setf (cdr prev-def) (cdr def)))
		   ((and (not (eq (cdr def) 'object))
			 (not (eq (cdr def) (cdr prev-def))))
		    (cond ((not *multityping*)
			   (error "clashing types ~s and ~s for ~s"
				  (cdr prev-def) (cdr def) (car def)))
			  (t (setq typed-things (cons def typed-things)))))
		   ))
	    (t (setq typed-things (cons def typed-things)))
	    )))
  typed-things)

(defun pddl-macro-expand (element)
  (cond ((not (listp element)) element)
	((eq (car element) ':pddl-macro-expand)
	 (if (not (= (length element) 2))
	     (error "ill-formed :expand: ~s" element))
	 (eval (cadr element)))
	(t (mapflat #'(lambda (el1)
			(cond ((and (listp el1)
				    (eq (car el1) ':pddl-macro-expand))
			       (if (not (= (length el1) 2))
				   (error "ill-formed :expand: ~s" el1))
			       (eval (cadr el1)))
			      (t (list (pddl-macro-expand el1)))))
		    element))))

(defun constants-in-action (action)
  (mapcar #'(lambda (x) (cons x 'object))
	  (do ((rem action (cddr rem)) (constants nil))
	      ((endp rem) constants)
	      (cond ((eq (car rem) ':precondition)
		     (dolist (newc (constants-in-expression (cadr rem)) t)
		       (pushnew newc constants)))
		    ((eq (car rem) ':effect)
		     (dolist (newc (constants-in-expression (cadr rem)) t)
		       (pushnew newc constants)))
		    ))
	  ))

(defun constants-in-expression (exp)
  (cond ((listp exp)
	 (cond ((or (eq (car exp) 'forall) (eq (car exp) 'exists))
		(if (not (= (length exp) 3))
		    (error "ill-formed quantified expression: ~s" exp))
		(constants-in-expression (third exp)))
	       (t (mapflat #'constants-in-expression (cdr exp)))))
	((and (symbolp exp)
	      (not (variable-p exp))
	      (not (eq exp '-)))
	 (list exp))
	(t nil)
	))

;; parse a (timed or untimed) plan: content is a list, as produced by
;; read-file

(defun parse-plan (filename content &key (timed nil) (split nil))
  (let ((plan-name filename)
	(plan-type 'unknown)
	(plan nil))
    (do () ((endp content) t)
	(cond
	 ;; a pddlcat extension: plan name
	 ((and (>= (length content) 2)
	       (eq (first content) ':name))
	  (setq plan-name (second content))
	  (setq content (nthcdr 2 content)))
	 ;; <time> <action> [ <duration> ]  (note: colon has been removed!)
	 ((and (>= (length content) 5)
	       (numberp (first content))
	       (listp (second content))
	       (eq (third content) '[)
	       (numberp (fourth content))
	       (eq (fifth content) ']))
	  (if (eq plan-type 'untimed)
	      (error "timestamped action ~s : ~s in untimed plan"
		     (first content) (second content)))
	  (setq plan (add-to-list-map (first content) (second content) plan))
	  (setq plan-type 'timed)
	  (setq content (subseq content 5)))
	 ;; <time> <action> [<duration>]  (note: colon has been removed!)
	 ((and (>= (length content) 3)
	       (numberp (first content))
	       (listp (second content))
	       (symbolp (third content)))
	  (if (eq plan-type 'untimed)
	      (error "timestamped action ~s : ~s in untimed plan"
		     (first content) (third content)))
	  (cond
	   (split
	    (let ((duration (parse-duration (third content))))
	      (setq plan (add-to-list-map (first content)
					  (list 'start (second content)) plan))
	      (setq plan (add-to-list-map (+ (first content) duration)
					  (list 'end (second content)) plan))
	      ))
	   (t
	    (setq plan (add-to-list-map (first content) (second content) plan)))
	   )
	  (setq plan-type 'timed)
	  (setq content (subseq content 3)))
	 ;; <time> <action>  (note: colon has been removed!)
	 ((and (>= (length content) 2)
	       (numberp (first content))
	       (listp (second content)))
	  (if (eq plan-type 'untimed)
	      (error "timestamped action ~s : ~s in untimed plan"
		     (first content) (third content)))
	  (setq plan (add-to-list-map (first content) (second content) plan))
	  (setq plan-type 'timed)
	  (setq content (subseq content 2)))
	 ((listp (first content))
	  (if (eq plan-type 'timed)
	      (error "untimed action ~s in timed plan" (third content)))
	  (setq plan (append plan (list (list (first content)))))
	  (setq plan-type 'untimed)
	  (setq content (cdr content)))
	 (t (error "can't parse plan file ~s: ~s" filename content))
	 ))
    (cons plan-name
	  (cond ((and (eq plan-type 'timed) timed)
		 (sort plan #'< :key #'car))
		((eq plan-type 'timed)
		 (let ((sorted-happenings (sort plan #'< :key #'car)))
		   (mapcar #'cdr sorted-happenings)))
		(timed (enumerate-list plan))
		(t plan)))
    ))

;; replace each element in list with the list `(index . element)`,
;; where index ranges from 0 to (length list) - 1.
(defun enumerate-list (list)
  (dotimes (index (length list) list)
    (setf (nth index list) (cons index (nth index list)))))

(defun parse-duration (sym)
  (let* ((str (symbol-name sym))
	 (mstr (subseq str 1 (- (length str) 1))))
    (read-from-string mstr)))
    

;;;;
;; Causal link analysis

;; Extract causal links from a plan. This is done by executing the plan
;; (in much the same was as execute-plan does), keeping track of which
;; action was the last to add each atom, and creating causal links for
;; the (positive) preconditions of each action using that information.
;; There are limitations to the current implementation: it does not work
;; with derived predicates (axioms), or fluents (object or number); and
;; it considers every atom read by the precondition of an action as a
;; precondition, which may lead to unintended results if actions have
;; disjunctive conditions or conditional effects.
;; plan - the plan (sans name)
;; state - initial state (same as in execute-plan)
;; actions - the list of actions (same as in execute-plan)
;; stratified-axioms - must be nil ;)
;; types - list of type declarations (same as in execute-plan)
;; objects - list of object declarations (same as in execute-plan)
;; clinks - input list of causal links (may be nil)
;; :producer-cost-select - function used to select/combine two values
;;   for producer-cost; will only be called with two arguments, both of
;;   which are numberp.
;; :consumer-cost-select - function used to select/combine two values
;;   for consumer-cost; will only be called with two arguments, both of
;;   which are numberp.
;; :filter - optional filter function; if given, will be called with the
;;   five elements of each causal link found as arguments, and the link
;;   will only be added to the list if the function return non-nil.
;; Returns: a list of causal links. Each entry in the list is a list
;;  (producer consumer atom pcost ccost), where
;; - producer is the (instantiated) producer action;
;; - consumer is the (instantiated) consumer action;
;; - atom is the (ground) atom provided;
;; - pcost is the value of the (total-cost) fluent in the state after
;;  the happening that includes the producer (may be nil if total-cost
;;  is not defined);
;; - ccost is the value of the (total-cost) fluent in the state after
;;  the happening that includes the consumer (may be nil if total-cost
;;  is not defined).
;; The returned list has at most one entry for each producer-consumer-atom
;; triplet. If the same causal link is found more than once, the
;; producer-cost-select and consumer-cost-select functions are used to
;; determine the pcost/ccost to be associated with it.

(defun extract-causal-links
  (plan state actions stratified-axioms types objects clinks
	&key (producer-cost-select #'min) (consumer-cost-select #'min)
	     (filter nil))
  (when stratified-axioms
    (error "causal link analysis not supported with axioms"))
  (let ((achievers nil))
    (loop
     (when (endp plan)
       (return clinks))
     ;; this is the main part of execute-happening:
     (let ((eas (mapcar
		 #'(lambda (a)
		     (cons a (check-action a state actions types objects)))
		 (first plan))))
       ;; if some check fails, return failure
       (when (or (not (every #'cadr eas)) (not (check-conflicts eas)))
	 (return nil))
       (let ((new-state (apply-effects eas state)))
	 ;; first, check for causal links terminating in preconditions of
	 ;; actions in the current happening:
	 (dolist (ea eas)
	   ;; for every atom read by the action,
	   (dolist (atom (third ea))
	     (let ((ach (assoc atom achievers :test #'equal)))
	       ;; if there is a current achiever for the atom, there
	       ;; is a causal link:
	       (when ach
		 ;; if no filter is provided, or the filter returns true
		 ;; when called with the new link...
		 (when (or (null filter)
			   (funcall filter
				    (cadr ach) (first ea) atom
				    (cddr ach) ; pcost
				    (find-fluent-value
				     '(total-cost) new-state)))
		   ;; then add it to the current set:
		   (setq clinks
			 (store-causal-link
			  (cadr ach) (first ea) atom ; prod. cons. atom
			  (cddr ach) ; pcost
			  (find-fluent-value '(total-cost) new-state) ; cost
			  clinks ; current list of links
			  :producer-cost-select producer-cost-select
			  :consumer-cost-select consumer-cost-select))))
	       )))
	 ;; next, remove deleted atoms from the achievers map:
	 (dolist (ea eas)
	   (dolist (atom (fifth ea))
	     (setq achievers
		   (remove atom achievers :test #'equal :key #'car))))
	 ;; then, add new achievers for added atoms (again, double iteration):
	 (dolist (ea eas)
	   ;; for every atom added by the action,
	   (dolist (atom (fourth ea))
	     ;; if there is no current achiever of the atom
	     (when (null (assoc atom achievers :test #'equal))
	       (setq achievers
		     (cons (cons atom
				 (cons (first ea)
				       (find-fluent-value
					'(total-cost) new-state)))
			   achievers)))))
	 ;; update state and plan
	 (setq state new-state)
	 (setq plan (rest plan))
	 )))
    ))

;; Apply causal link analysis to a list of plans. The returned list of
;; links has at most one entry for each producer-consumer-atom triplet.

(defun extract-causal-links-from-plan-set
  (plans state actions stratified-axioms types objects clinks
	 &key (producer-cost-select #'min) (consumer-cost-select #'min)
	      (filter nil))
  (if (endp plans) clinks
    (extract-causal-links-from-plan-set
     (rest plans) state actions stratified-axioms types objects
     (extract-causal-links 
      (first plans) state actions stratified-axioms types objects clinks
      :producer-cost-select producer-cost-select
      :consumer-cost-select consumer-cost-select
      :filter filter)
     :producer-cost-select producer-cost-select
     :consumer-cost-select consumer-cost-select
     :filter filter)))

;; Add a causal link to list: if the link already exists, update its
;; pcost/costs by applying given functions to the old and new values
;; (if either old or new value is nil, the other is stored). The default
;; selection function (for both costs) is to take the minimum value.

(defun store-causal-link (producer consumer atom pcost ccost clinks
				   &key (producer-cost-select #'min)
				        (consumer-cost-select #'min))
  (cond ((endp clinks) (list (list producer consumer atom pcost ccost)))
	((and (equal (first (first clinks)) producer)
	      (equal (second (first clinks)) consumer)
	      (equal (third (first clinks)) atom))
	 (cons (list producer consumer atom
		     (if (numberp (fourth (first clinks)))
			 (if (numberp pcost)
			     (funcall producer-cost-select
				      pcost (fourth (first clinks)))
			   (fourth (first clinks)))
		       pcost)
		     (if (numberp (fifth (first clinks)))
			 (if (numberp ccost)
			     (funcall consumer-cost-select
				      ccost (fifth (first clinks)))
			   (fifth (first clinks)))
		       ccost))
	       (rest clinks)))
	(t 
	 (cons (first clinks)
	       (store-causal-link producer consumer atom pcost ccost
				  (rest clinks))))
	))


;;;;
;; Utilities


;; Linearise a plan
;; Input is a plan that is a list of happenings; output is a plan where
;; all parallel actions (i.e., happenings with more than one action) have
;; been linearised (in arbitrary order), represented as a list of unit
;; happenings.

(defun linearise (plan)
  (mapcar #'list
	  (reduce #'append plan)))

(defun plan-to-action-sequence (plan)
  (reduce #'append plan))

;; Translate a plan, using a list of translation rules. Rules take
;; the form (pattern replacement*), where 'pattern' is a list of
;; symbols and variables (variables are indicated with '? as in PDDL),
;; and each 'replacement' is an action instance, which may use
;; variables that appeared in the pattern. Rules are processed in
;; order, first triggered rule is applied. The plan is linearised.

(defun translate-plan (plan rules)
  (mapcar #'list
	  (reduce #'append
		  (mapcar (lambda (act) (translate-action act rules))
			  (plan-to-action-sequence plan)))))

(defun translate-action (action rules)
  (if (endp rules) (list action)
    (let ((binds (match-pattern action (car (first rules)) nil)))
      (if (listp binds) (sublis binds (cdr (first rules)))
	(translate-action action (rest rules))))))

;; simple one-sided unify; returns the (extended) list of bindings if
;; successful, else 'no.
(defun match-pattern (exp pattern binds)
  (cond ((endp pattern)
	 (if (endp exp) binds 'no))
	((variable-p (car pattern))
	 (let ((b (assoc (car pattern) binds)))
	   (cond ((null b)
		  (match-pattern (cdr exp) (cdr pattern)
				 (cons (cons (car pattern) (car exp)) binds)))
		 ((equal (car exp) (cdr b))
		  (match-pattern (cdr exp) (cdr pattern) binds))
		 (t 'no))))
	((equal (car exp) (car pattern))
	 (match-pattern (cdr exp) (cdr pattern) binds))
	(t 'no)))


;; Convert a PDDL-style list of :keyword <exp> pairs to an assoc list.
;; If keyword argument last is non-nil, the last item in the struct,
;; if of odd length, will be paired with the value of last; otherwise
;; it is an error if the struct is not of even length.

(defun parse-struct (struct &key (last nil))
  (cond ((endp struct) nil)
	((and (symbolp (car struct))
	      (not (endp (cdr struct))))
	 (cons (cons (car struct) (cadr struct))
	       (parse-struct (cddr struct) :last last)))
	((and last (= (length struct) 1))
	 (list (cons last (car struct))))
	(t (error "ill-formed struct: ~s" struct))))


;; Convert a PDDL-style list of typed things (variables, objects or
;; typenames) to an assoc list of (thing . type) pairs.

(defun parse-typed-list (syms more default-type)
  (cond ((endp more)
	 (mapcar #'(lambda (sym) (cons sym default-type)) syms))
	((eq (first more) '-)
	 (if (endp (rest more))
	     (error "no type following '-' in ~s" syms))
	 (append (mapcar #'(lambda (sym) (cons sym (second more))) syms)
		 (parse-typed-list '() (rest (rest more)) default-type)))
	(t (parse-typed-list (append syms (list (first more)))
			     (rest more) default-type))
	))


;;;;
;; Unparsing.

;; - If plist is a list of (thing . type) pairs, convert it back
;; to a PDDL-style typed thing list;
;; - if plist is a list of plain symbols, return it as is.
;; - otherwise, fail.

(defun unparse-typed-list (plist)
  (cond ((every #'consp plist)
	 (mapflat #'(lambda (ttpair)
		      (list (car ttpair) '- (cdr ttpair)))
		  plist))
	((every #'symbolp plist)
	 plist)
	(t (error "can't unparse mixed list: ~a" plist))
	))

;; Convert an assoc list (back) to a PDDL-style struct.

(defun unparse-struct (pstruct)
  (cond ((endp pstruct) nil)
	(t (append (list (caar pstruct) (cdar pstruct))
		   (unparse-struct (cdr pstruct))))))


;; Check if x is a variable name (= symbol beginning with '?').

(defun variable-p (x)
  (cond ((not (symbolp x)) nil)
	((eq (elt (symbol-name x) 0) #\?) t)
	(t nil)))


;; Remove the '?' from the beginning of a variable (returning the
;; rest of the name as a string)

(defun variable-name (x)
  (cond ((not (variable-p x)) (error "~a is not a variable" x))
	(t (coerce (rest (coerce (symbol-name x) 'list)) 'string))))


;; Create a new symbol by concatenating a list of symbols and/or numbers.

(defun symnumcat (&rest symnums)
  (intern (coerce
	   (reduce #'append
		   (mapcar #'(lambda (s)
			       (cond ((symbolp s)
				      (coerce (symbol-name s) 'list))
				     ((numberp s)
				      (coerce (princ-to-string s) 'list))
				     ((listp s)
				      (coerce (princ-to-string (symnumcat s))
					      'list))
				     ))
			   (cond ((and (listp (first symnums))
				       (= (length symnums) 1))
				  (first symnums))
				 (t symnums))))
	   'string)))


;; A gensym functions for variable names:

(defvar *new-variable-count* 0)
(defun new-variable ()
  (setq *new-variable-count* (+ *new-variable-count* 1))
  (symnumcat '?newvar *new-variable-count*))

;; Rename variables any variables in 'vars' that conflict with any in
;; ex-vars. Both variable lists should be in parsed form, i.e., lists
;; of (var . type) pairs. Returns the renaming mapping, in the form of
;; of an assoc list (suitable for input to instantiate-1 or sublis).

(defun rename-variables (vars ex-vars)
  (cond ((endp vars) nil)
	((find (car (first vars)) ex-vars :key #'car)
	 (cons (cons (car (first vars)) (new-variable))
	       (rename-variables (rest vars) ex-vars)))
	(t (rename-variables (rest vars) ex-vars))))

;; Binary predicate for alphabetic order on symbol names.

(defun symbol-alpha (s1 s2)
  (string< (symbol-name s1) (symbol-name s2)))

;; Map is an assoc list mapping keys to lists (possibly with duplicates)
;; add-to-list-map adds 'item' to the list associated with 'key', or adds
;; a new assoc pair for 'key' if it isn't not in the map, and returns
;; the updated map (note: map may be changed desctructively).

(defun add-to-list-map (key item map &key (test #'eq))
  (let ((entry (assoc key map :test test)))
    (cond (entry
	   (rplacd entry (cons item (cdr entry)))
	   map)
	  (t (cons (cons key (list item)) map)))))


;; Similar to above, but add-to-set-map treats map entries as sets, and
;; only adds 'item' to the list associated with 'key' if it's not already
;; there.

(defun add-to-set-map (key item map &key (test #'eq))
  (let ((entry (assoc key map :test test)))
    (cond (entry
	   (cond ((not (find item (cdr entry) :test test))
		  (rplacd entry (cons item (cdr entry)))))
	   map)
	  (t (cons (cons key (list item)) map)))))


;; Check if pair (a b) is in the relation represented by a set-map

(defun set-map-contains (a b setmap &key (test #'eq))
  (let ((entry (assoc a setmap :test test)))
    (cond (entry (find b (cdr entry) :test test))
	  (t nil))))

;; Add 'item' to list 'set' unless it's already there.

(defun add-to-set (item set &key (test #'eq))
  (cond ((member item set :test test) set)
	(t (cons item set))))

;; Return the cdr (value) part of the (key . value) pair found in alist,
;; nil if key is not bound.

(defun assoc-val (key alist &key (test #'equal))
  (let ((pair (assoc key alist :test test)))
    (cond (pair (cdr pair))
	  (t nil))))

;; Return the list of all keys that map to 'val' in assoc list 'alist'.

(defun rassoc-all (val alist &key (test #'equal))
  (cond ((endp alist) nil)
	((funcall test (cdr (car alist)) val)
	 (cons (car (car alist)) (rassoc-all val (cdr alist) :test test)))
	(t (rassoc-all val (cdr alist) :test test))))


;; Return the list of all values mapped to by 'key' in assoc list 'alist'.

(defun assoc-all (key alist &key (test #'equal))
  (cond ((endp alist) nil)
	((funcall test (car (car alist)) key)
	 (cons (cdr (car alist)) (assoc-all key (cdr alist) :test test)))
	(t (assoc-all key (cdr alist) :test test))))

;; Recursively assoc all values for 'key' in alist; vals is an accumulator
;; variable (call with nil).

(defun assoc-rec (key vals alist &key (test #'equal))
  (let* ((new-vals (cons key vals))
	 (new-keys (remove-if #'(lambda (x) (member x vals))
			      (assoc-all key alist))))
    (dolist (nk new-keys)
      (when (not (member nk new-vals))
	(setq new-vals (assoc-rec nk new-vals alist :test test))))
    new-vals))

;; Reassoc key to val in alist, and return the new assoc list.

(defun reassoc (key val alist &key (test #'equal))
  (cons (cons key val) (unassoc key alist :test test)))

;; Reassoc key to val in alist, and return the new assoc list. May
;; destructively modify the alist. If key already exists in alist,
;; it will remain at the same position in the list.

(defun reassoc-destructively (key val alist &key (test #'equal))
  (let ((cb (assoc key alist :test test)))
    (cond (cb (rplacd cb val) alist)
	  (t (cons (cons key val) alist)))))

;; Reassoc key to val in alist, maintaining keys in the list ordered
;; by the given order predicate (defaults to alphabetic order on symbol
;; names). May destructively modify the list.

(defun reassoc-in-order (key val alist &key (order #'symbol-alpha) (test #'eq))
  (cond ((endp alist) (list (cons key val)))
	((funcall test key (car (car alist)))
	 (rplacd (car alist) val)
	 alist)
	((funcall order key (car (car alist)))
	 (cons (cons key val) alist))
	(t (rplacd alist (reassoc-in-order key val (cdr alist)
					   :order order :test test)))
	))

;; Remove key from assoc list.

(defun unassoc (key alist &key (test #'equal))
  (remove-if #'(lambda (apair) (equal (car apair) key)) alist))
  ;;(remove key alist :key #'car :test test))


;; Map and flatten: fun is applied to each tuple of elements of the
;; argument lists, and returns a list; these lists are concatenated.

(defun mapflat (fun &rest lsts)
  (reduce #'append (apply #'mapcar (cons fun lsts))))


;; Append a single element to a list ("end-cons").

(defun econs (l e) (append l (list e)))

;;;;
;; Alternative implementation of apply-axioms (fixpoint computation).
;;
;; This implementation is intended to be faster than the simple one
;; in apply-axioms, but it is way more complicated (and thus more
;; likely to be buggy) and has some limitations (currently, no
;; support for fluents of any kind, i.e., neither numeric or object).

(defun apply-axioms-2 (state axioms types objects)
  (let ((naxs (mapcar #'(lambda (ax) (normalise-axiom ax types)) axioms))
	(st (make-trie))
	(derived (make-trie))
	(loop-count 0)
	(done nil))
    ;; initialise st with current state (ignoring fluent assignments)
    (dolist (atom state)
      (cond ((eq (car atom) '=)
	     (cond ((and (every #'symbolp (second atom))
			 (symbolp (third atom)))
		    (setq st (trie-insert (fluent-to-atom atom) st)))
		   ((>= *verbosity* 2)
		    (format t "~&warning: ignoring fluent ~w in state~%"
			    atom))))
	    (t (setq st (trie-insert (fluent-to-atom atom) st)))))
    (loop
     (setq done t)
     (dolist (nax naxs)
       (if (>= *verbosity* 4) (format t "applying ~a~%" nax))
       (let ((sbs (satisfying-bindings
		   (third nax) st nil (second nax) types objects)))
	 (dolist (b sbs)
	   ;; (format t "b = ~a, derived = ~a~%" b derived)
	   (cond ((not (trie-contains-all
			(first nax) b derived (second nax) types objects))
		  (if (>= *verbosity* 5)
		      (format t "~&derived: ~a~%" (sublis b (first nax))))
		  (setq derived
			(trie-insert-all
			 (first nax) b derived (second nax) types objects))
		  (setq st
			(trie-insert-all
			 (first nax) b st (second nax) types objects))
		  ;; (format t "derived = ~a~%" derived)
		  (setq done nil))))
	 ))
     (if (>= *verbosity* 4)
	 (format t "end of loop ~a, done = ~a~%" (incf loop-count) done))
     (if done (return (nconc (trie-to-list derived) state))))
    ))

(defun normalise-axiom (axiom types)
  (let* ((head-args (parse-typed-list '() (cdadr axiom) 'object))
	 (head-vars (remove-duplicate-variables
		     (remove-if-not #'variable-p head-args :key #'car)
		     types))
	 (body-vars (remove-if #'(lambda (var) (find var head-vars :key #'car))
			       (free-variables (caddr axiom)))))
    (list (cons (caadr axiom) (mapcar #'car head-args))
	  head-vars
	  (cond (body-vars
		 (list 'exists body-vars
		       (fluent-to-atom (transform-to-nnf (caddr axiom) nil))))
		(t (fluent-to-atom (transform-to-nnf (caddr axiom) nil)))))
    ))

;; Transform fluent atoms (i.e., (= (f ...) x)) to flat atoms
;; (i.e., (= f .. a)). This is a hack to handle fluents in tries.
;; The function works on formulas and lists of formulas.

(defun fluent-to-atom (form)
  (if (not (listp form)) (error "not a formula or a list: ~a" form))
  (cond
   ((listp (car form))
    (mapcar #'fluent-to-atom form))
   ((or (eq (car form) 'and)
	(eq (car form) 'or))
    (cons (car form)
	  (fluent-to-atom (cdr form))))
   ((or (eq (car form) 'forall)
	(eq (car form) 'exists))
    (list (first form) (second form)
	  (fluent-to-atom (third form))))
   ((eq (car form) 'not)
    (list (car form)
	  (fluent-to-atom (second form))))
   ((eq (car form) 'imply)
    (list (car form)
	  (fluent-to-atom (second form))
	  (fluent-to-atom (third form))))
   ((and (eq (car form) '=)
	 (symbolp (second form)))
    (if (not (symbolp (third form)))
	(error "cannot transform formula: ~a" form))
    form)
   ((and (eq (car form) '=)
	 (listp (second form)))
    (if (or (not (every #'symbolp (second form)))
	    (not (symbolp (third form))))
	(error "cannot transform formula: ~a" form))
    (cons '= (econs (second form) (third form))))
   (t (if (not (every #'symbolp (cdr form)))
	  (error "cannot transform formula: ~a" form))
      form)))

;; Simple implementation of a Trie structure for storing a set of atoms.
;; Stored elements are assumed to be flat lists of symbols. Moreover,
;; lookup is actually prefix lookup, so it will not work correctly if
;; there are atoms with the same predicate but different arity. Insertion
;; is destructive.

(defun make-trie () nil)

(defun make-trie-from-list (atoms)
  (trie-insert-list atoms (make-trie)))

;; simple lookup: each element in atom is treated as a constant.

(defun trie-contains (atom trie)
  (cond ((endp atom) t)
	(t (let ((next (assoc (car atom) trie)))
	     (cond (next (trie-contains (cdr atom) (cdr next)))
		   (t nil))))))

;; universal lookup: atom may contain variables (according to variable-p),
;; and the function returns true only if the trie contains all instances
;; of the atom consistent with given bindings; the variable declaration
;; list (vars) is used only to find the type of an unbound variable.

(defun trie-contains-all (atom binds trie vars types objects)
  (cond ((endp atom) t)
	((variable-p (car atom))
	 (let ((val (assoc (car atom) binds)))
	   (cond ((null val)
		  (let ((ok t))
		    (dolist (obj (objects-of-type
				  (assoc-val (car atom) vars) types objects))
		      (if (not (let ((next (assoc obj trie)))
				 (cond (next
					(trie-contains-all
					 (cdr atom)
					 (cons (cons (car atom) obj) binds)
					 (cdr next) vars types objects))
				       (t nil))))
			  (return (setq ok nil))))
		    ok))
		 (t (let ((next (assoc (cdr val) trie)))
		      (cond (next (trie-contains-all
				   (cdr atom) binds (cdr next)
				   vars types objects))
			    (t nil))))
		 )))
	(t (let ((next (assoc (car atom) trie)))
	     (cond (next (trie-contains-all
			  (cdr atom) binds (cdr next) vars types objects))
		   (t nil))))))

;; lookup an atom that may have variables, using bindings to determine
;; variable values; it is an error if some variable is unbound.

(defun trie-eval-atom (atom binds trie)
  (cond ((endp atom) t)
	((variable-p (car atom))
	 (let ((val (assoc (car atom) binds)))
	   (if (null val)
	       (error "unbound variable ~a in ~a (bindings = ~a)"
		      (car atom) atom binds))
	   (let ((next (assoc (cdr val) trie)))
	     (cond (next (trie-eval-atom (cdr atom) binds (cdr next)))
		   (t nil)))))
	(t (let ((next (assoc (car atom) trie)))
	     (cond (next (trie-eval-atom (cdr atom) binds (cdr next)))
		   (t nil))))))

;; convert a trie to a list of atoms (works only for atoms, not fluents)

(defun trie-to-list (trie)
  (let ((res nil))
    (dolist (entry trie)
      (let ((subres (trie-to-list (cdr entry))))
	(cond
	 ((endp subres)
	  (push (list (car entry)) res))
	 (t
	  (dolist (subitem subres)
	    (push (cons (car entry) subitem) res))))))
    res))

;; trie insertion

(defun trie-insert (atom trie)
  (cond
   ((endp atom) trie)
   (t (let ((next (assoc (car atom) trie)))
	(cond (next (rplacd next (trie-insert (cdr atom) (cdr next)))
		    trie)
	      (t (reassoc-in-order
		  (car atom) (trie-insert (cdr atom) (make-trie))
		  trie)))))))

(defun trie-insert-list (atoms trie)
  (dolist (atom atoms)
    (setq trie (trie-insert atom trie)))
  trie)

(defun trie-insert-all (atom binds trie vars types objects)
  (cond
   ((endp atom) trie)
   ((variable-p (car atom))
    (let ((val (assoc (car atom) binds)))
      (cond
       ((null val)
	(dolist (obj (objects-of-type
		      (assoc-val (car atom) vars) types objects))
	  (let ((next (assoc obj trie)))
	    (cond
	     (next
	      (rplacd next (trie-insert-all
			    (cdr atom) binds (cdr next) vars types objects)))
	     (t (setq trie
		      (reassoc-in-order
		       obj (trie-insert-all
			    (cdr atom) binds (make-trie) vars types objects)
		       trie)))
	     )))
	trie)
       (t (let ((next (assoc (cdr val) trie)))
	    (cond
	     (next
	      (rplacd next (trie-insert-all
			    (cdr atom) binds (cdr next) vars types objects))
	      trie)
	     (t (reassoc-in-order
		 (cdr val) (trie-insert-all
			    (cdr atom) binds (make-trie) vars types objects)
		 trie)))))
       )))
   (t (let ((next (assoc (car atom) trie)))
	(cond
	 (next (rplacd next (trie-insert-all
			     (cdr atom) binds (cdr next) vars types objects))
	       trie)
	 (t (reassoc-in-order
	     (car atom) (trie-insert-all
			 (cdr atom) binds (make-trie) vars types objects)
	     trie)))))
   ))

;; using tries to store fluent values (experimental)

(defun trie-eval-fluent (fluent binds trie)
  (cond ((endp fluent)
	 (cond ((null trie) nil)
	       ((cdr trie) (error "multiple fluent values: ~a" trie))
	       (t (car trie))))
	((variable-p (car fluent))
	 (let ((val (assoc (car fluent) binds)))
	   (if (null val)
	       (error "unbound variable ~a in ~a (bindings = ~a)"
		      (car fluent) fluent binds))
	   (let ((next (assoc (cdr val) trie)))
	     (cond (next (trie-eval-fluent (cdr fluent) binds (cdr next)))
		   (t nil)))))
	(t (let ((next (assoc (car fluent) trie)))
	     (cond (next (trie-eval-fluent (cdr fluent) binds (cdr next)))
		   (t nil))))))

(defun trie-assign-fluent (fluent value trie)
  (cond
   ((endp fluent) (list value))
   (t (let ((next (assoc (car fluent) trie)))
	(cond
	 (next (let ((new-next
		      (trie-assign-fluent (cdr fluent) value (cdr next))))
		 (rplacd next new-next)
		 trie))
	 (t (reassoc-in-order
	     (car fluent) (trie-assign-fluent (cdr fluent) value (make-trie))
	     trie)))))))

;; Formula evaluation functions based on tries:
;; Returns: a list of all bindings (each an assoc list of (var . val) pairs)
;; that make a formula true in the state represented by the trie.

(defun satisfying-bindings (form trie binds vdecl types objects)
  (cond
   ;; empty list is treated as constant true
   ((null form) (list nil))
   ;; conjunction
   ((eq (car form) 'and)
    (satisfying-bindings-and (rest form) trie binds vdecl types objects))
   ;; disjunction
   ((eq (car form) 'or)
    (satisfying-bindings-or (rest form) trie binds vdecl types objects))
   ;; simple equality (= atomic-term atomic-term)
   ((is-simple-equality form)
    (satisfying-bindings-simple-equality
     (second form) (third form) trie binds vdecl nil types objects))
   ;; simple inequality (not (= atomic-term atomic-term))
   ((is-simple-inequality form)
    (satisfying-bindings-simple-inequality
     (second form) (third form) trie binds vdecl types objects))
   ;; non-simple equality: this is assumed to be a "flattened" fluent,
   ;; i.e., an atom of the form (= f arg .. arg val). It is handled
   ;; same as another atom, by lookup in the trie.
   ((eq (car form) '=)
    (matching-bindings form trie binds vdecl nil types objects))
   ;; negation: this is assumed (but not checked) to be over an atomic
   ;; formula only (i.e. the input formula should be on NNF); thus, the
   ;; value is given by the non-matching-bindings function.
   ((eq (car form) 'not)
    (non-matching-bindings (second form) trie binds vdecl nil types objects))
   ;; implication (should have been eliminated by rewrite to NNF)
   ((eq (car form) 'imply)
    (error "satisfying-bindings: can't handle formula ~s" form))
   ;; quantified formulas as handled by instantiating them and processing
   ;; the resulting conjunction/disjunction; it's much more efficient to
   ;; do this before calling satisfying-bindings
   ((eq (car form) 'forall)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (satisfying-bindings-forall
     (parse-typed-list nil (second form) 'object)
     (third form) trie binds vdecl types objects))
   ((eq (car form) 'exists)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (satisfying-bindings-exists
     (parse-typed-list nil (second form) 'object)
     (third form) trie binds vdecl types objects))
   ;; what to do about numeric predicates?
   ((assoc (car form) *builtin-numeric-predicates*)
    (error "satisfying-bindings: can't handle numeric predicate ~s" form))
   ;; type name used as predicate
   ((and *type-names-are-predicates*
	 (or (assoc (car form) types)
	     (rassoc (car form) types))
	 (= (length (cdr form)) 1))
    (error "NYI"))
   ;; atomic predicate or equality with a non-simple term: handled by
   ;; lookup in the current state trie
   (t (matching-bindings form trie binds vdecl nil types objects))
   ))

(defun is-simple-equality (form)
  (and (listp form)
       (eq (car form) '=)
       (= (length form) 3)
       (not (listp (second form)))
       (not (listp (third form)))))

(defun is-simple-inequality (form)
  (and (listp form)
       (eq (car form) 'not)
       (= (length form) 2)
       (is-simple-equality (second form))))

(defun matching-bindings (exp trie binds vdecl eqv types objects)
  (cond ((endp exp) (list nil))
	((find (car exp) eqv)
	 (let ((vartype (assoc-val (car exp) vdecl))
	       (res nil))
	   (dolist (subtrie trie)
	     (if (or (null vartype)
		     (object-can-substitute-for-type
		      (car subtrie) vartype types objects
		      'matching-bindings))
		 (dolist (newbinds (matching-bindings
				    (cdr exp) (cdr subtrie) binds
				    vdecl eqv types objects))
		   (cond ((null newbinds)
			  (setq res (list nil)))
			 ((not (find newbinds res :test #'equal))
			  (setq res (cons newbinds res))))
		   (if (eq res '(())) (return))
		   ))
	     (if (eq res '(())) (return)))
	   res))
	((variable-p (car exp))
	 (let ((varval (assoc-val (car exp) binds))
	       (vartype (assoc-val (car exp) vdecl)))
	   (mapflat
	    #'(lambda (subtrie)
		(cond ((and
			(or (null varval)
			    (equal varval (car subtrie)))
			(or (null vartype)
			    (object-can-substitute-for-type
			     (car subtrie) vartype types objects
			     'matching-bindings)))
		       (mapcar #'(lambda (newbinds)
				   (extend-binding
				    (car exp) (car subtrie) newbinds))
			       (matching-bindings (cdr exp)
						  (cdr subtrie) binds
						  vdecl eqv types objects)))
		      (t nil)))
	    trie)))
	(t (let ((next (assoc (car exp) trie)))
	     (cond (next (matching-bindings (cdr exp) (cdr next) binds
					    vdecl eqv types objects))
		   (t nil))))
	))

(defun non-matching-bindings (exp trie binds vdecl eqv types objects)
  (cond
   ((endp exp) nil)
   ((find (car exp) eqv)
    (let ((vartype (assoc-val (car exp) vdecl))
	  (res nil))
      (dolist (obj (objects-of-type vartype types objects))
	(let ((next (assoc obj trie)))
	  (cond
	   (next 
	    (dolist (newbinds (non-matching-bindings
			       (cdr exp) (cdr next) binds
			       vdecl eqv types objects))
	      (cond ((null newbinds)
		     (setq res (list nil)))
		    ((not (find newbinds res :test #'equal))
		     (setq res (cons newbinds res))))
	      (if (eq res '(())) (return))))
	   (t (setq res (list nil)))))
	(if (eq res '(())) (return)))
      res))
   ((variable-p (car exp))
    (let ((varval (assoc-val (car exp) binds))
	  (vartype (assoc-val (car exp) vdecl)))
      (cond
       (varval
	(let ((next (assoc varval trie)))
	  (cond (next (non-matching-bindings
		       (cdr exp) (cdr next) binds vdecl eqv types objects))
		(t (list nil)))))
       (t (mapflat
	   #'(lambda (obj)
	       (let ((next (assoc obj trie)))
		 (cond (next
			(mapcar
			 #'(lambda (newbinds)
			     (extend-binding (car exp) obj newbinds))
			 (non-matching-bindings
			  (cdr exp) (cdr next) binds vdecl eqv types objects)))
		       (t (list (list (cons (car exp) obj)))))))
	   (objects-of-type vartype types objects)))
       )))
   (t (let ((next (assoc (car exp) trie)))
	(cond (next (non-matching-bindings
		     (cdr exp) (cdr next) binds vdecl eqv types objects))
	      (t (list nil)))))
   ))

(defun satisfying-bindings-simple-equality
  (term1 term2 trie binds vdecl eqv types objects)
  (cond
   ((find term1 eqv) ;; first term is existentially quantified
    (cond
     ((find term2 eqv) ;; second term is also existentially quantified
      (let ((vartype1 (assoc-val term1 vdecl))
	    (vartype2 (assoc-val term2 vdecl)))
	(cond ((types-have-common-object vartype1 vartype2 types objects)
	       (list nil))
	      (t nil))))
     ((variable-p term2) ;; second term is a variable
      (let ((val2 (assoc-val term2 binds))
	    (vartype1 (assoc-val term1 vdecl))
	    (vartype2 (assoc-val term1 vdecl)))
	(cond ((null val2) ;; second term is an unbound variable
	       (let ((res nil))
		 (dolist (obj (objects-of-type vartype2 types objects))
		   (if (or (null vartype1)
			   (object-can-substitute-for-type
			    obj vartype1 types objects 'satifying-bindings))
		       (setq res (cons (list (cons term2 obj)) res))))
		 res))
	      (t ;; second term is a bound variable
	       (cond ((or (null vartype1)
			  (object-can-substitute-for-type
			   val2 vartype1 types objects 'satifying-bindings))
		      (list nil))
		     (t nil))))))
     (t  ;; second term is a constant
      (let ((vartype1 (assoc-val term1 vdecl)))
	(cond ((or (null vartype1)
		   (object-can-substitute-for-type
		    term2 vartype1 types objects 'satifying-bindings))
	       (list nil))
	      (t nil))))))
   ((variable-p term1) ;; first term is a variable
    (cond
     ((find term2 eqv) ;; second term is existentially quantified
      (let ((val1 (assoc-val term1 binds))
	    (vartype1 (assoc-val term1 vdecl))
	    (vartype2 (assoc-val term2 vdecl)))
	(cond ((null val1) ;; first term is an unbound variable
	       (let ((res nil))
		 (dolist (obj (objects-of-type vartype1 types objects))
		   (if (or (null vartype2)
			   (object-can-substitute-for-type
			    obj vartype2 types objects 'satifying-bindings))
		       (setq res (cons (list (cons term1 obj)) res))))
		 res))
	      (t ;; first term is a bound variable
	       (cond ((or (null vartype2)
			  (object-can-substitute-for-type
			   val1 vartype2 types objects 'satifying-bindings))
		      (list nil))
		     (t nil))))))
     ((variable-p term2) ;; second term is also a variable
      (let ((val1 (assoc-val term1 binds))
	    (vartype1 (assoc-val term1 vdecl))
	    (val2 (assoc-val term2 binds))
	    (vartype2 (assoc-val term2 vdecl)))
	(cond ((and (null val1) (null val2))
	       (mapcar #'(lambda (obj)
			   (list (cons term1 obj)
				 (cons term2 obj)))
		       (intersection
			(objects-of-type vartype1 types objects)
			(objects-of-type vartype2 types objects))))
	      ((null val2)
	       (cond ((or (null vartype2)
			  (object-can-substitute-for-type
			   val1 vartype2 types objects 'satifying-bindings))
		      (list (list (cons term2 val1))))
		     (t nil)))
	      ((null val1)
	       (cond ((or (null vartype1)
			  (object-can-substitute-for-type
			   val2 vartype1 types objects 'satifying-bindings))
		      (list (list (cons term1 val2))))
		     (t nil)))
	      ((equal val1 val2)
	       (list nil))
	      (t nil))))
     (t ;; second term is a constant
      (let ((val1 (assoc-val term1 binds))
	    (vartype1 (assoc-val term1 vdecl)))
	(cond ((null val1)
	       (cond ((or (null vartype1)
			  (object-can-substitute-for-type
			   term2 vartype1 types objects
			   'satifying-bindings))
		      (list (list (cons term1 term2))))
		     (t nil)))
	      ((equal val1 term2) (list nil))
	      (t nil))))
     ))
   (t ;; first term is a constant
    (cond
     ((find term2 eqv) ;; second term is existentially quantified
      (let ((vartype2 (assoc-val term2 vdecl)))
	(cond ((or (null vartype2)
		   (object-can-substitute-for-type
		    term1 vartype2 types objects 'satifying-bindings))
	       (list nil))
	      (t nil))))
     ((variable-p term2) ;; second term is a variable
      (let ((val2 (assoc-val term2 binds))
	    (vartype2 (assoc-val term2 vdecl)))
	(cond ((null val2)
	       (cond ((or (null vartype2)
			  (object-can-substitute-for-type
			   term1 vartype2 types objects
			   'satifying-bindings))
		      (list (list (cons term2 term1))))
		     (t nil)))
	      ((equal val2 term1) (list nil))
	      (t nil))))
     ;; second term is also a constant
     ((equal term1 term2) (list nil))
     ;; both terms are constants and not equal
     (t nil)))
   ))

(defun satisfying-bindings-simple-inequality
  (term1 term2 trie binds vdecl types objects)
  (cond
   ((variable-p term1) ;; first term is a variable
    (cond
     ((variable-p term2) ;; second term is also a variable
      (let ((val1 (assoc-val term1 binds))
	    (vartype1 (assoc-val term1 vdecl))
	    (val2 (assoc-val term2 binds))
	    (vartype2 (assoc-val term2 vdecl)))
	(cond
	 ;; both terms are unbound variables
	 ((and (null val1) (null val2))
	  (let ((newbinds nil))
	    (dolist (obj1 (objects-of-type vartype1 types objects))
	      (dolist (obj2 (objects-of-type vartype2 types objects))
		(if (not (equal obj1 obj2))
		    (setq newbinds
			  (cons (list (cons term1 obj1)
				      (cons term2 obj2))
				newbinds)))))
	    newbinds))
	 ;; first variable is bound, second is not
	 ((null val2)
	  (mapcar #'(lambda (obj)
		      (list (cons term2 obj)))
		  (remove val1 (objects-of-type vartype2 types object))))
	 ;; second variable is bound, first is not
	 ((null val1)
	  (mapcar #'(lambda (obj)
		      (list (cons term1 obj)))
		  (remove val2 (objects-of-type vartype1 types object))))
	 ;; both variables are bound with unequal values
	 ((not (equal v1 v2)) (list nil))
	 ;; both variables are bound, with equal values
	 (t nil))))
     (t ;; second term is a constant
      (let ((val1 (assoc-val term1 binds))
	    (vartype1 (assoc-val term1 vdecl)))
	(cond
	 ;; first term (variable) is unbound
	 ((null val1)
	  (mapcar #'(lambda (obj)
		      (list (cons term1 obj)))
		  (remove term2 (objects-of-type vartype1 types object))))
	 ;; first term (variable) is bound, but not equal to second
	 ;; term (constant)
	 ((not (equal val1 term2)) (list nil))
	 ;; first term (variable) is bound, and equal to second
	 ;; term (constant)	   
	 (t nil))))))
   (t ;; first term is a constant
    (cond
     ((variable-p term2) ;; second term is a variable
      (let ((val2 (assoc-val term2 binds))
	    (vartype2 (assoc-val term2 vdecl)))
	(cond
	 ;; second term (variable) is unbound
	 ((null val2)
	  (mapcar #'(lambda (obj)
		      (list (cons term2 obj)))
		  (remove term1 (objects-of-type vartype2 types object))))
	 ;; second term (variable) is bound, but not equal to first
	 ;; term (constant)
	 ((not (equal val2 term1)) (list nil))
	 ;; second term (variable) is bound, and equal to first
	 ;; term (constant)	   
	 (t nil))))
     ;; second term is also a constant, not equal to first term
     ((not (equal term1 term2)) (list nil))
     ;; both terms are constants and equal
     (t nil)))
   ))

(defun satisfying-bindings-and
  (clist trie binds vdecl types objects)
  (let ((f-other nil)
	(f-eq-neq nil)
	(blist (list (copy-list binds))))
    (dolist (f1 clist)
      (cond ((is-simple-inequality f1)
	     (setq f-eq-neq (cons f1 f-eq-neq)))
	    ((is-simple-equality f1)
	     (setq f-eq-neq (cons f1 f-eq-neq)))
	    (t (setq f-other (cons f1 f-other)))
	    ))
    (dolist (f1 f-other)
      (setq blist
	    (mapflat
	     #'(lambda (b)
		 (mapcar
		  #'(lambda (nb)
		      (extend-binding-with-binding b nb))
		  (satisfying-bindings f1 trie b vdecl types objects)))
	     blist)))
    (dolist (f1 f-eq-neq)
      (setq blist
	    (mapflat
	     #'(lambda (b)
		 (mapcar
		  #'(lambda (nb)
		      (extend-binding-with-binding b nb))
		  (satisfying-bindings f1 trie b vdecl types objects)))
	     blist)))
    blist
    ))

(defun satisfying-bindings-or
  (dlist trie binds vdecl types objects)
  (let ((all-new-binds
	 (sort (mapflat
		#'(lambda (f1)
		    (satisfying-bindings f1 trie binds vdecl types objects))
		dlist)
	       #'(lambda (b1 b2)
		   (< (length b1) (length b2)))))
	(new-binds nil))
    (dolist (nb all-new-binds)
      (if (not (find-if #'(lambda (b) (subsetp b nb :test #'equal))
			new-binds))
	  (setq new-binds (cons nb new-binds))))
    new-binds
    ))

(defun satisfying-bindings-exists
  (qvars form trie binds vdecl types objects)
  (remove-duplicates
   (mapcar #'(lambda (b)
	       (delete-if #'(lambda (bp) (assoc (car bp) qvars)) b))
	   (satisfying-bindings form trie binds
				(append qvars vdecl) types objects))
   :test #'equal))

(defun satisfying-bindings-forall (qvars form trie binds vdecl types objects)
  (cond
   ((endp qvars)
    (satisfying-bindings form trie binds vdecl types objects))
   (t (let ((blist (list (copy-list binds))))
	(dolist (obj (objects-of-type (cdar qvars) types objects))
	  (setq blist
		(mapflat
		 #'(lambda (b)
		     (mapcar #'(lambda (nb)
				 (extend-binding-with-binding b nb))
			     (satisfying-bindings-forall
			      (cdr qvars) form trie
			      (extend-binding (caar qvars) obj b)
			      vdecl types objects)))
		 blist)))
	blist))
   ))

;;;;
;; TODO: Interactive use functions.

(defun matching-atoms (pattern state)
  (let ((vdecl nil))
    (dolist (term pattern)
      (cond ((listp term) (push term vdecl))
	    ((variable-p term) (push (cons term 'object) vdecl))))
    (mapcar #'(lambda (b) (sublis b pattern))
	    (matching-bindings pattern (make-trie-from-list state)
			       nil vdecl nil *types* *objects*))))


(defun compute-derivations (state derivs strata types objects)
  (if (endp strata) derivs
    (let ((res1 (compute-derivations-1 state (first strata) types objects)))
      (compute-derivations (car res1) (append derivs (cdr res1)) (rest strata)
			   types objects))))

(defun compute-derivations-1 (state axioms types objects)
  (let ((rem (instantiate-axioms axioms types objects))
	(derivs nil)
	(new-atoms nil))
    (if (>= *verbosity* 4)
	(format t "~&applying ~s axioms in current stratum~%" (length rem)))
    ;; axiom application is a fixpoint computation: this is the outer loop
    (loop
     ;; clear new atoms
     (setq new-atoms nil)
     ;; for each remaining axiom...
     (dolist (axiom rem)
       ;; if the body of the axiom evaluates to true, add the head
       ;; atom to new-atoms
       (let ((v (eval-formula (third axiom) nil state types objects)))
       	 (if (and (first v) (second v)) ;; true and well-defined
       	       (if (not (find (second axiom) new-atoms :test #'equal))
		   (progn
		     (let ((expn (explain-formula
				  (third axiom) state types objects)))
		       (setq derivs (cons (list (second axiom)
						(third axiom)
						(third expn))
					  derivs)))
		     (push (second axiom) new-atoms)))))
       )
     ;; end of inner loop: if no new atoms were derived, we have reached
     ;; a fixpoint and return the state
     (if (endp new-atoms) (return (cons state derivs)))
     ;; else, add new atoms to state
     (setq state (append state new-atoms))
     ;; and remove from the remaining axioms list all axioms whose head
     ;; is an already derived atom.
     (setq rem (remove-if
		#'(lambda (a)
		    (find (second a) new-atoms :test #'equal))
		rem))
     )))

;; Returns (val def explanation-list).
(defun explain-formula (form state types objects)
  (cond
   ;; special case: treat an empty list as a true condition
   ((null form) (list t t nil))
   ;; logical connectives (note: handles n-ary and/or)
   ((eq (car form) 'and)
    (let ((ok t)
	  (val t)
	  (expn nil))
      (dolist (f1 (cdr form))
	(let ((v1 (explain-formula f1 state types objects)))
	  (cond
	   ;; formula becomes undefined
	   ((and ok (not (cadr v1)))
	    (setq ok nil)
	    (setq expn (caddr v1)))
	   ;; formula becomes false
	   ((and val ok (not (car v1)))
	    (setq val nil)
	    (setq expn (caddr v1)))
	   ;; formula is defined & true and remains so
	   ((and val ok (car v1) (cadr v1))
	    (setq expn (append expn (caddr v1)))))))
      (list val ok expn)))
   ((eq (car form) 'or)
    (let ((ok t)
	  (val nil)
	  (expn nil))
      (dolist (f1 (cdr form))
	(let ((v1 (explain-formula f1 state types objects)))
	  (cond
	   ;; formula becomes undefined
	   ((and ok (not (cadr v1)))
	    (setq ok nil)
	    (setq expn (caddr v1)))
	   ;; formula becomes true
	   ((and (not val) ok (car v1))
	    (setq val t)
	    (setq expn (caddr v1)))
	   ;; formula is defined & false and remains so
	   ((and (not val) ok (not (car v1)))
	    (setq expn (append expn (caddr v1)))))))
      (list val ok expn)))
   ((eq (car form) 'not)
    (if (not (= (length form) 2)) (error "ill-formed formula: ~s" form))
    (let ((v1 (explain-formula (cadr form) state types objects)))
      (list (not (car v1)) (cadr v1) (caddr v1))))
   ((eq (car form) 'imply)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let ((v1 (explain-formula (cadr form) state types objects))
	  (v2 (explain-formula (caddr form) state types objects)))
      (cond
       ;; both parts undefined
       ((and (not (cadr v1)) (not (cadr v2)))
	(list (or (not (car v1)) (car v2)) nil
	      (append (caddr v1) (caddr v2))))
       ;; antecedent undefined
       ((not (cadr v1))
	(list (or (not (car v1)) (car v2)) nil (caddr v1)))
       ;; consequent undefined
       ((not (cadr v2))
	(list (or (not (car v1)) (car v2)) nil (caddr v2)))
       ;; antecedent false
       ((not (car v1)) (list t t (caddr v1)))
       ;; consequent true
       ((car v2) (list t t (caddr v1)))
       ;; formula is false
       (t (list nil t (append (caddr v1) (caddr v2))))
       )))
   ;; quantifiers are handled by instantiating them as and/or lists
   ((eq (car form) 'forall)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let ((vars (parse-typed-list '() (cadr form) 'object)))
      (cond ((endp vars)
	     (explain-formula (caddr form) state types objects))
	    (t (explain-formula
		(cons 'and (instantiate (caddr form) nil vars types objects))
		state types objects)))))
   ((eq (car form) 'exists)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let ((vars (parse-typed-list '() (cadr form) 'object)))
      (cond ((endp vars)
	     (explain-formula (caddr form) state types objects))
	    (t (explain-formula
		(cons 'or (instantiate (caddr form) nil vars types objects))
		state types objects)))))
   ;; preference (ignored)
   ((eq (car form) 'preference)
    (if (or (< (length form) 2) (> (length form) 3))
	(error "ill-formed formula: ~s" form))
    (list t t nil))
   ;; equality
   ((eq (car form) '=)
    (if (not (= (length form) 3)) (error "ill-formed formula: ~s" form))
    (let* ((v1 (eval-term (cadr form) nil state))
	   (v2 (eval-term (caddr form) nil state)))
      (cond
       ;; undefined terms
       ((null (car v1)) (list nil nil (cadr form)))
       ((null (car v2)) (list nil nil (caddr form)))
       ;; equal
       ((equal (car v1) (car v2))
	(list t t (list (list '= (car v1) (car v2)))))
       ;; not equal
       (t (list nil t (list (list '= (car v1) (car v2))))))))
   ;; numeric predicates
   ((assoc (car form) *builtin-numeric-predicates*)
    (let ((pdef (assoc (car form) *builtin-numeric-predicates*))
	  (vlist (eval-term-list (cdr form) nil state)))
      (error "explain-formula not implemented for numeric predicates")))
   ;; type name used as unary predicate (if enabled)
   ((and *type-names-are-predicates*
	 (or (assoc (car form) types) (rassoc (car form) types))
	 (= (length (cdr form)) 1))
    (let ((vlist (eval-term-list (cdr form) nil state)))
      (cond
       ;; undefined term
       ((null (caar vlist)) (list nil nil (cadr form)))
       ;; defined term, of type
       ((object-can-substitute-for-type
	 (caar vlist) (car form) types objects nil)
	(list t t (caar vlist)))
       ;; not of type
       (t (list nil t (caar vlist))))))
   ;; finally, an atom: but the atom may have complex terms
   (t (let* ((vlist (eval-term-list (cdr form) nil state))
	     (ground-atom (cons (car form) (car vlist))))
	(cond
	 ;; undefined
	 ((some #'null (car vlist))
	  (list nil nil (remove-if #'null
				   (mapcar #'(lambda (term value)
					       (if value nil term))
					   (cdr form) vlist))))
	 ;; true
	 ((find ground-atom state :test #'equal)
	  (list t t (list ground-atom)))
	 ;; false
	 (t (list nil t (list (list 'not ground-atom)))))))
   ))


;; force update of symbol completion table on load
;; (eval-when (:load-toplevel)
;;   (if (find-package "ECL-READLINE")
;;       (let ((return-to-package *package*))
;; 	(in-package "ECL-READLINE")
;; 	(setq *current-package* nil)
;; 	(in-package return-to-package))))
