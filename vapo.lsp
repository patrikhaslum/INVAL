
;;;;
;; Validation of state-action policy for probabilistic domains (experimental).

;; policy can be either:
;;  - A function of one argument.
;;    It will be called with a state (list of literals) and is expected
;;    to return a list of candidate ((...) (action)) pairs (rules). The
;;    first component of the rule is intended to be a partial state (as
;;    in an explicit rule-list policy, below) but nothing, other than
;;    possibly the ambiguous-policy-resolver (see below) depends on this.
;;  - A list of ((partial state) (action)) pairs (rules).
;;    The rule antecedent (partial state) is a list of literals, which
;;    may be positive or negative; fluent expressions are limited to
;;    equalities or negated equalities.
;;    The extraction of candidate rules for a given state depends on the
;;    keyword argument 'exact:
;;    - if 'exact is non-nil, candidate rules are whose antecendent
;;      (partial state) match the state exactly, after all instances of
;;      predicates in 'predicates-to-ignore have been removed from the
;;      state;
;;    - if 'exact is nil, candidate rules are those whose antecedent is
;;      matched (i.e., implied) by the state and that are most specific;
;;      a partial state p is more specific than p' if p' is a strict
;;      subset of p.
;;
;; A policy (of any type) is said to be ambiguous iff it returns more
;; than one candidate rule for any state encountered in its exectution.
;; If the keyword parameter ambiguous-policy-resolver is nil, then ambiguity
;; is treated as an execution error. Otherwise, ambiguous-policy-resolver
;; is expected to be a function that takes the list of candidate rules
;; and returns one of them. To pick an arbitrary element from the list,
;; set the parameter to #'first.
;;
;; init, goal, actions, type and objects are as in validate-plan.
;;
;; reward-exp is a (numeric) term, or nil.
;;
;; Returns a list (ok expected-reward state-graph), where:
;;  ok: is t iff the policy is valid (executes without error), and is
;;      proper
;;  exepcted-reward: is the expected reward (negative cost); this
;;      value is only meaningful if the policy is valid and proper
;;  state-graph: is the policy-reachable sub-graph of the state space
;;      (as returned by build-state-graph).

(defun validate-policy (policy init goal actions types objects reward-exp
			       &key (exact nil)
			       (predicates-to-ignore nil)
			       (ambiguous-policy-resolver nil)
			       (expand-goal-states nil))
  (when (not (member 'probabilistic *quoted-argument-predicates*))
    (setq *quoted-argument-predicates*
	  (cons 'probabilistic *quoted-argument-predicates*)))
  (let* ((policy-fn
	  (cond
	   ((functionp policy)
	    (format t "~&using provided policy function~%")
	    policy)
	   (exact
	    (format t "~&using exact policy match,~%ignoring predicates ~a~%"
		    predicates-to-ignore)
	    (lambda (state)
	      (apply-exact-policy-to-state
	       (remove-if #'(lambda (atom)
			      (find (car atom) predicates-to-ignore))
			  state)
	       policy)))
	   (t
	    (format t "~&using most specific policy match~%")
	    (lambda (state)
	      (apply-most-specific-policy-to-state state policy)))
	   ))
	 (sg ;; list (ok graph)
	  (build-state-graph policy-fn init goal actions types objects
			     reward-exp (fluents-in-term reward-exp)
			     :ambiguous-policy-resolver ambiguous-policy-resolver
			     :expand-goal-states expand-goal-states)))
    (if (first sg) ;; policy executed without error
	(if (check-is-proper (second sg))
	    (list t (if reward-exp (compute-expected-reward (second sg)) 0)
		  (second sg))
	  (list nil 0 (second sg))))
    ))

(defun fluents-in-term (term)
  (let ((res (eval-term term nil nil :report-errors nil)))
    (second res)))

;; Check if a policy is proper. sgraph is the policy-reachable state graph
;; (as returned by build-state-graph). Returns t iff every terminal component
;; of the state graph is a goal state.

(defun check-is-proper (sgraph)
  (let* ((outgoing (state-graph-edges sgraph))
	 (incoming (reverse-edges outgoing))
	 (comps (scc (length sgraph) outgoing incoming)))
    (when (>= *verbosity* 2) (format t "~&state graph SCCs:~%~a~%" comps))
    (dolist (comp comps t)
      (when (is-terminal-component comp sgraph)
	(when (not (every #'(lambda (sg-index) (fourth (elt sgraph sg-index)))
			  comp))
	  (when (>= *verbosity* 1)
	    (format t "~&policy is NOT proper:~%component ~a is terminal but not a goal state~%" comp)
	    (return nil))))
      )))

;; comp is a list of state-graph indices: return non-nil iff this is a
;; terminal component (no transition to any state outside of it).
(defun is-terminal-component (comp sgraph)
  (dolist (sg-index comp t)
    (when (not (subsetp (mapcar #'second (third (elt sgraph sg-index))) comp))
      (return nil))
    ))

(defun state-graph-edges (sgraph)
  (let ((outgoing nil))
    (dotimes (index (length sgraph))
      (let ((translist (third (elt sgraph index))))
	(setq outgoing
	      (cons (cons index (mapcar #'second translist)) outgoing))))
    outgoing))

(defun reverse-edges (emap)
  (let ((rmap nil))
    (dolist (entry emap)
      (dolist (tnode (rest entry))
	(setq rmap (add-to-set-map tnode (first entry) rmap))))
    rmap))

(defun compute-expected-reward (sgraph)
  (let ((m (make-array (list (length sgraph) (+ (length sgraph) 1))
		       :element-type 'rational :initial-element 0)))
    ;; make coefficient matrix
    (dotimes (index (length sgraph))
      (let ((sg-node (elt sgraph index))
	    (rhs 0))
	(cond
	 ((fourth sg-node) ;; is a goal state
	  (setf (aref m index index) 1))
	 (t ;; not a goal state
	  (setf (aref m index index) 1)
	  (dolist (trans (third sg-node))
	    (setf (aref m index (second trans))
		  (+ (aref m index (second trans)) (* -1 (first trans))))
	    (setq rhs (+ rhs (* (first trans) (third trans)))))
	  (setf (aref m index (length sgraph)) rhs))
	 )))
    ;; solve it
    (solve m)
    ;; set value (expected reward) for each state
    (dotimes (index (length sgraph))
      (let ((sg-node (elt sgraph index)))
	(setf (fifth sg-node) (aref m index (length sgraph)))))
    ;; return value of S0
    (aref m 0 (length sgraph))
    ))

(defun solve (m)
  ;;(format t "~&input matrix:~%~a~%" m)
  ;; for each row from 0 .. n-1
  (dotimes (i (- (array-dimension m 0) 1))
    ;; m[i,i] should be non-zero
    (assert (not (= (aref m i i) 0)) () "~&m[~a,~a] is ~a" (aref m i i) i i)
    ;; for each row from i+1 to n
    (dotimes (j (- (array-dimension m 0) (+ i 1)))
      (add-to-row m (+ i j 1) (* -1 (/ (aref m (+ i j 1) i) (aref m i i))) i))
    )
  ;;(format t "~&triangular matrix:~%~a~%" m)
  ;; back substitution
  (do ((i (- (array-dimension m 0) 2) (- i 1))) ((< i 0))
      ;; v[i+1] = m[i+1,n]
      ;; for each row j in 0..i, subtract m[j,i+1] * v[i+1] from m[j,n],
      ;; and set m[j,i+1] to 0
      (dotimes (j (+ i 1))
	(setf (aref m j (- (array-dimension m 1) 1))
	      (- (aref m j (- (array-dimension m 1) 1))
		 (* (aref m j (+ i 1))
		    (aref m (+ i 1) (- (array-dimension m 1) 1)))))
	(setf (aref m j (+ i 1)) 0))
      ;; then set m[i,n] to m[i,n] / m[i,i] and m[i,i] to 1
      (setf (aref m i (- (array-dimension m 1) 1))
	    (/ (aref m i (- (array-dimension m 1) 1)) (aref m i i)))
      (setf (aref m i i) 1))
  ;;(format t "~&matrix after substitution:~%~a~%" m)
  )

;; add f * m[q,:] to m[r,:]
(defun add-to-row (m r f q)
  (dotimes (k (array-dimension m 1))
    (setf (aref m r k) (+ (aref m r k) (* f (aref m q k))))
    ))

;; Build the policy-reachable state graph from init.
;; policy-fn is a function that takes a state and returns a list of
;; ((state) (action)) pairs
;; Returns: a list (ok graph), where ok is non-nil iff the policy
;; executes without error, and the the state graph is a list of
;; (state action transitions is-goal expected-reward) lists;
;; transitions is a list of (probability index reward) pairs.

(defun build-state-graph (policy-fn init goal actions types objects
				    reward-exp reward-fluents
				    &key (ambiguous-policy-resolver nil)
				    (expand-goal-states nil))
  (do ((sgraph (list (list init nil nil nil nil)))
       (queue (list 0))
       (ok t)
       )
      ((or (endp queue) (not ok)) (list ok sgraph))
      (when (>= *verbosity* 2)
	(format t "~&expanding state ~s of ~s, |queue| = ~s~%"
		(car queue) (length sgraph) (length queue)))
      (let* ((next-state (first (nth (car queue) sgraph)))
	     (goal-eval (eval-formula goal nil next-state types objects))
	     (result
	      (if (and (first goal-eval) (second goal-eval)
		       (not expand-goal-states)) nil
		(expand-state next-state policy-fn ambiguous-policy-resolver
			      actions types objects reward-exp reward-fluents)))
	     (exp-ok
	      (if (and (first goal-eval) (second goal-eval)
		       (not expand-goal-states)) t
		(first result)))
	     (exp-action
	      (if (and (first goal-eval) (second goal-eval)
		       (not expand-goal-states)) nil
		(second result)))
	     (exp-succs
	      (if (and (first goal-eval) (second goal-eval)
		       (not expand-goal-states)) nil
		(third result)))
	     (trans nil))
	(when (>= *verbosity* 3)
	  (format t "~&goal: ~a~%result: ~a~%" goal-eval result))
	;; update graph with result of expansion, even if it failed
	(dolist (ps exp-succs)
	  (let ((index (find-state-in-graph (second ps) sgraph)))
	    (when (null index)
	      ;; state is new
	      (setq sgraph
		    (nconc sgraph (list (list (second ps) nil nil nil nil))))
	      (setq index (- (length sgraph) 1))
	      (setq queue (nconc queue (list index))))
	    (setq trans (nconc trans (list (list (first ps) index (third ps)))))))
	(setf (second (nth (car queue) sgraph)) exp-action)
	(setf (third (nth (car queue) sgraph)) trans)
	(setf (fourth (nth (car queue) sgraph))
	      (and (first goal-eval) (second goal-eval)))
	(setq queue (cdr queue))
	(when (not exp-ok)
	  (when (>= *verbosity* 1)
	    (format t "~&expanding state:~%~s~%failed~%" next-state))
	  (setq ok nil)) ;; break loop
	(when (not (second goal-eval))
	  (when (>= *verbosity* 1)
	    (format t "~&goal formula ~s undefined in state~%~s~%"
		    goal next-state))
	  (setq ok nil)) ;; break loop
	)))

(defun find-state-in-graph (state sgraph)
  (let ((index 0))
    (loop
     (when (endp sgraph) (return nil))
     (when (state-equals state (first (car sgraph)))
       (return index))
     (setq index (+ index 1))
     (setq sgraph (cdr sgraph))
     )))

;; Returns the list of ((state) (action)) pairs from the policy
;; that match the given state, using either exact or most specific
;; partial state matching.

(defun apply-policy-to-state
    (state policy &key (exact nil) (predicates-to-ignore nil))
  (cond
   (exact
    (apply-exact-policy-to-state
     (remove-if #'(lambda (atom)
		    (find (car atom) predicates-to-ignore))
		state)
     policy))
   (t
    (apply-most-specific-policy-to-state state policy))
   ))

;; Returns a list of the ((state) (action)) pairs from policy
;; where the state component matches the given state exactly.

(defun apply-exact-policy-to-state (state policy)
  (let ((cands nil))
    (dolist (item policy)
      (if (state-equals state (first item))
	  (setq cands (cons item cands))))
    cands))

;; Returns a list of the most specific ((partial state) (action))
;; pairs applicable to state.

(defun apply-most-specific-policy-to-state (state policy)
  (let ((cands nil))
    (dolist (item policy)
      (if (state-implies-partial-state state (first item))
	  (if (not (some #'(lambda (citem)
			     (more-specific (first citem) (first item)))
			 cands))
	      (setq cands
		    (cons item
			  (remove-if #'(lambda (citem)
					 (more-specific (first item) (first citem)))
				     cands))))))
    cands))


;; Expand a state using a policy.
;; Returns a list (ok action successors), where successors is a list
;; of pairs (probability state reward). Probabilities should sum to one.

(defun expand-state (state policy-fn ambiguous-policy-resolver actions types objects reward-exp reward-fluents)
  (let ((cands (funcall policy-fn state)))
    (cond
     ((endp cands)
      (when (>= *verbosity* 1)
	(format t "~&policy has no action for state ~s~%" state))
      (list t nil nil))
     ((> (length cands) 1)
      (when (>= *verbosity* 1)
	(format t "~&policy is ambiguous for state~% ~s~%" state)
	(dolist (item cands)
	  (format t "~% ~s -> ~s matches~%" (first item) (second item))))
      (if ambiguous-policy-resolver
	  (let ((chosen (funcall *ambiguous-policy-resolver* cands)))
	    (if chosen
		(expand-state-with-action state (second chosen) actions
					  types objects reward-exp
					  reward-fluents)
	      ;; if resolver returns nil, return failure
	      (list nil (mapcar #'second cands) nil)))
	;; if resolver is nil (not set), return a failure
	(list nil (mapcar #'second cands) nil)))
     (t ;; exactly one policy rule applies
      (expand-state-with-action state (second (first cands)) actions
				types objects reward-exp reward-fluents))
     )))

(defun expand-state-with-action (state action actions types objects reward-exp reward-fluents)
  (when (>= *verbosity* 2)
    (format t "~&applying action ~s~%" action))
  (let ((ea (check-action action state actions types objects)))
    (cond
     ((not (first ea))
      (when (>= *verbosity* 1)
	(format t "~&action ~s is undefined or inapplicable in state:~%~s~%" action state))
      (list nil action nil))
     (t (list t action
	      (apply-probabilistic-action (cons action ea) state
					  reward-exp reward-fluents))))
    ))


;; Apply the effects of a probabilistic action to a state
;; ea is the list (action ok read add del abs rel); probabilistic
;; effects appear in add.
;; reward-exp is the reward expression (a term)
;; reward-fluents is a list of ground fluents that appear in the reward
;; expressions; these are not updated by relative effects (increase/decrease),
;; since their effect is applied only to the reward expression.
;; Returns a list of (probability state reward) lists.

(defun apply-probabilistic-action (ea state reward-exp reward-fluents)
  (mapcar #'(lambda (oc)
	      (list (first oc)
		    (apply-effects
		     (list (list (first ea) t nil (second oc) (third oc)
				 (fourth oc)
				 (remove-if #'(lambda (rel-eff)
						(member (second rel-eff)
							reward-fluents
							:test #'equal))
					    (fifth oc))
				 nil))
		     state)
		    ;; compute transition reward
		    (if reward-exp
			(eval-delta reward-exp reward-fluents (fifth oc) state)
		      nil)
		    ))
	  (let ((oc (outcomes (fourth ea) nil (fifth ea) (sixth ea) (seventh ea))))
	    (when (>= *verbosity* 3)
	      (format t "~&effect translated into outcomes:~%~a~%" oc))
	    oc)
	  ))

;; Evaluate the effect of a set of fluent relative effects on a numeric term.
;; term is a (numeric) term
;; fluents is the list of fluents appearing in term
;; frels is a list of fluent relative effects (increase/decrease)
;; state is the state.
(defun eval-delta (term fluents frels state)
  (let ((rstate (eval-relative-effects fluents frels state)))
    (if (first rstate)
	(let ((val (eval-term term nil (second rstate))))
	  ;; (format t "~&frels: ~a, rstate: ~a, term: ~a, value: ~a~%" frels rstate term val)
	  (first val))
      nil)))

(defun eval-relative-effects (fluent-list frels state)
  (let ((rstate (mapcar #'(lambda (fluent) (list '= fluent 0)) fluent-list)))
    (dolist (fre frels (list t rstate))
      (when (member (second fre) fluent-list :test #'equal)
	(when (not (member (first fre) '(increase decrease)))
	  (format t "~&invalid fluent relative effect: ~a~%" fre)
	  (return (list nil nil)))
	(let ((cfa (find-fluent-assignment (second fre) rstate))
	      (v1 (eval-term (third fre) nil state)))
	  (when (not (first v1)) (return (list nil nil)))
	  ;; (format t "~&update ~a with ~a~%" cfa v1)
	  (setf (third cfa)
		(if (eq (car fre) 'increase) (+ (third cfa) (first v1))
		  (- (third cfa) (first v1))))))
      )))

;; Compute outcomes of a list
;; adds-and-prob is a list that may contain probabilistic and atomic
;; add effects. It is assumed that the effects contained in probabilistic
;; cases are non-conditional and non-quantified (though they may be
;; conjunctive).
;; adds is a list of atomic (unconditional) add effects.
;; dels is a list of atomic delete effects.
;; fabs is a list of absolute fluent effects (assignments).
;; dels is a list of relative fluent effects (increase/decrease)
;; Returns a list of outcomes (probability add del fabs frel), where add,
;; del, fabs frel are lists of atomic add/delete effects and fluent
;; assignment and relative effects.

(defun outcomes (adds-and-prob adds dels fabs frel)
  (cond ((endp adds-and-prob)
	 (list (list 1 adds dels fabs frel)))
	((eq (caar adds-and-prob) 'probabilistic)
	 (do ((cases (cdar adds-and-prob) (cddr cases))
	      (ocs nil)
	      (ptotal 0))
	     ((endp cases)
	      (if (< ptotal 1)
		  (let ((no-case-ocs
			 (outcomes (cdr adds-and-prob) adds dels fabs frel)))
		    (append ocs (mapcar #'(lambda (oc)
					    (cons (* (- 1 ptotal) (car oc))
						  (cdr oc)))
					no-case-ocs)))
		ocs))
	     (let* ((prob (car cases))
		    ;; collect-effects returns (ok read add del abs rel)
		    (peff (collect-effects
			   (cadr cases) t nil nil nil nil nil nil nil nil))
		    (case-ocs (outcomes (cdr adds-and-prob)
					(append (third peff) adds)
					(append (fourth peff) dels)
					(append (fifth peff) fabs)
					(append (sixth peff) frel)
					))
		    )
	       (setq ocs
		     (append ocs (mapcar #'(lambda (oc)
					     (cons (* prob (car oc)) (cdr oc)))
					 case-ocs)))
	       (setq ptotal (+ ptotal prob))
	       )))
	(t (outcomes (cdr adds-and-prob)
		     (cons (car adds-and-prob) adds)
		     dels fabs frel))
	))


;; Trivial implementation of (partial) state implication (non-strict).

(defun state-implies-partial-state (state pstate)
  (cond ((endp pstate) t)
	((eq (caar pstate) 'not)
	 (when (not (= (length (car pstate)) 2))
	   (error "ill-formed formula: ~s" (car (pstate))))
	 (if (not (find (second (car pstate)) state :test #'equal))
	     (state-implies-partial-state state (cdr pstate)) nil))
	((find (car pstate) state :test #'equal)
	 (state-implies-partial-state state (cdr pstate)))
	(t nil)))

;; t iff more-spec-pstate is a more specific partial state than
;; less-spec-pstate.
(defun more-specific (more-spec-pstate less-spec-pstate)
  (and (partial-state-contains more-spec-pstate less-spec-pstate)
       (> (length more-spec-pstate) (length less-spec-pstate))))

;; t iff state-a contains state-b and they have the same size
;; (this assumes no duplicates!)
(defun state-equals (state-a state-b)
  (and (= (length state-a) (length state-b))
       (partial-state-contains state-a state-b)))


(defun partial-state-contains (super-pstate sub-pstate)
  (cond ((endp sub-pstate) t)
	((find (car sub-pstate) super-pstate :test #'equal)
	 (partial-state-contains super-pstate (cdr sub-pstate)))
	(t nil)))
