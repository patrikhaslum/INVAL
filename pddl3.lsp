
;(load "inval.lsp")
;(load "itt.lsp")


;;;;
;; PDDL3 plan constraint compilation (destructive).

(defvar *eok-counter* 0)

;; Compile constraint (sometime alpha), where alpha is atomic, into
;; the domain & problem.

(defun compile-sometime (atom)
  (let ((ok-pred (symnumcat 'e-ok (setq *eok-counter* (+ *eok-counter* 1)))))
    (setq *predicates* (cons (list ok-pred) *predicates*))
    (setq *goal* (merge-conjunctions (list ok-pred) *goal*))
    (dolist (act *actions*)
      (let ((addcond (make-atom-true atom (cdr act))))
	(cond ((eq addcond ':true)
	       (rplacd act
		       (reassoc ':effect
				(merge-conjunctions
				 (list ok-pred)
				 (assoc-val ':effect (cdr act)))
				(cdr act))))
	      (addcond
	       (rplacd act
		       (reassoc ':effect
				(merge-conjunctions
				 (list 'when addcond (list ok-pred))
				 (assoc-val ':effect (cdr act)))
				(cdr act))))
	      )))
    ok-pred))

;; Compile constraint (sometime-before alpha beta), where alpha and beta
;; are both atomic, into the domain & problem.

(defun compile-sometime-before (alpha beta)
  (let ((ok-pred (compile-sometime beta)))
    (dolist (act *actions*)
      (let ((addcond (make-atom-true alpha (cdr act))))
	(cond ((eq addcond ':true)
	       (rplacd act
		       (reassoc ':precondition
				(merge-conjunctions
				 (list ok-pred)
				 (assoc-val ':precondition (cdr act)))
				(cdr act))))
	      (addcond
	       (rplacd act
		       (reassoc ':precondition
				(merge-conjunctions
				 (list 'imply addcond (list ok-pred))
				 (assoc-val ':effect (cdr act)))
				(cdr act))))
	      )))))

;; Compile in tracking of a specific action sequence (destructive).
;; The compiled domain will have conditional effects.
;; plan is a plan (list of happenings), as in *plans* but must be
;; sequential (exactly one action per happening)
;; plan-id is a symbol that will be used to prefix tracking predicates.
;; Returns: A list of two atoms ((plan-id-done) (plan-id-div)); on
;; execution of any plan in the compiled domain, (plan-done) will hold
;; in the final state if it matches the tracked action sequence (exactly);
;; if it does not, the condition (or (not (plan-done)) (plan-div)) will
;; hold.

(defun track-action-sequence (plan plan-id)
  (let ((splan (mapcar #'(lambda (step)
			   (when (> (length step) 1)
			     (error "~&plan is not a sequence: ~s~%" step))
			   (first step))
		       plan))
	(step-preds nil)
	(done-pred (list (symnumcat plan-id '-done)))
	(div-pred (list (symnumcat plan-id '-div)))
	)
    ;; create list of step predicates
    (dotimes (step-num (length splan))
      (setq step-preds
	    (nconc step-preds
		   (list (list (symnumcat plan-id '-step- step-num))))))
    (setq step-preds (nconc step-preds (list done-pred)))
    (setq step-preds (nconc step-preds (list div-pred)))
    ;; for each action
    (dolist (act *actions*)
      (let ((matches (find-indices splan (car act) :key #'first))
	    (new-effects nil))
	(dolist (index matches)
	  (when (not (eq (length (cdr (nth index splan)))
			 (length (assoc-val ':parameters (cdr act)))))
	    (error "~&step ~a : ~a does not match parameters of action:~%~a~%"
		   index (nth index splan) act))
	  (let* ((param-constraints
		  (mapcar #'(lambda (par arg) (list '= (car par) arg))
			  (assoc-val ':parameters (cdr act))
			  (cdr (nth index splan))))
		 (effcond (append (list 'and (nth index step-preds))
				  param-constraints))
		 (ce (list 'when effcond
			   (list 'and (nth (+ index 1) step-preds)
				 (list 'not (nth index step-preds))))))
	    (push ce new-effects)))
	(cond
	 ((null new-effects) (push div-pred new-effects))
	 (t (let ((div-cond
		   (cons 'and (mapcar #'(lambda (ce) (list 'not (second ce)))
				      new-effects))))
	      (push (list 'when div-cond div-pred) new-effects))))
	(rplacd act
		(reassoc ':effect
			 (merge-conjunctions
			  (cons 'and new-effects)
			  (assoc-val ':effect (cdr act)))
			 (cdr act)))
	))
    (setq *predicates* (nconc *predicates* step-preds))
    (setq *init* (cons (first step-preds) *init*))
    (list done-pred div-pred)
    ))

(defun find-indices (seq element &key (key #'identity))
  (let ((indices nil))
    (dotimes (i (length seq))
      (when (eq (funcall key (nth i seq)) element)
	(push i indices)))
    (reverse indices)))

;;;;
;; Plan set analysis

;; Find a set of constraints that hold in all *plans*.
;; Constraints returned are of the forms:
;;  (sometime phi) where phi is an atom or a disjunction of atoms
;;  (sometime-before alpha beta), where alpha and beta are atoms

(defun find-satisfied-constraints
  (&key (clean t) (static-pred nil) (limit nil))
  (let ((seqs (get-state-sequences :clean clean :static-pred static-pred)))
    (append
     (mapcar #'(lambda (atom-set)
		 (list 'always
		       (if (> (length atom-set) 1) (cons 'or atom-set)
			 (first atom-set))))
	     (find-common-always seqs '(()) :limit limit))
     (mapflat #'(lambda (pair)
		  (mapcar #'(lambda (atom)
			      (list 'sometime-before (car pair) atom))
			  (cdr pair)))
	      (find-common-sb seqs nil))
     ;; extraction of sometime-after constraints is not correct, so exclude
     ;; it for now.
     ;; (mapflat #'(lambda (pair)
     ;; 		  (mapcar #'(lambda (atom)
     ;; 			      (list 'sometime-after (car pair) atom))
     ;; 			  (cdr pair)))
     ;; 	      (find-common-sa seqs nil))
     )))

(defun find-violated-constraints
  (&key (clean t) (static-pred nil) (limit nil))
  (let ((seqs (get-state-sequences :clean clean :static-pred static-pred)))
    (append
     (mapcar #'(lambda (atom-set)
		 (list 'sometime
		       (if (> (length atom-set) 1)
			   (cons 'and (mapcar #'(lambda (atom)
						  (list 'not atom))
					      atom-set))
			 (list 'not (first atom-set)))))
	     (find-common-always seqs '(()) :limit limit))
     (mapflat #'(lambda (pair)
		  (mapcar #'(lambda (atom)
			      (list 'sometime-before atom (car pair)))
			  (cdr pair)))
	      (find-common-sb seqs nil))
     (mapflat #'(lambda (pair)
		  (mapcar #'(lambda (atom)
			      (list 'sometime-after atom (car pair)))
			  (cdr pair)))
	      (find-common-sa seqs nil))
     )))

;; get state sequences for valid plans, and optionally clean them

(defun get-state-sequences (&key (clean t) (static-pred nil))
  (mapcar #'third
	  (remove nil
		  (mapcar
		   #'(lambda (plan)
		       (validate-plan
			(car plan) (cdr plan) *init* *goal* *constraints* nil
			*actions* (stratify *axioms*) *types* *objects*
			:visualisation
			#'(lambda (p s)
			    (if clean
				(clean-state-seq s :static-pred static-pred)
			      s))))
		   *plans*)
		  :key #'first)))

;; remove fluent assignments and (optionally) static facts from each
;; state in a sequence.

(defun clean-state-seq (seq &key (static-pred nil))
  (mapcar #'(lambda (state)
	      (remove-if #'(lambda (atom)
			     (or (eq (car atom) '=)
				 (member (car atom) static-pred)))
			 state))
	  seq))

(defun save-satisfied-constraints
  (filename &key (clean t) (static-pred nil) (limit nil))
  (with-open-file
   (stream filename :direction :output)
   (format stream "(define (problem satisifed)~%")
   (format stream "  (:constraints~%")
   (format stream "   (and~%")
   (dolist (con (find-satisfied-constraints
		 :clean clean :static-pred static-pred :limit limit))
     (format stream "    ~a~%" con))
   (format stream "   )))~%")
   ))


;; Returns a list of sets of ground atoms such that the disjunction over
;; each set holds in every state in every sequence.

(defun find-common-always (seqs cands &key (limit nil))
  (if (endp seqs) cands
    (find-common-always (rest seqs)
			(find-always (first seqs) cands :limit limit)
			:limit limit)))

(defun find-always (seq cands &key (limit nil))
  (if (endp seq) cands
    (find-always (rest seq)
		 (check-always-candidates cands (first seq) nil :limit limit)
		 :limit limit)))

(defun check-always-candidates
  (cands state new-cands &key (limit nil))
  (cond ((endp cands) new-cands)
	((find-any (first cands) state :test #'equal)
	 (check-always-candidates
	  (rest cands) state (cons (first cands) new-cands)
	  :limit limit))
	((and (numberp limit) (>= (length (first cands)) limit))
	 (check-always-candidates
	  (rest cands) state new-cands :limit limit))
	(t (check-always-candidates
	    (rest cands) state
	    (extend-always-candidate
	     (first cands) state new-cands (rest cands))
	    :limit limit))
	))

(defun extend-always-candidate (cand state new-cands cands)
  (if (endp state) new-cands
    (let ((ecand (cons (first state) cand)))
      (if (or (some #'(lambda (x) (subsetp x ecand :test #'equal)) new-cands)
	      (some #'(lambda (x) (subsetp x ecand :test #'equal)) cands))
	  (extend-always-candidate cand (rest state) new-cands cands)
      (extend-always-candidate
       cand (rest state) (cons ecand new-cands) cands)))))

(defun find-any (lista listb &key (test #'eq))
  (some #'(lambda (el) (find el listb :test test)) lista))


;; Returns an assoc list of entries (atom . prev-atoms) such that each
;; atom in the list prev-atoms is true sometime (strictly) before the
;; first occurrence of 'atom in each state sequence.

(defun find-common-sb (seqs cands)
  (if (endp seqs) cands
    (find-common-sb
     (rest seqs) (combine-sb-candidates
		  (find-sb (first seqs) nil nil) cands))))

;; NOT CORRECT: We can find common _strict_ sa's by doing sb's on the
;; reversed seqeunces.
;; The problem is that common sb's can include constraints that are
;; satisfied on some sequences because the trigger is never true; this
;; makes the reversed sa constraint unsatisfied.
(defun find-common-sa (seqs cands)
  (find-common-sb (mapcar #'reverse seqs) cands))

(defun find-sb (seq prev cands)
  (if (endp seq) cands
    (let ((new-facts (set-difference (first seq) prev :test #'equal)))
      (find-sb (rest seq) (union prev new-facts :test #'equal)
	       (if prev (append (mapcar #'(lambda (f) (cons f prev))
					new-facts)
				cands)
		 cands)))))

;; For each entry (atom . list) in clist{1,2}: if there is an entry
;; with the same atom in the other clist, then assoc the atom with the
;; intersection of the two lists; else keep the entry as is.

(defun combine-sb-candidates (clist1 clist2)
  (append
   (remove nil
	   (mapcar #'(lambda (ent1)
		       (let ((ent2 (assoc (car ent1) clist2 :test #'equal)))
			 (if (null ent2) ent1
			   (let ((iset (intersection
					(cdr ent1) (cdr ent2) :test #'equal)))
			     (if iset (cons (car ent1) iset) nil)))))
		   clist1))
   (set-difference clist2 clist1 :key #'car :test #'equal)))
