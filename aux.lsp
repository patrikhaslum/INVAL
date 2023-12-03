
;;;;
;; Auxiliary (mostly domain-specific) functions

(defun next-state (state action)
  (let ((res (execute-plan (list (list action)) (cons '(= (reward) 0) state)
			   *actions* (stratify *axioms*) *types* *objects*)))
    (when (not (first res))
      (error "error executing ~a in~%~a~%" action state))
    (remove-if #'(lambda (atom)
		   (and (eq (car atom) '=) (equal (second atom) '(reward))))
	       (cdr res))))

(defun catan-dice-abs-fun (state aseq)
  (cond
   ((endp aseq) nil)
   ((eq (caar aseq) 'reroll)
    (let ((kept
	   (remove-if #'(lambda (count) (eq (second count) 'zero))
		      (mapcar #'(lambda (res)
				  (cons res
					(first (find-predicate-arguments
						'available '(2) '(1) (list res) state))))
			      '(ore grain wool timber brick gold)))))
      (if kept
	  (cons (cons 'keep kept)
		(catan-dice-abs-fun (next-state state (car aseq)) (cdr aseq)))
	(catan-dice-abs-fun (next-state state (car aseq)) (cdr aseq)))))
   ((eq (caar aseq) 'finish-build)
    (cons (car aseq)
	  (catan-dice-abs-fun (next-state state (car aseq)) (cdr aseq))))
   (t (catan-dice-abs-fun (next-state state (car aseq)) (cdr aseq)))
   ))
