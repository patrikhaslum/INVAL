
(define (domain lists)
  (:constants null)

  (:predicates
   (in-list ?e)
   (follows ?e1 ?e2)
   )

  (:functions
   (prev ?e) - object
   (next ?e) - object
   (first) - object
   (last) - object
   )

  (:derived (follows ?e (next ?e))
	    (and (in-list ?e) (in-list (next ?e))))

  (:derived (follows ?e1 ?e2)
  	    (and (in-list ?e1)
  		 (in-list ?e2)
  		 (follows (next ?e1) ?e2)))


  (:action make-list
   :parameters (?e)
   :precondition (forall (?x) (not (in-list ?x)))
   :effect (and (in-list ?e)
		(assign (prev ?e) null)
		(assign (next ?e) null)
		(assign (first) ?e)
		(assign (last) ?e))
   )

  (:action insert-before
   :parameters (?e ?p)
   :precondition (and (in-list ?p)
		      (not (in-list ?e)))
   :effect (and (assign (next ?e) ?p)
		(assign (prev ?e) (prev ?p))
		(assign (prev ?p) ?e)
		(assign (next (prev ?p)) ?e)
		(when (= (first) ?p) (assign (first) ?e))
		(in-list ?e))
   )

  (:action insert-after
   :parameters (?e ?p)
   :precondition (and (in-list ?p)
		      (not (in-list ?e)))
   :effect (and (assign (prev ?e) ?p)
		(assign (next ?e) (next ?p))
		(assign (next ?p) ?e)
		(assign (prev (next ?p)) ?e)
		(when (= (last) ?p) (assign (last) ?e))
		(in-list ?e))
   )

  (:action delete
   :parameters (?e)
   :precondition (in-list ?e)
   :effect (and (assign (next (prev ?e)) (next ?e))
		(assign (prev (next ?e)) (prev ?e))
		(assign (prev ?e) undefined)
		(assign (next ?e) undefined)
		(when (= (first) ?e) (assign (first) (next ?e)))
		(when (= (last) ?e) (assign (last) (prev ?e)))
		(not (in-list ?e)))
   )

  (:action reverse
   :effect (and (assign (first) (last))
		(assign (last) (first))
		(forall (?e)
			(when (in-list ?e)
			  (and (assign (prev ?e) (next ?e))
			       (assign (next ?e) (prev ?e))))))
   )

  )

(define (problem test)
  (:domain lists)

  (:objects a b c d)

  (:init ) ;)

  (:goal (and (= (first) d)
	      (= (next d) c)
	      (= (next c) b)
	      (= (next b) a)))
  )

(:plan
 (make-list b)
 (insert-before a b)
 (insert-after d b)
 (insert-before c d)
 (reverse)
 )
