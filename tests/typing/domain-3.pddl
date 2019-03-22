
(define (domain dummy)
  (:requirements :typing :adl)

  (:types typeA typeB - object
	  typeC - (either typeA typeB)
	  )

  (:predicates (p ?x - typeA) (q ?x - typeB) (static-true))

  (:action do-it
   :parameters (?x - object)
   :precondition (static-true)
   :effect (and (when (typeA ?x) (p ?x))
		(when (typeB ?x) (q ?x)))
   )

  )
