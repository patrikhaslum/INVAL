
(define (domain dummy)
  (:requirements :typing)

  (:types typeA typeB - object
	  typeC - (either typeA typeB)
	  )

  (:predicates (p ?x - typeA) (q ?x - typeB) (static-true))

  (:action do-p
   :parameters (?x - typeA)
   :precondition (static-true)
   :effect (p ?x)
   )

  (:action do-q
   :parameters (?x - typeB)
   :precondition (static-true)
   :effect (q ?x)
   )
  )
