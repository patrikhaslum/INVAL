
(define (domain mausam-kolobov-ex31a)
  (:predicates (s0) (s1) (s2) (sg))

  (:action a0
   :precondition (s0)
   :effect (and (not (s0))
		(probabilistic
		 6/10 (and (s1) (decrease (reward) 4))
		 4/10 (and (s2) (decrease (reward) 1))))
   )

  (:action a1
   :precondition (s1)
   :effect (and (not (s1)) (sg) (decrease (reward) 0))
   )

  (:action a2
   :precondition (s2)
   :effect (and (not (s2)) (sg) (decrease (reward) 3))
   )
  )

(define (problem ex31a)
  (:init (s0))
  (:goal (sg))
  )
