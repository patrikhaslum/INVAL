
(define (problem test)
  (:domain dummy)

  (:objects obA - typeA)
  (:objects obB - typeB)
  (:objects obC - typeC)

  (:init (static-true) )

  (:goal (and (p obA)
	      (q obB)
	      (or (p obC) (q obC))
	      ))
  )
