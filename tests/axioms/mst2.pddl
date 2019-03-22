
;; Example problem 2: Start out with a graph that has several
;; disconnected components, some of which are not trees. The
;; plan must contain both add and remove actions.

(define (problem grow-and-shrink-to-mst)
  (:domain make-spanning-tree)

  (:objects qld nsw vic sa nt wa)

  (:init
   (edge qld nsw)
   (edge qld sa)
   (edge nsw qld)
   (edge nsw sa)
   (edge nsw vic)
   (edge vic nsw)
   (edge vic sa)
   (edge nt wa)
   (edge sa qld)
   (edge sa nsw)
   (edge sa vic)
   (edge wa nt)
   )

  (:goal (and (is-connected)
	      (is-a-forest)))

  )
