
;; Example problem 1: Start out with a dense, connected graph
;; (which happens to be the mainland australian states and their
;; borders-on relation) and shrink it to a spanning tree by
;; removing edges.

(define (problem shrink-to-mst)
  (:domain make-spanning-tree)

  (:objects qld nsw vic sa nt wa)

  (:init
   (edge qld nsw)
   (edge qld nt)
   (edge qld sa)
   (edge nsw qld)
   (edge nsw sa)
   (edge nsw vic)
   (edge vic nsw)
   (edge vic sa)
   (edge nt qld)
   (edge nt sa)
   (edge nt wa)
   (edge sa qld)
   (edge sa nsw)
   (edge sa vic)
   (edge sa nt)
   (edge sa wa)
   (edge wa nt)
   (edge wa sa)
   )

  (:goal (is-a-forest))

  )
