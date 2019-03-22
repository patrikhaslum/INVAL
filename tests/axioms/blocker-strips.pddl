
(define (domain blocker-strips)
  (:requirements :strips :derived-predicates)

  ;; The set of objects are the numbers from 0 to N-1, where N is the
  ;; number of nodes in the graph. These are used both to represent the
  ;; nodes in the graph and distances (because distances in the graph
  ;; will never be greater than the number of nodes minus one).

  (:predicates
   ;; primary predicates:
   (cat ?x)
   (blocked ?x)
   (blockers-turn)
   (cats-turn)
   ;; static predicates:
   (exit ?x)
   (edge ?x ?y)
   (is-zero ?x)
   (next ?x ?y)
   ;; derived predicates:
   (prefer ?x ?y)
   (cat-moves ?from ?to)
   (distance-to-exit ?x ?n)
   (closer-or-equal-to-exit ?x ?y)
   (closer-to-exit ?x ?y)
   (less ?x ?y)
   (trapped)
   )

  ;; (distance-to-exit ?x ?n) holds if we can reach an exit node from
  ;; ?x in ?n steps or less, given the current set of blocked nodes.
  (:derived (distance-to-exit ?x ?z)
	    (and (exit ?x) (is-zero ?z)))

  (:derived (distance-to-exit ?x ?k)
	    (exists (?y ?j)
		    (and (edge ?x ?y)
		         (next ?j ?k)
			 (not (blocked ?y))
			 (distance-to-exit ?y ?j))))

  (:derived (distance-to-exit ?x ?k)
	    (exists (?j)
		    (and (next ?j ?k)
			 (distance-to-exit ?x ?j))))


  ;; (closer-to-exit ?x ?y) holds if the shortest distance to an exit
  ;; from ?x is stricly smaller than the shortest distance to an exit
  ;; from ?y.
  (:derived (closer-to-exit ?x ?y)
	    (exists (?k)
		    (and (distance-to-exit ?x ?k)
			 (not (distance-to-exit ?y ?k)))))

  ;; (closer-or-equal-to-exit ?x ?y) holds if the shortest distance to
  ;; an exit from ?x is less than or equal to the shortest distance to
  ;; an exit from ?y.
  (:derived (closer-or-equal-to-exit ?x ?y)
	    (not (closer-to-exit ?y ?x)))

  ;; (less ?x ?y) iff ?x is strictly less than ?y.
  (:derived (less ?x ?y)
	    (or (next ?x ?y)
		(exists (?z) (and (next ?x ?z) (less ?z ?y)))))

  ;; (trapped) is true iff the cat is trapped; that is, distance-to-exit
  ;; is false for every value from the cat's current position.
  (:derived (trapped)
	    (exists (?x)
		    (and (cat ?x)
			 (forall (?n) (not (distance-to-exit ?x ?n))))))

  ;; (prefer ?x ?y) iff cat prefers moving to ?x over ?y (only
  ;; relevant if ?x and ?y are both neighbours of the cat's current
  ;; position, but this is not tested for here). This is true if ?y
  ;; is blocked; ?x is strictly closer to an exit than ?y; or ?x and
  ;; ?y are at the same distance to exit but ?x is less than ?y (i.e.,
  ;; numeric order of the nodes is used as the final tie-breaker).
  (:derived (prefer ?x ?y)
	    (or (blocked ?y)
		(closer-to-exit ?x ?y)
		(and (closer-or-equal-to-exit ?x ?y)
		     (less ?x ?y))))

  ;; (cat-moves ?from ?to) iff ?to is the node that the cat will move to
  ;; from ?from. This is the node that is closest to an exit, or least
  ;; among the nodes the minimum distance to exit. If the cat is already
  ;; trapped, this predicate is false for all destinations.
  (:derived (cat-moves ?from ?to)
	    (and (edge ?from ?to)
		 (not (blocked ?to))
		 (not (trapped))
		 (forall (?alt)
			 (or (= ?to ?alt)
			     (not (edge ?from ?alt))
			     (prefer ?to ?alt)))))


  ;; In the strips formulation, the blocker's and cat's actions alternate.

  ;; Blocker's action:
  (:action block
   :parameters (?b)
   :precondition (and (blockers-turn)
		      (not (cat ?b)))
   :effect (and (blocked ?b)
		(not (blockers-turn))
		(cats-turn))
   )

  ;; Cat's action:
  (:action move
   :parameters (?from ?to)
   :precondition (and (cats-turn)
		      (cat ?from)
		      (not (exit ?from))
		      (cat-moves ?from ?to))
   :effect (and (not (cat ?from))
		(cat ?to)
		(not (cats-turn))
		(blockers-turn))
   )

  )
