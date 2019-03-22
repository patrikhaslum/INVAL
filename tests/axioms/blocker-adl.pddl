
(define (domain blocker-adl)
  (:requirements :adl :derived-predicates)

  (:predicates
   ;; primary predicates:
   (cat ?x)
   (blocked ?x)
   ;; static predicates:
   (exit ?x)
   (edge ?x ?y)
   (is-zero ?x)
   (next ?x ?y)
   ;; predicates not used in ADL formulation:
   (blockers-turn)
   (cats-turn)
   ;; derived predicates:
   (prefer ?x ?y ?b)
   (cat-next-pos ?x ?b)
   (distance-to-exit-2 ?x ?n)
   (distance-to-exit-3 ?x ?n ?b)
   (closer-or-equal-to-exit ?x ?y ?b)
   (closer-to-exit ?x ?y ?b)
   (less ?x ?y)
   (trapped)
   )

  ;; (distance-to-exit ?x ?n ?b) holds if we can reach an exit node
  ;; from ?x in ?n steps or less, given the current set of blocked
  ;; nodes including ?b.
  (:derived (distance-to-exit-3 ?x ?z ?b)
	    (and (exit ?x) (is-zero ?z)))

  (:derived (distance-to-exit-3 ?x ?k ?b)
	    (exists (?y ?j)
		    (and (edge ?x ?y)
		         (next ?j ?k)
			 (not (blocked ?y))
			 (not (= ?y ?b))
			 (distance-to-exit-3 ?y ?j ?b))))

  (:derived (distance-to-exit-3 ?x ?k ?b)
	    (exists (?j)
		    (and (next ?j ?k)
			 (distance-to-exit-3 ?x ?j ?b))))

  (:derived (distance-to-exit-2 ?x ?z)
	    (and (exit ?x) (is-zero ?z)))

  (:derived (distance-to-exit-2 ?x ?k)
	    (exists (?y ?j)
		    (and (edge ?x ?y)
		         (next ?j ?k)
			 (not (blocked ?y))
			 (distance-to-exit-2 ?y ?j))))

  (:derived (distance-to-exit-2 ?x ?k)
	    (exists (?j)
		    (and (next ?j ?k)
			 (distance-to-exit-2 ?x ?j))))

  ;; (closer-to-exit ?x ?y ?b) holds if the shortest distance to an
  ;; exit from ?x is stricly smaller than the shortest distance to an
  ;; exit from ?y.
  (:derived (closer-to-exit ?x ?y ?b)
	    (exists (?k)
		    (and (distance-to-exit-3 ?x ?k ?b)
			 (not (distance-to-exit-3 ?y ?k ?b)))))

  ;; (closer-or-equal-to-exit ?x ?y ?b) holds if the shortest distance
  ;; to an exit from ?x is less than or equal to the shortest distance
  ;; to an exit from ?y.
  (:derived (closer-or-equal-to-exit ?x ?y ?b)
	    (not (closer-to-exit ?y ?x ?b)))

  ;; (less ?x ?y) iff ?x is strictly less than ?y.
  (:derived (less ?x ?y)
	    (or (next ?x ?y)
		(exists (?z) (and (next ?x ?z) (less ?z ?y)))))

  ;; (trapped) is true iff the cat is trapped; that is, distance-to-exit
  ;; is false for every value from the cat's current position.
  (:derived (trapped)
	    (exists (?x)
		    (and (cat ?x)
			 (forall (?n) (not (distance-to-exit-2 ?x ?n))))))

  ;; (prefer ?x ?y) iff cat prefers moving to ?x over ?y (only
  ;; relevant if ?x and ?y are both neighbours of the cat's current
  ;; position, but this is not tested for here). This is true if ?y
  ;; is blocked; ?x is strictly closer to an exit than ?y; or ?x and
  ;; ?y are at the same distance to exit but ?x is less than ?y (i.e.,
  ;; numeric order of the nodes is used as the final tie-breaker).
  (:derived (prefer ?x ?y ?b)
	    (or (blocked ?y)
		(= ?y ?b)
		(closer-to-exit ?x ?y ?b)
		(and (closer-or-equal-to-exit ?x ?y ?b)
		     (less ?x ?y))))

  ;; (cat-next-pos ?x ?b) iff ?x is the node that the cat will move to
  ;; assuming ?b is the node blocked this move. If the cat is already
  ;; trapped, this predicate is false for all destinations.
  (:derived (cat-next-pos ?x ?b)
	    (exists (?y)
		    (and (cat ?y)
			 (edge ?y ?x)
			 (not (blocked ?x))
			 (not (= ?x ?b))
			 (not (trapped))
			 (forall (?alt)
				 (or (= ?x ?alt)
				     (not (edge ?y ?alt))
				     (prefer ?x ?alt ?b))))))

  (:action block
   :parameters (?b)
   :precondition (not (cat ?b))
   :effect (and (blocked ?b)
		(forall (?x)
			(and (when (not (cat-next-pos ?x ?b)) (not (cat ?x)))
			     (when (cat-next-pos ?x ?b) (cat ?x)))))
   )

  )
