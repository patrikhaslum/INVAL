
;; Problem of making a spanning tree out of an initial graph, by
;; adding edges (to connect disconnected components) and removing
;; edges (to reduce it to a tree).

(define (domain make-spanning-tree)
  (:requirements :adl :derived-predicates)

  (:predicates
   ;; The edge predicate is directed (?x to ?y) but we will treat
   ;; it as undirected; all actions that add/remove an edge add/del
   ;; both atoms.
   (edge ?x ?y)
   ;; Transitive and reflexive closure of edge:
   (path ?x ?y)
   ;; negation of path:
   (no-path ?x ?y)
   ;; Path from ?x to ?y not passing through node ?w:
   (path-not-through ?x ?y ?w)
   ;; Path from ?x to ?y not through an edge from ?x to ?y:
   (indirect-path ?x ?y)
   (marked ?x)
   (marked-aux ?x ?y ?z)
   (is-a-forest)
   (is-connected)
   )

  (:derived (path ?x ?y) (= ?x ?y))
  (:derived (path ?x ?y) (exists (?z) (and (edge ?x ?z) (path ?z ?y))))

  (:derived (no-path ?x ?y) (not (path ?x ?y)))

  (:derived (path-not-through ?x ?y ?w)
	    (and (= ?x ?y) (not (= ?x ?w))))
  (:derived (path-not-through ?x ?y ?w)
	    (and (not (= ?x ?w))
		 (exists (?z)
			 (and (edge ?x ?z) (path-not-through ?z ?y ?w)))))

  ;; A different way to check if we have a forest: A node is "marked"
  ;; if it has at most one unmarked neighbour. This means leafs in the
  ;; tree get marked first, then their parents, and so on. If, after
  ;; this is done, all nodes have been marked, then there are no
  ;; cycles.
  (:derived (marked ?x)
	    (forall (?y ?z) (marked-aux ?x ?y ?z)))

  (:derived (marked-aux ?x ?y ?z)
	    (or (= ?y ?z)
		(not (edge ?x ?y))
		(not (edge ?x ?z))
		(marked ?y)
		(marked ?z)))

  (:derived (is-a-forest) (forall (?x) (marked ?x)))

  (:derived (is-connected) (forall (?x ?y) (path ?x ?y)))

  ;; we have a forest iff
  ;; (:derived (is-a-forest)
  ;; 	    ;; for every pair of nodes:
  ;; 	    (forall (?x ?y)
  ;; 		    ;; if they are distinct and not neighbours:
  ;; 		    (or (= ?x ?y)
  ;; 			(edge ?x ?y)
  ;; 			(forall (?z)
  ;; 				;; then for every neighbour ?z of ?x:
  ;; 				(or (not (edge ?x ?z))
  ;; 				    ;; there is no path from ?x to ?y
  ;; 				    ;; not passing through ?z, or no
  ;; 				    ;; path from ?z to ?y not passing
  ;; 				    ;; through ?x:
  ;; 				    (not (path-not-through ?x ?y ?z))
  ;; 				    (not (path-not-through ?z ?y ?x))
  ;; 				    )))))

  ;; an indirect path exists iff...
  (:derived (indirect-path ?x ?y)
	    ;; there is a node ?x
	    (exists (?z)
		    ;; neighbour of ?x
		    (and (edge ?x ?z)
			 ;; not equal to ?y
			 (not (= ?z ?y))
			 ;; such that there is a path from ?z to ?y that
			 ;; does not pass through ?x.
			 (path-not-through ?z ?y ?x))))


  (:action add
   :parameters (?x ?y)
   :precondition (no-path ?x ?y)
   :effect (and (edge ?x ?y) (edge ?y ?x))
   )

  (:action remove
   :parameters (?x ?y)
   :precondition (indirect-path ?x ?y)
   :effect (and (not (edge ?x ?y)) (not (edge ?y ?x)))
   )

  )
