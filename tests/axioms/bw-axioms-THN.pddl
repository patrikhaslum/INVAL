
;; Blocksworld with axioms (from Thiebaux, Hoffmann & Nebel AIJ'05).
;; Typing has been added (though it's somewhat pointless, since there's
;; only one type), and some names changed, to enable using problems and
;; plans from the IPC2 set with this domain.

(define (domain blocksworld-with-axioms)

  (:requirements :strips :typing)

  (:types block)

  (:predicates
   ;; basic predicates
   (ontable ?x - block)
   (on ?x - block ?y - block)
   ;; derived predicates
   (holding ?x - block)
   (above ?x - block ?y - block)
   (clear ?x - block)
   (handempty))

  (:derived (holding ?x - block)
	    (and (not (ontable ?x))
		 (not (exists (?y - block)
			      (on ?x ?y)))))

  (:derived (above ?x - block ?y - block)
	    (or (on ?x ?y)
		(exists (?z - block)
			(and (on ?x ?z) (above ?z ?y)))))

  (:derived (clear ?x - block)
	    (and (not (holding ?x))
		 (not (exists (?y - block) (on ?y ?x)))))

  (:derived (handempty)
	    (forall (?x - block)
		    (not (holding ?x))))

  (:action pick-up
   :parameters (?ob - block)
   :precondition (and (clear ?ob) (ontable ?ob) (handempty))
   :effect (not (ontable ?ob))
   )

  (:action put-down
   :parameters (?ob - block)
   :precondition (holding ?ob)
   :effect (ontable ?ob)
   )

  (:action stack
   :parameters (?ob - block ?underob - block)
   :precondition (and (clear ?underob) (holding ?ob))
   :effect (on ?ob ?underob)
   )

  (:action unstack
   :parameters (?ob - block ?underob - block)
   :precondition (and (on ?ob ?underob) (clear ?ob) (handempty))
   :effect (not (on ?ob ?underob))
   )

  )
