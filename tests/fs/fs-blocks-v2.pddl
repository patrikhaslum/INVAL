
(define (domain blocksworld-FS)

  (:types block - place)

  (:constants table - place)

  (:functions
   (loc ?b - block) - place
   )

  (:predicates
   (clear ?p - place)
   )

  (:action move-to-block
   :parameters (?b - block ?to - block)
   :precondition (and (clear ?b)
		      (clear ?to)
		      (not (= ?b ?to)))
   :effect (and (clear (loc ?b))
		(assign (loc ?b) ?to)
		(not (clear ?to)))
   )

  (:action move-to-table
   :parameters (?b - block)
   :precondition (clear ?b)
   :effect (and (clear (loc ?b))
		(assign (loc ?b) table))
   )

  )

(define (problem sussman)
  (:domain blocksworld-FS)

  (:objects a b c - block)

  (:init
   (= (loc a) table)
   (= (loc b) table)
   (= (loc c) a)
   (clear c)
   (clear b)
   (clear table)
   )

  (:goal (and (= (loc a) b) (= (loc b) c)))

  )

(:plan
 (move-to-table c)
 (move-to-block b c)
 (move-to-block a b)
 )
