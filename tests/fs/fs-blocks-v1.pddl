
(define (domain blocksworld-FS)

  (:types block - place)

  (:constants table - place)

  (:functions
   (loc ?b - block) - place
   )

  ;; Hector's formulation has clear as a fluent with a boolean domain.
  ;; I've made it a predicate instead. Hector's formulation has the
  ;; assignment (assign (clear ?to) (= ?to table)) in the move action,
  ;; which of course cannot be done with clear a predicate, so I've
  ;; made that a conditional effect instead (with static condition).
  ;; The conditional effect can be removed by splitting the action into
  ;; two cases (one that has the ?to argument typed as 'block, one that
  ;; moves only to the table; see fs-blocks-v2.pddl).
  ;;
  ;; Another alternative would be to define 'boolean as a type, declare
  ;; contants 'true and 'false, make clear a fluent with boolean type,
  ;; and define a static fluent (is-equal-to-table ?p - place), which
  ;; could then be used in the effect. The static fluent, however, must
  ;; be given a value for every argument (all blocks plus the table)
  ;; by the initial state.

  (:predicates
   (clear ?p - place)
   )

  ;; Note that the move action requires the destination to be clear,
  ;; even if the destination is the table. Thus, (clear table) must
  ;; be present in the initial state. (It will never be deleted.)

  (:action move
   :parameters (?b - block ?to - place)
   :precondition (and (clear ?b)
		      (clear ?to)
		      (not (= ?b ?to)))
   :effect (and (clear (loc ?b))
		(assign (loc ?b) ?to)
		(when (not (= ?to table))
		  (not (clear ?to))))
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
 (move c table)
 (move b c)
 (move a b)
 )
