
(define (domain logistics-FS)

  (:types
   package - object
   airplane truck - vehicle
   vehicle - object
   airport - location
   location - object
   city - object
   )

  (:functions
   (loc ?x - (either package vehicle)) - (either location vehicle)
   (city-of ?l - location) - city
   )

  (:action load
   :parameters (?p - package ?v - vehicle)
   :precondition (= (loc ?p) (loc ?v))
   :effect (assign (loc ?p) ?v)
   )

  ;; The unload action is not type correct, because of the term
  ;; (loc (loc ?p)) in the assignment. The expression (loc ?p) is
  ;; of type (either location vehicle), but loc expects as argument
  ;; the type (either package vehicle), which is not a subtype of
  ;; the former.

  ;; Note that this action must use a "type test" (type name used
  ;; as static unary predicate) in the precondition.

  ;; One way to avoid the type safety problem here is to extend the
  ;; argument type of loc to (either package vehicle location). Since
  ;; (loc <l>) is not specified in the initial state for any location
  ;; <l> (and not set by any action), the action becomes inapplicable
  ;; in any state where package ?p is not in a vehicle (because in such
  ;; a state the value of the right hand side of the assignment is
  ;; undefined, which is an execution error), and thus this eliminates
  ;; the need for an explicit type test in the precondition.

  (:action unload
   :parameters (?p - package)
   :precondition (vehicle (loc ?p))
   :effect (assign (loc ?p) (loc (loc ?p)))
   )

  ;; The drive action is also not type correct, because of the term
  ;; (city-of (loc ?t)) in the precondition. Again, this is because
  ;; the type of (loc ?t) is (either location vehicle), but city-of
  ;; expects as argument only the type location. Also as above, the
  ;; problem can be "fixed" by widening the parameter type of city-of
  ;; to (either location vehicle) but leaving the function undefined
  ;; for all non-location arguments.

  (:action drive
   :parameters (?t - truck ?to - location)
   :precondition (= (city-of (loc ?t)) (city-of ?to))
   :effect (assign (loc ?t) ?to)
   )

  ;; Hector's formulation has an explicit type test on ?to in the
  ;; precondition, but that is redundant; thus, we're left with no
  ;; precondition.

  (:action fly
   :parameters (?a - airplane ?to - airport)
   :effect (assign (loc ?a) ?to)
   )

  )

(define (problem logistics)
  (:domain logistics-FS)

  (:objects
   barcelona basel canberra - city
   BCN BSL CBR - airport
   UPF UniBas ANU - location
   tbar tbas tcan - truck 
   airplane-one - airplane
   pkg1 pkg2 - package
   )

  (:init
   (= (loc tbar) UPF)
   (= (loc tcan) ANU)
   (= (loc tbas) BSL)
   (= (loc airplane-one) BCN)
   (= (loc pkg1) UniBas)
   (= (loc pkg2) ANU)
   (= (city-of UPF) barcelona)
   (= (city-of BCN) barcelona)
   (= (city-of ANU) canberra)
   (= (city-of CBR) canberra)
   (= (city-of UniBas) basel)
   (= (city-of BSL) basel)
   )

  (:goal (and (= (loc pkg1) ANU)
	      (= (loc pkg2) UPF)))

  )
