
(define (domain logistics-FS)

  (:types
   package - object
   airplane truck - vehicle
   airport - location
   location - object
   city - object
   )

  ;; In Hector's formulation, there is only one 'loc' function, for
  ;; both vehicles and package; this causes a type error in the
  ;; drive action, just as in logistics-domain-new.

  (:functions
   (vehicle-loc ?v - vehicle) - location
   (package-loc ?p - package) - (either location vehicle)
   (city-of ?l - location) - city
   )

  (:action load
   :parameters (?p - package ?v - vehicle)
   ;; Note that the equality predicate is implicitly declared as
   ;; (= ?o1 ?o2 - object), i.e., it accepts any argument types.
   :precondition (= (package-loc ?p) (vehicle-loc ?v))
   :effect (assign (package-loc ?p) ?v)
   )

  ;; Hector's formulation has an unload action with only one parameter,
  ;; the package being unloaded. This causes a type error in the
  ;; assignment, since the type of package-loc is (either location
  ;; vehicle), but vehicle-loc can only take a vehicle as argument.
  ;;
  ;; That could be "fixed" by assuming a more clever type checking
  ;; mechanism, which infers from the precondition that for any
  ;; applicable instance of the action, the value of (package-loc ?p)
  ;; in the assignment is of type vehicle. But that requires specifying
  ;; exactly what kind of inference the type checker should do. (And,
  ;; imho, that inference should be polynomial.)
  ;;
  ;; In the absence of such a smart type checker, we have to supply
  ;; the vehicle as an explicit argument.

  (:action unload
   :parameters (?p - package ?v - vehicle)
   :precondition (= (package-loc ?p) ?v)
   :effect (assign (package-loc ?p) (vehicle-loc ?v))
   )

  (:action drive
   :parameters (?t - truck ?to - location)
   :precondition (= (city-of (vehicle-loc ?t)) (city-of ?to))
   :effect (assign (vehicle-loc ?t) ?to)
   )

  ;; Hector's formulation has an explicit type test on ?to in
  ;; the precondition, but that is redundant; thus, we're left
  ;; with no precondition.

  (:action fly
   :parameters (?a - airplane ?to - airport)
   :effect (assign (vehicle-loc ?a) ?to)
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
   (= (vehicle-loc tbar) UPF)
   (= (vehicle-loc tcan) ANU)
   (= (vehicle-loc tbas) BSL)
   (= (vehicle-loc airplane-one) BCN)
   (= (package-loc pkg1) UniBas)
   (= (package-loc pkg2) ANU)
   (= (city-of UPF) barcelona)
   (= (city-of BCN) barcelona)
   (= (city-of ANU) canberra)
   (= (city-of CBR) canberra)
   (= (city-of UniBas) basel)
   (= (city-of BSL) basel)
   )

  (:goal (and (= (package-loc pkg1) ANU)
	      (= (package-loc pkg2) UPF)))

  )
