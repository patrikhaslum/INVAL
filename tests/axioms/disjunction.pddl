
;; This is an (artificial) example domain to illustrate how disjunctions
;; can arise among derived predicates by using negations of non-derived
;; (primary) predicates.

(define (domain disjunction-via-axioms)
  (:requirements :strips :derived-predicates :negative-preconditions)

  (:predicates
   ;; predicates are named "primary", "secondary" and "static" just to
   ;; show the role they play in the domain.
   (primary-p ?x)
   (secondary-q ?x)
   (static-a ?x ?y)
   (static-b ?x ?y)
   (static-e ?x ?y)
   (static-c ?x)
   )

  ;; (secondary-q ?x) propagates along "edges" defined by static-e
  (:derived (secondary-q ?x)
	    (exists (?y) (and (static-e ?x ?y) (secondary-q ?y))))

  ;; (primary-p ?y) implies (secondary-q ?x) iff (static-a ?x ?y)
  (:derived (secondary-q ?x)
	    (exists (?y) (and (static-a ?x ?y) (primary-p ?y))))

  ;; (not (primary-p ?y)) implies (secondary-q ?x) iff (static-b ?x ?y)
  (:derived (secondary-q ?x)
	    (exists (?y) (and (static-b ?x ?y) (not (primary-p ?y)))))

  (:action set-p
   :parameters (?x)
   :precondition (static-c ?x)
   :effect (primary-p ?x)
   )

  ;; (:action dummy-op
  ;;  :parameters (?x ?y)
  ;;  :precondition (and (static-c ?x) (secondary-q ?y))
  ;;  :effect (primary-p ?x)
  ;;  )

  ) ;; end domain def
