
(define (domain buckets)
  (:requirements :strips :typing :equality :fluents)

  (:types bucket quantity)

  (:constants zero - quantity)

  (:predicates
   (less-or-equal ?a ?b - quantity) ;; ?a <= ?b
   )

  (:functions
   (in ?b - bucket) - quantity ;; amount currently in ?b
   (capacity ?b - bucket) - quantity ;; capacity of ?b
   (sum ?a ?b - quantity) - quantity ;; ?a + ?b
   (diff ?a ?b - quantity) - quantity ;; ?a - ?b
   )

  ;; all of ?bfrom fits in ?bto:
  (:action empty-into
   :parameters (?bfrom ?bto - bucket)
   :precondition (and (not (= ?bfrom ?bto))
		      (less-or-equal (sum (in ?bfrom) (in ?bto))
				     (capacity ?bto)))
   :effect (and (assign (in ?bto) (sum (in ?bfrom) (in ?bto)))
		(assign (in ?bfrom) zero))
   )

  ;; pour from ?bfrom until ?bto full:
  (:action fill-from
   :parameters (?bfrom ?bto - bucket)
   :precondition (and (not (= ?bfrom ?bto))
		      (less-or-equal (diff (capacity ?bto) (in ?bto))
				     (in ?bfrom)))
   :effect (and (assign (in ?bto) (capacity ?bto))
		(assign (in ?bfrom)
			(diff (in ?bfrom) (diff (capacity ?bto) (in ?bto)))))
   )

  )
