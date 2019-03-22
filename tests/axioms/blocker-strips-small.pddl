
;;     (0)
;;    / | 
;; [1]-(2)
;;      |
;;     [3]

(define (problem four)
  (:domain blocker-strips)

  (:objects n0 n1 n2 n3)

  (:init (exit n1)
	 (exit n3)
	 (edge n0 n1)
	 (edge n0 n2)
	 (edge n1 n0)
	 (edge n1 n2)
	 (edge n2 n0)
	 (edge n2 n1)
	 (edge n2 n3)
	 (edge n3 n2)
	 (is-zero n0)
	 (next n0 n1)
	 (next n1 n2)
	 (next n2 n3)
	 (cat n0)
	 (blockers-turn)
	 )

  (:goal (trapped))

  )
