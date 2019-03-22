
;; A solvable variant of the "disjunction-via-axioms" problem.

(define (problem unsolvable)
  (:domain disjunction-via-axioms)

  ;; Four elements connected in a "diamond" shape: "top" has
  ;; (bi-directional) edges (static-e) to left and right; left and
  ;; right both have static-b to bottom; bottom is "controllable"
  ;; (static-c).
  (:objects top bottom left right)

  (:init
   (static-e top left)
   (static-e top right)
   (static-e left top)
   (static-e right top)

   (static-b left bottom)
   (static-b right bottom)
   (static-c bottom)
   )

  ;; The goal should be reachable by a single action, (set-p bottom).
  (:goal (not (secondary-q top)))
  )
