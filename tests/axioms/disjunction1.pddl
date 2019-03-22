
;; An unsolvable problem for the "disjunction-via-axioms" domain.

(define (problem unsolvable)
  (:domain disjunction-via-axioms)

  ;; Four elements connected in a "diamond" shape: "top" has
  ;; (bi-directional) edges (static-e) to left and right; left has
  ;; static-a to bottom, and right has static-b to bottom; bottom is
  ;; "controllable" (static-c).
  (:objects top bottom left right)

  (:init
   (static-e top left)
   (static-e top right)
   (static-e left top)
   (static-e right top)

   (static-a left bottom)
   (static-b right bottom)
   (static-c bottom)
   )

  ;; The goal is unreachable: Whatever the value of (primary-p bottom),
  ;; at least one of (secondary-q left) and (secondary-q right) will
  ;; be true, and this will make (secondary-q top) true.
  (:goal (not (secondary-q top)))
  )
