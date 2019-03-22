
(define (domain hanoi-FS)

  (:types disk peg)

  ;; an untyped constant, to represent the bottom of a peg
  (:constants bottom)

  (:functions
   ;; here, we allow a union type to mention not only atomic types but
   ;; also named constants; in other words, each constant is also a type
   ;; (with itself as the only element)
   (top ?p - peg) - (either disk bottom)
   (below ?disk - disk) - (either disk bottom)
   (size ?ds - (either disk bottom)) - number
   )

  ;; As in the original formulation of version 1, this action will
  ;; fail to type check because (top ?pi) has type (either disk bottom)
  ;; and the argument to below must be of type disk; however, since
  ;; we know that the range of top consists of only disks plus the
  ;; constant bottom, and we explicitly rule out (top ?pi) = bottom
  ;; in the precondition, a clever type checker should be able to
  ;; tell that the assignment is ok.
  (:action move
   :parameters (?pi ?pj - peg)
   :precondition (and (not (= (top ?pi) bottom))
		      (< (size (top ?pi)) (size (top ?pj))))
   :effect (and (assign (top ?pi) (below (top ?pi)))
		(assign (below (top ?pi)) (top ?pj))
		(assign (top ?pj) (top ?pi)))
   )

  )

(define (problem hanoi-4)
  (:domain hanoi-FS)

  (:objects
   p1 p2 p3 - peg
   d1 d2 d3 d4 - disk
   )

  (:init
   (= (below d4) bottom)
   (= (below d3) d4)
   (= (below d2) d3)
   (= (below d1) d2)
   (= (top p1) d1)
   (= (top p2) bottom)
   (= (top p3) bottom)
   (= (size d1) 1)
   (= (size d2) 2)
   (= (size d3) 3)
   (= (size d4) 4)
   (= (size bottom) 4)
   )

  (:goal (and (= (below d4) bottom)
	      (= (below d3) d4)
	      (= (below d2) d3)
	      (= (below d1) d2)
	      (= (top p3) d1)))
  )
