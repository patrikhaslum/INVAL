
(define (domain hanoi-FS)

  (:types
   disk - disk*
   peg)

  ;; In Hector's formulation, the type of the argument ?d of the 'loc'
  ;; function has type disk, not disk*. That makes the move action fail
  ;; to type check, because it assigns (loc (top ?pi)), and (top ?pi)
  ;; has type disk*.

  ;; The fact that (top ?pi) is explicitly constrained to not equal the
  ;; constant 'bottom and that 'bottom is the only element of type disk*
  ;; that is not also of type disk of course means that the assignment
  ;; is, for any applicable instance of the action, type safe, but this
  ;; is not discovered by static analysis (in fact, cannot be discovered
  ;; by analysis of the domain alone).

  (:functions
   (top ?p - peg) - disk*
   (loc ?ds - disk*) - disk*
   (size ?ds - disk*) - number
   )

  (:constants
   bottom - disk*
   )

  (:action move
   :parameters (?pi ?pj - peg)
   :precondition (and (not (= (top ?pi) bottom))
		      (< (size (top ?pi)) (size (top ?pj))))
   :effect (and (assign (top ?pi) (loc (top ?pi)))
		(assign (loc (top ?pi)) (top ?pj))
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
   (= (loc d4) bottom)
   (= (loc d3) d4)
   (= (loc d2) d3)
   (= (loc d1) d2)
   (= (top p1) d1)
   (= (top p2) bottom)
   (= (top p3) bottom)
   (= (size d1) 1)
   (= (size d2) 2)
   (= (size d3) 3)
   (= (size d4) 4)
   (= (size bottom) 5)
   )

  (:goal (and (= (loc d4) bottom)
	      (= (loc d3) d4)
	      (= (loc d2) d3)
	      (= (loc d1) d2)
	      (= (top p3) d1)))
  )

(:plan
 (move p1 p2) ; d1
 (move p1 p3) ; d2
 (move p2 p3) ; d1
 (move p1 p2) ; d3
 (move p3 p1) ; d1
 (move p3 p2) ; d2
 (move p1 p2) ; d1
 (move p1 p3) ; d4
 (move p2 p3) ; d1
 (move p2 p1) ; d2
 (move p3 p1) ; d1
 (move p2 p3) ; d3
 (move p1 p2) ; d1
 (move p1 p3) ; d2
 (move p2 p3) ; d1
 )
