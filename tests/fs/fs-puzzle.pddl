
(define (domain puzzle-FS)

  (:types
   pos - pos*
   direction
   tile
   )

  (:constants
   nowhere - pos*
   up down left right - direction
   )

  ;; Similarly to the hanoi domain, Hector's formulation has the
  ;; tile-at function's parameter typed as pos, not pos*, which
  ;; makes the expression (tile-at (next ?d (blank))) in the effect
  ;; of the move action type incorrect.

  (:functions
   (tile-at ?p - pos*) - tile
   (blank) - pos
   (next ?d - direction ?p - pos) - pos*
   )

  (:action move
   :parameters (?d - direction)
   :precondition (not (= (next ?d (blank)) nowhere))
   :effect (and (assign (blank) (next ?d (blank)))
		(assign (tile-at (blank)) (tile-at (next ?d (blank))))
		(assign (tile-at (next ?d (blank))) undefined))
   )

  )

(define (problem eight31a)
  (:domain puzzle-FS)

  (:objects
   tl tm tr ml mm mr bl bm br - pos
   t1 t2 t3 t4 t5 t6 t7 t8 - tile
   )

  (:init
   ;; the static 'next' function (of course we would prefer to have
   ;; this as part of the domain definition, but what can you do?)
   (= (next up tl) nowhere)
   (= (next up tm) nowhere)
   (= (next up tr) nowhere)
   (= (next up ml) tl)
   (= (next up mm) tm)
   (= (next up mr) tr)
   (= (next up bl) ml)
   (= (next up bm) mm)
   (= (next up br) mr)
   (= (next down tl) ml)
   (= (next down tm) mm)
   (= (next down tr) mr)
   (= (next down ml) bl)
   (= (next down mm) bm)
   (= (next down mr) br)
   (= (next down bl) nowhere)
   (= (next down bm) nowhere)
   (= (next down br) nowhere)
   (= (next left tl) nowhere)
   (= (next left tm) tl)
   (= (next left tr) tm)
   (= (next left ml) nowhere)
   (= (next left mm) ml)
   (= (next left mr) mm)
   (= (next left bl) nowhere)
   (= (next left bm) bl)
   (= (next left br) bm)
   (= (next right tl) tm)
   (= (next right tm) tr)
   (= (next right tr) nowhere)
   (= (next right ml) mm)
   (= (next right mm) mr)
   (= (next right mr) nowhere)
   (= (next right bl) bm)
   (= (next right bm) br)
   (= (next right br) nowhere)

   ;; the actual initial state
   (= (blank) tl)
   (= (tile-at tm) t1)
   (= (tile-at tr) t2)
   (= (tile-at ml) t3)
   (= (tile-at mm) t4)
   (= (tile-at mr) t5)
   (= (tile-at bl) t6)
   (= (tile-at bm) t7)
   (= (tile-at br) t8)
   )

  (:goal (and (= (tile-at tl) t8)
	      (= (tile-at tm) t7)
	      (= (tile-at tr) t6)
	      (= (tile-at mm) t4)
	      (= (tile-at mr) t1)
	      (= (tile-at bl) t2)
	      (= (tile-at bm) t5)
	      (= (tile-at br) t3)))

  )
