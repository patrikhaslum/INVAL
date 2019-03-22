
(define (problem size-five) 
  (:domain blocksworld-with-axioms)
  (:objects A B C D E - block)
  (:init (ontable A) (on B A) (on C B) (ontable D) (on E D))
  (:goal (and (on A D) (on C B)))
  )
