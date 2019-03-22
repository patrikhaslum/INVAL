
(define (problem three)
  (:domain buckets)

  (:objects b8 b5 b3 - bucket
	    one two three four five six seven eight - quantity)

  (:init
   (= (in b8) eight)
   (= (in b5) zero)
   (= (in b3) zero)

   (= (capacity b8) eight)
   (= (capacity b5) five)
   (= (capacity b3) three)

   (less-or-equal zero zero)
   (less-or-equal zero one)
   (less-or-equal zero two)
   (less-or-equal zero three)
   (less-or-equal zero four)
   (less-or-equal zero five)
   (less-or-equal zero six)
   (less-or-equal zero seven)
   (less-or-equal zero eight)
   (less-or-equal one one)
   (less-or-equal one two)
   (less-or-equal one three)
   (less-or-equal one four)
   (less-or-equal one five)
   (less-or-equal one six)
   (less-or-equal one seven)
   (less-or-equal one eight)
   (less-or-equal two two)
   (less-or-equal two three)
   (less-or-equal two four)
   (less-or-equal two five)
   (less-or-equal two six)
   (less-or-equal two seven)
   (less-or-equal two eight)
   (less-or-equal three three)
   (less-or-equal three four)
   (less-or-equal three five)
   (less-or-equal three six)
   (less-or-equal three seven)
   (less-or-equal three eight)
   (less-or-equal four four)
   (less-or-equal four five)
   (less-or-equal four six)
   (less-or-equal four seven)
   (less-or-equal four eight)
   (less-or-equal five five)
   (less-or-equal five six)
   (less-or-equal five seven)
   (less-or-equal five eight)
   (less-or-equal six six)
   (less-or-equal six seven)
   (less-or-equal six eight)
   (less-or-equal seven seven)
   (less-or-equal seven eight)
   (less-or-equal eight eight)

   (= (sum zero zero) zero)
   (= (sum zero one) one)
   (= (sum zero two) two)
   (= (sum zero three) three)
   (= (sum zero four) four)
   (= (sum zero five) five)
   (= (sum zero six) six)
   (= (sum zero seven) seven)
   (= (sum zero eight) eight)
   (= (sum one zero) one)
   (= (sum one one) two)
   (= (sum one two) three)
   (= (sum one three) four)
   (= (sum one four) five)
   (= (sum one five) six)
   (= (sum one six) seven)
   (= (sum one seven) eight)
   (= (sum two zero) two)
   (= (sum two one) three)
   (= (sum two two) four)
   (= (sum two three) five)
   (= (sum two four) six)
   (= (sum two five) seven)
   (= (sum two six) eight)
   (= (sum three zero) three)
   (= (sum three one) four)
   (= (sum three two) five)
   (= (sum three three) six)
   (= (sum three four) seven)
   (= (sum three five) eight)
   (= (sum four zero) four)
   (= (sum four one) five)
   (= (sum four two) six)
   (= (sum four three) seven)
   (= (sum four four) eight)
   (= (sum five zero) five)
   (= (sum five one) six)
   (= (sum five two) seven)
   (= (sum five three) eight)
   (= (sum six zero) six)
   (= (sum six one) seven)
   (= (sum six two) eight)
   (= (sum seven zero) seven)
   (= (sum seven one) eight)
   (= (sum eight zero) eight)

   (= (diff eight zero) eight)
   (= (diff eight one) seven)
   (= (diff eight two) six)
   (= (diff eight three) five)
   (= (diff eight four) four)
   (= (diff eight five) three)
   (= (diff eight six) two)
   (= (diff eight seven) one)
   (= (diff eight eight) zero)
   (= (diff seven zero) seven)
   (= (diff seven one) six)
   (= (diff seven two) five)
   (= (diff seven three) four)
   (= (diff seven four) three)
   (= (diff seven five) two)
   (= (diff seven six) one)
   (= (diff seven seven) zero)
   (= (diff six zero) six)
   (= (diff six one) five)
   (= (diff six two) four)
   (= (diff six three) three)
   (= (diff six four) two)
   (= (diff six five) one)
   (= (diff six six) zero)
   (= (diff five zero) five)
   (= (diff five one) four)
   (= (diff five two) three)
   (= (diff five three) two)
   (= (diff five four) one)
   (= (diff five five) zero)
   (= (diff four zero) four)
   (= (diff four one) three)
   (= (diff four two) two)
   (= (diff four three) one)
   (= (diff four four) zero)
   (= (diff three zero) three)
   (= (diff three one) two)
   (= (diff three two) one)
   (= (diff three three) zero)
   (= (diff two zero) two)
   (= (diff two one) one)
   (= (diff two two) zero)
   (= (diff one zero) one)
   (= (diff one one) zero)
   (= (diff zero zero) zero)

   )

  (:goal (and (= (in b8) four) (= (in b5) four)))

  )
