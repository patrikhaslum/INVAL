
;; Social planning with a theory of mind.
;;
;; Based loosely on "Planning-Based Narrative Generation in Simulated
;; Game Universes" (IEEE Trans. on Computational Intelligence and AI
;; in Games, 2009) and "Simulation-Based Story Generation with a Theory
;; of Mind" (AIIDE 2008), both by Hsueh-Min Chang and Von-Wun Soo.
;;
;; This PDDL encoding was written entirely by Patrik Haslum. Chang and
;; Soo did not formulate the full model in PDDL, and did not make their
;; partial model publicly available.

(define (domain social-planning)
  (:requirements :adl :typing :derived-predicates)

  (:types locatable place - object
	  character item - locatable)

  (:predicates
   ;; static properties/relations:
   (man ?c - character)
   (woman ?c - character)
   (married ?a - character ?b - character)
   (friend-of ?a - character ?b - character)
   (precious ?i - item)
   (main-character ?c - character)
   ;; character traits (also static):
   (is-greedy ?c - character)
   (is-curious ?c - character)
   (is-pursuing ?c - character)
   (is-obedient ?c - character)
   (is-suspicious ?c - character)
   (is-jealous ?c - character)
   (is-vain ?c - character)
   (is-lustful ?c - character)
   (is-wrathful ?c - character)
   (is-evil ?c - character)

   ;; state of the world:
   (alive ?c - character)
   (dead ?c - character)
   (at ?l - locatable ?p - place)
   (has ?c - character ?i - item)
   ;; state of mind:
   (loves ?c - character ?d - character)
   (believes-loves ?a - character ?c - character ?d - character)
   ;; records of passed actions:
   (requested-at ?a - character ?c - character ?p - place)
   (requested-has ?a - character ?c - character ?i - item)
   (gift ?from - character ?to - character ?i - item)
   (killed ?a - character ?c - character)

   ;; derived predicates:
   (can-see ?c - character ?l - locatable)
   (alone-at ?c - character ?p - place)
   (motive-for-has ?a - character ?c - character ?i - item)
   (motive-for-at ?a - character ?l - locatable ?p - place)
   (motive-for-dead ?a - character ?c - character)
   (reason-to-believe-loves ?a - character ?c - character ?d - character)
   (reason-to-love ?a - character ?c - character)
   )

  (:derived (can-see ?c - character ?l - locatable)
	    (exists (?p - place)
		    (and (at ?c ?p)
			 (at ?l ?p))))

  (:derived (alone-at ?c - character ?p - place)
	    (forall (?d - character)
		    (or (not (at ?d ?p))
			(= ?d ?c))))

  ;; ?a has motive for (has ?a ?i) if ?a is greedy and ?i is precious:
  (:derived (motive-for-has ?a - character ?a - character ?i - item)
	    (and (is-greedy ?a)
		 (precious ?i)
		 (can-see ?a ?i)))

  ;; ?a has motive for (at ?a ?p) if ?a is curiuous and a friend of
  ;; ?a has asked ?a to be at ?p:
  (:derived (motive-for-at ?a - character ?a - character ?p - place)
	    (and (is-curious ?a)
		 (exists (?f - character)
			 (and (friend-of ?a ?f)
			      (requested-at ?f ?a ?p)))))

  ;; ?a has motive for (has ?c ?i) if ?a is "pursuing", in love
  ;; with ?c, and ?i is precious:
  (:derived (motive-for-has ?a - character ?c - character ?i - item)
	    (and (is-pursuing ?a)
		 (loves ?a ?c)
		 (precious ?i)))

  ;; ?a has motive for (has ?c ?i) if ?a is obedient, loves ?c,
  ;; and ?c has requested to have ?i
  (:derived (motive-for-has ?a - character ?c - character ?i - item)
	    (and (is-obedient ?a)
		 (loves ?a ?c)
		 (requested-has ?c ?c ?i)))

  ;; ?a has motive for (has ?a ?i) if ?a has motive for (has ?c ?i):
  (:derived (motive-for-has ?a - character ?a - character ?i - item)
	    (exists (?c - character)
		    (motive-for-has ?a ?c ?i)))

  ;; ?a has motive for (at ?a ?p) if ?a has motive for (has ?c ?i)
  ;; ?a has ?i, and ?c is at ?p:
  (:derived (motive-for-at ?a - character ?a - character ?p - place)
	    (exists (?c - character ?i - item)
		    (and (motive-for-has ?a ?c ?i)
			 (has ?a ?i)
			 (at ?c ?p))))

  ;; ?a has motive for (at ?a ?p) if ?a has motive for (has ?a ?i)
  ;; and ?i is at ?p:
  (:derived (motive-for-at ?a - character ?a - character ?p - place)
	    (exists (?i - item)
		    (and (motive-for-has ?a ?a ?i)
			 (at ?i ?p))))

  ;; ?a has motive for (at ?c ?p) if ?a has motive for (has ?a ?i)
  ;; and ?c is at ?q and ?i is at ?q and ?p != ?q (i.e., ?a is
  ;; planning to steal ?i at ?p):
  (:derived (motive-for-at ?a - character ?c - character ?p - place)
	    (exists (?i - item ?q - place)
		    (and (motive-for-has ?a ?a ?i)
			 (at ?i ?q)
			 (at ?c ?q))))

  ;; ?a has motive for (dead ?c) if ?a is jealous, ?c is the spouse of ?a,
  ;; and ?a believes ?c loves ?d:
  (:derived (motive-for-dead ?a - character ?c - character)
	    (and (is-jealous ?a)
		 (not (= ?c ?a))
		 (exists (?d - character)
			 (and (married ?a ?c)
			      (believes-loves ?a ?c ?d)))))

  ;; ?a has motive for (dead ?d) if ?a is jealous, ?c is the spouse of ?a,
  ;; and ?a believes ?c loves ?d:
  (:derived (motive-for-dead ?a - character ?d - character)
	    (and (is-jealous ?a)
		 (not (= ?d ?a))
		 (exists (?c - character)
			 (and (married ?a ?c)
			      (believes-loves ?a ?c ?d)))))

  ;; ?a has motive for (dead ?c) if ?a is wrathful, ?a loves ?d, and
  ;; ?c has killed ?d:
  (:derived (motive-for-dead ?a - character ?c - character)
	    (and (is-wrathful ?a)
		 (not (= ?c ?a))
		 (exists (?d - character)
			 (and (loves ?a ?d)
			      (killed ?c ?d)))))

  ;; ?a has motive for (at ?a ?p) if ?a has motive for (dead ?c)
  ;; and ?c is at ?p:
  (:derived (motive-for-at ?a - character ?a - character ?p - place)
	    (exists (?c - character)
		    (and (motive-for-dead ?a ?c)
			 (at ?c ?p))))

  ;; Belief revision rules:

  ;; ?a may (believe-loves ?a ?c ?d) if ?a is suspicious, and ?a observes
  ;; (has ?d ?i) for an ?i that was a gift from ?a to ?c
  (:derived (reason-to-believe-loves
	     ?a - character ?c - character ?d - character)
	    (and (is-suspicious ?a)
		 (not (= ?c ?d))
		 (not (= ?a ?c))
		 (not (= ?a ?d))
		 (exists (?i - item)
			 (and (gift ?a ?c ?i)
			      (has ?d ?i)
			      (can-see ?a ?d)))))

  ;; ?a may fall in love with ?c if ?a is a woman, ?a is vain,
  ;; ?c is a man, and ?c has given ?a something precious:
  (:derived (reason-to-love ?a - character ?c - character)
	    (and (woman ?a)
		 (is-vain ?a)
		 (man ?c)
		 (exists (?i - item)
			 (and (gift ?c ?a ?i)
			      (precious ?i)))))

  ;; ?a may fall in love with ?c if ?a is a man, ?a is "lustful",
  ;; ?c is a woman, and ?c is wearing ("has") something precious:
  (:derived (reason-to-love ?a - character ?c - character)
	    (and (man ?a)
		 (is-lustful ?a)
		 (woman ?c)
		 (can-see ?a ?c)
		 (exists (?i - item)
			 (and (has ?c ?i)
			      (precious ?i)))))

  ;; Belief revision actions:
  ;; Beliefs can persist beyond the current state, so we need to have
  ;; actions that allow characters to adopt beliefs.

  (:action adopt-belief-loves
   :parameters (?a - character ?c - character ?d - character)
   :precondition (and (reason-to-believe-loves ?a ?c ?d)
		      (alive ?a)
		      (alive ?c))
   :effect (believes-loves ?a ?c ?d)
   )

  (:action fall-in-love
   :parameters (?a - character ?c - character)
   :precondition (and (reason-to-love ?a ?c)
		      (not (= ?a ?c))
		      (alive ?a)
		      (alive ?c))
   :effect (loves ?a ?c)
   )

  ;; Character actions:

  (:action take
   :parameters (?a - character ?i - item ?p - place)
   :precondition (and (or (main-character ?a)
			  (motive-for-has ?a ?a ?i))
		      (alive ?a)
		      (at ?i ?p)
		      (at ?a ?p)
		      (alone-at ?a ?p))
   :effect (and (not (at ?i ?p))
		(has ?a ?i))
   )

  (:action drop
   :parameters (?a - character ?i - item ?p - place)
   :precondition (and (or (main-character ?a)
			  (motive-for-at ?a ?i ?p))
		      (alive ?a)
		      (has ?a ?i)
		      (at ?a ?p))
   :effect (and (not (has ?a ?i))
		(at ?i ?p))
   )

  (:action give
   :parameters (?a - character ?c - character ?i - item ?p - place)
   :precondition (and (or (main-character ?a)
			  (motive-for-has ?a ?c ?i))
		      (alive ?a)
		      (alive ?c)
		      (has ?a ?i)
		      (at ?a ?p)
		      (at ?c ?p))
   :effect (and (not (has ?a ?i))
		(has ?c ?i)
		(gift ?a ?c ?i))
   )

  (:action goto
   :parameters (?a - character ?p - place ?from - place)
   :precondition (and (or (main-character ?a)
			  (motive-for-at ?a ?a ?p))
		      (alive ?a)
		      (at ?a ?from)
		      (not (= ?p ?from)))
   :effect (and (not (at ?a ?from))
		(at ?a ?p))
   )

  ;; Although he is evil, Iago is too cautious to kill other
  ;; characters himself...
  (:action kill
   :parameters (?a - character ?c - character ?p - place)
   :precondition (and (motive-for-dead ?a ?c)
		      (alive ?a)
		      (alive ?c)
		      (at ?a ?p)
		      (at ?c ?p))
   :effect (and (not (alive ?c))
		(dead ?c)
		(killed ?a ?c))
   )

  ;; Communicative actions. Note that requests (as modelled here) are
  ;; not made to a specific character.

  (:action request-at
   :parameters (?a - character ?c - character ?p - place)
   :precondition (and (or (main-character ?a)
			  (motive-for-at ?a ?c ?p))
		      (alive ?a)
		      (alive ?c))
   :effect (requested-at ?a ?c ?p)
   )

  (:action request-has
   :parameters (?a - character ?c - character ?i - item)
   :precondition (and (or (main-character ?a)
			  (motive-for-has ?a ?c ?i))
		      (alive ?a)
		      (alive ?c))
   :effect (requested-has ?a ?c ?i)
   )

  )
