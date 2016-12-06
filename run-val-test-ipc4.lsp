
;; Running as a script
;;;;
;;
;; #!/usr/local/bin/ecl -shell
;;
;; (load "inval.lsp")
;; (load "val-test-util.lsp")
;;
;; (defun get-commandline-args ()
;;   (cdr ext:*unprocessed-ecl-command-args*))
;;
;;;;

(setq *max-tests-per-domain* 2)

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))

 ;; Airport

 (format t "~&~%=== Airport/ADL ===~%~%")
 (do-test-all
  "domain" "../domains/ipc4/airport/adl/p??_airport*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/airport/nontemporal/adl/*/"
  :max-n *max-tests-per-domain*)

 (format t "~&~%=== Airport/STRIPS ===~%~%")
 (do-test-all
  nil "../domains/ipc4/airport/strips/p??_airport*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/airport/nontemporal/strips/*/"
  :max-n *max-tests-per-domain*)

 ;; Pipesworld
 
 (format t "~&~%=== Pipesworld-Notankage/STRIPS ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/pipesworld/notankage-nontemporal/strips/p??_net*.pddl"
  :max-n *max-tests-per-domain*)

 (format t "~&~%=== Pipesworld-Tankage/STRIPS ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/pipesworld/tankage-nontemporal/strips/p??_net*.pddl"
  :max-n *max-tests-per-domain*)

 ;; Promela (Philosophers)

 ;; Philosophers non-numeric ADL formulations all declare a type with name
 ;; 'number' which is not allowed by recent versions of VAL; all tests in
 ;; these domain formulations fail.

 ;; (format t "~&~%=== Philosophers/ADL ===~%~%")
 ;; (do-test-all
 ;;  "domain" "../domains/ipc4/promela/philosophers/adl/p??_*.pddl"
 ;;  "../domains/ipc4/RESULTS/promela/philosophers/adl/*/")

 (format t "~&~%=== Philosophers/STRIPS ===~%~%")
 (do-test-all
  nil "../domains/ipc4/promela/philosophers/strips/p0?.pddl"
  :plan-loc "../domains/ipc4/RESULTS/promela/philosophers/strips/*/"
  :max-n *max-tests-per-domain*)

 ;; (format t "~&~%=== Philosophers-DerivedPred/ADL-DerivedPred ===~%~%")
 ;; (do-test-all
 ;;  "domain"
 ;;  "../domains/ipc4/promela/philosophers_derivedpredicates/adl_derivedpredicates/p0?_phil*.pddl"
 ;;  "../domains/ipc4/RESULTS/promela/philosophers_derivedpredicates/adl_derivedpredicates/*/")

 (format t "~&~%=== Philosophers-DerivedPred/STRIPS-DerivedPred ===~%~%")
 (do-test-all
  nil
  "../domains/ipc4/promela/philosophers_derivedpredicates/strips_derivedpredicates/p0?_phil*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/promela/philosophers_derivedpredicates/strips_derivedpredicates/*/"
  :max-n *max-tests-per-domain*)

 (format t "~&~%=== Philosophers-Fluents/ADL-Fluents ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/promela/philosophers_fluents/adl_fluents/p0?_phil*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/promela/philosophers_fluents/adl_fluents/*/"
  :max-n *max-tests-per-domain*)

 (format t "~&~%=== Philosophers-Fluents-DerivedPred/ADL-Fluents-DerivedPred ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/promela/philosophers_fluents_derivedpre/adl_fluents_derivedpredicates/p0?_phil*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/promela/philosophers_fluents_derivedpre/adl_fluents_derivedpredicates/*/"
  :max-n *max-tests-per-domain*)

 ;; PSR

 ;; Use fast fixpoint computation for the ADL versions of this domain.
 ;; In the STRIPS version, axioms are grounded, so it does not improve.
 ;; (setq *fast-axiom-compute-fixpoint* t)

 ;; (format t "~&~%=== PSR-Middle/ADL-DerivedPred ===~%~%")
 ;; (do-test-all
 ;;  "domain"
 ;;  "../domains/ipc4/psr/middle/adl_derivedpredicates/p*.pddl"
 ;;  :plan-loc "../domains/ipc4/RESULTS/psr/middle/adl_derivedpredicates/*/"
 ;;  :max-n *max-tests-per-domain*)

 ;; (format t "~&~%=== PSR-Middle/SimpleADL-DerivedPred ===~%~%")
 ;; (do-test-all
 ;;  nil
 ;;  "../domains/ipc4/psr/middle/simpleadl_derivedpredicates/p??_s*.pddl"
 ;;  :plan-loc "../domains/ipc4/RESULTS/psr/middle/simpleadl_derivedpredicates/*/"
 ;;  :max-n *max-tests-per-domain*)

 ;; (setq *fast-axiom-compute-fixpoint* nil)

 ;; (format t "~&~%=== PSR-Middle/STRIPS-DerivedPred ===~%~%")
 ;; (do-test-all
 ;;  nil
 ;;  "../domains/ipc4/psr/middle/strips_derivedpredicates/p0?_s*.pddl"
 ;;  :plan-loc "../domains/ipc4/RESULTS/psr/middle/strips_derivedpredicates/*/"
 ;;  :max-n *max-tests-per-domain*)

 (format t "~&~%=== PSR-Small/STRIPS ===~%~%")
 (do-test-all
  nil
  "../domains/ipc4/psr/small/strips/p??.pddl"
  :plan-loc "../domains/ipc4/RESULTS/psr/small/strips/*/"
  :max-n *max-tests-per-domain*)

 ;; Satellite

 (format t "~&~%=== Satellite-STRIPS/STRIPS ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/satellite/strips/strips/p*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/satellite/strips/strips/*/"
  :max-n *max-tests-per-domain*)

 (format t "~&~%=== Satellite-Numeric/STRIPS-Fluents ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/satellite/numeric/strips_fluents/p*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/satellite/numeric/strips_fluents/*/"
  :max-n *max-tests-per-domain*)

 ;; Settlers

 (format t "~&~%=== Settlers/STRIPS-Fluents ===~%~%")
 (do-test-all
  "domain"
  "../domains/ipc4/settlers/strips_fluents/p*.pddl"
  :plan-loc "../domains/ipc4/RESULTS/settlers/ipc_3/strips_fluents/*/"
  :max-n *max-tests-per-domain*)

 ) ; end of handler-bind

(quit)
