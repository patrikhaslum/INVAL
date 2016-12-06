;;#!/usr/lib/gcl-2.6.8/unixport/saved_gcl -f

;; Note: Load is only requried when running as a script.
;;(load "inval.lsp")
;;(load "rsk.lsp")

;; GCL version
;; (defun get-commandline-args ()
;;   (cdr si::*command-args*))

;; ECL version
(defun get-commandline-args ()
  (cdr (ext:command-args)))

;; note: when running as a script with ECL, use:
;; (defun get-commandline-args ()
;;   ext:*unprocessed-ecl-command-args*)


(setq *typecheck* nil)
(setq *target* 'strips)
(setq *declare-constants* t)

(defun print-help ()
  (format t "~&rsk [option | file]*~%")
  (format t "~&options:~%")
  (format t "~& -c : Type-check before compilation, abort if check fails.~%")
  (format t "~& -f : Flatten only (output PDDL3.1 without nested fluent terms).~%")
  (format t "~& -s : Compile to \"sas\" (output flat PDDL3.1 with atomic rhs's).~%")
  (format t "~&      Default output is PDDL without object fluents.~%")
  (format t "~& -n : Do not use :constants declaration in domain.~%")
  (format t "~& -r <new domain requirements list>~%")
  (format t "~& -D <output domain file>~%")
  (format t "~& -P <output problem file>~%")
  (format t "~&Any non-option argument is assumed to be an input file.~%")
  (quit))

(defun rsk-main ()
  (let ((requirements '(:adl :typing :equality :fluents))
	(domain-file-name "rsk-domain.pddl")
	(problem-file-name "rsk-problem.pddl"))
    (if (endp (get-commandline-args)) (print-help))
    (do ((rem-arg-list (get-commandline-args) (cdr rem-arg-list)))
	((endp rem-arg-list) t)
      (let ((arg (car rem-arg-list)))
	(cond ((equal arg "-c")
	       (setq *typecheck* t))
	      ((equal arg "-s")
	       (setq *target* 'sas))
	      ((equal arg "-f")
	       (setq *target* nil))
	      ((equal arg "-n")
	       (setq *declare-constants* nil))
	      ((equal arg "-r")
	       (if (endp (cdr rem-arg-list))
		   (format t "~&option -r requires an argument (requirements list)~%")
		 (setq requirements
		       (read-from-string (car (cdr rem-arg-list))))))
	      ((equal arg "-D")
	       (if (endp (cdr rem-arg-list))
		   (format t "~&option -D requires an argument (domain file name)~%")
		 (setq domain-file-name (car (cdr rem-arg-list)))))
	      ((equal arg "-P")
	       (if (endp (cdr rem-arg-list))
		   (format t "~&option -P requires an argument (problem file name)~%")
		 (setq problem-file-name (car (cdr rem-arg-list)))))
	      (t (format t "~&reading ~a...~%" arg)
		 (let ((contents (read-file arg)))
		   (parse-file arg contents))))))
    ;; Type-checking:
    (when *typecheck*
      (cond ((type-check)
	     (format t "~&~s/~s type check ok~%" *domain-name* *problem-name*))
	    (t (quit))))
    (multiple-value-bind
	(new-domain declared-constants)
	(rsk-domain *domain-name* requirements *objects* *types*
		    *predicates* *functions* *axioms* *actions*
		    :target *target* :declare-constants *declare-constants*)
      (let ((new-problem
	     (rsk-problem *problem-name* *domain-name* *objects* *types*
			  *functions* *init* *goal* *metric-type* *metric*
			  declared-constants :target *target*)))
	(format t "~&writing domain to ~a...~%" domain-file-name)
	(write-PDDL domain-file-name new-domain)
	(format t "~&writing problem to ~a...~%" problem-file-name)
	(write-PDDL problem-file-name new-problem)
	))))

;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (rsk-main))
(quit)
