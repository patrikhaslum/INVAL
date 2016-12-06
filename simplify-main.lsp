;;#!/usr/local/bin/ecl -shell

;; Note: Load is only requried when used interactively or as a script.
;; (load "inval.lsp")
;; (load "rsk.lsp")
;; (load "simplify.lsp")

;; GCL version
;; (defun get-commandline-args ()
;;   (cdr si::*command-args*))

;; ECL version
(defun get-commandline-args ()
  (cdr (ext:command-args)))

;; Note: When running as a script with ECL, use:
;; (defun get-commandline-args ()
;;   ext:*unprocessed-ecl-command-args*)


(setq *typecheck* nil)
(setq *declare-constants* t)
(setq *simplify* t)
(setq *ground* nil)
(setq *detype* nil)
(setq *output-types* nil)
(setq *compile-disjunctive-goal* t)
(setq *force-print-problem* nil)
(setq *input-files* nil)
(setq *domain-name-prefix* "domain-")
(setq *problem-name-prefix* "simplified-")

(defun print-help ()
  (format t "~&simplify [options] <domain> <problem>~%")
  (format t "~& -c : Type-check before simplifying~%")
  (format t "~& -n : Do not use :constants declaration in domain.~%")
  (format t "~& -d : Leave disjunctive goal formula uncompiled.~%")
  (format t "~& -a : Leave all ADL constructs uncompiled.~%")
  (format t "~& -t : Convert types to predicates.~%")
  (format t "~& -T : Convert types to predicates and force typed output.~%")
  (format t "~& -D <prefix> : Set compiled domain name prefix.~%")
  (format t "~& -P <prefix> : Set compiled problem name prefix.~%")
  (quit))

(defun simplify-main ()
  (do ((rem-arg-list (get-commandline-args) (cdr rem-arg-list)))
      ((endp rem-arg-list) t)
      (let ((arg (car rem-arg-list)))
	(cond ((equal arg "-c")
	       (setq *typecheck* t))
	      ((equal arg "-n")
	       (setq *declare-constants* nil))
	      ((equal arg "-d")
	       (setq *compile-disjunctive-goal* nil))
	      ((equal arg "-p")
	       (setq *force-print-problem* t))
	      ((equal arg "-a")
	       (setq *simplify* nil))
	      ((equal arg "-g")
	       (setq *ground* t))
	      ((equal arg "-t")
	       (setq *detype* t))
	      ((equal arg "-T")
	       (setq *detype* t)
	       (setq *output-types* 'force))
	      ((equal arg "-D")
	       (when (endp (cdr rem-arg-list))
		 (format t "~&option -D requires an argument~%")
		 (quit))
	       (setq *domain-name-prefix* (car (cdr rem-arg-list)))
	       (setq rem-arg-list (cdr rem-arg-list)))
	      ((equal arg "-P")
	       (when (endp (cdr rem-arg-list))
		 (format t "~&option -P requires an argument~%")
		 (quit))
	       (setq *problem-name-prefix* (car (cdr rem-arg-list)))
	       (setq rem-arg-list (cdr rem-arg-list)))
	      (t (setq *input-files* (append *input-files* (list arg))))
	      )))
  (when (endp *input-files*) (print-help))
  ;; read input
  (dolist (fname *input-files*)
    (format t "~&reading ~a...~%" fname)
    (let ((contents (read-file fname)))
      (parse-file fname contents)))
  ;; type-checking:
  (when *typecheck*
    (cond ((type-check)
	   (format t "~&~s/~s type check ok~%" *domain-name* *problem-name*))
	  (t (quit))))
  ;; simplify and write output
  (multiple-value-bind
      (new-domain new-problem)
      (if *simplify*
	  (simplify *domain-name* *problem-name* '(:adl :typing :equality)
		    *predicates* *functions* *actions* *axioms* *init* *goal*
		    *metric-type* *metric* *types* *objects*
		    :declare-constants *declare-constants*
		    :compile-disjunctive-goal *compile-disjunctive-goal*
		    :with-types *output-types*
		    :ground-all-parameters *ground*)
	(let ((constants nil))
	  (when *declare-constants*
	    (dolist (act *actions*)
	      (dolist (cname (constants-in-expression
			      (cdr (assoc ':precondition (cdr act)))))
		(pushnew cname constants))
	      (dolist (cname (constants-in-expression
			      (cdr (assoc ':effect (cdr act)))))
		(pushnew cname constants))))
	  (values
	   (make-domain-definition
	    *domain-name* '(:adl :typing :equality) *types* *objects*
	    constants *predicates* *functions* *axioms* *actions*
	    :with-types *output-types*)
	   (make-problem-definition
	    *problem-name* *domain-name*
	    (remove-if #'(lambda (od) (find (car od) constants)) *objects*)
	    *init* *goal* *metric-type* *metric*
	    :with-types *output-types*))))
    (when (and (null new-problem) (or *force-print-problem* *detype*))
      (setq new-problem
	    (make-problem-definition *problem-name* *domain-name*
				     *objects* *init* *goal*
				     *metric-type* *metric*
				     :with-types *output-types*)))
    (when *detype*
      (clear-definitions)
      (parse-definition "new domain" new-domain)
      (parse-definition "new problem" new-problem)
      (multiple-value-setq (new-domain new-problem)
	(detype '(:adl :equality) :with-types *output-types*)))
    (let ((new-domain-file
	   (concatenate 'string "domain-"
			(pathname-name (nth (- (length *input-files*) 1)
					    *input-files*)) ".pddl"))
	  (new-problem-file
	   (concatenate 'string	"simplified-"
			(pathname-name (nth (- (length *input-files*) 1)
					    *input-files*)) ".pddl")))
      (format t "~&writing domain to ~a...~%" new-domain-file)
      (write-PDDL new-domain-file new-domain)
      (when new-problem
	(format t "~&writing problem to ~a...~%" new-problem-file)
	(write-PDDL new-problem-file new-problem))
      )))

;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (simplify-main))
(quit)
