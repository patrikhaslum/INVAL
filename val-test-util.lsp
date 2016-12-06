
;; Utilities for comparing VAL and INVAL on sets of problems and plans.
;;;;

;; Run INVAL and VAL on domain + problem + file and compare their
;; output. domain-file, problem-file and plan-file can be either
;; pathnames or strings (designating files). Returns T iff both
;; validators are in agreement, nil otherwise. Also prints the test
;; (files) and the outcome.
;;
;; The metric value output for a plan can sometimes differ because
;; of decimal printing precision. The variable *precision-threshold*
;; determines how large a difference is accepted as a "precision
;; issue", rather than a true disagreement between the validators.
;; Precision mismatches still count as failed tests, but they are
;; printed differently.

(defvar *precision-threshold* 0.001)

(defun do-test (domain-file problem-file plan-file)
  (format t "~&test: ~a ~a ~a~%" domain-file problem-file plan-file)
  (setq *verbosity* 0)
  (clear-definitions)
  (parse-file domain-file (read-file domain-file))
  (parse-file problem-file (read-file problem-file))
  (let ((the-plan (parse-plan plan-file (read-file plan-file))))
    (let ((inval-res
	   (cond ((type-check)
		  (validate-plan (car the-plan) (cdr the-plan) *init* *goal*
				 *constraints* *metric* *actions*
				 (stratify *axioms*) *types* *objects*))
		 (t nil)))
	  (val-res (run-val domain-file problem-file plan-file)))
      (cond ((not (eq (null inval-res) (null val-res)))
	     (format t "mismatch: ~s ~s~%" inval-res val-res)
	     nil)
	    ((not (eq (null (car inval-res)) (null (car val-res))))
	     (format t "mismatch: ~s ~s~%" inval-res val-res)
	     nil)
	    ((and *metric* (car inval-res)
		  (not (equal (cadr inval-res) (cadr val-res))))
	     (if (< (abs (- (cadr inval-res) (cadr val-res)))
		    *precision-threshold*)
		 (format t "precision: ~s ~s~%" inval-res val-res)
	       (format t "mismatch: ~s ~s~%" inval-res val-res))
	     nil)
	    (t (format t "ok~%" inval-res val-res)
	       t)
	    ))))


;; Run INVAL vs. VAL test on a collection of problems and plans.
;; domain-file: Name of the domain file, without .pddl extension.
;;  The domain file is assumed to reside in the same directory
;;  as problem files. To search for per-problem domain files,
;;  pass nil as this argument.
;; problem-file-pattern: a pattern (pathname with wildcards) for
;;  the set of problem files to test on.
;; plan-dir: Directory where to search for plan files. May contain
;;  wildcards (to search directory subtree). Must have trailing slash.
;;  If nil, defaults to the same directory as problem files. Plan files
;;  are assumed to to have the same name (or same first three letters)
;;  as the problem file, and extension [.<something>].soln[.<number>],
;;  in place of .pddl if the problem file has that extension.
;; Returns a two-element list with the number of successful and
;; failed tests. Each test run also prints the status of that test.

(defun do-test-all (domain-file problem-file-pattern
				&key (plan-loc nil) (dry-run nil) (max-n nil))
  (let ((pflist (sort (directory problem-file-pattern)
		      #'string< :key #'namestring))
	(n-ok 0)
	(n-failed 0))
    (dolist (problem-file (if max-n (list-first-n pflist max-n) pflist))
      (let ((checked-df (find-domain-for-problem domain-file problem-file)))
	(cond (checked-df
	       (dolist (plan-file (plan-file-list-for-problem
				   problem-file plan-loc))
		 (cond
		  (dry-run
		   (format t "found: ~a ~a ~a~%"
			   checked-df problem-file plan-file))
		  (t
		   (if (do-test checked-df problem-file plan-file)
		       (incf n-ok) (incf n-failed)))
		  )))
	      (t (format t "~&no domain file found for problem ~a~%"
			 problem-file)))))
    (list n-ok n-failed)))

(defun list-first-n (lst n)
  (if (> (length lst) n) (butlast lst (- (length lst) n)) lst))

(defun find-domain-for-problem (domain-file problem-pname)
  (if domain-file (probe-file
		   (make-pathname
		    :directory (pathname-directory problem-pname)
		    :name domain-file :type "pddl"))
    (let ((f1 (probe-file
	       (make-pathname
		:directory (pathname-directory problem-pname)
		:name (concatenate 'string (pathname-name problem-pname)
				   "-domain")
		:type "pddl")))
	  (f2 (probe-file
	       (make-pathname
		:directory (pathname-directory problem-pname)
		:name (concatenate 'string "domain_"
				   (pathname-name problem-pname))
		:type "pddl")))
	  (f3 (probe-file
	       (make-pathname
		:directory (pathname-directory problem-pname)
		:name (concatenate 'string
				   (subseq (pathname-name problem-pname) 0 3)
				   "_domain")
		:type "pddl"))))
      (if f1 f1
	(if f2 f2
	  f3)))))

(defun plan-file-list-for-problem (problem-pname plan-loc)
  (cond
   (plan-loc
    (nconc
     (directory (concatenate 'string plan-loc
			     (pathname-name problem-pname)
			     "*.soln"))
     (directory (concatenate 'string plan-loc
			     (subseq (pathname-name problem-pname) 0 3)
			     "*.soln"))
     (directory (concatenate 'string plan-loc
			     (pathname-name problem-pname)
			     "*.soln.*"))
     ))
   (t (nconc
       (directory
	(namestring
	 (make-pathname :directory (pathname-directory problem-pname)
			:name (pathname-name problem-pname)
			:type "*.soln")))
       (directory
	(namestring
	 (make-pathname :directory (pathname-directory problem-pname)
			:name (subseq (pathname-name problem-pname) 0 3)
			:type "*.soln")))
       (directory
	(namestring
	 (make-pathname :directory (pathname-directory problem-pname)
			:name (pathname-name problem-pname)
			:type "*.soln.*")))
       ))
   ))


;; Run VAL on domain-file, problem-file and plan-file, which can be
;; either pathnames or strings (designating files). Returns a list
;; (ok value), where 'ok' (T/NIL) indicates the validation outcome
;; and 'value' the plan value, or NIL if VAL fails to parse or type
;; check any of the inputs.

(defun run-val (domain-file problem-file plan-file &key (program "validate"))
  (let ((stream (ext:run-program
		 program (list "-S" (path-as-string domain-file)
			       (path-as-string problem-file)
			       (path-as-string plan-file))
		 :input NIL :output :stream :error :output)))
    (if (null stream)
	(error "failed to run VAL executable (~s)" program))
    (let ((res (let ((*readtable* *pddl-readtable*))
		 (read stream nil nil))))
      (cond ((numberp res) (list t res))
	    ((eq res 'failed) (list nil nil))
	    (t nil)))))

(defun path-as-string (pathname-or-string)
  (cond ((pathnamep pathname-or-string)
	 (namestring pathname-or-string))
	(t pathname-or-string)))



;; force update of symbol completion table on load
;; (if (find-package "ECL-READLINE")
;;     (setq ecl-readline::*current-package* nil))
