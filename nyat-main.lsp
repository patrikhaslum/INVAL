;; #!/usr/local/bin/ecl -shell

;; (load "inval.lsp")
;; (load "rsk.lsp")
;; (load "simplify.lsp")
;; (load "fdr3.lsp")

;; GCL version
;; (defun get-commandline-args ()
;;   (cdr si::*command-args*))

;; ECL version
(defun get-commandline-args ()
  (cdr (ext:command-args)))

;; set config options
(setq *verbosity* 0)
(setq *typecheck* t)

;; increase memory limit to 2Gb
;; (ext:set-limit 'ext:heap-size (* 2 1024 1024 1024))
;; (let ((heap-lim (ext:get-limit 'ext:heap-size)))
;;   (format t "heap size limit: ~a~%" heap-lim))

(defun new-yat-main ()
  ;; read/parse input files
  (do ((rem-arg-list (get-commandline-args) (cdr rem-arg-list)))
      ((endp rem-arg-list) t)
      (let ((arg (car rem-arg-list)))
	(cond ((string= arg "-v")
	       (setq *verbosity* (+ *verbosity* 1)))
	      ((string= arg "-m")
	       (if (endp (cdr rem-arg-list))
		   (error "option -m requires an argument (heap size in Mb)"))
	       (let ((new-lim (read-from-string (cadr rem-arg-list))))
		 (if (not (numberp new-lim))
		     (error "argument to -m must be a number!"))
		 (ext:set-limit 'ext:heap-size (* new-lim 1024 1024))
		 (let ((heap-lim (ext:get-limit 'ext:heap-size)))
		   (format t "heap size limit: ~a~%" heap-lim))
		 (setq rem-arg-list (cdr rem-arg-list))))
	      ((string= arg "-enum-names")
	       (setq *name-FDR-variable-by-atom-name* nil))
	      ((string= arg "-no-cost")
	       (setq *force-non-metric* t))
	      ((string= arg "-no-type-check")
	       (setq *typecheck* nil))
	      (t (format t "~&reading ~a...~%" arg)
		 (let ((contents (read-file arg)))
		   (parse-file arg contents))))))
  ;; Type-checking:
  (cond (*typecheck*
	 (setq *axioms*
	       (mapcar #'(lambda (axiom)
			   (type-enhance-axiom axiom *predicates* *types*))
		       *axioms*))
	 (if (not (type-check)) (quit)
	   (format t "~&domain/problem type check ok~%"))))
  (when (>= *verbosity* 1) (format t "~&rsk to SAS...~%"))
  (let ((sfun (collect-static-functions *functions* *actions*)))
    (when (>= *verbosity* 1) (format t "~&static functions: ~a~%" sfun))
    (rsk-internal :target 'sas
		  :static-fun sfun))
  (when (>= *verbosity* 1) (format t "~&grounding...~%"))
  (multiple-value-bind (fluents atoms ground-actions ground-axioms)
      (simple-ground *predicates* *functions* *actions* *axioms*
		     *init* *goal* *types* *objects*)
    (multiple-value-bind
	(axiom-strata dp-strata) (stratify *axioms*)
      (format t "~&writing output.sas...~%")
      (with-open-file
       (stream "output.sas" :direction :output)
       (output-FDR-v3 stream fluents atoms dp-strata
		      (filter-sas-actions ground-actions)
		      ground-axioms *init* *goal*)
       ))))

;; call main with a print-and-quit handler for all error conditions
(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (new-yat-main))
(quit)
