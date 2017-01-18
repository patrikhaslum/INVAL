
;; To run as script using ECL:
;;
;; Make the following the first line of this file:
;;
;; #!/usr/local/bin/ecl -shell
;;
;; Uncomment the following:
;;
;; (load "inval.lsp")
;; (load "vis.lsp")
;; (defun get-commandline-args ()
;;   (cdr ext:*unprocessed-ecl-command-args*))

;; To run as script using GCL
;;
;; Make the following the first line of this file:
;;
;; #!/usr/lib/gcl-2.6.8/unixport/saved_gcl -f
;;
;; Uncomment the following:
;;
;; (load "inval.lsp")
;; (load "vis.lsp")
;; (defun get-commandline-args ()
;;   (cdr si::*command-args*))

;; To compile a stand-alone executable using ECL:
;;
;; Uncomment the following:
(defun get-commandline-args ()
  (cdr (ext:command-args)))


;; Defs below are unchanged.

(setq *typecheck* nil)
(setq *linearise* nil)
(setq *force-metric-total-time* nil)
(setq *visualisation* nil)
(setq *visualisation-document-type* nil)
(setq *visualisation-file* nil)
(setq *translation-rules* nil)
(setq *causal-link-analysis* nil)
(setq *causal-link-bounded-cost* t)
(setq *dddl* nil)

(setq *visualisations*
      (list (list 'strips-sliding-tile #'visualise-sliding-tile-puzzle 'latex)
	    (list 'blocksworld #'visualise-bw3 'latex)
	    (list 'genome-edit-distance #'visualise-ged 'latex)
	    (list 'sokoban-sequential #'visualise-sokoban-IPC6 'latex)
	    (list 'openstacks-sequencedstrips-ADL #'visualise-openstacks 'latex)
	    (list 'openstacks-sequencedstrips-nonADL-nonNegated
		  #'visualise-openstacks 'latex)
	    (list 'parking-game #'visualise-rush-hour 'latex)
	    (list 'hydraulic_blocks_world #'visualise-numeric-hbw 'html)
	    (list 'html-table #'visualise-html-table 'html)
	    ))

(defun visualisation-preamble (doctype)
  (cond ((eq doctype 'latex)
	 '("\\documentclass[10pt,a4paper]{article}"
	   "\\usepackage{pgf}"
	   "\\usepackage{tikz}"
	   "\\begin{document}"))
	((eq doctype 'html)
	 '("<html>"
	   "<head><title>Plan Validation Result</title></head>"
	   "<body>"))
	(t (error "unknown document type: ~a" doctype))
	))

(defun visualisation-postamble (doctype)
  (cond ((eq doctype 'latex)
	 '("\\end{document}"))
	((eq doctype 'html)
	 '("</body>"
	   "</html>"))
	(t (error "unknown document type: ~a" doctype))
	))

(defun latex-escape-string (str)
  (with-output-to-string
    (result)
    (dotimes (i (length str))
      (cond ((eq (elt str i) #\_) (format result "\\_"))
	    ((eq (elt str i) #\#) (format result "\\#"))
	    (t (format result "~c" (elt str i)))
	    ))))

(defun visualise-plan-header (doctype plan-name plan-valid plan-value)
  (cond ((eq doctype 'latex)
	 (with-output-to-string
	   (result)
	   (format result "\\section*{~a}~%" (latex-escape-string plan-name))
	   (format result "Valid: ~a\\\\~%" (if plan-valid "Yes" "No"))
	   (format result "Metric: ~a~%~%\\noindent" plan-value)
	   ))
	((eq doctype 'html)
	 (with-output-to-string
	   (result)
	   (format result "<h1>~a</h1>~%" plan-name)
	   (format result "<p>Valid: ~a</p>~%" (if plan-valid "Yes" "No"))
	   (format result "<p>Metric: ~a</p>~%" plan-value)
	   ))
	(t (error "unknown document type: ~a" doctype))
	))

(defun print-visualisation-list ()
  (format t "~&Defined visualisations (name / format):~%")
  (dolist (vis *visualisations*)
    (format t " ~a / ~a~%" (first vis) (third vis))))

(defun print-visualisation (stream val-res-list)
  (dolist
      (ln (visualisation-preamble *visualisation-document-type*))
    (format stream "~&~a~%" ln))
  (dolist (val-res val-res-list)
    (format stream "~&~a~%"
	    (visualise-plan-header
	     *visualisation-document-type*
	     (first (first val-res))
	     (second val-res)
	     (third val-res)))
    (format stream "~&~a~%" (fourth val-res)))
  (dolist
      (ln (visualisation-postamble *visualisation-document-type*))
    (format stream "~&~a~%" ln))
  )

;; apply pre-validation processing (as specified by global options) to
;; input plan (plan only - no name).
(defun preprocess (plan)
  (cond (*translation-rules*
	 (translate-plan plan *translation-rules*))
	(*linearise*
	 (linearise plan))
	(t plan)
	))

;; returns a sorted assoc list from (numeric) metric values of valid plans
;; to list of plan names. input is the list of validation results, each a
;; list (name valid value [vis-output]); visualisation output is ignored.
(defun group-by-values (val-res-list)
  (let ((mvlist nil))
    (dolist (val-res val-res-list)
      (when (and (second val-res) (numberp (third val-res)))
	(let ((current (assoc (third val-res) mvlist)))
	  (setq mvlist (reassoc-in-order
			(third val-res)
			(if current
			    (cons (first (first val-res)) (cdr current))
			  (list (first (first val-res))))
			mvlist :order #'<)))))
    mvlist))

(defun average-value (mvlist)
  (/ (reduce #'+ (mapcar #'(lambda (entry)
			     (* (car entry) (length (cdr entry))))
			 mvlist)
	     :initial-value 0)
     (reduce #'+ (mapcar #'(lambda (entry)
			     (length (cdr entry)))
			 mvlist)
	     :initial-value 0)))

(defun print-help ()
  (format t "~&inval [option | file]*~%")
  (format t "~&Options:~%")
  (format t "~& -v : Increase verbosity by +1~%")
  (format t "~& -q : Set verbosity to 0~%")
  (format t "~& -c : Type-check before validation, abort if check fails.~%")
  (format t "~& -m : Force metric to be (total-time).~%")
  (format t "~& -l : Linearise plans prior to validation.~%")
  (format t "~&Plan visualisation:~%")
  (format t "~& -z : Domain-specific visualisation.~%")
  (format t "~& -Z <visualisation name> : Select a generic visualisation.~%")
  (format t "~& -o <file> : Save visualisation to <file>.~%")
  (print-visualisation-list)
  (format t "~&Exerimental options:~%")
  (format t "~& -tx : Don't check argument types against action parameters.")
  (format t "~& -te : (either ..) in declarations is disjunctive.")
  (format t "~& -ignore : Ignore excess arguments and undefined actions.~%")
  (format t "~& -f : Use fast axiom fixpoint computation.~%")
  (format t "~& -s : Use maximal axiom stratification.~%")
  (format t "~& -cl : Causal link analysis.~%")
  (format t "~&Any non-option argument is assumed to be an input file.~%")
  (quit)
  )

(defun inval-main ()
  ;; Process command line arguments and read input files.
  ;; undocumented options:
  ;; -dddl : Special option to validate plans against domains
  ;;      compiled from a DDDL spec. Sets the metric to multi-set
  ;;      of faults.
  (if (endp (get-commandline-args)) (print-help))
  (do ((rem-arg-list (get-commandline-args) (cdr rem-arg-list)))
      ((endp rem-arg-list) t)
    (let ((arg (car rem-arg-list)))
      (cond ((equal arg "-v")
	     (setq *verbosity* (+ *verbosity* 1)))
	    ((equal arg "-q")
	     (setq *verbosity* 0))
	    ((equal arg "-c")
	     (setq *typecheck* t))
	    ((equal arg "-m")
	     (setq *force-metric-total-time* t))
	    ((equal arg "-z")
	     (let ((vfun (assoc *domain-name* *visualisations*)))
	       (cond (vfun
		      (setq *visualisation* (second vfun))
		      (setq *visualisation-document-type* (third vfun)))
		     (t (format t "~&no visualisation defined for domain ~s~%"
				*domain-name*)
			(print-visualisation-list)
			(quit)))))
	    ((equal arg "-Z")
	     (when (endp (cdr rem-arg-list))
	       (format t "~&option -Z requires an argument (visualisation name)~%")
	       (print-visualisation-list)
	       (quit))
	     (let ((vname (read-from-string (car (cdr rem-arg-list)))))
	       (setq rem-arg-list (cdr rem-arg-list))
	       (let ((vfun (assoc vname *visualisations*)))
		 (cond (vfun
			(setq *visualisation* (second vfun))
			(setq *visualisation-document-type* (third vfun)))
		       (t (format t "~&no visualisation named ~s~%" vname)
			  (print-visualisation-list)
			  (quit))))))
	    ((equal arg "-o")
	     (when (endp (cdr rem-arg-list))
	       (format t "~&option -o requires an argument~%")
	       (quit))
	     (setq *visualisation-file* (car (cdr rem-arg-list)))
	     (setq rem-arg-list (cdr rem-arg-list)))
	    ((equal arg "-T")
	     (when (endp (cdr rem-arg-list))
	       (format t "~&option -T requires an argument~%")
	       (quit))
	     (setq *translation-rules* (read-file (car (cdr rem-arg-list))))
	     (setq rem-arg-list (cdr rem-arg-list)))
	    ((equal arg "-l")
	     (setq *linearise* t))
	    ((equal arg "-tx")
	     (setq *action-parameter-types-are-preconditions* nil))
	    ((equal arg "-te")
	     (setq *either-in-declarations-means-and* nil))
	    ((equal arg "-ignore")
	     (setq *ignore-excess-arguments* t)
	     (setq *ignore-undefined-actions* t))
	    ((equal arg "-f")
	     (setq *fast-axiom-fixpoint* t))
	    ((equal arg "-s")
	     (setq *stratify-axioms-maximally* t))
	    ((equal arg "-cl")
	     (setq *causal-link-analysis* t))
	    ((equal arg "-clu")
	     (setq *causal-link-analysis* t)
	     (setq *causal-link-bounded-cost* nil))
	    ((equal arg "-dddl")
	     (setq *quoted-argument-predicates* '(fault observe))
	     (setq *duplicated-predicates* '(fault))
	     (setq *dddl* t)
	     (setq *metric* #'collect-faults))
	    (t
	     (format t "~&reading ~a...~%" arg)
	     (let ((contents (read-file arg)))
	       (parse-file arg contents))))))
  (when (or (null *metric*) *force-metric-total-time*)
    (setq *metric* '(total-time))
    (setq *metric-type* 'minimize))
  ;; Type-checking:
  (cond (*typecheck*
	 (setq *axioms*
	       (mapcar #'(lambda (axiom)
			   (type-enhance-axiom axiom *predicates* *types*))
		       *axioms*))
	 (if (not (type-check)) (quit)
	   (format t "~&domain/problem type check ok~%"))))
  ;; Stratify domain axioms (if any):
  (let* ((stratified-axioms (stratify *axioms*))
    ;; Validate each plan...
	 (val-res-list
	  (mapcar
	   #'(lambda (plan)
	       (cons (list (car plan)
			   (reduce #'+ (cdr plan) :key #'length)
			   (length (cdr plan)))
		     (validate-plan
		      (car plan) (preprocess (cdr plan))
		      *init* *goal* *constraints* *metric*
		      *actions* stratified-axioms *types* *objects*
		      :visualisation *visualisation*)))
	   *plans*))
	 (metric-value-list (group-by-values val-res-list)))
    ;; ...and print a nice summary.
    (dolist (val-res val-res-list t)
      (format t "~&plan ~a: ~a, value: ~a (~a actions, ~a steps)~%"
	      (first (first val-res))
	      (if (second val-res) "valid" "not valid")
	      (if (numberp (third val-res)) (third val-res) '-)
	      (second (first val-res))
	      (third (first val-res)))
      )
    ;; If metric-value-list is non-empty, print some stats
    (when metric-value-list
      (format t "~&distribution of metric values:~%")
      (dolist (entry metric-value-list)
	(format t " ~a : ~a~%" (car entry) (length (cdr entry))))
      (format t "~&average value: ~a~%" (average-value metric-value-list))
      (format t "~&min value: ~a~%" (car (car metric-value-list))))
    ;; If causal link analysis is on, and we have at least two different
    ;; metric values...
    (when (and *causal-link-analysis*
	       (> (length metric-value-list) 1))
      (let ((cl-opt (extract-causal-links-from-plan-set
		     (mapcar #'(lambda (pn) (assoc-val pn *plans*))
			     (cdr (first metric-value-list)))
		     *init* *actions* stratified-axioms *types* *objects*
		     nil))
	    (threats (collect-threats *actions*))
	    (cl-rej nil))
	(when (> *verbosity* 0)
	  (format t "~&found ~a good causal links...~%" (length cl-opt)))
	(dolist (entry (rest metric-value-list))
	  (setq cl-rej (extract-causal-links-from-plan-set
			(mapcar #'(lambda (pn) (assoc-val pn *plans*))
				(cdr entry))
			*init* *actions* stratified-axioms *types* *objects*
			cl-rej
			:filter #'(lambda (p c a pc cc)
				    (cl-reject-filter
				     p c a pc cc
				     (car (first metric-value-list))
				     cl-opt))))
	  (when (> *verbosity* 0)
	    (format t "~&now ~a bad causal links...~%" (length cl-rej)))
	  )
	(format t "~&REJECT LIST:~%")
	(dolist (cl cl-rej)
	  (format t "~&~a [~a] => ~a [~a] ; ~a [~a]~%"
		  (first cl) (fourth cl) (second cl) (fifth cl) (third cl)
		  (let ((atom-threats (assoc (first (third cl)) threats)))
		    (if atom-threats (length (cdr atom-threats)) 0))
		  ))
	))
    ;; If visualisation is on, print the vresult for each plan:
    (cond ((and *visualisation* *visualisation-file*)
	   (with-open-file
	    (vs *visualisation-file* :direction :output)
	    (print-visualisation vs val-res-list)))
	  (*visualisation*
	   (print-visualisation t val-res-list))
	  )
    ;; If option dddl is set, print a dominance graph:
    (cond (*dddl*
	   (format t "~&digraph dominance {~%")
	   (dolist (val-res val-res-list t)
	     (cond ((second val-res)
		    (format t "~& ~a [label=\"~a\"];~%"
			    (first (first val-res))
			    (first (first val-res))))))
	   (dolist (val-res-1 val-res-list t)
	     (dolist (val-res-2 val-res-list t)
	       (cond ((and (second val-res-1)
			   (second val-res-2)
			   (strictly-preferred
			    (third val-res-1) (third val-res-2)))
		      (format t "~& ~a -> ~a;~%"
			      (first (first val-res-1))
			      (first (first val-res-2)))))))
	   (format t "~&}~%")
	   ))
    ))

;; supporting functions for causal link analysis:

;; note: filter function should return true (non-nil) for links that
;; we want to KEEP.
;; (defun cl-reject-filter (producer consumer atom pcost ccost opt-cost opt-cl)
;;   (and (if (and *causal-link-bounded-cost* (numberp ccost))
;; 	   (<= ccost opt-cost) t)
;;        (not (find-if #'(lambda (cl)
;; 			 (and (equal (first cl) producer)
;; 			      (equal (second cl) consumer)
;; 			      (equal (third cl) atom)))
;; 		     opt-cl))))

(defun cl-reject-filter (producer consumer atom pcost ccost opt-cost opt-cl)
  (cond ((and *causal-link-bounded-cost* (numberp ccost) (> ccost opt-cost))
	 (when (> *verbosity* 1)
	   (format t "~&discarding (~a ~a ~a) because ~a > ~a~%"
		   producer consumer atom ccost opt-cost))
	 nil)
	((find-if #'(lambda (cl)
		      (and (equal (first cl) producer)
			   (equal (second cl) consumer)
			   (equal (third cl) atom)))
		  opt-cl)
	 (when (> *verbosity* 1)
	   (format t "~&discarding (~a ~a ~a) because it is a good link~%"
		   producer consumer atom))
	 nil)
	(t t)))

(defun collect-deleted-predicates (form dels)
  (cond ((eq (car form) 'and)
	 (dolist (f1 (cdr form))
	   (setq dels (collect-deleted-predicates f1 dels)))
	 dels)
	((eq (car form) 'forall)
	 (collect-deleted-predicates (third form) dels))
	((eq (car form) 'when)
	 (collect-deleted-predicates (third form) dels))
	((eq (car form) 'not)
	 (if (not (member (first (second form)) dels))
	     (cons (first (second form)) dels)
	   dels))
	(t dels)))

(defun collect-threats (actions)
  (let ((threat-map nil))
    (dolist (act actions)
      (let ((dels (collect-deleted-predicates
		   (assoc-val ':effect (cdr act)) nil)))
	(dolist (pred dels)
	  (setq threat-map (add-to-set-map pred (car act) threat-map)))))
    threat-map))

;; custom DDDL stuff:

(defun collect-faults (state)
  (let ((fault-count nil))
    (dolist (atom state)
      (cond ((eq (car atom) 'fault)
	     (let ((cur (assoc (cadr atom) fault-count :test #'equal)))
	       (cond (cur (rplacd cur (+ (cdr cur) 1)))
		     (t (setq fault-count
			      (cons (cons (cadr atom) 1) fault-count)))
		     )))))
    fault-count))

(defun preferred (hyp1 hyp2)
  (every #'(lambda (fc1)
	     (let ((fc2 (assoc (car fc1) hyp2 :test #'equal)))
	       (cond (fc2 (>= (cdr fc2) (cdr fc1)))
		     (t nil))))
	 hyp1))

(defun strictly-preferred (hyp1 hyp2)
  (and (preferred hyp1 hyp2) (not (preferred hyp2 hyp1))))


;; Call main function inside an error handler.

(handler-bind
 ((condition #'(lambda (erc)
		 (format *error-output* "~&~A~&" erc)
		 (quit))))
 (inval-main))
(quit)
