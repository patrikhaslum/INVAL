
;; Visualisation help functions.

(defun find-predicates (predicate-list state)
  (let ((res nil))
    (dolist (atom state)
      (if (find (car atom) predicate-list)
	  (push atom res)))
    res))

(defun find-predicate-arguments (predicate posl keys values state)
  (let ((res nil))
    (dolist (atom state)
      (if (eq (car atom) predicate)
	  (let ((kv (mapcar #'(lambda (i) (nth i atom)) keys)))
	    (if (or (null keys) (equal kv values))
		(push (mapcar #'(lambda (i) (nth i atom)) posl) res)))))
    res))

(defun find-sequence (predicate ppos npos first-obj state)
  (let ((seq (list first-obj))
	(cur first-obj))
    (loop
     (let ((next (find-predicate-arguments
		  predicate (list npos) (list ppos) (list cur) state)))
       (if (> (length next) 1)
	   (error "no unique next for ~a in sequence defined by ~a"
		  cur predicate))
       (if (null next) (return seq))
       (setq seq (append seq (first next)))
       (setq cur (first (first next)))
       ))))

(defun find-sequence-2 (predicate state)
  (let* ((p1 (find-predicate-arguments predicate '(1) nil nil state))
	 (p2 (find-predicate-arguments predicate '(2) nil nil state))
	 (sfirst (set-difference p1 p2 :test #'equal)))
    (cond ((> (length sfirst) 1)
	   (error "no unique first element in sequence defined by ~a"
		  predicate))
	  ((= (length sfirst) 1)
	   (let ((seq (first sfirst))
		 (cur (first (first sfirst))))
	     (loop
	      (let ((next (find-predicate-arguments
			   predicate '(2) '(1) (list cur) state)))
		(if (> (length next) 1)
		    (error "no unique next for ~a in sequence defined by ~a"
			   cur predicate))
		(if (null next) (return seq))
		(setq seq (append seq (first next)))
		(setq cur (first (first next)))))))
	  (t nil))
    ))

(defun find-cycle (predicate first-obj state)
  (let ((cyc (list first-obj))
	(cur first-obj))
    (loop
     (let ((next-obj (find-predicate-arguments
		      predicate '(2) '(1) (list cur) state)))
       (if (not (= (length next-obj) 1))
	   (error "no unique next for ~a in cycle defined by ~a (~s)"
		  cur predicate next-obj))
       (if (eq (first (first next-obj)) first-obj)
	   (return cyc))
       (setq cyc (append cyc (first next-obj)))
       (setq cur (first (first next-obj)))
       ))))


;; Domain-specific Visualisations
;;;

;; sliding-tile puzzle

(defvar sliding-tile-puzzle-action-abbrev
  '((move-up . "U") (move-down . "D") (move-left . "L") (move-right . "R")))

(defun visualise-sliding-tile-puzzle (plan ss)
  (setq plan (reverse plan))
  (setq ss (reverse ss))
  (let ((first-state (first ss)))
    (let ((numbers (find-sequence-2 'inc first-state))
	  (tiles (find-predicate-arguments 'at '(1) nil nil first-state)))
      (with-output-to-string
	(result)
	(do* ((rem-ss ss (rest rem-ss))
	      (state (first rem-ss) (first rem-ss))
	      (rem-plan plan (rest rem-plan))
	      (next-action (if rem-plan (first (first rem-plan)) nil)
			   (if rem-plan (first (first rem-plan)) nil)))
	    ((endp rem-ss) nil)
	  (format result "~&\\begin{tabular}{")
	  (dolist (num numbers) (format result "|c"))
	  (format result "|}\\hline~%")
	  (dotimes (i (length numbers))
	    (dotimes (j (length numbers))
	      (let ((tile (find-predicate-arguments
			   'at '(1) '(2 3) (list (nth j numbers)
						 (nth i numbers))
			   state)))
		(if tile
		    (format result "~a"
			    (subseq (symbol-name (first (first tile))) 1))))
	      (if (< (+ j 1) (length numbers))
		  (format result " &")))
	    (format result "\\\\ \\hline~%"))
	  (format result "\\end{tabular}~%")
	  (cond (next-action
		 (format result "~~$[$")
		 (let ((aletter (assoc (first next-action)
				       sliding-tile-puzzle-action-abbrev)))
		   (format result "~a" (if aletter (cdr aletter) "?")))
		 (format result "$\\rangle$~~~%")))
	  )))))

;; GED

(defun fix-element-name (el)
  (let ((name (symbol-name el)))
    (cond ((and (> (length name) 3)
		(string= (subseq name 0 3) "SUB"))
	   (concatenate 'string "$S_{" (subseq name 3) "}$"))
	  (t name))))

(defun split-ged-plan (as ss)
  (if (not (= (+ (length as) 1) (length ss)))
      (error "visualise-ged: action and state sequences don't match"))
  (let ((op nil) (ops nil) (iss (list (first ss))))
    (do ((rem-as as (rest rem-as))
	 (rem-ss (rest ss) (rest rem-ss)))
	((endp rem-as) nil)
      (cond
       ;; handling ged1 (relational single-step) formulation:
       ((eq (car (first rem-as)) 'invert)
	(setq ops (append ops (list (list (third (first rem-as))
					  (fourth (first rem-as))))))
	(setq iss (append iss (list (first rem-ss)))))
       ((eq (car (first rem-as)) 'invert-single-gene)
	(setq ops (append ops (list (list (second (first rem-as))))))
	(setq iss (append iss (list (first rem-ss)))))
       ((eq (car (first rem-as)) 'transpose)
	(setq ops (append ops (list (list (third (first rem-as))
					  (fourth (first rem-as))))))
	(setq iss (append iss (list (first rem-ss)))))
       ((eq (car (first rem-as)) 'transvert)
	(setq ops (append ops (list (list (third (first rem-as))
					  (fourth (first rem-as))))))
	(setq iss (append iss (list (first rem-ss)))))
       ;; handling ged3/ged2 formulation:
       ((eq (car (first rem-as)) 'invert-single-gene-A)
	(setq ops (append ops (list (list (second (first rem-as))))))
	(setq iss (append iss (list (first rem-ss)))))
       ((eq (car (first rem-as)) 'invert-single-gene-B)
	(setq ops (append ops (list (list (second (first rem-as))))))
	(setq iss (append iss (list (first rem-ss)))))
       ((eq (car (first rem-as)) 'begin-cut)
	(setq op (list (third (first rem-as)))))
       ((eq (car (first rem-as)) 'continue-cut)
	(setq op (append op (list (third (first rem-as))))))
       ((eq (car (first rem-as)) 'reset-1)
	(setq ops (append ops (list op)))
	(setq iss (append iss (list (first rem-ss)))))
       ((endp (rest rem-as))
	(setq ops (append ops (list op)))
	(setq iss (append iss (list (first rem-ss)))))
       ))
    (mapcar #'list (cons nil ops) iss (append ops '(nil)))
    ))

(defun visualise-ged (plan ss)
  (let ((vss (split-ged-plan (plan-to-action-sequence plan) ss))
	(first-obj (first (first (find-predicate-arguments
				  'cw '(1) nil nil (first ss))))))
    (with-output-to-string
      (result)
      (dolist (mspair vss)
	(format result "~&\\begin{tikzpicture}~%")
	(let* ((cyc (find-cycle 'cw first-obj (second mspair)))
	       (diam (/ (* (length cyc) 0.3) 3.14))
	       (astep (/ 360.0 (length cyc)))
	       (angle 0))
	  (dolist (el cyc)
	    (if (member el (first mspair))
		(format result "\\fill [color=lightgray] (~f:~f) -- (~f:~f) arc (~f:~f:~f) -- (~f:~f) arc (~f:~f:~f) ;~%"
			(- angle (/ astep 2)) (- diam 0.2)
			(- angle (/ astep 2)) (+ diam 0.2)
			(- angle (/ astep 2)) (+ angle (/ astep 2)) (+ diam 0.2)
			(+ angle (/ astep 2)) (- diam 0.2)
			(+ angle (/ astep 2)) (- angle (/ astep 2)) (- diam 0.2)))
	    (if (member el (third mspair))
		(format result "\\draw [dashed] (~f:~f) -- (~f:~f) arc (~f:~f:~f) -- (~f:~f) arc (~f:~f:~f) ;~%"
			(- angle (/ astep 2)) (- diam 0.2)
			(- angle (/ astep 2)) (+ diam 0.2)
			(- angle (/ astep 2)) (+ angle (/ astep 2)) (+ diam 0.2)
			(+ angle (/ astep 2)) (- diam 0.2)
			(+ angle (/ astep 2)) (- angle (/ astep 2)) (- diam 0.2)))
	    (format result "\\node at (~f:~f) {{\\tiny " angle diam)
	    (setq angle (+ angle (/ 360.0 (length cyc))))
	    (if (member (list 'inverted el) (second mspair) :test #'equal)
		(format result "$-$"))
	    (format result "~a}} ;~%" (fix-element-name el))
	    ))
	(format result "~&\\end{tikzpicture}~%~~~%")
	)
      )))

;; blocksworld (3-ops)

(defun symbol-alpha (x y)
  (string-lessp (symbol-name x) (symbol-name y)))

(defun bw-get-towers (state)
  (mapcar #'(lambda (b) (find-sequence 'on 2 1 b state))
	  (sort (mapcar #'first (find-predicate-arguments
				 'on-table '(1) nil nil state))
		#'symbol-alpha)))

(defun visualise-bw3 (plan ss)
  (with-output-to-string
    (result)
    (dolist (state ss)
      (let ((towers (bw-get-towers state))
	    (tpos 0)
	    (vpos 0))
	(format result "~&\\begin{tikzpicture}~%")
	;; the table
	(format result "\\draw[thick] (0.2,0) -- (~d,0) -- +(0.8,0);~%"
		(length towers))
	(dolist (tower towers)
	  (setq vpos 0)
	  (dolist (blk tower)
	    (format result "\\draw[draw=black] (~d,~d*0.9) ++(1,0) +(-0.45,0) rectangle +(0.45,0.9);~%"
		    tpos vpos)
	    (format result "\\path (~d,~d*0.9) ++(1,0) +(0,0.45) node {~a};~%"
		    tpos vpos blk)
	    (setq vpos (+ vpos 1))
	    )
	  (setq tpos (+ tpos 1))
	  )
	(format result "~&\\end{tikzpicture}~%~~~%")
	))
    ))


;; sokoban (IPC6 version)

(defun segment-sokoban-plan (plan &key (breaks nil))
  (let ((slist nil)
	(poff 0)
	(seg-type nil)
	(seg-args nil)
	(seg-start nil)
	(seg-off 0)
	(x 0)
	(y 0))
    (dolist (act plan)
      (cond
       ((eq (car (car act)) 'move)
	(cond ((and (or (not (eq seg-type 'move))
			(member poff breaks))
		    (not (null seg-type)))
	       (setq slist
		     (append slist
			     (list (cons seg-off
					 (cons seg-type
					       (cons seg-start seg-args))))))
	       (setq seg-type 'move)
	       (setq seg-args nil)
	       (setq seg-start (list x y))
	       (setq seg-off poff))
	      ((null seg-type)
	       (setq seg-type 'move)
	       (setq seg-start (list x y))
	       (setq seg-off poff)))
	(cond ((eq (nth 4 (car act)) 'dir-up)
	       (setq y (+ y 1))
	       (setq seg-args (append seg-args (list (list 0 1)))))
	      ((eq (nth 4 (car act)) 'dir-down)
	       (setq y (- y 1))
	       (setq seg-args (append seg-args (list (list 0 -1)))))
	      ((eq (nth 4 (car act)) 'dir-left)
	       (setq x (- x 1))
	       (setq seg-args (append seg-args (list (list -1 0)))))
	      ((eq (nth 4 (car act)) 'dir-right)
	       (setq x (+ x 1))
	       (setq seg-args (append seg-args (list (list 1 0)))))
	      (t (error "unknown direction ~a in ~a"
			(nth 4 (car act)) (car act)))))
       ((member (nth 6 (car act)) '(dir-up dir-down dir-left dir-right))
	(cond ((and (or (not (eq seg-type (nth 6 (car act))))
			(member poff breaks))
		    (not (null seg-type)))
	       (setq slist
		     (append slist
			     (list (cons seg-off
					  (cons seg-type
						(cons seg-start seg-args))))))
	       (setq seg-type (nth 6 (car act)))
	       (setq seg-args (list 0 0))
	       (setq seg-off poff)
	       (setq seg-start (list x y)))
	      ((null seg-type)
	       (setq seg-type (nth 6 (car act)))
	       (setq seg-off poff)
	       (setq seg-start (list x y))))
	(cond ((eq (nth 6 (car act)) 'dir-up)
	       (setq y (+ y 1))
	       (setq seg-args (list (first seg-args) (+ (second seg-args) 1))))
	      ((eq (nth 6 (car act)) 'dir-down)
	       (setq y (- y 1))
	       (setq seg-args (list (first seg-args) (- (second seg-args) 1))))
	      ((eq (nth 6 (car act)) 'dir-left)
	       (setq x (- x 1))
	       (setq seg-args (list (- (first seg-args) 1) (second seg-args))))
	      ((eq (nth 6 (car act)) 'dir-right)
	       (setq x (+ x 1))
	       (setq seg-args (list (+ (first seg-args) 1) (second seg-args))))
	      ))
       (t (error "cannot identify action ~a" (car act))))
      (setq poff (+ poff 1))
      )
    (append slist
	    (list (cons seg-off (cons seg-type (cons seg-start seg-args)))))
    ))

(defun calc-bounding-box (slist)
  (let ((x 0) (y 0) (x-min 0) (y-min 0) (x-max 0) (y-max 0))
    (dolist (seg slist)
      (cond ((eq (cadr seg) 'move)
    	     (dolist (arg (cdddr seg))
    	       (setq x (+ x (first arg)))
    	       (setq y (+ y (second arg)))
    	       (setq x-min (min x x-min))
    	       (setq x-max (max x x-max))
    	       (setq y-min (min y y-min))
    	       (setq y-max (max y y-max))))
	    ((eq (cadr seg) 'dir-up)
	     (setq y (+ y (fifth seg)))
	     (setq y-max (max (+ y 1) y-max)))
	    ((eq (cadr seg) 'dir-down)
	     (setq y (+ y (fifth seg)))
	     (setq y-min (min (- y 1) y-min)))
	    ((eq (cadr seg) 'dir-right)
	     (setq x (+ x (fourth seg)))
	     (setq x-max (max (+ x 1) x-max)))
	    ((eq (cadr seg) 'dir-left)
	     (setq x (+ x (fourth seg)))
	     (setq x-min (min (- x 1) x-min)))
	    (t (error "invalid segment type: ~a" (cadr seg)))
	    ))
    (list (list x-min y-min) (list x-max y-max))
    ))

(defun draw-sokoban-segment (seg color to-stream)
  (cond ((eq (cadr seg) 'move)
	 (format to-stream "\\draw[->,thick,color=~a] (~a,~a)"
		 color (first (third seg)) (second (third seg)))
	 (dolist (arg (cdddr seg))
	   (format to-stream " -- ++(~a,~a)" (first arg) (second arg)))
	 (format to-stream ";~%"))
	((eq (cadr seg) 'dir-up)
	 (format to-stream "\\draw[->,thick,color=~a] (~a,~a) -- ++(~a,~a);~%"
		 color (first (third seg)) (second (third seg))
		 (fourth seg) (fifth seg))
	 (format to-stream "\\draw[dashed,color=~a] (~a,~a) rectangle ++(~a,~a);~%"
		 color (- (first (third seg)) 0.5)
		 (+ (second (third seg)) 0.5)
		 (+ (fourth seg) 1) (+ (fifth seg) 1))
	 )
	((eq (cadr seg) 'dir-down)
	 (format to-stream "\\draw[->,thick,color=~a] (~a,~a) -- ++(~a,~a);~%"
		 color (first (third seg)) (second (third seg))
		 (fourth seg) (fifth seg))
	 (format to-stream "\\draw[dashed,color=~a] (~a,~a) rectangle ++(~a,~a);~%"
		 color (- (first (third seg)) 0.5)
		 (- (second (third seg)) 0.5)
		 (+ (fourth seg) 1) (- (fifth seg) 1))
	 )
	((eq (cadr seg) 'dir-left)
	 (format to-stream "\\draw[->,thick,color=~a] (~a,~a) -- ++(~a,~a);~%"
		 color (first (third seg)) (second (third seg))
		 (fourth seg) (fifth seg))
	 (format to-stream "\\draw[dashed,color=~a] (~a,~a) rectangle ++(~a,~a);~%"
		 color (- (first (third seg)) 0.5)
		 (- (second (third seg)) 0.5)
		 (- (fourth seg) 1) (+ (fifth seg) 1))
	 )
	((eq (cadr seg) 'dir-right)
	 (format to-stream "\\draw[->,thick,color=~a] (~a,~a) -- ++(~a,~a);~%"
		 color (first (third seg)) (second (third seg))
		 (fourth seg) (fifth seg))
	 (format to-stream "\\draw[dashed,color=~a] (~a,~a) rectangle ++(~a,~a);~%"
		 color (+ (first (third seg)) 0.5)
		 (- (second (third seg)) 0.5)
		 (+ (fourth seg) 1) (+ (fifth seg) 1))
	 )
	(t (error "invalid segment type: ~a" (cadr seg)))
	))

;; (defun draw-sokoban-boxes (blist color to-stream)
;;   (dolist (box blist)
;;     (format to-stream "\\draw[thick,color=~a] (~a,~a) rectangle ++(~a,~a);~%"
;; 	    color (- (first box) 0.5) (- (second box) 0.5) 1 1)))

(defun draw-sokoban-boxes (blist color to-stream)
  (dolist (box blist)
    (format to-stream "\\draw[thick,color=~a] (~a,~a) rectangle ++(~a,~a);~%"
	    color (- (first box) 0.45) (- (second box) 0.45) 0.9 0.9)))

(defvar *vis-sokoban-ghost-list-length* 1)

(defun visualise-sokoban-IPC6 (plan ss &key (breaks nil) (boxlist nil))
  (let* ((slist (segment-sokoban-plan plan :breaks breaks))
	 (glist nil)
	 (blist boxlist)
	 (bbox (calc-bounding-box slist)))
    (with-output-to-string
      (result)
      (dolist (seg slist)
	(format result "~&\\begin{tikzpicture}[scale=0.5]~%")
	(format result "\\draw (~a,~a) rectangle (~a,~a);~%"
		(- (first (first bbox)) 0.5) (- (second (first bbox)) 0.5)
		(+ (first (second bbox)) 0.5) (+ (second (second bbox)) 0.5))
	(format result "\\node at (~a,~a) {~a};~%"
		(first (first bbox)) (second (second bbox)) (car seg))
	(dolist (seg glist)
	  (draw-sokoban-segment seg "gray" result))
	(draw-sokoban-segment seg "black" result)
	(cond ((eq (cadr seg) 'dir-up)
	       (let ((oldpos (list (first (third seg))
				   (+ (second (third seg)) 1)))
		     (newpos (list (first (third seg))
				   (+ (second (third seg))
				      (fifth seg) 1))))
		 (setq blist
		       (cons newpos
			     (remove oldpos blist :test #'equal)))))
	      ((eq (cadr seg) 'dir-down)
	       (let ((oldpos (list (first (third seg))
				   (- (second (third seg)) 1)))
		     (newpos (list (first (third seg))
				   (- (+ (second (third seg))
					 (fifth seg)) 1))))
		 (setq blist
		       (cons newpos
			     (remove oldpos blist :test #'equal)))))
	      ((eq (cadr seg) 'dir-left)
	       (let ((oldpos (list (- (first (third seg)) 1)
				   (second (third seg))))
		     (newpos (list (- (+ (first (third seg))
					 (fourth seg)) 1)
				   (second (third seg)))))
		 (setq blist
		       (cons newpos
			     (remove oldpos blist :test #'equal)))))
	      ((eq (cadr seg) 'dir-right)
	       (let ((oldpos (list (+ (first (third seg)) 1)
				   (second (third seg))))
		     (newpos (list (+ (first (third seg)) (fourth seg) 1)
				   (second (third seg)))))
		 (setq blist
		       (cons newpos
			     (remove oldpos blist :test #'equal)))))
	      )
	(draw-sokoban-boxes blist "black" result)
	(if (> *vis-sokoban-ghost-list-length* 0)
	    (cond ((>= (length glist) *vis-sokoban-ghost-list-length*)
		   (setq glist (append (cdr glist) (list seg))))
		  (t (setq glist (append glist (list seg))))))
	(format result "~&\\end{tikzpicture}~%~~~%")
	))))


;; openstacks (IPC6, ADL and STRIPS)

(defun visualise-openstacks (plan ss)
  (let ((waiting-orders
	 (reduce #'append
		 (find-predicate-arguments 'waiting '(1) nil nil (first ss))))
	(open-orders nil)
	(shipped-orders nil)
	(made-products nil)
	(cols nil))
    (dolist (state ss)
      (let ((new-open
	     (set-difference 
	      (reduce #'append
		      (find-predicate-arguments 'started '(1) nil nil state))
	      open-orders))
	    (new-shipped
	     (set-difference 
	      (reduce #'append
		      (find-predicate-arguments 'shipped '(1) nil nil state))
	      shipped-orders))
	    (new-made
	     (set-difference 
	      (reduce #'append
		      (find-predicate-arguments 'made '(1) nil nil state))
	      made-products)))
	(setq open-orders
	      (union (set-difference open-orders new-shipped) new-open))
	(setq made-products
	      (union made-products new-made))
	(if new-made
	    (setq cols
		  (append cols (list (cons (car new-made) open-orders)))))
	))
    ;;;(format t "~s" cols)
    (with-output-to-string
      (result)
      ;; table header
      (format result "\\begin{tabular}{l")
      (dolist (col cols)
	(format result "c"))
      (format result "}~%")
      ;; product sequence
      (format result "make:")
      (dolist (col cols)
	(format result " & ~a" (car col)))
      (format result " \\\\ \\hline~%")
      ;; #stacks
      (format result "\\#stacks:")
      (dolist (col cols)
	(format result " & ~a" (length (cdr col))))
      (format result " \\\\ \\hline~%")
      ;; order states
      (dolist (ord waiting-orders)
	(format result "~a" ord)
	(dolist (col cols)
	  (format result " & ~a"
		  (cond ((find-predicate-arguments
			  'includes nil '(1 2) (list ord (car col)) (first ss))
			 "X")
			((find ord (cdr col)) "--")
			(t ""))))
	(format result " \\\\~%"))
      (format result "\\hline~%")
      (format result "\\end{tabular}~%")
      )))


;; RushHour (my STRIPS or ADL version) 

(defun rush-hour-car-color (car-name)
  (cond ((eq car-name 'R) "red")
	((eq car-name 'B) "blue")
	((eq car-name 'G) "green")
	((eq car-name 'Y) "yellow")
	((eq car-name 'K) "black")
	((eq car-name 'O) "orange")
	((eq car-name 'N) "brown")
	((eq car-name 'C) "cyan")
	((eq car-name 'L) "olive")
	((eq car-name 'I) "pink")
	((eq car-name 'P) "purple")
	((eq car-name 'M) "magenta")
	((eq car-name 'S) "lightgray")
	(t "white")))

(defun visualise-rush-hour (plan ss)
  (let ((coords (find-sequence 'next 1 2 'p0 (first ss)))
	(h-cars (mapcar #'car (find-predicate-arguments
			       'row '(1) nil nil (first ss))))
	(v-cars (mapcar #'car (find-predicate-arguments
			       'col '(1) nil nil (first ss))))
	(current-move nil)
	(steps 1))
    (with-output-to-string
      (result)
      (do ((rss ss (cdr rss)))
	  ((endp rss) nil)
	(let ((next-move
	       (if (endp (cdr rss)) nil
		 (find-predicates
		  '(last-move-right last-move-left last-move-up last-move-down)
		  (cadr rss)))))
	  (cond
	   ((> (length next-move) 1)
	    (error "~s in state" next-move))
	   ;; if next-move is not equal to current-move, and current-move
	   ;; is not nil, draw the state:
	   ((and (not (equal (car next-move) current-move))
		 current-move)
	    (format result "~&\\begin{tikzpicture}~%")
	    ;; (format result "\\node at (~a,~a) {~a ~a ~a} ;~%"
	    ;; 	    (/ (length coords) 2) (length coords)
	    ;; 	    (second current-move)
	    ;; 	    (cdr (assoc (first current-move)
	    ;; 			'((last-move-right . right)
	    ;; 			  (last-move-left . left)
	    ;; 			  (last-move-up . up)
	    ;; 			  (last-move-down . down))))
	    ;; 	    steps)
	    ;; draw grid:
	    (format result "\\draw[very thick] (-0.5,-0.5) rectangle (~a,~a) ;~%"
		    (- (length coords) 0.5) (- (length coords) 0.5))
	    (dotimes (i (- (length coords) 1))
	      (format result "\\draw (~a,-0.5) -- (~a,~a) ;~%"
		      (+ i 0.5) (+ i 0.5) (- (length coords) 0.5))
	      (format result "\\draw (-0.5,~a) -- (~a,~a) ;~%"
		      (+ i 0.5) (- (length coords) 0.5) (+ i 0.5)))
	    (let ((crow (position
			(caar (find-predicate-arguments
			       'row '(2) '(1) (list (second current-move))
			       (first rss)))
			coords))
		  (ccol (position
			(caar (find-predicate-arguments
			       'col '(2) '(1) (list (second current-move))
			       (first rss)))
			coords))
		  (cf (position
		       (caar (find-predicate-arguments
			      'first '(2) '(1) (list (second current-move))
			      (first rss)))
		       coords))
		  (cl (position
		       (caar (find-predicate-arguments
			      'last '(2) '(1) (list (second current-move))
			      (first rss)))
		       coords)))
	      (cond ((eq (first current-move) 'last-move-right)
		     (format result "\\draw[dashed] (~a,~a) rectangle (~a,~a) ;~%"
			     (- (- cf steps) 0.45) (- crow 0.45)
			     (+ (- cl steps) 0.45) (+ crow 0.45)))
		    ((eq (first current-move) 'last-move-left)
		     (format result "\\draw[dashed] (~a,~a) rectangle (~a,~a) ;~%"
			     (- (+ cf steps) 0.45) (- crow 0.45)
			     (+ (+ cl steps) 0.45) (+ crow 0.45)))
		    ((eq (first current-move) 'last-move-up)
		     (format result "\\draw[dashed] (~a,~a) rectangle (~a,~a) ;~%"
			     (- ccol 0.45) (- (- cf steps) 0.45)
			     (+ ccol 0.45) (+ (- cl steps) 0.45)))
		    ((eq (first current-move) 'last-move-down)
		     (format result "\\draw[dashed] (~a,~a) rectangle (~a,~a) ;~%"
			     (- ccol 0.45) (- (+ cf steps) 0.45)
			     (+ ccol 0.45) (+ (+ cl steps) 0.45)))
		    ))
	    (dolist (hcar h-cars)
	      (let ((y (position
			(caar (find-predicate-arguments
			       'row '(2) '(1) (list hcar) (first rss)))
			coords))
		    (x1 (position
			 (caar (find-predicate-arguments
				'first '(2) '(1) (list hcar) (first rss)))
			 coords))
		    (x2 (position
			 (caar (find-predicate-arguments
				'last '(2) '(1) (list hcar) (first rss)))
			 coords)))
		(when (or (null y) (null x1) (null x2))
		  (error "horizontal car ~a: ~a ~a ~a" hcar y x1 x2))
		(format result "\\draw[fill=~a] (~a,~a) rectangle (~a,~a) ;~%"
			(rush-hour-car-color hcar)
			(- x1 0.45) (- y 0.45) (+ x2 0.45) (+ y 0.45))
		(format result "\\node at (~a,~a) {~a} ;~%"
			(/ (+ x1 x2) 2.0) y hcar)
		))
	    (dolist (vcar v-cars)
	      (let ((x (position
			(caar (find-predicate-arguments
			       'col '(2) '(1) (list vcar) (first rss)))
			coords))
		    (y1 (position
			 (caar (find-predicate-arguments
				'first '(2) '(1) (list vcar) (first rss)))
			 coords))
		    (y2 (position
			 (caar (find-predicate-arguments
				'last '(2) '(1) (list vcar) (first rss)))
			 coords)))
		(when (or (null x) (null y1) (null y2))
		  (error "vertical car ~a: ~a ~a ~a" vcar x y1 y2))
		(format result "\\draw[fill=~a] (~a,~a) rectangle (~a,~a) ;~%"
			(rush-hour-car-color vcar)
			(- x 0.45) (- y1 0.45) (+ x 0.45) (+ y2 0.45))
		(format result "\\node at (~a,~a) {~a} ;~%"
			x (/ (+ y1 y2) 2.0) vcar)
		))
	    (format result "\\end{tikzpicture}~%")
	    ;; update last-move:
	    (setq current-move (car next-move))
	    (setq steps 1)
	    )
	   ;; if current-move is nil, update it
	   ((null current-move)
	    (setq current-move (car next-move))
	    (setq steps 1))
	   ;; else, current-move is non-nil and equal to next-move:
	   (t (setq steps (+ steps 1)))
	   )))
      )))


;; HTML table (any domain)

(defun print-state-html (stream state pstate &key (first-state nil))
  (let ((cstate (if first-state (sort (copy-seq state) #'atom-lex)
		  (delete-duplicates
		   (merge 'list
			  (sort (copy-seq state) #'atom-lex)
			  (sort (copy-seq pstate) #'atom-lex)
			  #'atom-lex)
		   :test #'equal)))
	(first-atom t))
    (dolist (atom cstate)
      (cond (first-atom (format stream "      "))
	    (t (format stream ",~%      ")))
      (setq first-atom nil)
      (cond ((and (not first-state) (not (find atom state :test #'equal)))
	     (format stream "<strike><tt>~a</tt></strike>" atom))
	    ((and (not first-state) (not (find atom pstate :test #'equal)))
	     (format stream "<b><tt>~a</tt></b>" atom))
	    (t (format stream "<tt>~a</tt>" atom)))
      )
    (format stream "~%")
    ))

(defun atom-lex (atom1 atom2)
  (cond ((null atom1)
	 (cond ((null atom2) nil)
	       (t t)))
	((null atom2) nil)
	((symbolp (car atom1))
	 (cond ((eq (car atom1) (car atom2))
		(atom-lex (cdr atom1) (cdr atom2)))
	       ((symbolp (car atom2))
		(symbol-alpha (car atom1) (car atom2)))
	       (t t)))
	((numberp (car atom1))
	 (cond ((symbolp (car atom2)) nil)
	       ((numberp (car atom2)) (< (car atom1) (car atom2)))
	       (t t)))
	((listp (car atom1))
	 (cond ((symbolp (car atom2)) nil)
	       ((numberp (car atom2)) nil)
	       ((listp (car atom2))
		(cond ((atom-lex (car atom1) (car atom2)) t)
		      ((atom-lex (car atom2) (car atom1)) nil)
		      (t (atom-lex (cdr atom1) (cdr atom2)))))
	       (t (error "atom ~s is neither symbol, number or list!" atom2))))
	(t (error "atom ~s is neither symbol, number or list!" atom1))))

(defun visualise-html-table (plan ss)
  (with-output-to-string
    (result)
    ;; table header
    (format result "~&<table border=\"1\">~%")
    (format result "  <tr>~%  <td align=\"center\"><i>Action</i></td>~%")
    (format result "    <td align=\"center\"><i>State</i></td>~%  </tr>~%")
    ;; initial state
    (format result "  <tr>~%    <td>Initial state</td>~%    <td>~%")
    (print-state-html result (first ss) nil :first-state t)
    (format result "    </td>~%  <tr>~%")
    ;; main loop
    (do ((rem-plan plan (cdr rem-plan))
	 (rem-ss ss (cdr rem-ss)))
	((endp rem-plan) t)
      (format result "  <tr>~%    <td><tt>~a</tt></td>~%    <td>~%"
	      (car rem-plan))
      (when (cdr rem-ss)
	(print-state-html result (cadr rem-ss) (car rem-ss)))
      (format result "    </td>~%  <tr>~%"))
    ;; end table
    (format result "~&</table>~%")
    ))

;; custom table generator

(defun print-custom-table-row (stream cols state)
  (dolist (col cols)
    (format stream "    <td>~%")
    ;; (first ss) is the state
    (let ((exp (second col)))
      (cond
       ((eq (car exp) 'find-predicate-arguments)
	(let ((res (find-predicate-arguments
		    (second exp) (third exp) (fourth exp) (fifth exp)
		    (first ss))))
	  (format stream "~a" res)))
       (t
	(let ((res (eval-term exp nil (first ss))))
	  (format stream "~a" (car res))))
       ))
    (format stream "    </td>~%")
    ))

(defun visualise-custom-table (cols plan ss)
  (with-output-to-string
    (result)
    ;; table header
    (format result "~&<table border=\"1\">~%")
    (format result "  <tr>~%  <td align=\"center\"><i>Action</i></td>~%")
    (dolist (col cols)
      (format result "    <td align=\"center\"><i>~a</i></td>~%  </tr>~%" (first col))
      )
    ;; initial state
    (format result "  <tr>~%    <td>Initial state</td>~%")
    (print-custom-table-row result cols (first ss))
    (format result "  <tr>~%")
    ;; main loop
    (do ((rem-plan plan (cdr rem-plan))
	 (rem-ss (cdr ss) (cdr rem-ss)))
	((endp rem-plan) t)
      (format result "  <tr>~%    <td><tt>~a</tt></td>~%"
	      (car rem-plan))
      (print-state-html result cols (car rem-ss))
      (format result "  <tr>~%"))
    ;; end table
    (format result "~&</table>~%")
    ))

;; numeric hbw, table form

(defun visualise-numeric-hbw (plan ss)
  (let ((cyls (objects-of-type 'cylinder *types* *objects*)))
    (cond
     ((= (length cyls) 3)
      (visualise-custom-table
       '(((in c0) (find-predicate-arguments in (1) (2) (c0)))
	 ((h c0) (+ (* (/ 1 (total_area)) (volume))
		    (+ (* (/ 1 (total_area)) (/ (weight_on c1) (density)))
		       (- (* (/ 1 (total_area)) (/ (weight_on c2) (density)))
			  (* (/ (- (total_area) (area c0))
				(* (total_area) (area c0)))
			     (/ (weight_on c0) (density)))))))
	 ((in c1) (find-predicate-arguments in (1) (2) (c1)))
	 ((h c1) (+ (* (/ 1 (total_area)) (volume))
		    (+ (* (/ 1 (total_area)) (/ (weight_on c0) (density)))
		       (- (* (/ 1 (total_area)) (/ (weight_on c2) (density)))
			  (* (/ (- (total_area) (area c1))
				(* (total_area) (area c1)))
			     (/ (weight_on c1) (density)))))))
	 ((in c2) (find-predicate-arguments in (1) (2) (c2)))
	 ((h c2) (+ (* (/ 1 (total_area)) (volume))
		    (+ (* (/ 1 (total_area)) (/ (weight_on c0) (density)))
		       (- (* (/ 1 (total_area)) (/ (weight_on c1) (density)))
			  (* (/ (- (total_area) (area c2))
				(* (total_area) (area c2)))
			     (/ (weight_on c2) (density)))))))
	 )
       plan ss))
     (t (error "visualisation not defined for cylinders ~s" cyls))
     )))
