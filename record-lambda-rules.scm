;;; define-record-lambda --- define-syntax

(define err-str "define-record-lambda: invisible or immutable field")
(define-syntax unquote-get
  (syntax-rules ()
    ((unquote-get symbol ((n0 v0) n1 ...))
     (if (eq? symbol 'n0)
	 v0
	 (unquote-get symbol (n1 ...))))
    ((unquote-get symbol (n0 n1 ...))
     (if (eq? symbol 'n0)
	 n0
	 (unquote-get symbol (n1 ...))))
    ((unquote-get symbol ())
     (error err-str symbol))))

(define-syntax unquote-set!
  (syntax-rules ()
    ((unquote-set! symbol new-val (n0 n1 ...))
     (if (eq? symbol 'n0)
	 (set! n0 new-val)
	 (unquote-set! symbol new-val (n1 ...))))
    ((unquote-set! symbol new-val ())
     (error err-str symbol))))

(define-syntax seq-lambda
  (syntax-rules ()
    ((seq-lambda () (r ...) () body)
     (lambda (r ...) body))
    ((seq-lambda () (r ...) (o oo ...) body)
     (lambda (r ... . z)
       (seq-lambda (z) () (o oo ...) body)))
    ((seq-lambda (z) () ((o v) . e) body)
     (let ((o (if (null? z) v (car z)))
	   (z (if (null? z) z (cdr z))))
       (seq-lambda (z) () e body)))
    ((seq-lambda (z) () () body)
     (if (null? z)
	 body
	 (error "define-record-lambda: too many arguments" z)))))

(define (field-key z k d)
  (let ((x (car z)) (y (cdr z)))
    (if (null? y)
	(cons d z)
	(if (eq? k x)
	    y
	    (let lp ((head (list x (car y))) (tail (cdr y)))
	      (if (null? tail)
		  (cons d z)
		  (let ((x (car tail)) (y (cdr tail)))
		    (if (null? y)
			(cons d z)
			(if (eq? k x)
			    (cons (car y) (append head (cdr y)))
			    (lp (cons x (cons (car y) head)) (cdr y)))))))))))
(define-syntax field-key!
  (syntax-rules ()
    ((field-key! z k d)
     (let ((x (car z)) (y (cdr z)))
       (if (null? y)
	   d
	   (if (eq? k x)
	       (begin (set! z (cdr y)) (car y))
	       (let lp ((head (list x (car y))) (tail (cdr y)))
		 (if (null? tail)
		     d
		     (let ((x (car tail)) (y (cdr tail)))
		       (if (null? y)
			   d
			   (if (eq? k x)
			       (begin
				 (set! z (append head (cdr y)))
				 (car y))
			       (lp (cons x (cons (car y) head)) (cdr y)))))))))))))
(define-syntax key-lambda
  (syntax-rules ()
    ((key-lambda () (r ...) () body)
     (lambda (r ...) body))
    ((key-lambda () (r ...) (o oo ...) body)
     (lambda (r ... . z)
       (key-lambda (z) () (o oo ...) body)))
    ((key-lambda (z) () ((o t v) . e) body)
     (let ((t (if (null? z) v (field-key! z 'o v))))
     ;; (let* ((z (if (null? z) (cons v z) (field-key z 'o v)))
     ;;		    (t (car z))
     ;;		    (z (cdr z)))
       (key-lambda (z) () e body)))
    ((key-lambda (z) () () body)
     (if (null? z)
	 body
	 (error "define-record-lambda: too many arguments" z)))))

(define (check-duplicate ls err-str)
  (cond ((null? ls) #f)
	((memq (car ls) (cdr ls)) (error err-str (car ls)))
	(else (check-duplicate (cdr ls) err-str))))

(define (number-alist ls)
  (let loop ((ls ls) (n 0))
    (if (null? ls)
	'()
	(cons (cons (car ls) n) (loop (cdr ls) (+ 1 n))))))

(define-syntax define-lambda
  (syntax-rules ()
    ((define-lambda name unique-name make-record make-record-by-name make-record/s make-record-by-name/s pred-record (name-fm ...) (name-fi ...) (fm ...) ((fi fd) ...) ((c ct cv) ...) ((r rt) ...) ((o ot ov) ...) ((a at av) ...) (h ...) (i ...) (v ...))
     (begin
       ;; A vector or list can be used instead of unquote-get & unquote-set!.
       ;; cf. (eval-variant expression implementation-specific-namespace)

       (define name-alist-a (number-alist '(name-fm ... name-fi ...)))
       (define name-alist-m (number-alist '(name-fm ...)))
       (define num-a (length name-alist-a))
       (define num-m (length name-alist-m))
       (define name-fi (cdr (assq 'name-fi name-alist-a))) ...
       (define name-fm (cdr (assq 'name-fm name-alist-m))) ...

       ;; You can choose a suitable constructor.
       ;; 1. number
       (define maker
	 (let* ((ct cv) ...)
	   (cons (seq-lambda () (rt ...) ((ot ov) ...)
		   (let* ((at av) ...)
		     (define unique-name
		       (if (and (null? '((c ct cv) ...)) (null? '((o ot ov) ...)) (null? '((a at av) ...)) (null? '(v ...)))
			   (let ((v-all (vector fm ... fd ...)))
			     (cond
			      ((null? '(fi ...))
			       ;; (case-lambda
			       ;;	((arg) (vector-ref v-all arg))
			       ;;	((arg val) (vector-set! v-all arg val))))
			       (lambda (arg . args)
				 (if (null? args)
				     (vector-ref v-all arg)
				     (vector-set! v-all arg (car args)))))
			      ((null? '(fm ...))
			       (lambda (arg) (vector-ref v-all arg)))
			      (else
			       ;; (case-lambda
			       ;;	((arg) (vector-ref v-all arg))
			       ;;	((arg val) (if (< arg num-m)
			       ;;		       (vector-set! v-all arg val)
			       ;;		       (error err-str arg)))))))
			       (lambda (arg . args)
				 (if (null? args)
				     (vector-ref v-all arg)
				     (if (< arg num-m)
					 (vector-set! v-all arg (car args))
					 (error err-str arg)))))))
			   (let ((v-all (vector (lambda (x) (if (eq? 'unique-name x) fm (set! fm x))) ... (lambda (x) (if (eq? 'unique-name x) fd (error err-str))) ...)))
			     ;; (case-lambda
			     ;;	 ((arg) ((vector-ref v-all arg) 'unique-name))
			     ;;	 ((arg val) ((vector-ref v-all arg) val))))))
			     (lambda (arg . args)
			       (if (null? args)
				   ((vector-ref v-all arg) 'unique-name)
				   ((vector-ref v-all arg) (car args)))))))
		     unique-name))
		 (key-lambda () (rt ...) ((o ot ov) ...)
		   (let* ((at av) ...)
		     (define unique-name
		       (if (and (null? '((c ct cv) ...)) (null? '((o ot ov) ...)) (null? '((a at av) ...)) (null? '(v ...)))
			   (let ((v-all (vector fm ... fd ...)))
			     (cond
			      ((null? '(fi ...))
			       ;; (case-lambda
			       ;;	((arg) (vector-ref v-all arg))
			       ;;	((arg val) (vector-set! v-all arg val))))
			       (lambda (arg . args)
				 (if (null? args)
				     (vector-ref v-all arg)
				     (vector-set! v-all arg (car args)))))
			      ((null? '(fm ...))
			       (lambda (arg) (vector-ref v-all arg)))
			      (else
			       ;; (case-lambda
			       ;;	((arg) (vector-ref v-all arg))
			       ;;	((arg val) (if (< arg num-m)
			       ;;		       (vector-set! v-all arg val)
			       ;;		       (error err-str arg)))))))
			       (lambda (arg . args)
				 (if (null? args)
				     (vector-ref v-all arg)
				     (if (< arg num-m)
					 (vector-set! v-all arg (car args))
					 (error err-str arg)))))))
			   (let ((v-all (vector (lambda (x) (if (eq? 'unique-name x) fm (set! fm x))) ... (lambda (x) (if (eq? 'unique-name x) fd (error err-str))) ...)))
			     ;; (case-lambda
			     ;;	 ((arg) ((vector-ref v-all arg) 'unique-name))
			     ;;	 ((arg val) ((vector-ref v-all arg) val))))))
			     (lambda (arg . args)
			       (if (null? args)
				   ((vector-ref v-all arg) 'unique-name)
				   ((vector-ref v-all arg) (car args)))))))
		     unique-name)))))
       (define make-record (car maker))
       (define make-record-by-name (cdr maker))

       ;; 2. symbol
       (define maker/s
	 (let* ((ct cv) ...)
	   (cons (seq-lambda () (rt ...) ((ot ov) ...)
		   (let* ((at av) ...)
		     (define unique-name
		       ;; (case-lambda
		       ;;	((arg) (unquote-get arg ((fm fm) ... (fi fd) ...)))
		       ;;	((arg val) (unquote-set! arg val (fm ...)))))
		       (lambda (arg . args)
			 (if (null? args)
			     (unquote-get arg ((fm fm) ... (fi fd) ...))
			     (unquote-set! arg (car args) (fm ...)))))
		     unique-name))
		 (key-lambda () (rt ...) ((o ot ov) ...)
		   (let* ((at av) ...)
		     (define unique-name
		       ;; (case-lambda
		       ;;	((arg) (unquote-get arg ((fm fm) ... (fi fd) ...)))
		       ;;	((arg val) (unquote-set! arg val (fm ...)))))
		       (lambda (arg . args)
			 (if (null? args)
			     (unquote-get arg ((fm fm) ... (fi fd) ...))
			     (unquote-set! arg (car args) (fm ...)))))
		     unique-name)))))
       (define make-record/s (car maker/s))
       (define make-record-by-name/s (cdr maker/s))

       ;; The predicate procedure is implementation dependant.
       ;; A procedure such as `object-name' is necessary for this to work.
       ;; In the following explicit-renaming or syntax-case macro, the `gensym'
       ;; procedure is necessary.

       (define (pred-record record)	;racket
	 (eq? 'unique-name (object-name record)))

       (define name
	 (let ((constructor `(,maker ,maker/s))
	       (predicate pred-record)
	       (field `((total (read-write-field (fm ...))
			       (read-only-field (fi ...))
			       (invisible-field ,(map car '(h ...))))
			(types (common-field (c ...))
			       (required-field (r ...))
			       (optional-field (o ...))
			       (automatic-field (a ... ,@(map car '(v ...))))
			       (immutable-field ,(map car '(i ...)))
			       (invisible-field ,(map car '(h ...)))
			       (virtual-field ,(map car '(v ...))))))
	       (index name-alist-a))
	   (check-duplicate '(fm ... fi ... ,@(map car '(h ...)))
			    "define-record-lambda: duplicated field")
	   (lambda (sym)
	     (unquote-get sym (constructor predicate field index)))))))))

;; conventional-lisp macro
;; (define-macro (define-identifier name fm fi c r o a h i v)
;;   (let ((nm-str (symbol->string name)))
;;     (let ((unique-name (gensym))
;;	  (make-record (string->symbol (string-append "make-" nm-str)))
;;	  (make-record-by-name (string->symbol (string-append "make-" nm-str "-by-name")))
;;	  (make-record/s (string->symbol (string-append "make-" nm-str "/s")))
;;	  (make-record-by-name/s (string->symbol (string-append "make-" nm-str "-by-name/s")))
;;	  (pred-record (string->symbol (string-append nm-str "?")))
;;	  (name-fm (map (lambda (x) (string->symbol (string-append nm-str "-" (symbol->string x)))) fm))
;;	  (name-fi (map (lambda (x) (string->symbol (string-append nm-str "-" (symbol->string x)))) (map car fi))))
;;	 `(define-lambda ,name ,unique-name ,make-record ,make-record-by-name ,make-record/s ,make-record-by-name/s ,pred-record ,name-fm ,name-fi ,fm ,fi ,c ,r ,o ,a ,h ,i ,v))))

;; explicit renaming macro
;; (define-syntax define-identifier
;;   (er-macro-transformer
;;    (lambda (form rename compare)
;;	(let* ((name (cadr form))
;;	    (fields (cddr form))
;;	    (nm-str (symbol->string name)))
;;	  (let ((unique-name (gensym))
;;	     (make-record (string->symbol (string-append "make-" nm-str)))
;;	     (make-record-by-name (string->symbol (string-append "make-" nm-str "-by-name")))
;;	     (make-record/s (string->symbol (string-append "make-" nm-str "/s")))
;;	     (make-record-by-name/s (string->symbol (string-append "make-" nm-str "-by-name/s")))
;;	     (pred-record (string->symbol (string-append nm-str "?")))
;;	     (name-fm (map (lambda (x) (string->symbol (string-append nm-str "-" (symbol->string x)))) (car fields)))
;;	     (name-fi (map (lambda (x) (string->symbol (string-append nm-str "-" (symbol->string x)))) (map car (cadr fields))))
;;	     (%define-lambda (rename 'define-lambda)))
;;	 `(,%define-lambda ,name ,unique-name ,make-record ,make-record-by-name ,make-record/s ,make-record-by-name/s ,pred-record ,name-fm ,name-fi ,@fields))))))

;; syntax-case macro
(define-syntax define-identifier
  (lambda (x)
    (syntax-case x ()
      ((_ nm fm fi c r o a h i v)
       (let* ((name (syntax->datum #'nm))
	      (fmm (syntax->datum #'fm))
	      (fii (syntax->datum #'fi))
	      (nm-str (symbol->string name)))
	 (let ((unique-nm (gensym))
	       (make-obj (string->symbol (string-append "make-" nm-str)))
	       (make-obj-by-name (string->symbol (string-append "make-" nm-str "-by-name")))
	       (make-obj/s (string->symbol (string-append "make-" nm-str "/s")))
	       (make-obj-by-name/s (string->symbol (string-append "make-" nm-str "-by-name/s")))
	       (pred-obj (string->symbol (string-append nm-str "?")))
	       (n-fm (map (lambda (x) (string->symbol (string-append nm-str "-" (symbol->string x)))) fmm))
	       (n-fi (map (lambda (x) (string->symbol (string-append nm-str "-" (symbol->string x)))) (map car fii))))
	   (with-syntax
	    ((unique-name (datum->syntax #'nm unique-nm))
	     (make-record (datum->syntax #'nm make-obj))
	     (make-record-by-name (datum->syntax #'nm make-obj-by-name))
	     (make-record/s (datum->syntax #'nm make-obj/s))
	     (make-record-by-name/s (datum->syntax #'nm make-obj-by-name/s))
	     (pred-record (datum->syntax #'nm pred-obj))
	     (name-fm (datum->syntax #'nm n-fm))
	     (name-fi (datum->syntax #'nm n-fi)))
	    #'(define-lambda nm unique-name make-record make-record-by-name make-record/s make-record-by-name/s pred-record name-fm name-fi fm fi c r o a h i v))))))))

(define-syntax define-field
  (syntax-rules (quote quasiquote unquote unquote-splicing)
    ((define-field nm ((`,@n d) . e) fm fi (c ...) () () () (h ...) i ())
     (define-field nm e fm fi (c ... (n n d)) () () () (h ... (n d)) i ()))
    ((define-field nm ((',@n d) . e) fm (fi ...) (c ...) () () () h (i ...) ())
     (define-field nm e fm (fi ... (n t)) (c ... (n t d)) () () () h (i ... (n d)) ()))
    ((define-field nm ((`,n d) . e) fm fi c r o (a ...) (h ...) i v)
     (define-field nm e fm fi c r o (a ... (n n d)) (h ... (n d)) i v))
    ((define-field nm ((',n d) . e) fm (fi ...) c r o (a ...) h (i ...) v)
     (define-field nm e fm (fi ... (n t)) c r o (a ... (n t d)) h (i ... (n d)) v))
    ((define-field nm ((,,n d) . e) fm (fi ...) c r o a h i (v ...))
     (define-field nm e fm (fi ... (n d)) c r o a h i (v ... (n d))))
    ((define-field nm (((,@n) d) . e) (fm ...) fi (c ...) () () () h i ())
     (define-field nm e (fm ... n) fi (c ... (n n d)) () () () h i ()))
    ((define-field nm (((,n) d) . e) (fm ...) fi c r o (a ...) h i v)
     (define-field nm e (fm ... n) fi c r o (a ... (n n d)) h i v))
    ((define-field nm ((,@n d) . e) fm (fi ...) (c ...) () () () h i ())
     (define-field nm e fm (fi ... (n n)) (c ... (n n d)) () () () h i ()))
    ((define-field nm ((,n d) . e) fm (fi ...) c r o (a ...) h i v)
     (define-field nm e fm (fi ... (n n)) c r o (a ... (n n d)) h i v))
    ((define-field nm ((`n d) . e) fm fi c r (o ...) () (h ...) i ())
     (define-field nm e fm fi c r (o ... (n n d)) () (h ... (n d)) i ()))
    ((define-field nm (('n d) . e) fm (fi ...) c r (o ...) () h (i ...) ())
     (define-field nm e fm (fi ... (n t)) c r (o ... (n t d)) () h (i ... (n d)) ()))
    ((define-field nm (((n) d) . e) (fm ...) fi c r (o ...) () h i ())
     (define-field nm e (fm ... n) fi c r (o ... (n n d)) () h i ()))

    ((define-field nm (`n . e) fm fi c (r ...) () () (h ...) i ())
     (define-field nm e fm fi c (r ... (n n)) () () (h ... (n n)) i ()))
    ((define-field nm ('n . e) fm (fi ...) c (r ...) () () h (i ...) ())
     (define-field nm e fm (fi ... (n t)) c (r ... (n t)) () () h (i ... (n n)) ()))

    ((define-field nm ((n d) . e) fm (fi ...) c r (o ...) () h i ())
     (define-field nm e fm (fi ... (n n)) c r (o ... (n n d)) () h i ()))
    ((define-field nm ((n) . e) (fm ...) fi c (r ...) () () h i ())
     (define-field nm e (fm ... n) fi c (r ... (n n)) () () h i ()))
    ((define-field nm (n . e) fm (fi ...) c (r ...) () () h i ())
     (define-field nm e fm (fi ... (n n)) c (r ... (n n)) () () h i ()))
    ((define-field nm () fm fi c r o a h i v)
     (define-identifier nm fm fi c r o a h i v))))

(define-syntax define-record-lambda
  (syntax-rules ()
    ((define-record-lambda name . f)
     (define-field name f () () () () () () () () ()))))

;;; eof
