;;;; sigla-query.lisp
;;;; An implementation of SigLA's typed λ-term query language in Common Lisp,
;;;; running against the full Linear A corpus (corpus.sexp, 1722 documents).
;;;;
;;;; SigLA (Salgarella & Castellan) represents searches as typed λ-terms
;;;; built from primitives over Document / Word / Sign objects, e.g.
;;;;   words : Document → [Word]
;;;; and criteria are terms of type Document → Bool. Their URL syntax
;;;;   document: C1 && C2 // [doc-site:groupKey; doc-name:sort]
;;;; maps here to:
;;;;   (run-query '(λ (d) (and C1 C2)) :group-by 'site)
;;;;
;;;; This file provides:
;;;;   - terms as s-expressions: variables, literals, (λ (x ..) body), application
;;;;   - type inference with unification (polymorphic primitives like exists)
;;;;   - an evaluator (terms compile to curried CL closures)
;;;;   - SigLA word-pattern matching: "ku-ro", "ku-", "-ro", "ku--ro", "ku-?-ro"
;;;;
;;;; Run:  sbcl --script sigla-query.lisp        (demo at bottom)
;;;; REPL: sbcl --load sigla-query.lisp, then e.g.
;;;;   (typecheck '(λ (d) (exists (λ (w) (matches "ku--ro" w)) (words d))))
;;;;   (run-query '(λ (d) (= (site d) "Zakros")))

(defpackage :sigla-query
  (:use :cl)
  (:export #:typecheck #:run-query #:search-words #:load-corpus
           #:suggest #:fill-holes #:parse-sigla-url))
(in-package :sigla-query)

;;; =====================================================================
;;; Corpus
;;; =====================================================================

(defparameter *corpus* nil)

(defun load-corpus (&optional (path "corpus.sexp"))
  (with-open-file (in path :external-format :utf-8)
    (let ((*read-eval* nil))
      (setf *corpus* (read in))))
  (length *corpus*))

(defun signs-of (word)
  "Split a transliterated word into its signs: \"KU-PA3-NU\" -> (KU PA3 NU)."
  (loop with start = 0
        for pos = (position #\- word :start start)
        collect (subseq word start pos)
        while pos do (setf start (1+ pos))))

(defun word-token-p (tok)
  (and (every (lambda (c) (< (char-code c) 128)) tok)
       (find #\- tok)))

(defun doc-words (d)
  (remove-if-not #'word-token-p (getf d :words)))

;;; =====================================================================
;;; SigLA word-pattern matching
;;; =====================================================================
;;; From the SigLA help page:
;;;   ku-ro   exact word        ku-     prefix        -ro     suffix
;;;   ku--ro  ku .. ro with any subsequence between
;;;   ?       exactly one arbitrary sign, e.g. ku-?-ro

(defun parse-pattern (pat)
  (loop with start = 0 with items = '()
        for pos = (position #\- pat :start start)
        for chunk = (subseq pat start pos)
        do (push (cond ((string= chunk "")  :gap)
                       ((string= chunk "?") :any)
                       (t chunk))
                 items)
        while pos do (setf start (1+ pos))
        finally (return (nreverse items))))

(defun match-signs (pat signs)
  (cond ((null pat) (null signs))
        ((eq (first pat) :gap)                       ; zero or more signs
         (or (match-signs (rest pat) signs)
             (and signs (match-signs pat (rest signs)))))
        ((null signs) nil)
        ((eq (first pat) :any)                       ; exactly one sign
         (match-signs (rest pat) (rest signs)))
        ((string-equal (first pat) (first signs))
         (match-signs (rest pat) (rest signs)))))

(defun match-word (pattern word)
  (match-signs (parse-pattern pattern) (signs-of word)))

;;; =====================================================================
;;; Types
;;; =====================================================================
;;; Ground types: :doc :word :str :num :bool
;;; Compound:     (:list T)  (:fun A B)
;;; Variables:    (:tv G)    — created fresh during inference

(defun tv () (list :tv (gensym "T")))
(defun tv-p (ty) (and (consp ty) (eq (first ty) :tv)))

(defun walk (ty subst)
  "Resolve TY one level through the substitution."
  (if (tv-p ty)
      (let ((b (assoc (second ty) subst)))
        (if b (walk (cdr b) subst) ty))
      ty))

(defun resolve (ty subst)
  "Fully resolve TY through the substitution."
  (let ((ty (walk ty subst)))
    (if (consp ty)
        (cons (first ty) (mapcar (lambda (x) (resolve x subst)) (rest ty)))
        ty)))

(defun occurs-p (var ty subst)
  (let ((ty (walk ty subst)))
    (cond ((tv-p ty) (eq (second ty) var))
          ((consp ty) (some (lambda (x) (occurs-p var x subst)) (rest ty)))
          (t nil))))

(define-condition type-error* (error)
  ((msg :initarg :msg :reader msg))
  (:report (lambda (c s) (format s "Type error: ~a" (msg c)))))

(defun type->string (ty &optional (subst nil))
  (let ((ty (resolve ty subst)))
    (cond ((eq ty :doc) "Doc") ((eq ty :word) "Word") ((eq ty :str) "Str")
          ((eq ty :num) "Num") ((eq ty :bool) "Bool")
          ((tv-p ty) (string-downcase (subseq (symbol-name (second ty)) 0 2)))
          ((and (symbolp ty) (not (keywordp ty)))
           (string-downcase (symbol-name ty)))   ; scheme vars a, b
          ((eq (first ty) :list) (format nil "[~a]" (type->string (second ty))))
          ((eq (first ty) :fun)
           (let ((a (second ty)))
             (format nil "~:[~a~;(~a)~] → ~a"
                     (and (consp a) (eq (first a) :fun))
                     (type->string a) (type->string (third ty)))))
          (t (format nil "~a" ty)))))

(defun unify (a b subst)
  (let ((a (walk a subst)) (b (walk b subst)))
    (cond ((equal a b) subst)
          ((tv-p a)
           (when (occurs-p (second a) b subst)
             (error 'type-error* :msg "infinite type"))
           (acons (second a) b subst))
          ((tv-p b) (unify b a subst))
          ((and (consp a) (consp b)
                (eq (first a) (first b))
                (= (length a) (length b)))
           (loop for x in (rest a) for y in (rest b)
                 do (setf subst (unify x y subst)))
           subst)
          (t (error 'type-error*
                    :msg (format nil "cannot unify ~a with ~a"
                                 (type->string a subst)
                                 (type->string b subst)))))))

;;; =====================================================================
;;; Primitives
;;; =====================================================================
;;; Each primitive has a type scheme (VARS TYPE) and a curried implementation.

(defparameter *prims* (make-hash-table :test #'equal))

(defun prim (sym)
  "Package-independent primitive lookup, so queries can be written from
any package (e.g. a CL-USER REPL after --load)."
  (gethash (symbol-name sym) *prims*))

(defun reg (name vars type impl)
  (setf (gethash (symbol-name name) *prims*) (list vars type impl)))

(defun instantiate (vars type)
  (sublis (mapcar (lambda (v) (cons v (tv))) vars) type))

(macrolet ((c2 (fn) `(lambda (x) (lambda (y) (,fn x y)))))
  ;; Document properties
  (reg 'site    '() '(:fun :doc :str)  (lambda (d) (getf d :site)))
  (reg 'docname '() '(:fun :doc :str)  (lambda (d) (getf d :name)))
  (reg 'support '() '(:fun :doc :str)  (lambda (d) (getf d :support)))
  (reg 'words   '() '(:fun :doc (:list :word)) #'doc-words)
  ;; Word properties
  (reg 'reading '() '(:fun :word :str) #'identity)
  (reg 'wlen    '() '(:fun :word :num)
       (lambda (w) (length (signs-of w))))
  (reg 'signs   '() '(:fun :word (:list :str)) #'signs-of)
  (reg 'matches '() '(:fun :str (:fun :word :bool)) (c2 match-word))
  ;; Logic & comparison
  (reg '=  '(a) '(:fun a (:fun a :bool))
       (lambda (x) (lambda (y)
         (if (and (stringp x) (stringp y)) (string-equal x y) (equal x y)))))
  (reg '>  '() '(:fun :num (:fun :num :bool)) (c2 >))
  (reg '<  '() '(:fun :num (:fun :num :bool)) (c2 <))
  (reg '>= '() '(:fun :num (:fun :num :bool)) (c2 >=))
  (reg '<= '() '(:fun :num (:fun :num :bool)) (c2 <=))
  (reg 'and '() '(:fun :bool (:fun :bool :bool)) (c2 and))
  (reg 'or  '() '(:fun :bool (:fun :bool :bool)) (c2 or))
  (reg 'not '() '(:fun :bool :bool) #'not)
  ;; List combinators (polymorphic)
  (reg 'exists '(a) '(:fun (:fun a :bool) (:fun (:list a) :bool))
       (lambda (p) (lambda (xs) (some (lambda (x) (funcall p x)) xs))))
  (reg 'forall '(a) '(:fun (:fun a :bool) (:fun (:list a) :bool))
       (lambda (p) (lambda (xs) (every (lambda (x) (funcall p x)) xs))))
  (reg 'count  '(a) '(:fun (:fun a :bool) (:fun (:list a) :num))
       (lambda (p) (lambda (xs) (count-if (lambda (x) (funcall p x)) xs))))
  (reg 'len    '(a) '(:fun (:list a) :num) #'length))

;;; Sign-level primitives (positional / palaeographic-flavoured)
(reg 'initial '() '(:fun :word :str)
     (lambda (w) (first (signs-of w))))
(reg 'final   '() '(:fun :word :str)
     (lambda (w) (first (last (signs-of w)))))
(reg 'has-sign '() '(:fun :str (:fun :word :bool))
     (lambda (s) (lambda (w)
       (and (member s (signs-of w) :test #'string-equal) t))))
(reg 'true  '() :bool t)
(reg 'false '() :bool nil)

;;; =====================================================================
;;; Terms: inference and evaluation
;;; =====================================================================

(defun lam-p (term)
  (and (consp term) (symbolp (first term))
       (member (symbol-name (first term)) '("λ" "Λ" "LAM" "FN")
               :test #'string=)))

;;; Holes: _ (anonymous) or (? label). During inference each hole gets a
;;; fresh type variable; SUGGEST later reports what could fill it. This is
;;; SigLA's interactive query builder: at every point, offer exactly the
;;; primitives whose types fit.

(defvar *holes* '() "Entries (label type-var value-env) found during INFER.")

(defun hole-p (term)
  (or (and (symbolp term) (string= (symbol-name term) "_"))
      (and (consp term) (symbolp (first term))
           (string= (symbol-name (first term)) "?"))))

(defun hole-label (term) (if (consp term) (second term) '_))

(defun infer (term venv subst)
  "Returns (values type subst)."
  (cond
    ((stringp term)   (values :str subst))
    ((rationalp term) (values :num subst))
    ((hole-p term)
     (let ((ht (tv)))
       (push (list (hole-label term) ht venv) *holes*)
       (values ht subst)))
    ((symbolp term)
     (let ((b (assoc term venv)))
       (cond (b (values (cdr b) subst))
             ((prim term)
              (destructuring-bind (vars type impl) (prim term)
                (declare (ignore impl))
                (values (instantiate vars type) subst)))
             (t (error 'type-error* :msg (format nil "unbound name ~a" term))))))
    ((lam-p term)
     (destructuring-bind (args body) (rest term)
       (let* ((tvs (mapcar (lambda (a) (cons a (tv))) args))
              (bt  nil))
         (multiple-value-setq (bt subst)
           (infer body (append tvs venv) subst))
         (values (reduce (lambda (a acc) (list :fun (cdr a) acc))
                         tvs :from-end t :initial-value bt)
                 subst))))
    ((consp term)                       ; application, left-associated
     (multiple-value-bind (ft subst) (infer (first term) venv subst)
       (dolist (arg (rest term) (values ft subst))
         (multiple-value-bind (at s) (infer arg venv subst)
           (let ((rt (tv)))
             (setf subst (unify ft (list :fun at rt) s)
                   ft rt))))))
    (t (error 'type-error* :msg (format nil "bad term ~s" term)))))

(defun typecheck (term)
  "Infer and return the resolved type of TERM."
  (let ((*holes* '()))
    (multiple-value-bind (ty subst) (infer term '() '())
      (resolve ty subst))))

(defun evaluate (term venv)
  (cond
    ((stringp term) term)
    ((rationalp term) term)
    ((symbolp term)
     (let ((b (assoc term venv)))
       (if b (cdr b) (third (prim term)))))
    ((lam-p term)
     (destructuring-bind (args body) (rest term)
       (labels ((close-over (args venv)
                  (lambda (v)
                    (let ((venv (acons (first args) v venv)))
                      (if (rest args)
                          (close-over (rest args) venv)
                          (evaluate body venv))))))
         (close-over args venv))))
    ((consp term)
     (let ((f (evaluate (first term) venv)))
       (dolist (arg (rest term) f)
         (setf f (funcall f (evaluate arg venv))))))))

(defun compile-query (term expected-type)
  "Typecheck TERM against EXPECTED-TYPE, then return it as a CL function."
  (let ((*holes* '()))
    (multiple-value-bind (ty subst) (infer term '() '())
      (unify ty expected-type subst))  ; signals type-error* on mismatch
    (when *holes*
      (error 'type-error*
             :msg (format nil "query has unfilled holes: ~{~a~^, ~}"
                          (mapcar #'first *holes*)))))
  (evaluate term '()))

;;; =====================================================================
;;; Type-directed suggestions — SigLA's interactive query builder
;;; =====================================================================
;;; For each hole, offer: literals of its type, in-scope variables that
;;; fit, and every primitive that fits after 0..k applications (shown as
;;; a template with _ for the arguments still needed).

(defun unifies-p (a b subst)
  (handler-case (progn (unify a b subst) t)
    (type-error* () nil)))

(defun peelings (type)
  "((n-args type-after-n-applications) ...) for n = 0, 1, ..."
  (loop for ty = type then (third ty)
        for n from 0
        collect (list n ty)
        while (and (consp ty) (eq (first ty) :fun))))

(defun candidate-syntax (name n)
  (if (zerop n)
      (format nil "~(~a~)" name)
      (format nil "(~(~a~)~{ ~a~})" name (make-list n :initial-element '_))))

(defun suggest (term)
  "Report each hole in TERM with everything that could fill it."
  (let ((*holes* '()))
    (multiple-value-bind (ty subst) (infer term '() '())
      (format t "~&term : ~s~%type : ~a~%" term (type->string ty subst))
      (loop for (label htv venv) in (reverse *holes*)
            for i from 1
            for hty = (resolve htv subst)
            do (format t "~%  hole ~a : ~a — candidates:~%"
                       (if (string= (symbol-name label) "_")
                           (format nil "_~a" i) label)
                       (type->string hty))
               (when (member hty '(:str :num))
                 (format t "    a ~(~a~) literal~%" hty))
               (loop for (v . vty) in venv
                     when (unifies-p vty htv subst)
                       do (format t "    ~(~a~) : ~a  (in scope)~%"
                                  v (type->string vty subst)))
               (let ((cands '()))
                 (maphash
                  (lambda (name spec)
                    (destructuring-bind (vars type impl) spec
                      (declare (ignore impl))
                      (let ((peel (find-if
                                   (lambda (p)
                                     (unifies-p (second p) htv subst))
                                   (peelings (instantiate vars type)))))
                        (when peel
                          (push (list name (first peel) type) cands)))))
                  *prims*)
                 (loop for (name n type)
                         in (sort cands #'string< :key #'first)
                       do (format t "    ~a : ~a~%"
                                  (candidate-syntax name n)
                                  (type->string type))))))))

(defun fill-holes (term bindings)
  "Replace named holes (? label) using BINDINGS, an alist label -> term."
  (cond ((hole-p term)
         (let ((b (assoc (hole-label term) bindings
                         :test (lambda (a b)
                                 (string= (symbol-name a) (symbol-name b))))))
           (if b (cdr b) term)))
        ((consp term) (mapcar (lambda (x) (fill-holes x bindings)) term))
        (t term)))

;;; =====================================================================
;;; SigLA URL-fragment parsing
;;; =====================================================================
;;; Best-effort parser for the serialized query in a SigLA URL fragment:
;;;   document: .[doc-site @ !unit:] (belongs-location @ ![location]:[])
;;;             && .[doc-type @ !unit:] (belongs-kind @ ![kind]:[])
;;;             // [doc-site:groupKey/\; doc-name:sort/\]
;;; Empty ![name]:[] slots become named holes, so an unfilled template URL
;;; parses to a term you can SUGGEST on, FILL-HOLES, then RUN-QUERY.

(defparameter *url-properties*
  '(("belongs-location" . site)    ("doc-site" . site)
    ("belongs-kind"     . support) ("doc-type" . support)
    ("doc-name"         . docname)))

(defun url-decode (s)
  (with-output-to-string (out)
    (loop with i = 0
          while (< i (length s))
          do (let ((c (char s i)))
               (if (and (char= c #\%) (< (+ i 2) (length s)))
                   (progn (write-char (code-char (parse-integer
                                                  s :start (1+ i) :end (+ i 3)
                                                  :radix 16))
                                      out)
                          (incf i 3))
                   (progn (write-char c out) (incf i)))))))

(defun split-on (sep s)
  (loop with start = 0
        for pos = (search sep s :start2 start)
        collect (subseq s start pos)
        while pos do (setf start (+ pos (length sep)))))

(defun parse-criterion (c)
  "One '&&'-separated criterion -> a term like (= (site d) (? location))."
  (let* ((prop (loop for (key . prim) in *url-properties*
                     when (search key c) return prim))
         (hpos (search "![" c))
         (label (when hpos
                  (let ((end (position #\] c :start hpos)))
                    (intern (string-upcase (subseq c (+ hpos 2) end)))))))
    (when prop
      `(= (,prop d) ,(if label `(? ,label) '_)))))

(defun parse-sigla-url (url)
  "Returns (:target .. :term .. :group-by .. :sort-by ..)."
  (let* ((hash (position #\# url))
         (frag (url-decode (subseq url (if hash (1+ hash) 0))))
         (colon (position #\: frag))
         (target (subseq frag 0 colon))
         (body+g (subseq frag (1+ colon)))
         (gpos (search "//" body+g))
         (body (subseq body+g 0 gpos))
         (grouping (when gpos (subseq body+g (+ gpos 2))))
         (criteria (remove nil (mapcar #'parse-criterion
                                       (split-on "&&" body))))
         (term `(λ (d) ,(if criteria
                            (reduce (lambda (a b) `(and ,a ,b)) criteria)
                            'true)))
         (group-by nil) (sort-by nil))
    (when grouping
      (dolist (entry (split-on ";" (string-trim "[]" grouping)))
        (let* ((clean (remove #\\ (remove #\/ entry)))
               (parts (split-on ":" clean))
               (prop (loop for (key . prim) in *url-properties*
                           when (search key (first parts)) return prim)))
          (when (and prop (second parts))
            (cond ((search "groupKey" (second parts)) (setf group-by prop))
                  ((search "sort" (second parts))     (setf sort-by prop)))))))
    (list :target target :term term :group-by group-by :sort-by sort-by)))



(defun run-query (filter &key group-by (limit 8))
  "FILTER : Doc → Bool selects documents.
GROUP-BY : Doc → Str (a term, e.g. 'site) groups the results — this is
SigLA's groupKey. Prints results; returns the matching document names
(use (doc-plist name) via *corpus* if you need the full records)."
  (format t "~&query   : ~s~%type    : ~a~%"
          filter (type->string (typecheck filter)))
  (let* ((pred (compile-query filter '(:fun :doc :bool)))
         (hits (remove-if-not (lambda (d) (funcall pred d)) *corpus*)))
    (format t "matched : ~a of ~a documents~%" (length hits) (length *corpus*))
    (if group-by
        (let ((keyfn (compile-query group-by '(:fun :doc :str)))
              (groups (make-hash-table :test #'equal)))
          (dolist (d hits) (push d (gethash (funcall keyfn d) groups)))
          (loop for key in (sort (loop for k being the hash-keys of groups
                                       collect k)
                                 #'string<)
                for ds = (sort (gethash key groups) #'string<
                               :key (lambda (d) (getf d :name)))
                do (format t "  ~a (~a): ~{~a~^, ~}~:[~;, ...~]~%"
                           key (length ds)
                           (mapcar (lambda (d) (getf d :name))
                                   (subseq ds 0 (min limit (length ds))))
                           (> (length ds) limit))))
        (format t "  ~{~a~^, ~}~:[~;, ...~]~%"
                (mapcar (lambda (d) (getf d :name))
                        (subseq hits 0 (min limit (length hits))))
                (> (length hits) limit)))
    (mapcar (lambda (d) (getf d :name)) hits)))

(defun search-words (pattern)
  "SigLA word search: distinct words matching PATTERN, with counts."
  (let ((counts (make-hash-table :test #'equalp)))
    (dolist (d *corpus*)
      (dolist (w (doc-words d))
        (when (match-word pattern w) (incf (gethash w counts 0)))))
    (sort (loop for k being the hash-keys of counts using (hash-value v)
                collect (cons k v))
          #'> :key #'cdr)))

;;; =====================================================================
;;; Demo
;;; =====================================================================

(defparameter *example-url*
  "https://www.inscribercproject.com/SigLA/search-document.html#document:.[doc-site%20@%20!unit:]%20(belongs-location%20@%20![location]:[])%20&&%20.[doc-type%20@%20!unit:]%20(belongs-kind%20@%20![kind]:[])//[doc-site:groupKey/\\;doc-name:sort/\\]")

(defun demo ()
  (format t "Loaded ~a documents.~2%" (load-corpus))

  ;; 1. Parse the SigLA URL template into a term with named holes.
  (format t "--- Parsing a SigLA URL fragment ---~%")
  (let* ((parsed (parse-sigla-url *example-url*))
         (term (getf parsed :term)))
    (format t "target   : ~a~%group-by : ~(~a~), sort-by : ~(~a~)~2%"
            (getf parsed :target)
            (getf parsed :group-by) (getf parsed :sort-by))

    ;; 2. Type-directed suggestions for the holes — SigLA's query builder.
    (format t "--- Suggestions for the unfilled template ---~%")
    (suggest term)

    ;; 3. Fill the holes and run, grouped as the URL requested.
    (format t "~2%--- Filled: location = Zakros, kind = Tablet ---~%")
    (run-query (fill-holes term '((location . "Zakros") (kind . "Tablet")))
               :group-by (getf parsed :group-by)))

  ;; 4. Suggestions work mid-construction on any term with a hole.
  (format t "~2%--- Building a query interactively ---~%")
  (suggest '(λ (d) (exists (λ (w) (> (wlen w) _)) (words d))))

  ;; 5. Sign-level primitives: positional queries.
  (format t "~2%--- Khania documents with a word ending in sign 'u' ---~%")
  (run-query '(λ (d) (and (= (site d) "Khania")
                          (exists (λ (w) (= (final w) "u")) (words d))))))

(demo)
