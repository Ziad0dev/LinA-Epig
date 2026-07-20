;;;; linear-a.lisp
;;;; A Linear A corpus toolkit in Common Lisp.
;;;;
;;;; Linear A is undeciphered; this program does what epigraphers do:
;;;; transliteration (phonetic values borrowed from Linear B), annotation
;;;; of the few understood elements (KU-RO "total", KI-RO "deficit",
;;;; logograms, numerals), corpus statistics, concordance, and arithmetic
;;;; verification of tablet totals — the very method by which KU-RO's
;;;; meaning was identified.
;;;;
;;;; Data: corpus.sexp — 1722 documents converted from lineara.xyz
;;;; (John Younger's transliterations of GORILA), CC-licensed.
;;;;
;;;; Run:  sbcl --script linear-a.lisp
;;;; Or load into a REPL and explore: (concordance "KU-RO"), etc.

(defpackage :linear-a
  (:use :cl)
  (:export #:load-corpus #:doc #:concordance #:word-frequencies
           #:audit-totals #:show-document))
(in-package :linear-a)

;;; ---------------------------------------------------------------------
;;; Corpus loading
;;; ---------------------------------------------------------------------

(defparameter *corpus* nil
  "List of documents. Each document is a plist:
   (:name .. :site .. :support .. :words (..) :glosses (..))")

(defun load-corpus (&optional (path "corpus.sexp"))
  (with-open-file (in path :external-format :utf-8)
    (let ((*read-eval* nil))            ; never evaluate data
      (setf *corpus* (read in))))
  (length *corpus*))

(defun doc (name)
  "Find a document by name, e.g. (doc \"HT13\")."
  (find name *corpus* :key (lambda (d) (getf d :name))
                      :test #'string-equal))

;;; ---------------------------------------------------------------------
;;; Token classification
;;; ---------------------------------------------------------------------
;;; Younger-style tokens: words "KU-RO", logograms "GRA"/"VIN"/"OLE",
;;; numerals "197", fractions "1/2", divider signs and breakage marks
;;; in the Aegean Unicode blocks.

(defun ascii-p (tok) (every (lambda (c) (< (char-code c) 128)) tok))

(defun normalize-numeral (tok)
  "Map superscript digits and the fraction slash to ASCII: ¹⁄2 -> 1/2."
  (map 'string (lambda (c)
                 (case c
                   (#\SUPERSCRIPT_ZERO #\0) (#\SUPERSCRIPT_ONE #\1)
                   (#\SUPERSCRIPT_TWO #\2)  (#\SUPERSCRIPT_THREE #\3)
                   (#\SUPERSCRIPT_FOUR #\4) (#\SUPERSCRIPT_FIVE #\5)
                   (#\FRACTION_SLASH #\/)
                   (t c)))
       tok))

(defun parse-number (tok)
  "Integer or exact rational for numeral tokens, else NIL.
Handles '197', '1/2', '¹⁄2', and mixed '5 1/2' Common-Lisp-natively."
  (let ((tok (normalize-numeral tok)))
    (when (and (plusp (length tok)) (ascii-p tok)
             (every (lambda (c) (find c "0123456789/ ")) tok)
             (digit-char-p (char tok 0)))
    (handler-case
        (let* ((chunks (loop with start = 0
                             for pos = (position #\Space tok :start start)
                             collect (subseq tok start pos)
                             while pos do (setf start (1+ pos))))
               (parts (mapcar (lambda (p) (read-from-string p)) chunks)))
          (when (every #'rationalp parts) (reduce #'+ parts)))
      (error () nil)))))

(defun word-p (tok)
  "Heuristic: a syllabic sign-sequence (vs numeral/logogram/divider)."
  (and (ascii-p tok)
       (not (parse-number tok))
       (find #\- tok)))                 ; multi-sign sequences

;;; ---------------------------------------------------------------------
;;; The understood vocabulary (kept honest)
;;; ---------------------------------------------------------------------

(defparameter *lexicon*
  '(("KU-RO"       "total"                   :secure)
    ("PO-TO-KU-RO" "grand total"             :secure)
    ("KI-RO"       "deficit / owed"          :probable)
    ("KU-PA3-NU"   "personal name"           :probable)
    ("SA-RA2"      "frequent HT term, referent debated" :opaque)
    ("A-TA-I-*301-WA-JA" "libation-formula opening"     :secure)
    ("JA-SA-SA-RA-ME"    "libation-formula term, possibly divine name" :probable)
    ("KU-NI-SU"    "emmer wheat? (cf. Akkadian kunnisu)" :speculative)))

(defun gloss (word)
  (let ((hit (assoc word *lexicon* :test #'string-equal)))
    (when hit (format nil "~a [~(~a~)]" (second hit) (third hit)))))

;;; ---------------------------------------------------------------------
;;; Corpus statistics
;;; ---------------------------------------------------------------------

(defun word-frequencies (&key (site nil) (min-count 2))
  "Sign-sequence frequencies across the corpus, most common first."
  (let ((counts (make-hash-table :test #'equal)))
    (dolist (d *corpus*)
      (when (or (null site) (string-equal site (getf d :site)))
        (dolist (tok (getf d :words))
          (when (word-p tok) (incf (gethash tok counts 0))))))
    (sort (loop for k being the hash-keys of counts using (hash-value v)
                when (>= v min-count) collect (cons k v))
          #'> :key #'cdr)))

(defun concordance (word)
  "All documents attesting WORD."
  (loop for d in *corpus*
        when (member word (getf d :words) :test #'string-equal)
          collect (getf d :name)))

;;; ---------------------------------------------------------------------
;;; KU-RO arithmetic audit
;;; ---------------------------------------------------------------------
;;; A tablet lists entries with quantities, then KU-RO <n> where n should
;;; equal the sum. We replay that: accumulate numbers, and at each KU-RO
;;; compare the following number against the running sum. Exact rational
;;; arithmetic means fractions like 1/2 Just Work.

(defun merge-numerals (tokens)
  "Collapse runs of adjacent numeral tokens: '130' '¹⁄2' -> 261/2."
  (let ((out '()) (acc nil))
    (dolist (tok tokens)
      (let ((n (parse-number tok)))
        (cond (n (setf acc (+ (or acc 0) n)))
              (t (when acc (push acc out) (setf acc nil))
                 (push tok out)))))
    (when acc (push acc out))
    (nreverse out)))

(defun audit-document (d)
  "Returns checks; each check is (claimed sum consistent-p)."
  (let ((sum 0) (expecting nil) (checks '()))
    (dolist (tok (merge-numerals (getf d :words)))
      (cond ((and expecting (rationalp tok))
             (push (list tok sum (= tok sum)) checks)
             (setf sum 0 expecting nil))
            ((rationalp tok) (incf sum tok))
            ((string-equal tok "KU-RO") (setf expecting t))))
    (nreverse checks)))

(defun audit-totals (&key (site "Haghia Triada"))
  "Scan tablets with a KU-RO line and report arithmetic consistency."
  (let ((ok 0) (bad 0) (examples '()))
    (dolist (d *corpus*)
      (when (or (null site) (string-equal site (getf d :site)))
        (dolist (check (audit-document d))
          (destructuring-bind (claimed sum consistent) check
            (if consistent (incf ok)
                (progn (incf bad)
                       (push (list (getf d :name) claimed sum) examples)))))))
    (format t "~&KU-RO totals checked: ~a consistent, ~a discrepant~%" ok bad)
    (format t "(Discrepancies are expected: damaged tablets, lost entries,~
               ~% multi-commodity sections — the same gaps scholars wrestle with.)~%")
    (loop for (name claimed sum) in (subseq examples 0 (min 5 (length examples)))
          do (format t "  ~a: scribe wrote ~a, extant entries sum to ~a~%"
                     name claimed sum))
    (values ok bad)))

;;; ---------------------------------------------------------------------
;;; Document display
;;; ---------------------------------------------------------------------

(defun show-document (name)
  (let ((d (doc name)))
    (unless d (format t "No document ~a~%" name) (return-from show-document))
    (format t "~&=== ~a (~a, ~a) ===~%"
            (getf d :name) (getf d :site) (getf d :support))
    (loop for tok in (getf d :words)
          for g = (getf d :glosses)     ; parallel gloss list, same length
          do (format t "  ~a~@[   ; ~a~]~%" tok (gloss tok)))
    (let ((checks (audit-document d)))
      (dolist (c checks)
        (destructuring-bind (claimed sum consistent) c
          (format t "  -> KU-RO arithmetic: entries sum to ~a, scribe wrote ~a (~a)~%"
                  sum claimed (if consistent "CONSISTENT" "DISCREPANCY")))))))

;;; ---------------------------------------------------------------------
;;; Demo
;;; ---------------------------------------------------------------------

(defun demo ()
  (format t "~&Loaded ~a documents.~2%" (load-corpus))

  (format t "=== Most frequent sign-sequences (whole corpus) ===~%")
  (loop for (word . n) in (word-frequencies) repeat 12
        do (format t "  ~4d  ~a~@[   ; ~a~]~%" n word (gloss word)))

  (format t "~2%=== KU-RO attestations ===~%~a documents: ~{~a~^, ~} ...~%"
          (length (concordance "KU-RO"))
          (subseq (concordance "KU-RO") 0 10))

  (format t "~2%=== Arithmetic audit, Haghia Triada ===~%")
  (audit-totals)

  (format t "~2%")
  (show-document "HT13"))

(demo)
