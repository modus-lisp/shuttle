;;;; semver.lisp — npm's version algebra: parse, compare, and range satisfaction.
;;;;
;;;; This is the half of a package manager that decides WHICH code you get, so being approximately
;;;; right is not a partial success -- it silently installs a different program than the lockfile
;;;; says.  The rules that actually bite are not in the headline grammar:
;;;;
;;;;   PRERELEASE PRECEDENCE.  1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta <
;;;;   1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0.  Numeric identifiers compare NUMERICALLY
;;;;   and rank BELOW alphanumeric ones, so beta.11 > beta.2 even though "11" < "2" as text.
;;;;
;;;;   A PRERELEASE IS NOT AN ORDINARY VERSION.  `^1.2.3` does not match 1.9.9-rc.1, even though
;;;;   the ordering puts it inside the interval.  A prerelease satisfies a range only if some
;;;;   comparator in the SAME conjunction pins the same major.minor.patch AND is itself a
;;;;   prerelease -- i.e. only if you asked for prereleases of exactly that version.  Get this
;;;;   wrong and `npm install` starts handing out release candidates.
;;;;
;;;;   UPPER BOUNDS CARRY `-0`.  `^1.2.3` desugars to `>=1.2.3 <2.0.0-0`, not `<2.0.0`, because
;;;;   2.0.0-rc.1 sorts BELOW 2.0.0 and would otherwise sneak in under the bound.
;;;;
;;;; Graded against the `semver` package npm itself resolves with -- see inspect/semver-gate.lisp.
;;;; Nothing here was written from memory of the spec: the corpus was generated first and the
;;;; implementation moved until it agreed.

(in-package #:shuttle)

(defclass semver ()
  ((major :initarg :major :reader semver-major)
   (minor :initarg :minor :reader semver-minor)
   (patch :initarg :patch :reader semver-patch)
   (prerelease :initarg :prerelease :initform '() :reader semver-prerelease
               :documentation "Identifiers as a list of INTEGERs (numeric) and STRINGs.")
   (build :initarg :build :initform nil :reader semver-build
          :documentation "Ignored by every comparison; kept so a version can be printed back."))
  (:documentation "A semantic version.  See semver.org 2.0.0."))

(defun %digits-p (s) (and (plusp (length s)) (every #'digit-char-p s)))

(defun %ident-chars-p (s)
  (and (plusp (length s))
       (every (lambda (c) (or (alphanumericp c) (char= c #\-))) s)
       ;; ASCII only: `alphanumericp` is true of plenty that a version identifier may not contain.
       (every (lambda (c) (< (char-code c) 128)) s)))

(defun %split (string char)
  (loop with start = 0
        for p = (position char string :start start)
        collect (subseq string start p)
        while p do (setf start (1+ p))))

(defun %parse-numeric (s)
  "S as a non-negative integer with NO leading zero, or NIL.  `01.2.3` is not a version."
  (and (%digits-p s)
       (or (= 1 (length s)) (char/= (char s 0) #\0))
       (parse-integer s)))

(defun parse-semver (string &key (errorp nil))
  "STRING as a SEMVER, or NIL.  A leading `v` and surrounding whitespace are tolerated, which is
what the reference implementation does and therefore what published metadata contains."
  (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) string))
         (s (if (and (plusp (length s)) (member (char s 0) '(#\v #\V))) (subseq s 1) s)))
    (flet ((fail () (if errorp (error "not a semantic version: ~s" string) (return-from parse-semver nil))))
      (when (zerop (length s)) (fail))
      (let* ((plus (position #\+ s))
             (build (and plus (subseq s (1+ plus))))
             (s (if plus (subseq s 0 plus) s))
             (dash (position #\- s))
             (pre (and dash (subseq s (1+ dash))))
             (core (if dash (subseq s 0 dash) s))
             (parts (%split core #\.)))
        (when (and plus (zerop (length build))) (fail))
        (unless (= 3 (length parts)) (fail))
        (let ((nums (mapcar #'%parse-numeric parts)))
          (when (some #'null nums) (fail))
          (let ((ids '()))
            (when dash
              (when (zerop (length pre)) (fail))
              (dolist (id (%split pre #\.))
                (unless (%ident-chars-p id) (fail))
                ;; A purely numeric identifier compares as a number and may not have a leading
                ;; zero; an identifier that merely starts with a digit but has letters is text.
                (push (if (%digits-p id)
                          (or (%parse-numeric id) (fail))
                          id)
                      ids)))
            (when (and build (notevery (lambda (id) (%ident-chars-p id)) (%split build #\.)))
              (fail))
            (make-instance 'semver :major (first nums) :minor (second nums) :patch (third nums)
                                   :prerelease (nreverse ids) :build build)))))))

(defun semver-string (v)
  (format nil "~d.~d.~d~@[-~a~]~@[+~a~]" (semver-major v) (semver-minor v) (semver-patch v)
          (when (semver-prerelease v)
            (format nil "~{~a~^.~}" (semver-prerelease v)))
          (semver-build v)))

(defun %compare-ident (a b)
  "Numeric identifiers rank BELOW alphanumeric ones, and compare as numbers."
  (cond ((and (integerp a) (integerp b)) (signum (- a b)))
        ((integerp a) -1)
        ((integerp b) 1)
        ((string< a b) -1)
        ((string> a b) 1)
        (t 0)))

(defun %compare-prerelease (a b)
  "A version WITH a prerelease is lower than the same version without one."
  (cond ((and (null a) (null b)) 0)
        ((null a) 1)
        ((null b) -1)
        (t (loop for x in a for y in b
                 for c = (%compare-ident x y)
                 unless (zerop c) do (return c)
                   finally (return (signum (- (length a) (length b))))))))

(defun semver-compare (a b)
  "-1, 0 or 1.  BUILD METADATA IS IGNORED -- 1.0.0+build and 1.0.0+other are the same version."
  (let ((c (signum (- (semver-major a) (semver-major b)))))
    (when (zerop c) (setf c (signum (- (semver-minor a) (semver-minor b)))))
    (when (zerop c) (setf c (signum (- (semver-patch a) (semver-patch b)))))
    (if (zerop c) (%compare-prerelease (semver-prerelease a) (semver-prerelease b)) c)))

(defun semver< (a b) (minusp (semver-compare a b)))
(defun semver= (a b) (zerop (semver-compare a b)))

;;; ---- ranges ---------------------------------------------------------------------------------

(defclass comparator ()
  ((op :initarg :op :reader comparator-op :documentation "One of :LT :LTE :GT :GTE :EQ, or :ANY.")
   (version :initarg :version :initform nil :reader comparator-version)))

(defun %cmp (op version) (make-instance 'comparator :op op :version version))

(defun %partial (string)
  "Parse a possibly-partial version like `1`, `1.2`, `1.2.x`.  Returns
(values MAJOR MINOR PATCH PRERELEASE ANY-X-P OK-P) where a wildcard component is NIL."
  (let* ((s (string-trim '(#\Space #\Tab) string))
         (s (if (and (plusp (length s)) (member (char s 0) '(#\v #\V))) (subseq s 1) s)))
    (when (zerop (length s)) (return-from %partial (values nil nil nil nil t t)))
    (let* ((plus (position #\+ s))
           (s (if plus (subseq s 0 plus) s))
           (dash (position #\- s))
           (pre (and dash (subseq s (1+ dash))))
           (core (if dash (subseq s 0 dash) s))
           (parts (%split core #\.))
           (out '()))
      (when (> (length parts) 3) (return-from %partial (values nil nil nil nil nil nil)))
      (dolist (p parts)
        (push (cond ((or (string= p "*") (string-equal p "x") (string= p "")) nil)
                    ((%parse-numeric p))
                    (t (return-from %partial (values nil nil nil nil nil nil))))
              out))
      (setf out (nreverse out))
      (let ((m (first out)) (n (second out)) (p (third out))
            (ids (when pre
                   (let ((v (parse-semver (format nil "0.0.0-~a" pre))))
                     (unless v (return-from %partial (values nil nil nil nil nil nil)))
                     (semver-prerelease v)))))
        (values m n p ids
                (or (null m) (null n) (null p) (< (length parts) 3))
                t)))))

(defun %v (major minor patch &optional pre)
  (make-instance 'semver :major major :minor minor :patch patch :prerelease pre))

(defun %zero-pre () (list 0))   ; the `-0` that keeps a prerelease from sneaking under a bound

(defun %desugar (token)
  "One whitespace-separated range token -> a list of COMPARATORs, or :FAIL.

MAJ/MNR/PAT rather than M/m/p because Lisp folds case: `M` and `m` are ONE symbol, so the obvious
spelling binds the same variable twice and the minor number silently becomes the major."
  (let* ((tok (string-trim '(#\Space #\Tab) token)))
    (when (zerop (length tok)) (return-from %desugar '()))
    (let* ((op-len (cond ((and (>= (length tok) 2)
                               (member (subseq tok 0 2) '(">=" "<=") :test #'string=)) 2)
                         ((member (char tok 0) '(#\< #\> #\=)) 1)
                         ((member (char tok 0) '(#\~ #\^)) 1)
                         (t 0)))
           (op (subseq tok 0 op-len))
           (rest (subseq tok op-len)))
      ;; `~>` is npm's spelling of `~`.
      (when (and (string= op "~") (plusp (length rest)) (char= (char rest 0) #\>))
        (setf rest (subseq rest 1)))
      ;; AN OPERATOR WITH NOTHING AFTER IT IS NOT A RANGE.  `>=` on its own parsed as an X-range
      ;; with every component wildcarded, i.e. `>=0.0.0` -- so a truncated or malformed range
      ;; silently became `*` and would match ANY published version.  That is the exact failure
      ;; PARSE-RANGE exists to prevent, so it is refused here rather than widened.
      (when (and (plusp (length op)) (zerop (length (string-trim '(#\Space #\Tab) rest))))
        (return-from %desugar :fail))
      (multiple-value-bind (maj mnr pat pre anyx ok) (%partial rest)
        (unless ok (return-from %desugar :fail))
        (cond
          ;; ---- ^ : pin the leftmost NON-ZERO component ---------------------------------------
          ((string= op "^")
           (cond ((null maj) (list (%cmp :gte (%v 0 0 0))))
                 ((null mnr) (list (%cmp :gte (%v maj 0 0))
                                   (%cmp :lt (%v (1+ maj) 0 0 (%zero-pre)))))
                 ((null pat)
                  (if (zerop maj)
                      (list (%cmp :gte (%v 0 mnr 0)) (%cmp :lt (%v 0 (1+ mnr) 0 (%zero-pre))))
                      (list (%cmp :gte (%v maj mnr 0)) (%cmp :lt (%v (1+ maj) 0 0 (%zero-pre))))))
                 ((plusp maj) (list (%cmp :gte (%v maj mnr pat pre))
                                    (%cmp :lt (%v (1+ maj) 0 0 (%zero-pre)))))
                 ((plusp mnr) (list (%cmp :gte (%v 0 mnr pat pre))
                                    (%cmp :lt (%v 0 (1+ mnr) 0 (%zero-pre)))))
                 (t (list (%cmp :gte (%v 0 0 pat pre))
                          (%cmp :lt (%v 0 0 (1+ pat) (%zero-pre)))))))
          ;; ---- ~ : allow patch-level changes -------------------------------------------------
          ((string= op "~")
           (cond ((null maj) (list (%cmp :gte (%v 0 0 0))))
                 ((null mnr) (list (%cmp :gte (%v maj 0 0))
                                   (%cmp :lt (%v (1+ maj) 0 0 (%zero-pre)))))
                 (t (list (%cmp :gte (%v maj mnr (or pat 0) pre))
                          (%cmp :lt (%v maj (1+ mnr) 0 (%zero-pre)))))))
          ;; ---- an X-range carrying a comparison operator -------------------------------------
          ((and anyx (plusp (length op)) (not (string= op "=")))
           (cond ((null maj)
                  ;; `>x` and `<x` can match nothing; `>=x` is everything.
                  (if (member op '(">" "<") :test #'string=)
                      (list (%cmp :lt (%v 0 0 0 (%zero-pre))))
                      (list (%cmp :gte (%v 0 0 0)))))
                 (t (let ((mm (or mnr 0)))
                      (cond ((string= op ">")
                             (if (null mnr)
                                 (list (%cmp :gte (%v (1+ maj) 0 0)))
                                 (list (%cmp :gte (%v maj (1+ mm) 0)))))
                            ((string= op "<=")
                             (if (null mnr)
                                 (list (%cmp :lt (%v (1+ maj) 0 0 (%zero-pre))))
                                 (list (%cmp :lt (%v maj (1+ mm) 0 (%zero-pre))))))
                            ((string= op "<") (list (%cmp :lt (%v maj mm 0 (%zero-pre)))))
                            (t (list (%cmp :gte (%v maj mm 0)))))))))
          ;; ---- a bare X-range ---------------------------------------------------------------
          (anyx
           (cond ((null maj) (list (%cmp :gte (%v 0 0 0))))
                 ((null mnr) (list (%cmp :gte (%v maj 0 0))
                                   (%cmp :lt (%v (1+ maj) 0 0 (%zero-pre)))))
                 (t (list (%cmp :gte (%v maj mnr 0))
                          (%cmp :lt (%v maj (1+ mnr) 0 (%zero-pre)))))))
          ;; ---- a plain comparator -----------------------------------------------------------
          (t (list (%cmp (cond ((string= op ">") :gt) ((string= op ">=") :gte)
                               ((string= op "<") :lt) ((string= op "<=") :lte)
                               (t :eq))
                         (%v maj mnr pat pre)))))))))

(defun %desugar-hyphen (left right)
  "`A - B`: the lower bound is A padded with zeros, the upper is B rounded UP over whatever it left
unspecified -- `1.2.3 - 2.3` ends below 2.4.0, not at 2.3.0."
  (multiple-value-bind (lmaj lmnr lpat lpre lx lok) (%partial left)
    (declare (ignore lx))
    (multiple-value-bind (rmaj rmnr rpat rpre rx rok) (%partial right)
      (declare (ignore rx))
      (unless (and lok rok) (return-from %desugar-hyphen :fail))
      (list (if (null lmaj)
                (%cmp :gte (%v 0 0 0))
                (%cmp :gte (%v lmaj (or lmnr 0) (or lpat 0) lpre)))
            (cond ((null rmaj) (%cmp :gte (%v 0 0 0)))
                  ((null rmnr) (%cmp :lt (%v (1+ rmaj) 0 0 (%zero-pre))))
                  ((null rpat) (%cmp :lt (%v rmaj (1+ rmnr) 0 (%zero-pre))))
                  (t (%cmp :lte (%v rmaj rmnr rpat rpre))))))))

(defun %tokenize-range (s)
  "Split one range on whitespace, keeping `A - B` together and gluing `>= 1.2.3` back up."
  (let ((raw (remove "" (%split (substitute #\Space #\Tab s) #\Space) :test #'string=))
        (out '()))
    (loop while raw
          do (let ((tok (pop raw)))
               (cond ((and raw (string= (first raw) "-") (rest raw))
                      (pop raw)
                      (push (list :hyphen tok (pop raw)) out))
                     ;; an operator standing alone binds to the next token
                     ((and (member tok '(">" ">=" "<" "<=" "=" "~" "^") :test #'string=) raw)
                      (push (list :tok (concatenate 'string tok (pop raw))) out))
                     (t (push (list :tok tok) out)))))
    (nreverse out)))

(defun parse-range (string)
  "A range -> a list of conjunctions, each a list of COMPARATORs.  NIL if it does not parse.

An unparsable range must be REFUSED rather than treated as `*`: a resolver that widens a range it
did not understand installs something nobody asked for."
  (let ((sets '()))
    (dolist (part (let ((acc '()) (start 0))
                    (loop for p = (search "||" string :start2 start)
                          do (push (subseq string start p) acc)
                          while p do (setf start (+ p 2)))
                    (nreverse acc)))
      (let ((comps '()))
        (dolist (item (%tokenize-range part))
          (let ((got (ecase (first item)
                       (:hyphen (%desugar-hyphen (second item) (third item)))
                       (:tok (%desugar (second item))))))
            (when (eq got :fail) (return-from parse-range nil))
            (setf comps (append comps got))))
        ;; An empty conjunction is `*`.
        (push (or comps (list (%cmp :gte (%v 0 0 0)))) sets)))
    (and sets (nreverse sets))))

(defun %comparator-test (v c)
  (let ((r (semver-compare v (comparator-version c))))
    (ecase (comparator-op c)
      (:eq (zerop r)) (:lt (minusp r)) (:lte (<= r 0)) (:gt (plusp r)) (:gte (>= r 0)))))

(defun %set-test (v comps)
  (and (every (lambda (c) (%comparator-test v c)) comps)
       ;; THE PRERELEASE RULE.  A prerelease version is admitted only where it was explicitly
       ;; asked for: some comparator in THIS conjunction must pin the same major.minor.patch and
       ;; itself be a prerelease.  Without this, `^1.2.3` would match 1.9.9-rc.1.
       (or (null (semver-prerelease v))
           (some (lambda (c)
                   (let ((cv (comparator-version c)))
                     (and cv (semver-prerelease cv)
                          (= (semver-major cv) (semver-major v))
                          (= (semver-minor cv) (semver-minor v))
                          (= (semver-patch cv) (semver-patch v)))))
                 comps))))

(defun semver-satisfies-p (version range)
  "Does VERSION (a SEMVER or a string) satisfy RANGE (a string or a parsed range)?"
  (let ((v (if (stringp version) (parse-semver version) version))
        (r (if (stringp range) (parse-range range) range)))
    (and v r (some (lambda (comps) (%set-test v comps)) r))))

(defun semver-max-satisfying (versions range)
  "The HIGHEST of VERSIONS satisfying RANGE, or NIL -- what a resolver actually asks."
  (let ((r (if (stringp range) (parse-range range) range)) (best nil))
    (when r
      (dolist (v versions best)
        (let ((pv (if (stringp v) (parse-semver v) v)))
          (when (and pv (%set-test-any pv r) (or (null best) (plusp (semver-compare pv best))))
            (setf best pv)))))))

(defun %set-test-any (v r) (some (lambda (comps) (%set-test v comps)) r))
