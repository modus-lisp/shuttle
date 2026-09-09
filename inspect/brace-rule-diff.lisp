;;;; brace-rule-diff.lisp — isolate ONE lexer rule change across the whole corpus, deterministically.
;;;;
;;;; `/` after `}` is the only place the lexer must guess regex-vs-division from context.  The old
;;;; rule called every `)` before the `{` a statement body, which is right for a function
;;;; DECLARATION and wrong for a function EXPRESSION.  This parses every test262 file under both
;;;; rules and reports every file whose parse differs.
;;;;
;;;; It exists because comparing two test262 RUNS could not answer the question: a per-test timeout
;;;; makes the score depend on machine load, and the two runs disagreed on 27 of 45 slices by up to
;;;; 267 tests in BOTH directions -- noise far larger than any effect this rule could have.
;;;; Parsing has no clock in it, so this comparison is exact and repeatable.
;;;;
;;;;   SHUTTLE_TEST262=<checkout> sbcl --script inspect/brace-rule-diff.lisp

(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*)))
      asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle/bundle")))
(in-package #:shuttle)

(defparameter *root*
  (let ((r (or (sb-ext:posix-getenv "SHUTTLE_TEST262")
               (namestring (merge-pathnames "test262-full" (truename "./"))))))
    (if (char= (char r (1- (length r))) #\/) r (concatenate 'string r "/"))))

(defun tree-equal* (x y)
  (cond ((and (vectorp x) (vectorp y) (not (stringp x)))
         (and (= (length x) (length y)) (every #'tree-equal* x y)))
        ((and (consp x) (consp y)) (and (tree-equal* (car x) (car y)) (tree-equal* (cdr x) (cdr y))))
        (t (equal x y))))

(defun parse-under (src legacy)
  (let ((*legacy-brace-rule* legacy))
    (handler-case (list :ok (parse-program src))
      (error (e) (list :err (format nil "~a" e))))))

(let ((files (sort (remove-if (lambda (p) (search "_FIXTURE" (namestring p)))
                              (directory (merge-pathnames "test/**/*.js" *root*)))
                   #'string< :key #'namestring))
      (n 0) (differ 0) (old-only 0) (new-only 0) (both 0) (examples '())
      ;; THE POSITIVE CONTROL.  "0 differences" is only meaningful if this comparison is capable of
      ;; reporting a difference at all, and the whole reason the corpus shows none is that
      ;; SCAN-REGEX abandons a regex candidate at a line terminator -- so in hand-written source
      ;; the old rule's wrong guess died at end of line.  Take the newlines away, which is what
      ;; minifying does and what every bundle on the web already looks like, and the wrong guess
      ;; runs on.  These counters must be NON-ZERO, or the run above proved nothing.
      (mn 0) (mdiffer 0) (mrescued 0) (mexamples '()))
  (dolist (p files)
    (let ((src (handler-case (slurp-file p) (error () nil))))
      (when src
        (incf n)
        (let* ((a (parse-under src t))          ; the rule as it was
               (b (parse-under src nil)))       ; the rule as it is now
          (unless (and (eq (first a) (first b))
                       (if (eq (first a) :ok) (tree-equal* (second a) (second b))
                           (equal (second a) (second b))))
            (incf differ)
            (cond ((and (eq (first a) :err) (eq (first b) :ok)) (incf new-only))
                  ((and (eq (first a) :ok) (eq (first b) :err)) (incf old-only))
                  (t (incf both)))
            (when (< (length examples) 25)
              (push (list (namestring p) (first a) (first b)
                          (if (eq (first a) :err) (second a) ""))
                    examples)))))))
  ;; ---- positive control: the same diff, on the same files, MINIFIED ----
  (dolist (p files)
    (let* ((src (handler-case (slurp-file p) (error () nil)))
           (min (and src (handler-case (let ((*legacy-brace-rule* nil)) (minify-source src))
                           (error () nil)))))
      (when min
        (incf mn)
        (let ((a (parse-under min t)) (b (parse-under min nil)))
          (unless (and (eq (first a) (first b))
                       (if (eq (first a) :ok) (tree-equal* (second a) (second b))
                           (equal (second a) (second b))))
            (incf mdiffer)
            (when (and (eq (first a) :err) (eq (first b) :ok)) (incf mrescued))
            (when (< (length mexamples) 8)
              (push (list (namestring p) (first a) (first b)) mexamples)))))))

  (format t "~&parsed ~d files under both rules~%" n)
  (format t "differing: ~d   (old FAILED / new parses: ~d)  (old parsed / new FAILS: ~d)  ~
(both parse, different tree: ~d)~%" differ new-only old-only both)
  (dolist (e (reverse examples))
    (format t "  ~a~%      old=~a new=~a ~a~%" (first e) (second e) (third e) (fourth e)))

  (format t "~&~%-- positive control: the same files, minified --~%")
  (format t "minified and parsed ~d files under both rules~%" mn)
  (format t "differing: ~d   (of which the OLD rule could not parse at all: ~d)~%" mdiffer mrescued)
  (dolist (e (reverse mexamples))
    (format t "  ~a~%      old=~a new=~a~%" (first e) (second e) (third e)))
  (when (zerop mdiffer)
    (format t "~&CONTROL FAILED: this comparison cannot detect a difference, so the 0 above ~
means nothing.~%")
    (sb-ext:exit :code 1))
  (sb-ext:exit :code 0))
