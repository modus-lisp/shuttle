;;;; minify-gate.lisp — prove the minifier changes no program's MEANING, over the whole of test262.
;;;;
;;;; MINIFY already re-lexes its own output and demands the same token sequence, and that check
;;;; runs on every real build.  It is necessary and it is NOT sufficient, and the gap between the
;;;; two is precisely where the dangerous rule lives.
;;;;
;;;; Automatic semicolon insertion reads LINE TERMINATORS, and it reads them in the PARSER, after
;;;; the lexer is done.  So deleting a newline that mattered produces the identical token stream
;;;; and a different program -- exactly the mutation the token check is blind to.  `a = 1 \n b = 2`
;;;; and `a = 1 b = 2` have the same tokens; one is two statements and the other does not parse.
;;;;
;;;; So the oracle here is the PARSE TREE.  Shuttle's AST carries no source offsets -- positions
;;;; live in the token vector, not the nodes -- which means two ASTs are equal exactly when the two
;;;; sources are the same program.  Parse the original, minify, parse that, compare.  A whitespace
;;;; minifier is correct if and only if this never differs, and test262 is 53,000 programs written
;;;; specifically to sit on the language's edges.
;;;;
;;;; Files whose ORIGINAL does not parse are skipped: test262 is full of deliberate syntax errors,
;;;; and there is no tree to compare against.
;;;;
;;;;   SHUTTLE_TEST262=<checkout> [SHUTTLE_MINGATE=start:count] sbcl --script inspect/minify-gate.lisp

(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*)))
      asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle/bundle")))
(in-package #:shuttle)

(defparameter *root*
  ;; The trailing slash is load-bearing: without it MERGE-PATHNAMES reads the last component as a
  ;; FILE NAME and replaces it, so the glob below silently searches the parent and matches nothing
  ;; -- a gate that reports "0 mismatches" because it checked zero files.
  (let ((r (or (sb-ext:posix-getenv "SHUTTLE_TEST262")
               (namestring (merge-pathnames "test262-full" (truename "./"))))))
    (if (char= (char r (1- (length r))) #\/) r (concatenate 'string r "/"))))

(defun ast-equal (x y)
  (cond ((and (vectorp x) (vectorp y) (not (stringp x)))
         (and (= (length x) (length y)) (every #'ast-equal x y)))
        ((and (consp x) (consp y)) (and (ast-equal (car x) (car y)) (ast-equal (cdr x) (cdr y))))
        (t (equal x y))))

(defun parse-either (src)
  "The tree, and which parser produced it.  A module-only file (it has `import`) will not parse as
a script, so try both -- but ALWAYS re-parse the minified text with the SAME one, or the
comparison is between two different grammars rather than two spellings of one program.

For a module it is MODULE-ITEMS that comes back, not the record.  The record's import and export
tables carry SOURCE SPANS -- character offsets the bundler splices at -- and those are supposed to
move when characters are deleted.  Comparing them would report a mismatch on every module in the
corpus for doing exactly what it says on the tin, and the first one found was precisely that: a
false alarm whose `items` were identical.  The items are the program."
  (handler-case (values (parse-program src) :script)
    (error () (handler-case (values (module-items (parse-module src)) :module)
                (error () (values nil nil))))))

(let* ((slice (sb-ext:posix-getenv "SHUTTLE_MINGATE"))
       (colon (and slice (position #\: slice)))
       (start (if colon (parse-integer slice :end colon) 0))
       (count (if colon (parse-integer slice :start (1+ colon)) most-positive-fixnum))
       (files (sort (remove-if (lambda (p) (search "_FIXTURE" (namestring p)))
                               (directory (merge-pathnames "test/**/*.js" *root*)))
                    #'string< :key #'namestring))
       (checked 0) (skipped 0) (bad 0) (raw 0) (small 0) (examples '()))
  (loop for p in (subseq files (min start (length files))
                         (min (length files) (+ start count)))
        do (let ((src (handler-case (slurp-file p) (error () nil))))
             (when src
               (multiple-value-bind (tree kind) (parse-either src)
                 (if (null kind)
                     (incf skipped)               ; a deliberate syntax error; nothing to compare
                     (let ((min (handler-case (minify-source src)
                                  (error (e)
                                    (incf bad)
                                    (push (list (namestring p) (format nil "~a" e)) examples)
                                    nil))))
                       (when min
                         (incf checked) (incf raw (length src)) (incf small (length min))
                         (let ((tree2 (handler-case (if (eq kind :script)
                                                        (parse-program min)
                                                        (module-items (parse-module min)))
                                        (error (e) (list :parse-failed (format nil "~a" e))))))
                           (unless (ast-equal tree tree2)
                             (incf bad)
                             (push (list (namestring p)
                                         (if (and (consp tree2) (eq (car tree2) :parse-failed))
                                             (second tree2) "AST DIFFERS"))
                                   examples)))))))))) 
  (format t "~&checked ~d   skipped(unparsable original) ~d   MISMATCHES ~d~%" checked skipped bad)
  (when (plusp checked)
    (format t "bytes ~d -> ~d  (~,1f%)~%" raw small (* 100.0 (/ small raw))))
  (dolist (e (subseq (nreverse examples) 0 (min 12 (length examples))))
    (format t "  ~a~%      ~a~%" (first e) (second e)))
  (sb-ext:exit :code (if (zerop bad) 0 1)))
