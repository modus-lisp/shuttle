#!/usr/bin/env bash
# Parse a real ESM dependency tree with PARSE-MODULE.  Synthetic forms are in module-gate.lisp;
# this is the other half of the oracle -- code nobody wrote to be parsed by us.
#   inspect/module-corpus.sh [tree]        (default: the nsite build's node_modules)
set -u
cd "$(dirname "$0")/.."
TREE="${1:-$HOME/nsite-build/node_modules}"
[ -d "$TREE" ] || { echo "no such tree: $TREE (skipping)"; exit 77; }
exec sbcl --dynamic-space-size 4096 --script /dev/stdin <<LISP
(require :asdf)
(push (truename "$PWD/") asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle")))
(in-package #:shuttle)
(defun slurp (p) (with-open-file (s p :external-format :utf-8)
                   (let ((b (make-string (file-length s)))) (subseq b 0 (read-sequence b s)))))
(let ((files (remove-if (lambda (p)
                          (let ((n (namestring p)))
                            (or (search "/cjs/" n) (search ".min.js" n) (search "bundle" n))))
                        (directory "$TREE/**/*.js")))
      (ok 0) (bad 0) (fails '()))
  (dolist (f files)
    (handler-case (progn (parse-module (slurp f)) (incf ok))
      (error (e) (incf bad)
        (push (list (namestring f)
                    (let ((s (princ-to-string e))) (subseq s 0 (min 70 (length s))))) fails))))
  (format t "~&parsed ~a of ~a real ESM files~%" ok (+ ok bad))
  (dolist (f (subseq (nreverse fails) 0 (min 15 (length fails))))
    (format t "  FAIL ~a~%       ~a~%" (first f) (second f)))
  (sb-ext:exit :code (if (zerop bad) 0 1)))
LISP
