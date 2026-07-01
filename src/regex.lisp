;;;; regex.lisp — a clean-room backtracking regular-expression engine for shuttle.
;;;; Compiles a JS RegExp source string + flags to a matcher used by RegExp.prototype
;;;; and the String regex methods. (Filled by the RegExp subagent.)
(in-package #:shuttle)
;; TODO(regex): (defun regex-compile (source flags) ...) -> matcher
;;              (defun regex-exec (matcher input start) ...) -> (values match-end captures) | nil
