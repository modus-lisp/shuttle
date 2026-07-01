;;;; builtins/string-regex.lisp — String.prototype regex methods (match/matchAll/
;;;; replace/replaceAll/search/split) delegating to RegExp. Uses src/regex.lisp.
(in-package #:shuttle)

(defun install-string-regex (realm)
  (declare (ignorable realm))
  ;; TODO(regex): add match/matchAll/replace/replaceAll/search/split to (realm-string-proto realm)
  )

(register-builtin-installer 'install-string-regex)
