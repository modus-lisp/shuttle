;;;; builtins/regexp.lisp — the RegExp global + RegExp.prototype (test/exec/flags/
;;;; source/lastIndex/@@match/@@replace/@@split/@@search). Uses src/regex.lisp.
(in-package #:shuttle)

(defun install-regexp (realm)
  (declare (ignorable realm))
  ;; TODO(regex): (define-global realm "RegExp" ctor)
  )

(register-builtin-installer 'install-regexp)
