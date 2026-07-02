;;;; builtins/intl-numberformat.lisp — Intl.NumberFormat (+ PluralRules shares number machinery).
(in-package #:shuttle)

(defun install-intl_numberformat (realm)
  (declare (ignorable realm))
  ;; TODO(intl)
  )

(register-builtin-installer 'install-intl_numberformat)
