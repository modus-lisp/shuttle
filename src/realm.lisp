;;;; realm.lisp — the consumer API (the seam weft builds DOM bindings on):
;;;; make-realm, eval-script, define-global, make-host-object, native-function,
;;;; invoke. Plus a minimal set of intrinsics (the full built-in library is the
;;;; src/builtins/, one test262-pinned file per group).
(in-package #:shuttle)

(defun native-function (realm name fn &optional (len 0))
  "Wrap a CL function (THIS ARGS-list) -> JS value as a callable JS object."
  (let ((*current-realm* realm))
    (let ((o (make-object :proto (%fn-proto) :class "Function")))
      (setf (js-object-call o) fn)
      (put o "name" name :enumerable nil :writable nil)
      (put o "length" (float len 1d0) :enumerable nil :writable nil)
      o)))

(defun make-realm ()
  "Create a fresh realm (per-document global environment + intrinsics)."
  (let* ((obj-proto (make-object :proto *null*))
         (fn-proto  (make-object :proto obj-proto :class "Function"))
         (arr-proto (make-object :proto obj-proto :class "Array"))
         (realm (%make-realm :object-proto obj-proto :function-proto fn-proto :array-proto arr-proto)))
    (let ((*current-realm* realm))
      (setf (realm-global realm) (make-object :proto obj-proto)
            (realm-global-env realm) (new-env nil))
      (define-global realm "globalThis" (realm-global realm))
      (install-intrinsics realm)
      realm)))

(defun define-global (realm name value)
  (env-declare (realm-global-env realm) name value)
  (put (realm-global realm) name value)
  value)

(defun eval-script (realm source)
  "Compile and run SOURCE against REALM; return the completion value."
  (let ((*current-realm* realm))
    (with-js-floats (run (compile-toplevel source) (realm-global-env realm) (realm-global realm)))))

(defun invoke (realm fn this args)
  "Call a JS function from the host (event handlers, timers)."
  (let ((*current-realm* realm)) (with-js-floats (js-call fn this args))))

(defun make-host-object (realm &key get set has delete own-keys call (proto :object))
  "A JS object whose internal methods are CL closures — the binding primitive.
   weft backs document/element/style with these and hangs reflow on the SET trap.
   Trap signatures: get (o key receiver), set (o key v receiver), has (o key),
   delete (o key), own-keys (o), call (this args)."
  (let ((*current-realm* realm) (internal '()))
    (when get (setf (getf internal :get) get))
    (when set (setf (getf internal :set) set))
    (when has (setf (getf internal :has) has))
    (when delete (setf (getf internal :delete) delete))
    (when own-keys (setf (getf internal :own-keys) own-keys))
    (make-object :proto (if (eq proto :object) (%obj-proto) proto) :internal internal :call call)))

;;; ---- a minimal slice of intrinsics (the rest = the library) ----
(defun install-intrinsics (realm)
  (flet ((meth (proto name fn &optional (len 0))
           (put proto name (native-function realm name fn len) :enumerable nil)))
    (let ((op (realm-object-proto realm)))
      (meth op "hasOwnProperty"
            (lambda (this args) (js-bool (and (js-object-p this)
                                              (nth-value 1 (gethash (prop-key (or (first args) *undefined*))
                                                                    (js-object-props this)))))))
      (meth op "toString" (lambda (this args) (declare (ignore args this)) "[object Object]")))
    (let ((ap (realm-array-proto realm)))
      (meth ap "push"
            (lambda (this args)
              (let ((len (truncate (to-number (js-get this "length")))))
                (dolist (a args) (js-set this (princ-to-string len) a) (incf len))
                (js-set this "length" (float len 1d0)) (float len 1d0))))
      (meth ap "join"
            (lambda (this args)
              (let ((sep (if (and args (not (js-undefined-p (first args)))) (to-string (first args)) ","))
                    (len (truncate (to-number (js-get this "length")))))
                (with-output-to-string (s)
                  (dotimes (i len) (when (plusp i) (write-string sep s))
                    (let ((v (js-get this (princ-to-string i))))
                      (unless (js-null-or-undef v) (write-string (to-string v) s)))))))))
    ;; Math
    (let ((math (make-object :proto (realm-object-proto realm))))
      (put math "PI" pi)
      (macrolet ((m1 (name fn) `(meth math ,name (lambda (this args) (declare (ignore this))
                                                   (with-js-floats (float (,fn (to-number (or (first args) *undefined*))) 1d0))))))
        (m1 "abs" abs) (m1 "floor" ffloor) (m1 "ceil" fceiling) (m1 "round" fround) (m1 "sqrt" sqrt))
      (meth math "max" (lambda (this args) (declare (ignore this))
                         (if args (with-js-floats (reduce #'max (mapcar #'to-number args))) *-inf*)))
      (meth math "min" (lambda (this args) (declare (ignore this))
                         (if args (with-js-floats (reduce #'min (mapcar #'to-number args))) *inf*)))
      (meth math "pow" (lambda (this args) (declare (ignore this))
                         (with-js-floats (float (expt (to-number (first args)) (to-number (second args))) 1d0))))
      (define-global realm "Math" math))
    ;; console.log
    (let ((console (make-object :proto (realm-object-proto realm))))
      (meth console "log" (lambda (this args) (declare (ignore this))
                            (format t "~&~{~a~^ ~}~%" (mapcar #'to-string args)) *undefined*))
      (define-global realm "console" console))))
