;;;; self-test.lisp — exercises the source->bytecode->VM pipeline and the host
;;;; binding seam. A stand-in gate until the test262 runner lands.
;;;;   sbcl --script inspect/self-test.lisp
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*))) asdf:*central-registry*)
(asdf:load-system "shuttle")
(in-package #:shuttle)

(defvar *pass* 0) (defvar *fail* 0)
(defun chk (label src expected &key (test #'=))
  (let* ((realm (make-realm))
         (got (handler-case (eval-script realm src) (error (e) (cons :error (princ-to-string e))))))
    (if (ignore-errors (funcall test got expected)) (incf *pass*)
        (progn (incf *fail*)
               (format t "~&FAIL ~a: ~s~%  got ~s want ~s~%" label src
                       (if (stringp got) got (ignore-errors (to-string got))) expected)))))

(macrolet ((n= (a b) `(and (numberp ,a) (= ,a ,b))))
  (chk "arith"        "1 + 2 * 3" 7d0)
  (chk "precedence"   "(1 + 2) * 3 - 4 / 2" 7d0)
  (chk "concat"       "'foo' + 'bar'" "foobar" :test #'string=)
  (chk "add-coerce"   "1 + '2'" "12" :test #'string=)
  (chk "mul-coerce"   "'3' * 2" 6d0)
  (chk "vars"         "var x = 5; x = x + 1; x" 6d0)
  (chk "compound"     "var x = 10; x += 5; x *= 2; x" 30d0)
  (chk "function"     "function add(a,b){ return a + b; } add(2, 3)" 5d0)
  (chk "closure"      "var c = (function(){ var n = 0; return function(){ return ++n; }; })(); c(); c(); c()" 3d0)
  (chk "arrow"        "var sq = x => x * x; sq(4)" 16d0)
  (chk "recursion"    "function fib(n){ return n < 2 ? n : fib(n-1) + fib(n-2); } fib(10)" 55d0)
  (chk "while-loop"   "var s = 0, i = 0; while (i < 5) { s = s + i; i = i + 1; } s" 10d0)
  (chk "if-else"      "var x = 7; if (x % 2 === 0) { 'even' } else { 'odd' }" "odd" :test #'string=)
  (chk "ternary"      "true && 2 || 3" 2d0)
  (chk "logical-or"   "false || 'fallback'" "fallback" :test #'string=)
  (chk "typeof-num"   "typeof 42" "number" :test #'string=)
  (chk "typeof-undef" "typeof nope" "undefined" :test #'string=)
  (chk "strict-eq"    "1 === 1 && '1' !== 1" *true* :test #'eq)
  (chk "object"       "var o = { a: 1, b: 2 }; o.a + o['b']" 3d0)
  (chk "array"        "var a = [10, 20, 30]; a[1] + a.length" 23d0)
  (chk "array-push"   "var a = [1, 2]; a.push(3); a.push(4); a.length" 4d0)
  (chk "array-join"   "[1, 2, 3].join('-')" "1-2-3" :test #'string=)
  (chk "math"         "Math.max(1, 5, 3) + Math.floor(2.9)" 7d0)
  (chk "new"          "function P(x){ this.x = x; } var p = new P(7); p.x" 7d0)
  (chk "method-this"  "var o = { v: 10, get: function(){ return this.v; } }; o.get()" 10d0))

;; ---- the seam: JS mutating a host object fires a CL "reflow" callback ----
(let* ((realm (make-realm)) (reflows '()) (stored nil))
  (let ((el (make-host-object
             realm
             :get (lambda (o key &optional r) (declare (ignore o r))
                    (if (string= key "textContent") (or stored *undefined*) *undefined*))
             :set (lambda (o key v &optional r) (declare (ignore o r))
                    (when (string= key "textContent")
                      (setf stored (to-string v)) (push stored reflows))  ; <- weft would relayout here
                    *true*))))
    (define-global realm "el" el)
    (eval-script realm "el.textContent = 'hi ' + (1 + 2)")
    (let ((ok (and (equal reflows '("hi 3"))
                   (string= (to-string (eval-script realm "el.textContent")) "hi 3"))))
      (if ok (incf *pass*)
          (progn (incf *fail*) (format t "~&FAIL seam: reflows=~s~%" reflows))))))

(format t "~&~%shuttle self-test: ~d passed, ~d failed~%" *pass* *fail*)
(sb-ext:exit :code (if (zerop *fail*) 0 1))
