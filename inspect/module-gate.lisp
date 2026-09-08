;;;; module-gate.lisp — every ModuleItem form, parsed, with the static tables it yields.
;;;;
;;;; The oracle for the RUNTIME half of modules is test262, which shuttle skips.  The oracle for
;;;; the STATIC half is this file plus the real world: inspect/module-corpus.sh parses the whole
;;;; nostr-tools + @noble + @scure dependency tree, which is the actual thing the bundler has to
;;;; read.  A form that parses here and dies there is the interesting case, so run both.
;;;;
;;;; Run:  sbcl --script inspect/module-gate.lisp
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*)))
      asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle")))
(in-package #:shuttle)
(defvar *bad* 0)
(defun try (label src)
  (handler-case
      (let ((m (parse-module src)))
        (format t "~&  ok   ~22a req=~s imp=~s exp=~s~%" label (module-requests m)
                (mapcar (lambda (e) (list (entry-import-name e) (entry-local-name e))) (module-imports m))
                (mapcar (lambda (e) (list (entry-export-name e)
                                          (or (entry-local-name e) (entry-import-name e))))
                        (module-exports m))))
    (error (e) (incf *bad*)
      (format t "~&  FAIL ~22a ~a~%" label
              (let ((s (princ-to-string e))) (subseq s 0 (min 70 (length s))))))))
(try "side-effect"        "import \"m\";")
(try "default"            "import d from \"m\";")
(try "namespace"          "import * as ns from \"m\";")
(try "named"              "import {a, b as c} from \"m\";")
(try "default+named"      "import d, {a} from \"m\";")
(try "default+ns"         "import d, * as ns from \"m\";")
(try "string name"        "import {\"a-b\" as ab} from \"m\";")
(try "export const"       "export const x = 1, y = 2;")
(try "export destructure" "export const {a, b: [c]} = o;")
(try "export function"    "export function f(){}")
(try "export class"       "export class C {}")
;; the names have to EXIST: `export {a}` with no declaration of a is an early SyntaxError, which
;; this fixture was quietly relying on not being checked.
(try "export named"       "const a = 1, b = 2; export {a, b as c};")
(try "export re-export"   "export {a as b} from \"m\";")
(try "export star"        "export * from \"m\";")
(try "export star as"     "export * as ns from \"m\";")
(try "export default"     "export default 1 + 2;")
(try "default anon fn"    "export default function(){};")
(try "default class"      "export default class {};")
(try "dynamic import"     "const p = import(\"m\");")
(try "import.meta"        "const u = import.meta.url;")
(format t "~&~%~[all forms parsed~:;~:*~d FAILED~]~%" *bad*)
(sb-ext:exit :code (if (zerop *bad*) 0 1))
