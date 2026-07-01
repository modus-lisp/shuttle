;;;; shuttle.asd — a Lisp-native JavaScript engine.
(asdf:defsystem :shuttle
  :description "A Lisp-native JavaScript engine, clean-room (no FFI): source ->
bytecode -> stack VM, with objects built on dispatchable internal methods (the
host-binding seam a consumer like weft hangs DOM objects + reflow on). Oracle: test262."
  :version "0.0.1" :author "ynniv" :license "MIT"
  :depends-on ()
  :serial t
  :components ((:module "src" :serial t
                :components ((:file "packages") (:file "value") (:file "lex")
                             (:file "parse") (:file "compile") (:file "vm")
                             (:file "realm")
                             ;; built-in method groups (one file per group)
                             (:module "builtins" :serial t
                              :components ((:file "array-iteration")))))))
