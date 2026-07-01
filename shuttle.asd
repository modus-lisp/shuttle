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
                             (:file "regex")
                             ;; built-in method groups (one file per group)
                             (:module "builtins" :serial t
                              :components ((:file "array-iteration")
                                           (:file "array-mutators")
                                           (:file "array-search")
                                           (:file "array-transform")
                                           (:file "array-immutable")
                                           (:file "json")
                                           (:file "math-extra")
                                           (:file "number-methods")
                                           (:file "string-methods")
                                           (:file "map-set")
                                           (:file "weak")
                                           (:file "object-extras")
                                           (:file "date")
                                           (:file "regexp")
                                           (:file "string-regex")
                                           (:file "iterator")
                                           (:file "arraybuffer")
                                           (:file "typedarray")
                                           (:file "dataview")
                                           (:file "proxy")
                                           (:file "global-funcs")))))))
