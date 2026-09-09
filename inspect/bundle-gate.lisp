;;;; bundle-gate.lisp — build a module graph, bundle it, and RUN the bundle.
;;;;
;;;; The bundler's output is a plain script, which means shuttle can execute it: the gate does not
;;;; need a browser to find out whether the emitted program means what the modules meant.  It
;;;; builds a fixture graph covering every shape the emitter has a branch for, bundles it, evals
;;;; the result, and reads the answers out of the entry's exports.
;;;;
;;;; Run:  sbcl --script inspect/bundle-gate.lisp

(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*)))
      asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle/bundle")))
(in-package #:shuttle)

;; NOTE: this file is IN-PACKAGE SHUTTLE so it can reach the internals, which means every helper
;; defined here can shadow one of the engine's own.  `put` did exactly that -- shuttle installs
;; properties with PUT, so a fixture-writing helper of that name broke MAKE-REALM from underneath
;; INSTALL-SYMBOLS.  Helpers here are prefixed.
(defvar *fails* 0)
(defun ok (name p &optional detail)
  (format t "~&  ~:[FAIL~;ok  ~] ~a~@[   ~a~]~%" p name detail)
  (unless p (incf *fails*)))

(defparameter *dir* "/tmp/shuttle-bundle-fixture/")

(defun put-file (name text)
  (with-open-file (s (concatenate 'string *dir* name) :direction :output
                                                      :if-exists :supersede :external-format :utf-8)
    (write-string text s)))

(ensure-directories-exist *dir*)

;;; ---- the fixture: one file per emitter branch ----------------------------------------------

;; A default export that is a NAMED function declaration.  It binds its name in module scope as
;; well as exporting it, and calling it locally is the shape that caught the emitter treating it
;; as a function expression -- whose name is visible only inside its own body.
(put-file "named-default.js" "
export default function makeTable() { return 41; }
export const built = makeTable() + 1;
")

;; An anonymous default, which really does need a synthesised local.
(put-file "anon-default.js" "export default function () { return 'anon'; };")

;; A LIVE binding: exported with `let` and reassigned after evaluation, from a function the
;; importer calls.  An importer holding a snapshot sees 1 forever.
(put-file "live.js" "
export let n = 1;
export function bump() { n = n + 1; }
export const frozen = 100;
")

;; Re-exports, both named and star, plus `export * as`.
(put-file "leaf.js" "export const x = 'x'; export const y = 'y';")
(put-file "reexport.js" "
export { x as renamedX } from './leaf.js';
export * from './leaf.js';
export * as everything from './leaf.js';
")

;; Ordinary shapes: const/let/function/class, and a local rename on the way out.
(put-file "shapes.js" "
export const K = 7;
const hidden = 'h';
export { hidden as shown };
export class Thing { who() { return 'thing'; } }
export const { d1, d2 } = { d1: 'd1', d2: 'd2' };
")

(put-file "entry.mjs" "
import makeTable, { built } from './named-default.js';
import anon from './anon-default.js';
import { n, bump, frozen } from './live.js';
import * as re from './reexport.js';
import { K, shown, Thing, d1, d2 } from './shapes.js';

bump();
bump();

export const answers = {
  named_default_call: makeTable(),
  named_default_local: built,
  anon_default: anon(),
  live_after_two_bumps: n,
  const_export: frozen,
  reexport_renamed: re.renamedX,
  reexport_star: re.x + re.y,
  reexport_star_as: re.everything.y,
  plain_const: K,
  local_rename: shown,
  class_method: new Thing().who(),
  destructured: d1 + d2
};
")

;;; ---- bundle, then run it -------------------------------------------------------------------

(format t "~&~%== the bundler ==~%")

;; Run the fixture's answers out of a bundle, so the SAME twelve checks can be pointed at the
;; minified output as at the plain one.  Minification is a source-to-source rewrite of a program
;; this gate already knows the right answers for, which makes running it here nearly free -- and
;; it is an EXECUTION check, which the corpus-wide AST gate deliberately is not.
(defun check-bundle (out label)
  (let* ((realm (make-realm))
         (val (handler-case (eval-script realm (format nil "var __out = ~a; __out.answers" out))
                (error (e) (format t "~&  FAIL running the ~a bundle: ~a~%" label e) (incf *fails*) nil))))
    (when val
      (flet ((got (k) (let ((v (js-get val k))) (if (js-undefined-p v) :missing v)))
             (num= (a b) (and (numberp b) (= a b))))   ; a JS number arrives as a double
          (ok "a NAMED default export is a declaration, so the module can call it"
              (num= 41 (got "named_default_call")) (got "named_default_call"))
          (ok "and its name is bound locally too — the crc-table shape"
              (num= 42 (got "named_default_local")) (got "named_default_local"))
          (ok "an ANONYMOUS default still gets a local to hang off"
              (equal "anon" (got "anon_default")) (got "anon_default"))
          (ok "a LIVE export reaches its importer: two bumps are visible"
              (num= 3 (got "live_after_two_bumps")) (got "live_after_two_bumps"))
          (ok "while a const export is snapshotted, which is all it can be"
              (num= 100 (got "const_export")) (got "const_export"))
          (ok "a renaming re-export carries the new name"
              (equal "x" (got "reexport_renamed")) (got "reexport_renamed"))
          (ok "export * forwards every name" (equal "xy" (got "reexport_star")) (got "reexport_star"))
          (ok "export * as binds the namespace"
              (equal "y" (got "reexport_star_as")) (got "reexport_star_as"))
          (ok "a plain const export" (num= 7 (got "plain_const")) (got "plain_const"))
          (ok "a local renamed on the way out" (equal "h" (got "local_rename")) (got "local_rename"))
          (ok "an exported class keeps its methods"
              (equal "thing" (got "class_method")) (got "class_method"))
        (ok "a destructuring export exports both names"
            (equal "d1d2" (got "destructured")) (got "destructured"))))))

(let ((out nil))
  (handler-case
      (setf out (bundle (concatenate 'string *dir* "entry.mjs") :id-root (pathname *dir*)))
    (error (e) (format t "~&  FAIL bundling: ~a~%" e) (incf *fails*)))
  (when out
    (ok "the bundle is one script, and it parses" (plusp (length out))
        (format nil "~a bytes" (length out)))
    (check-bundle out "plain")

    ;; The same graph, minified.  A whitespace minifier that broke one of these would be breaking
    ;; a program whose correct answers are written down two screens up.
    (format t "~&~%-- and again, minified --~%")
    (let ((small (handler-case (bundle (concatenate 'string *dir* "entry.mjs")
                                       :id-root (pathname *dir*) :minify t)
                   (error (e) (format t "~&  FAIL minifying: ~a~%" e) (incf *fails*) nil))))
      (when small
        (ok "minifying the bundle makes it smaller and it still parses"
            (< (length small) (length out))
            (format nil "~d -> ~d bytes (~,1f%)" (length out) (length small)
                    (* 100.0 (/ (length small) (length out)))))
        (check-bundle small "minified")))))

;;; ---- and the refusals, which are half the design --------------------------------------------

(format t "~&~%-- what it refuses rather than guesses at --~%")

(put-file "cyc-a.js" "import { b } from './cyc-b.js'; export const a = 'a' + b;")
(put-file "cyc-b.js" "import { a } from './cyc-a.js'; export const b = 'b';")
(ok "a cycle is named, not silently ordered"
    (handler-case (progn (bundle (concatenate 'string *dir* "cyc-a.js") :id-root (pathname *dir*)) nil)
      (bundle-error (e) (search "cycle" (bundle-error-text e)))))

(put-file "missing.js" "import x from './there-is-no-such-file.js'; export default x;")
(ok "an unresolvable specifier says which one"
    (handler-case (progn (bundle (concatenate 'string *dir* "missing.js") :id-root (pathname *dir*)) nil)
      (bundle-error (e) (search "cannot resolve" (bundle-error-text e)))))

(format t "~&~%== ~[all checks passed~:;~:*~d FAILED~] ==~%~%" *fails*)
(sb-ext:exit :code (if (zerop *fails*) 0 1))
