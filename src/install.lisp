;;;; install.lisp — write a resolved tree to disk, and write down exactly what was written.
;;;;
;;;; ============================================================================================
;;;; EVERY BYTE IS VERIFIED BEFORE IT REACHES THE FILESYSTEM
;;;; ============================================================================================
;;;;
;;;; FETCH-PACKAGE has already refused anything whose hash does not match what the registry
;;;; published, and cram's tar reader has already refused any entry name that would escape its
;;;; destination.  Neither check is optional and neither has a flag.  What is left here is the
;;;; boring part -- create directories, write files -- and the boring part is where an installer
;;;; usually grows its own path handling and its own second-guessing of the first two.  It does
;;;; not: the only path arithmetic below is joining a name cram already declared safe to a root.
;;;;
;;;; npm tarballs wrap everything in a single top directory, conventionally `package/`.  That
;;;; prefix is stripped, and it is stripped by taking whatever the FIRST component actually is
;;;; rather than by assuming the convention -- a handful of old packages use a different name, and
;;;; assuming would silently install `package/index.js` as a literal subdirectory.
;;;;
;;;; ============================================================================================
;;;; THE LOCKFILE PINS BYTES, NOT VERSIONS
;;;; ============================================================================================
;;;;
;;;; A version number is a label the registry can move; the integrity hash is the bytes.  So the
;;;; lockfile records the hash, the resolved URL, and the tree POSITION of every package -- the
;;;; position because a tree is a claim about where files sit, and two different layouts of the
;;;; same version set are two different programs.  It is written sorted, so a re-resolve that
;;;; changes nothing produces a byte-identical file and a diff means something changed.

(in-package #:shuttle)

(defun %ensure-dir (path) (ensure-directories-exist path) path)

(defun %strip-top-component (name)
  "`package/index.js` -> `index.js`.  NIL if NAME has no directory part."
  (let ((slash (position #\/ name)))
    (and slash (< (1+ slash) (length name)) (subseq name (1+ slash)))))

(defun %write-file (root relative bytes)
  (let ((path (merge-pathnames relative (pathname root))))
    (%ensure-dir (make-pathname :directory (pathname-directory path)
                                :device (pathname-device path) :host (pathname-host path)))
    (with-open-file (s path :direction :output :element-type '(unsigned-byte 8)
                            :if-exists :supersede :if-does-not-exist :create)
      (write-sequence bytes s))
    path))

(defun install-node (node root)
  "Fetch, verify and unpack one NODE beneath ROOT.  Returns the number of files written."
  (let* ((r (node-resolved node))
         (tar (fetch-package r))                 ; verified, or it signalled
         (entries (cram:tar-extract tar))        ; unsafe names refused, or it signalled
         (dir (format nil "~a/~a/" root (node-path-string node)))
         (written 0))
    (dolist (e entries)
      (let ((rel (%strip-top-component (car e))))
        (when rel
          (%write-file dir rel (cdr e))
          (incf written))))
    written))

(defun install-tree (root-deps &key (into "node_modules-shuttle") (progress t))
  "Resolve ROOT-DEPS, verify and unpack every package under INTO, and return (VALUES TREE COUNT).

Refuses to write anything if the resolved tree does not check out: an installer that lays down a
tree it knows is broken has done worse than nothing, because the failure then surfaces as a
confusing import error somewhere else entirely."
  (multiple-value-bind (tree n) (resolve-tree root-deps :progress progress)
    (let ((bad (tree-violations tree)))
      (when bad
        (error 'registry-error
               :text (format nil "the resolved tree does not satisfy itself; nothing was ~
written:~%~{  ~{~a needs ~a@~a, would find ~a~}~%~}" bad)))
      (%ensure-dir (pathname (format nil "~a/" into)))
      (let ((files 0))
        (dolist (node (tree-nodes tree))
          (incf files (install-node node into))
          (when progress
            (format t "~&  unpacked ~a@~a~%" (node-name node)
                    (resolved-version (node-resolved node)))))
        (values tree n files)))))

(defun write-lockfile (tree path &key (root-deps '()))
  "Write a deterministic lockfile describing TREE.

Sorted by tree position, so re-resolving an unchanged dependency set produces an identical file.
JSON because a lockfile that only one program can read is a private note, not a lock."
  (with-open-file (s path :direction :output :if-exists :supersede :external-format :utf-8)
    (format s "{~%  \"lockfileVersion\": 1,~%  \"comment\": \"written by shuttle; ~
integrity pins the BYTES, position pins the tree\",~%  \"root\": {~%")
    (let ((sorted (sort (copy-list root-deps) #'string< :key #'car)))
      (loop for (name . range) in sorted for i from 0
            do (format s "    ~s: ~s~:[~;,~]~%" name range (< (1+ i) (length sorted)))))
    (format s "  },~%  \"packages\": {~%")
    (let ((nodes (sort (copy-list (tree-nodes tree)) #'string< :key #'node-path-string)))
      (loop for node in nodes for i from 0
            for r = (node-resolved node)
            do (format s "    ~s: {~%      \"version\": ~s,~%      \"resolved\": ~s,~%      ~
\"integrity\": ~s,~%      \"algorithm\": ~s~%    }~:[~;,~]~%"
                       (node-path-string node) (resolved-version r) (resolved-tarball r)
                       (resolved-integrity r) (string-downcase (symbol-name (resolved-algorithm r)))
                       (< (1+ i) (length nodes)))))
    (format s "  }~%}~%"))
  path)

;;; ---- reading a lockfile back --------------------------------------------------------------
;;;
;;; A lockfile you cannot install FROM is a receipt, not a lock.  The point of writing one is that
;;; a later install reproduces the same bytes without asking the registry what `^1.2.3` means
;;; today -- so this reads it back, and the install path prefers it whenever it still covers what
;;; the project declares.

(defun %lock-json (path)
  (unless *json-realm* (setf *json-realm* (make-realm)))
  (define-global *json-realm* "__locktext" (slurp-file path))
  (eval-script *json-realm* "JSON.parse(__locktext)"))

(defun read-lockfile (path)
  "Reconstruct the tree recorded in PATH.  Returns (VALUES ROOT-NODE ROOT-DEPS).

Rebuilt from the recorded POSITIONS, shortest path first, so a parent always exists before the
child that nests inside it."
  (let* ((json (%lock-json path))
         (packages (jsref json "packages"))
         (root (make-instance 'node))
         (deps '()))
    (let ((rd (jsref json "root")))
      (when rd
        (dolist (k (remove-if-not #'stringp (ordinary-own-keys rd)))
          (push (cons k (jsstr (jsref rd k))) deps))))
    (unless packages (%reg-fail "~a: no `packages` section" path))
    (let ((paths (sort (remove-if-not #'stringp (ordinary-own-keys packages))
                       #'< :key (lambda (p) (count #\/ p)))))
      (dolist (p paths)
        (let* ((entry (jsref packages p))
               ;; "node_modules/a/node_modules/@scope/b" -> the names, in order
               (names (let ((acc '()) (parts (%split p #\/)))
                        (loop while parts
                              do (let ((seg (pop parts)))
                                   (when (string= seg "node_modules")
                                     (let ((n (pop parts)))
                                       (when (and n (plusp (length n)) (char= (char n 0) #\@))
                                         (setf n (concatenate 'string n "/" (pop parts))))
                                       (push n acc)))))
                        (nreverse acc)))
               (parent root))
          (dolist (n (butlast names))
            (setf parent (or (gethash n (node-children parent))
                             (%reg-fail "~a: ~s nests inside ~s, which the lockfile does not list"
                                        path p n))))
          (let ((leaf (car (last names))))
            (setf (gethash leaf (node-children parent))
                  (make-instance 'node :name leaf :parent parent
                                 :resolved (make-instance 'resolved
                                             :name leaf
                                             :version (jsstr (jsref entry "version"))
                                             :tarball (jsstr (jsref entry "resolved"))
                                             :integrity (jsstr (jsref entry "integrity"))
                                             :algorithm (if (equal (jsstr (jsref entry "algorithm"))
                                                                   "sha1")
                                                            :sha1 :sha512))))))))
    (values root (nreverse deps))))

(defun lock-covers-p (root declared)
  "Does the locked tree still satisfy what the project DECLARES?

A lockfile is only usable while it agrees with package.json; when someone widens or changes a
range, the honest answer is to re-resolve rather than install a version nobody asked for any more."
  (every (lambda (d)
           (let ((hit (gethash (car d) (node-children root))))
             (and hit (semver-satisfies-p (resolved-version (node-resolved hit)) (cdr d)))))
         declared))

(defun install-locked (root into &key (progress t))
  "Fetch, verify and unpack exactly what the lockfile pinned.  Returns the file count."
  (let ((files 0))
    (dolist (node (tree-nodes root))
      (incf files (install-node node into))
      (when progress
        (format t "~&  ~a@~a~%" (node-name node) (resolved-version (node-resolved node)))))
    files))

(defun project-dependencies (package-json &key (dev t))
  "What a project declares: `dependencies`, plus `devDependencies` unless :DEV is NIL.

DEV DEPENDENCIES BELONG TO THE ROOT ONLY.  They are the tools a project is built and tested with,
and they are emphatically not part of what it means to USE that project -- so they are read here,
from the package.json in front of us, and never followed for anything fetched from the registry.
A resolver that treated a dependency's devDependencies as its own would install a test runner for
every package in the tree.

Where a name appears in both, `dependencies` wins: it is the stronger claim, and installing the
dev range over it would ship a version the runtime dependency did not ask for."
  (let* ((json (parse-json-file package-json))
         (deps (manifest-dependencies json))
         (devs (and dev (manifest-dependencies json :field "devDependencies"))))
    (append deps (remove-if (lambda (d) (assoc (car d) deps :test #'string=)) devs))))


;;; ---- writing a dependency back into package.json --------------------------------------------

(defun save-dependencies (package-json additions &key (field "dependencies"))
  "Merge ADDITIONS -- an alist of (NAME . RANGE) -- into PACKAGE-JSON and rewrite it.

`shuttle install foo` has to record that the project now depends on foo, or the next install
forgets.  The file is re-serialised through the engine's own JSON.stringify with two-space
indentation, which is what npm writes, so a project that uses both does not get a whole-file diff
every time it changes tools.

Insertion order is preserved by parse and by stringify alike, so an existing file keeps its shape
and a genuinely new key lands at the end -- a rewrite that reordered a package.json would make
every install look like a large change in review."
  (unless *json-realm* (setf *json-realm* (make-realm)))
  (define-global *json-realm* "__pj" (slurp-file package-json))
  (define-global *json-realm* "__field" field)
  (define-global *json-realm* "__adds"
    (let ((pairs (with-output-to-string (o)
                   (format o "[")
                   (loop for (n . r) in additions for i from 0
                         do (format o "~:[~;,~][~s,~s]" (plusp i) n r))
                   (format o "]"))))
      pairs))
  (let ((text (to-string
               (eval-script *json-realm* "
(function () {
  var pj = JSON.parse(__pj);
  var adds = JSON.parse(__adds);
  if (!pj[__field]) pj[__field] = {};
  for (var i = 0; i < adds.length; i++) pj[__field][adds[i][0]] = adds[i][1];
  // Sorted, because npm sorts these and an unsorted rewrite would churn the diff.
  var keys = Object.keys(pj[__field]).sort();
  var sorted = {};
  for (var j = 0; j < keys.length; j++) sorted[keys[j]] = pj[__field][keys[j]];
  pj[__field] = sorted;
  return JSON.stringify(pj, null, 2) + \"\\n\";
})()"))))
    (with-open-file (s package-json :direction :output :if-exists :supersede
                                    :external-format :utf-8)
      (write-string text s))
    package-json))

(defun save-range-for (spec-range resolved-version)
  "What to record in package.json for a package the user named.

A RANGE the user typed is kept verbatim -- `^5`, `>=2 <4`, `1.x` are all things they meant.  A
bare name, or an exact VERSION, becomes `^version`: that is what npm writes, and writing the exact
version instead would pin the project to a patch release nobody asked to be pinned to.  The
distinction is whether the spec parses as a single version, not whether it contains punctuation."
  (cond ((null resolved-version) (or spec-range "*"))
        ((or (null spec-range) (string= spec-range "*")) (format nil "^~a" resolved-version))
        ((parse-semver spec-range) (format nil "^~a" resolved-version))   ; an exact version
        (t spec-range)))
