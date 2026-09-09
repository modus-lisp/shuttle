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
