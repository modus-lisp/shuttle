;;;; builtins/string-regex.lisp — String.prototype regex methods (match/matchAll/
;;;; replace/replaceAll/search/split) delegating to RegExp. Uses src/regex.lisp +
;;;; builtins/regexp.lisp.
(in-package #:shuttle)

;;; Dispatch helper implementing GetMethod(obj, sym) + Call semantics:
;;;   - property undefined/null -> method absent -> (values nil nil)
;;;   - property present but not callable -> TypeError (GetMethod step 3)
;;;   - callable -> Call(method, obj, «this-arg, method-args…») -> (values r T)
(defun call-symbol-method (obj sym this-arg &rest method-args)
  (let ((m (js-get obj sym)))
    (cond
      ((js-null-or-undef m) (values nil nil))
      ((js-callable-p m) (values (js-call m obj (cons this-arg method-args)) t))
      (t (js-throw (make-native-error "TypeError" "method is not callable"))))))

(defun regexp-like-p (v)
  "IsRegExp: has @@match truthy, or is a RegExp exotic."
  (and (js-object-p v)
       (let ((m (and *symbol-match* (js-get v *symbol-match*))))
         (if (js-undefined-p m)
             (regexp-object-p v)
             (js-truthy m)))))

(defun install-string-regex (realm)
  (let ((sp (realm-string-proto realm)))
    ;; NOTE: per spec, ToString(this) is performed AFTER the @@symbol dispatch,
    ;; so a poisoned receiver toString isn't observed when the arg handles it.
    ;; ---- match ----
    (def-method realm sp "match" 1 (this args)
      (block done
        (require-object-coercible this)
        (let ((regexp (arg 0 args)))
          (when (js-object-p regexp)
            (multiple-value-bind (r present) (call-symbol-method regexp *symbol-match* this)
              (when present (return-from done r))))
          (let ((s (to-string this))
                (rx (make-regexp-object realm (if (js-undefined-p regexp) "" (to-string regexp)) "")))
            (js-call (js-get rx *symbol-match*) rx (list s))))))
    ;; ---- matchAll ----
    (def-method realm sp "matchAll" 1 (this args)
      (block done
        (require-object-coercible this)
        (let ((regexp (arg 0 args)))
          (when (regexp-like-p regexp)
            (let ((flags (js-get regexp "flags")))
              (require-object-coercible flags)
              (unless (find #\g (to-string flags))
                (js-throw (make-native-error "TypeError" "matchAll must be called with a global RegExp")))))
          (when (js-object-p regexp)
            (multiple-value-bind (r present) (call-symbol-method regexp *symbol-match-all* this)
              (when present (return-from done r))))
          (let ((s (to-string this))
                (rx (make-regexp-object realm (if (js-undefined-p regexp) "" (to-string regexp)) "g")))
            (js-call (js-get rx *symbol-match-all*) rx (list s))))))
    ;; ---- search ----
    (def-method realm sp "search" 1 (this args)
      (block done
        (require-object-coercible this)
        (let ((regexp (arg 0 args)))
          (when (js-object-p regexp)
            (multiple-value-bind (r present) (call-symbol-method regexp *symbol-search* this)
              (when present (return-from done r))))
          (let ((s (to-string this))
                (rx (make-regexp-object realm (if (js-undefined-p regexp) "" (to-string regexp)) "")))
            (js-call (js-get rx *symbol-search*) rx (list s))))))
    ;; ---- split ----
    (def-method realm sp "split" 2 (this args)
      (block done
        (require-object-coercible this)
        (let ((separator (arg 0 args)) (limit (arg 1 args)))
          (when (js-object-p separator)
            (multiple-value-bind (r present) (call-symbol-method separator *symbol-split* this limit)
              (when present (return-from done r))))
          ;; Fallback String.prototype.split (no @@split) — spec order (21.1.3.23):
          ;;   3. S := ToString(O)
          ;;   6. lim := (limit undefined) ? 2^32-1 : ToUint32(limit)
          ;;   7. R := ToString(separator)   <-- BEFORE the lim=0 check
          ;;   8. If lim = 0, return empty array
          ;; (We do the ToString/ToUint32 here rather than in string-split, which
          ;; short-circuits on lim=0 before ToString and clamps instead of doing
          ;; ToUint32 — see core-bug proposal.)
          (let* ((s (to-string this))
                 (lim (if (js-undefined-p limit) #xFFFFFFFF (to-uint32 limit)))
                 (rsep (to-string separator)))     ; must run even when lim=0
            (string-split-plain realm s separator rsep lim)))))
    ;; ---- replace ----
    (def-method realm sp "replace" 2 (this args)
      (block done
        (require-object-coercible this)
        (let ((search-value (arg 0 args)) (replace-value (arg 1 args)))
          (when (js-object-p search-value)
            (multiple-value-bind (r present) (call-symbol-method search-value *symbol-replace* this replace-value)
              (when present (return-from done r))))
          (string-replace-plain realm (to-string this) search-value replace-value nil))))
    ;; ---- replaceAll ----
    (def-method realm sp "replaceAll" 2 (this args)
      (block done
        (require-object-coercible this)
        (let ((search-value (arg 0 args)) (replace-value (arg 1 args)))
          (when (regexp-like-p search-value)
            (let ((flags (js-get search-value "flags")))
              (require-object-coercible flags)
              (unless (find #\g (to-string flags))
                (js-throw (make-native-error "TypeError" "replaceAll must be called with a global RegExp")))))
          (when (js-object-p search-value)
            (multiple-value-bind (r present) (call-symbol-method search-value *symbol-replace* this replace-value)
              (when present (return-from done r))))
          (string-replace-plain realm (to-string this) search-value replace-value t))))))

;;; --- plain (non-regex) split, used when separator has no @@split ---
;;; S / RSEP already coerced (ToString); SEPARATOR is the raw value (to detect
;;; undefined); LIM is the already-ToUint32'd limit.
(defun string-split-plain (realm s separator rsep lim)
  (declare (ignorable realm))
  (cond
    ((zerop lim) (make-array-object '()))
    ((js-undefined-p separator) (make-array-object (list s)))
    (t
     (let ((out '()))
       (if (string= rsep "")
           ;; empty separator: split into individual UTF-16 code units, up to LIM
           (loop for c across s while (< (length out) lim) do (push (string c) out))
           (let ((start 0) (slen (length rsep)))
             (loop
               (let ((p (search rsep s :start2 start)))
                 (cond
                   ((or (null p) (>= (length out) lim))
                    (when (< (length out) lim) (push (subseq s start) out))
                    (return))
                   (t (push (subseq s start p) out)
                      (setf start (+ p slen))))))))
       (make-array-object (nreverse out))))))

;;; --- plain (non-regex) replace, used when searchValue has no @@replace ---
(defun string-replace-plain (realm s search-value replace-value all)
  (declare (ignorable realm))
  (let* ((search-str (to-string search-value))
         (functional (js-callable-p replace-value))
         (rep-str (unless functional (to-string replace-value))))
    (if (not all)
        (let ((pos (search search-str s)))
          (if (null pos) s
              (let ((replacement
                      (if functional
                          (to-string (js-call replace-value *undefined*
                                              (list search-str (float pos 1d0) s)))
                          (get-substitution search-str s pos '() nil rep-str))))
                (concatenate 'string (subseq s 0 pos) replacement (subseq s (+ pos (length search-str)))))))
        (let ((out (make-string-output-stream)) (start 0) (slen (length search-str)))
          (if (zerop slen)
              (progn
                (loop for i from 0 to (length s) do
                  (let ((replacement
                          (if functional
                              (to-string (js-call replace-value *undefined* (list "" (float i 1d0) s)))
                              (get-substitution "" s i '() nil rep-str))))
                    (write-string replacement out)
                    (when (< i (length s)) (write-char (char s i) out))))
                (get-output-stream-string out))
              (progn
                (loop
                  (let ((pos (search search-str s :start2 start)))
                    (if (null pos)
                        (progn (write-string (subseq s start) out) (return))
                        (let ((replacement
                                (if functional
                                    (to-string (js-call replace-value *undefined*
                                                        (list search-str (float pos 1d0) s)))
                                    (get-substitution search-str s pos '() nil rep-str))))
                          (write-string (subseq s start pos) out)
                          (write-string replacement out)
                          (setf start (+ pos slen))))))
                (get-output-stream-string out)))))))

(register-builtin-installer 'install-string-regex)
