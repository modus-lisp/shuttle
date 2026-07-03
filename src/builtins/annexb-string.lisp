;;;; builtins/annexb-string.lisp — Annex B String.prototype HTML methods
;;;; (anchor/big/blink/bold/fixed/fontcolor/fontsize/italics/link/small/strike/
;;;; sub/sup). See array-iteration.lisp for the convention.
(in-package #:shuttle)

(defun %create-html (s tag attribute value)
  "CreateHTML(string, tag, attribute, value): wrap S in an HTML tag.
   S is already the ToString'd receiver. ATTRIBUTE is a CL string ('' -> none).
   VALUE is a JS value; if ATTRIBUTE is non-empty, ToString(VALUE) with each
   `\"` replaced by `&quot;` is used as the attribute value."
  (let ((p (concatenate 'string "<" tag)))
    (when (plusp (length attribute))
      (let* ((v (to-string value))
             (escaped (with-output-to-string (out)
                        (loop for c across v do
                          (if (char= c #\") (write-string "&quot;" out) (write-char c out))))))
        (setf p (concatenate 'string p " " attribute "=\"" escaped "\""))))
    (concatenate 'string p ">" s "</" tag ">")))

(defun install-annexb-string (realm)
  (let ((sp (realm-string-proto realm)))
    ;; attribute-taking methods: .length 1
    (macrolet ((html-attr (name tag attribute)
                 `(def-method realm sp ,name 1 (this args)
                    (require-object-coercible this)
                    (%create-html (to-string this) ,tag ,attribute (arg 0 args))))
               (html-noattr (name tag)
                 `(def-method realm sp ,name 0 (this args)
                    (require-object-coercible this)
                    (%create-html (to-string this) ,tag "" *undefined*))))
      (html-attr "anchor" "a" "name")
      (html-attr "link" "a" "href")
      (html-attr "fontcolor" "font" "color")
      (html-attr "fontsize" "font" "size")
      (html-noattr "big" "big")
      (html-noattr "blink" "blink")
      (html-noattr "bold" "b")
      (html-noattr "fixed" "tt")
      (html-noattr "italics" "i")
      (html-noattr "small" "small")
      (html-noattr "strike" "strike")
      (html-noattr "sub" "sub")
      (html-noattr "sup" "sup"))))

(register-builtin-installer 'install-annexb-string)
