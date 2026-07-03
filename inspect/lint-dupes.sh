#!/usr/bin/env bash
# Duplicate top-level defun detector: everything lives in ONE package (#:shuttle),
# so a same-named defun in a later-loaded file silently clobbers the earlier one
# (this broke Temporal rounding + DisposableStack once). Known-intentional
# overrides are whitelisted. Exit 1 on new duplicates.
cd "$(dirname "$0")/.."
WHITELIST='^(make-array-iterator|make-string-iterator|js-mod|iterable-to-list|add-iso-date|temporal-branded-object-p)$'
dupes=$(grep -h "^(defun " src/*.lisp src/builtins/*.lisp | sed 's/.*(defun \([^ (]*\).*/\1/' | sort | uniq -d | grep -Ev "$WHITELIST")
if [ -n "$dupes" ]; then echo "DUPLICATE top-level defuns (later file clobbers earlier):"; echo "$dupes" | sed 's/^/  /'; exit 1; fi
echo "no unexpected duplicate defuns"
