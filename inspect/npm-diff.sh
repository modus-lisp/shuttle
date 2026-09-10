#!/usr/bin/env bash
# npm-diff.sh — install the same packages with npm and with shuttle, and diff the trees.
#
# This is the only test that can support the claim "shuttle is npm": not that each piece is
# individually graded, but that the whole thing lands the same FILES IN THE SAME PLACES as the
# implementation it replaces.  A dependency tree is a claim about where files sit, so the
# comparison is over (path, version) pairs — a right version in the wrong directory is a different
# program, and a set-of-versions comparison would call it a pass.
#
# npm runs with --ignore-scripts, because shuttle does not run lifecycle scripts at all and a
# postinstall that writes files would show up as a spurious difference.  --no-audit/--no-fund just
# quieten it.
#
# KNOWN DIFFERENCE: jest@29.7.0 produces 267 packages either way, every dependency resolving in
# both, but npm hoists semver@6.3.1 and camelcase@5.3.1 to the root where shuttle hoists semver@7
# and camelcase@6 (each nesting the other three times over).  Which version wins a hoisted slot is
# decided by which request arrives first, and npm's arborist walks the graph in an order this does
# not reproduce.  Both trees are valid installs; matching it exactly would mean reimplementing
# arborist's traversal.  Recorded here rather than quietly tolerated.
#
#   inspect/npm-diff.sh [package ...]
set -u
HERE=$(cd -- "$(dirname -- "$0")/.." && pwd)
SHUTTLE="$HERE/bin/shuttle"
WORK=${NPM_DIFF_WORK:-/tmp/npm-diff}
PKGS=("$@")
if [ ${#PKGS[@]} -eq 0 ]; then
  PKGS=(left-pad react-dom@18.3.1 nostr-tools@2.15.0 express@4.19.2 chalk@5.3.0 \
        vite@5.2.0 semver@7.6.0 @babel/plugin-transform-runtime@7.24.0 rxjs@7.8.1 \
        eslint-plugin-react-hooks@4.6.0 debug@4.3.4 node-fetch@3.3.2)
fi

# Every package.json under node_modules, as "path<TAB>version", sorted.
tree_of() {
  # Every PACKAGE ROOT: the immediate children of any node_modules, plus one level more for
  # @scope/name.  Enumerating by "find package.json and guess from the path" dropped scoped
  # packages silently, which made a tree look smaller than it was and a real difference look
  # like agreement.
  ( cd "$1" 2>/dev/null || return
    find . -type d -name node_modules 2>/dev/null | while read -r nm; do
      for d in "$nm"/*; do
        [ -d "$d" ] || continue
        case "$(basename "$d")" in
          @*) for sd in "$d"/*; do
                [ -f "$sd/package.json" ] && echo "${sd#./}"
              done ;;
          *) [ -f "$d/package.json" ] && echo "${d#./}" ;;
        esac
      done
    done | while read -r d; do
      v=$(node -e "try{process.stdout.write(require('$PWD/$d/package.json').version||'?')}catch(e){process.stdout.write('?')}" 2>/dev/null)
      printf '%s\t%s\n' "$d" "$v"
    done | sort )
}

rm -rf "$WORK"; mkdir -p "$WORK"
same=0; diffn=0; failed=0
printf '%-46s %8s %8s  %s\n' package npm shuttle result
for spec in "${PKGS[@]}"; do
  slug=$(echo "$spec" | tr '/@.' '___')
  n="$WORK/npm-$slug"; s="$WORK/sh-$slug"
  mkdir -p "$n" "$s"
  ( cd "$n" && echo '{"name":"x","version":"1.0.0"}' > package.json &&
    npm install --ignore-scripts --no-audit --no-fund --silent "$spec" ) >/dev/null 2>&1
  # npm skips an OPTIONAL dependency whose engines.node the RUNNING node does not satisfy.
  # Shuttle has no running node, so for the comparison to be apples-to-apples it is told which
  # node npm is being judged against.  Without this the two disagree about @napi-rs binaries that
  # require node 22 on a box running node 20 -- a difference in the question, not in the answer.
  ( cd "$s" && echo '{"name":"x","version":"1.0.0"}' > package.json &&
    "$SHUTTLE" install --target-node "$(node -v)" "$spec" ) >"$s/.log" 2>&1
  tree_of "$n" > "$WORK/$slug.npm"
  tree_of "$s" > "$WORK/$slug.shuttle"
  ncount=$(wc -l < "$WORK/$slug.npm"); scount=$(wc -l < "$WORK/$slug.shuttle")
  if [ ! -s "$WORK/$slug.shuttle" ]; then
    printf '%-46s %8s %8s  SHUTTLE FAILED: %s\n' "$spec" "$ncount" "$scount" \
      "$(tail -1 "$s/.log" | cut -c1-70)"; failed=$((failed+1)); continue
  fi
  if diff -q "$WORK/$slug.npm" "$WORK/$slug.shuttle" >/dev/null; then
    printf '%-46s %8s %8s  identical\n' "$spec" "$ncount" "$scount"; same=$((same+1))
  else
    d=$(diff "$WORK/$slug.npm" "$WORK/$slug.shuttle" | grep -c '^[<>]')
    printf '%-46s %8s %8s  %s line(s) differ\n' "$spec" "$ncount" "$scount" "$d"
    diffn=$((diffn+1))
  fi
done
echo
echo "identical: $same   differing: $diffn   failed: $failed"
echo "trees in $WORK/*.npm and $WORK/*.shuttle"
[ "$diffn" -eq 0 ] && [ "$failed" -eq 0 ]
