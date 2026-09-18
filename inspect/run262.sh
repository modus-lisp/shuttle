#!/usr/bin/env bash
# Batched test262 runner: each slice runs in its own SBCL so a fatal condition
# (heap/stack exhaustion) kills only that slice. Aggregates all slices into a
# headline + per-area table. Usage: SHUTTLE_TEST262=<checkout> inspect/run262.sh [slice_size]
set -u
cd "$(dirname "$0")/.."
: "${SHUTTLE_TEST262:=$PWD/test262-full}"; export SHUTTLE_TEST262
SLICE="${1:-1000}"
# ONE SBCL PER SLICE, AND AS MANY AT ONCE AS THERE ARE CORES.  The isolation was
# always per-slice -- a heap or stack death costs one slice, not the run -- so the
# slices were already independent, and were being run one at a time on a 116-core
# box.  Sharding them is a scheduling change, not a semantic one.
JOBS="${SHUTTLE_JOBS:-$(nproc)}"
# EACH SLICE GETS ITS OWN RESULT FILE.  Appending to one shared file from N
# concurrent writers is only atomic for small writes on some filesystems, and a
# torn line here would be miscounted silently rather than noticed.
OUTDIR="/tmp/slices.$$"; mkdir -p "$OUTDIR"
OUT="/tmp/slice-results.$$"; : > "$OUT"

TOTAL=$(find "$SHUTTLE_TEST262/test" -name '*.js' ! -name '*_FIXTURE*' | wc -l)
echo "corpus: $TOTAL files, slice size $SLICE, $JOBS parallel"
export SHUTTLE_TEST262 SLICE OUTDIR
seq 0 "$SLICE" $((TOTAL-1)) | \
  xargs -P "$JOBS" -I{} bash -c '
    SHUTTLE_SLICE="{}:$SLICE" SHUTTLE_SLICE_OUT="$OUTDIR/{}.tsv" \
      sbcl --control-stack-size 256 --dynamic-space-size 4096 \
           --script inspect/test262-slice.lisp >/dev/null 2>>"$OUTDIR/{}.err"'

# A slice that produced no SLICE line died: count it and SAY so, rather than
# letting a missing slice quietly turn the headline into a floor.
crashed=0
for start in $(seq 0 "$SLICE" $((TOTAL-1))); do
  f="$OUTDIR/$start.tsv"
  if [ -s "$f" ] && grep -q '^SLICE' "$f"; then
    cat "$f" >> "$OUT"
  else
    echo "  slice $start:$SLICE CRASHED - recording 0, continuing"
    crashed=$((crashed+1))
  fi
done

echo "=== test262 (batched) ==="
awk -F'\t' '
  $1=="AREA"  { split($2,a,"/"); top=a[1]; p[top]+=$3; t[top]+=$4 }
  $1=="SLICE" { TP+=$4; TT+=$5; SK+=$6 }
  END {
    n=asorti(p, keys)
    for (k=1;k<=n;k++){ top=keys[k]; printf "  %6d/%-6d  %5.1f%%  %s\n", p[top], t[top], (t[top]?100*p[top]/t[top]:0), top }
    printf "  ----\n  TOTAL %d/%d  (%.2f%%)   [%d skipped]\n", TP, TT, (TT?100*TP/TT:0), SK
    printf "SUMMARY %d %d\n", TP, TT
  }' "$OUT"
[ "$crashed" -gt 0 ] && echo "($crashed slice(s) crashed and were counted as 0 — headline is a floor)"
cp "$OUT" /tmp/slice-results.last
