#!/usr/bin/env bash
# Batched test262 runner: each slice runs in its own SBCL so a fatal condition
# (heap/stack exhaustion) kills only that slice. Aggregates all slices into a
# headline + per-area table. Usage: SHUTTLE_TEST262=<checkout> inspect/run262.sh [slice_size]
set -u
cd "$(dirname "$0")/.."
: "${SHUTTLE_TEST262:=$PWD/test262-full}"; export SHUTTLE_TEST262
SLICE="${1:-1000}"
OUT="/tmp/slice-results.$$"; : > "$OUT"; export SHUTTLE_SLICE_OUT="$OUT"
SBCL=(sbcl --control-stack-size 256 --dynamic-space-size 4096 --script inspect/test262-slice.lisp)

# total runnable file count (fixtures excluded)
TOTAL=$(find "$SHUTTLE_TEST262/test" -name '*.js' ! -name '*_FIXTURE*' | wc -l)
echo "corpus: $TOTAL files, slice size $SLICE"
start=0; crashed=0
while [ "$start" -lt "$TOTAL" ]; do
  # `grep -c` already prints 0 when nothing matches -- but it EXITS 1, so a `|| echo 0` appended a
  # SECOND line and the count became "0\n0".  `[` then failed with "integer expression expected"
  # and the comparison below evaluated false, so a slice that died on the first iteration was
  # never counted as crashed and the headline silently became a floor instead of a measurement.
  # That is the exact failure this script exists to prevent.
  before=$(grep -c '^SLICE' "$OUT" 2>/dev/null); before=${before:-0}
  SHUTTLE_SLICE="$start:$SLICE" "${SBCL[@]}" >/dev/null 2>>"/tmp/run262.err.$$"
  after=$(grep -c '^SLICE' "$OUT" 2>/dev/null); after=${after:-0}
  if [ "$after" -le "$before" ]; then
    echo "  slice $start:$SLICE CRASHED at $(cat /tmp/cur262 2>/dev/null) — recording 0, continuing"
    crashed=$((crashed+1))
  fi
  start=$((start+SLICE))
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
