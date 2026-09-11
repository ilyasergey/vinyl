#!/usr/bin/env bash
# ci_assertions.sh -- standing conformance/coverage assertions that are
# cheaper than a fuzzer and catch the same regressions. Run from fuzz/ after a
# build. These are ASSERTIONS (non-zero exit on failure), so they belong in CI,
# not in a campaign.
#
#   1. encoder-image corpus is real FLAC: `flac -t` accepts every committed
#      decode/wide + decode/hires seed (D1 -- verifies the generator's streams
#      libFLAC can actually decode, incl. the MD5 the generator writes).
#   2. encode-side float search is reachable: the encode coverage replay must hit
#      the LPC estimator (levinson/partitionSearch), else the encode corpus went
#      stale and the encode-side probes are fuzzing blind.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
fail=0

echo "== 1. encoder-image corpus is libFLAC-decodable (flac -t) =="
command -v flac >/dev/null || { echo "FAIL: flac CLI not found"; exit 1; }
bad=0 n=0
for dir in corpus/decode/wide corpus/decode/hires; do
  [ -d "$dir" ] || continue
  for f in "$dir"/*; do
    [ -f "$f" ] || continue
    n=$((n+1))
    flac -st "$f" >/dev/null 2>&1 || { echo "  REJECT: $f"; bad=$((bad+1)); }
  done
done
if [ "$bad" -gt 0 ]; then
  echo "FAIL: $bad/$n encoder-image seeds rejected by libFLAC"; fail=1
else
  echo "OK: $n/$n encoder-image seeds accepted by libFLAC"
fi

echo "== 2. encode float search is reachable (Heuristics.c coverage on an encode target) =="
# The encoder LPC float search lives in Flac/Native/Heuristics.c (levinson /
# partitionSearch / autocorrF). It is reached only by ENCODING real PCM, which the
# round-trip target fz_roundtrip does over corpus/encode/gen. ci.sh step 7 already
# produced the per-target native report; assert Heuristics.c has non-zero region
# coverage there (a stale/empty encode corpus would leave the float search dark).
RPT=cov/report/latest/fz_roundtrip.native.txt
if [ ! -f "$RPT" ]; then
  # produce it if this script is run standalone (not via ci.sh step 7)
  make --no-print-directory covfuzz >/dev/null 2>&1 || true
  python3 cov/per_target.py fz_roundtrip fz_encode_diff --seeds-only >/dev/null 2>&1 || true
fi
hcov=""
for RPT in cov/report/latest/fz_roundtrip.native.txt cov/report/latest/fz_encode_diff.native.txt; do
  [ -f "$RPT" ] || continue
  # llvm-cov report line: <path/Heuristics.c>  <regions> <missed> <cover%> ...
  # covered regions = regions - missed; assert > 0.
  # llvm-cov strips the common path prefix, so the row may read "Heuristics.c" or
  # ".../Native/Heuristics.c" -- match the basename either way.
  line=$(grep -E "(^|/)Heuristics\.c" "$RPT" || true)
  if [ -n "$line" ]; then
    reg=$(echo "$line" | awk '{print $2}'); miss=$(echo "$line" | awk '{print $3}')
    if [ -n "$reg" ] && [ -n "$miss" ] && [ "$((reg - miss))" -gt 0 ]; then
      hcov="$RPT: $((reg - miss)) covered regions"; break
    fi
  fi
done
if [ -n "$hcov" ]; then
  echo "OK: encoder float search reached (Heuristics.c $hcov)"
else
  echo "FAIL: Heuristics.c float search shows 0 covered regions on encode targets (encode corpus stale?)"; fail=1
fi

echo "== 3. Audio-level encode scales sub-quadratically (paired resource assertion) =="
# The cost half of the paired bound for the recursion/chunking class (scripts/scaling_assert.py):
# double the frame count and require the wall-time growth to stay well under a quadratic's 4x.
# The August "assert exit 0 under a small stack limit" catches the stack half only; a stack fix
# can still be quadratic in time (it was), and the frame chunker's length-test was separately
# quadratic (issue 5). Load-sensitive by nature, so it uses a wide threshold and SKIPS rather
# than fails when it cannot get a usable measurement. Needs the vinyl exe.
VINYL=../.lake/build/bin/vinyl
[ -x "$VINYL" ] || { (cd .. && lake build vinyl >/dev/null 2>&1) || true; }
if [ ! -x "$VINYL" ]; then
  echo "SKIP: vinyl exe not built; scaling assertion not run"
else
  sa_out=$(python3 scripts/scaling_assert.py "$VINYL"); sa_code=$?
  echo "  $sa_out"
  [ "$sa_code" -eq 0 ] || fail=1
fi

[ "$fail" -eq 0 ] && echo "CI-ASSERTIONS: ALL GREEN" || echo "CI-ASSERTIONS: FAILURES ABOVE"
exit "$fail"
