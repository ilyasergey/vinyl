#!/usr/bin/env bash
# regress.sh -- detector selftest. Replays each filed reproducer through the
# target that detects it, at FUZZ_STRICT=2, and asserts the detector ABORTS
# (a nonzero exit = the strict-gated abort path fired). A detector that stops
# firing on its own witness is a silent regression -- exactly the "the target
# exists but its abort is unreachable" failure the review round found. Run from
# fuzz/ after `make`.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
fail=0

# Each strict-gated abort detector must fire on a stream that exhibits its class.
# libFuzzer run with a single file argument executes that unit once; an abort()
# makes it exit nonzero.
check() {  # target  witness  what
  local t="$1" w="$2" what="$3"
  [ -x "build/bin/$t.fuzz" ] || { echo "FAIL: build/bin/$t.fuzz not built"; fail=1; return; }
  [ -f "$w" ] || { echo "FAIL: witness $w missing"; fail=1; return; }
  FUZZ_STRICT=2 timeout 60 "build/bin/$t.fuzz" "$w" >/dev/null 2>&1
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "PASS: $t aborts under strict on $(basename "$w") -- $what"
  else
    echo "FAIL: $t did NOT abort on $(basename "$w") -- $what detector regressed"
    fail=1
  fi
}

echo "== detector selftest (strict-mode abort on the filed witnesses) =="
check fz_self_consistent       findings/channel-truncation-CONFIRMED/repro.flac \
      "decoded channel count != STREAMINFO (channel truncation)"
check fz_streaminfo_contradict findings/samplerate-zero-CONFIRMED/repro.flac \
      "sample rate 0 accepted with audio (RFC 9639 9.1.7)"

# The encoder stack overflow is a resource MEASUREMENT (no in-band abort target);
# its regression guard is the measured threshold, not a strict abort.
echo "note: encoder-stack-overflow is measured by tools/stack_probe.sh (not a strict-abort detector)"

[ "$fail" -eq 0 ] && echo "REGRESS: ALL DETECTORS FIRE" || echo "REGRESS: FAILURES ABOVE"
exit "$fail"
