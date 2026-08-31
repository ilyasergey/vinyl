#!/usr/bin/env bash
# thread_probes.sh -- probe the Vinyl CLI's thread-flag handling.
#
# Each probe is a distinct check that prints PASS / FAIL / NOTE and is written so
# it can never wedge the machine: every invocation is wrapped in `timeout`, and
# the one probe that could spawn a runaway number of OS threads is additionally
# sandboxed in an isolated subshell with a virtual-memory ulimit and SIGKILL.
#
# Note: pure CLI-argument quirks are LOW value, so they are reported
# as NOTEs (footguns) rather than FAILs unless something actually crashes/hangs.
#
#   VINYL=/path/to/vinyl ./thread_probes.sh
set -uo pipefail

# Derive the repo root from this script's location (fuzz/tools/ -> repo root) so
# the CLI path is not hardcoded to one machine's checkout.
_REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
VINYL="${VINYL:-$_REPO/.lake/build/bin/vinyl}"
FLAC_BIN="${FLAC_BIN:-flac}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pass=0 fail=0 note=0
say() { printf '%-6s %s\n' "$1" "$2"; }
ok()   { say "PASS" "$1"; pass=$((pass + 1)); }
bad()  { say "FAIL" "$1"; fail=$((fail + 1)); }
info() { say "NOTE" "$1"; note=$((note + 1)); }

[ -x "$VINYL" ] || { echo "vinyl binary not found/executable: $VINYL" >&2; exit 3; }

echo "== Vinyl CLI thread-flag probes =="
echo "vinyl: $VINYL"
echo

# --- build one valid tiny FLAC for the positive path ------------------------
RAW="$TMP/sig.raw"
FLAC="$TMP/test.flac"
head -c 16384 /dev/zero > "$RAW"   # 4096 stereo 16-bit LE samples of silence
if "$FLAC_BIN" --silent --force --endian=little --sign=signed --channels=2 \
     --bps=16 --sample-rate=44100 -o "$FLAC" "$RAW" 2>/dev/null; then
  echo "built valid test stream: $(stat -c%s "$FLAC") bytes"
else
  echo "WARNING: could not build a test FLAC with '$FLAC_BIN'; positive probe will be skipped" >&2
  FLAC=""
fi
echo

# Run vinyl with a timeout; capture stderr+stdout and exit code into globals.
run() {  # run <timeout_s> <args...>
  local t="$1"; shift
  OUT="$(timeout "$t" "$VINYL" "$@" 2>&1)"; RC=$?
}

# --------------------------------------------------------------------------
# Probe 1: invalid worker counts must be rejected cleanly (nonzero + message).
# --------------------------------------------------------------------------
echo "-- Probe 1: reject invalid -j / --threads values --"
reject_ok=1
for spec in "-j 0" "-j -1" "--threads=0" "--threads abc" "--threads=xyz"; do
  # shellcheck disable=SC2086
  run 10 $spec --help
  if [ "$RC" -ne 0 ] && [ "$RC" -ne 124 ] && [ -n "$OUT" ]; then
    printf '   %-18s -> exit %-3s : %s\n' "$spec" "$RC" "$(printf '%s' "$OUT" | head -n1)"
  else
    reject_ok=0
    printf '   %-18s -> exit %-3s (unexpected: no clean rejection)\n' "$spec" "$RC"
  fi
done
if [ "$reject_ok" -eq 1 ]; then
  ok "invalid worker counts rejected cleanly (exit 2 + diagnostic, no crash/hang)"
else
  bad "at least one invalid worker count was NOT rejected cleanly"
fi
echo

# --------------------------------------------------------------------------
# Probe 2: an absurdly large -j is ACCEPTED (not bounds-checked). Proven safely
# via the guard ordering in withThreads: toNat? -> zero-check -> sentinel-check.
# With the sentinel pre-set, a rejected value would still print the count error;
# reaching the "refusing to re-execute twice" message proves 999999 passed
# validation. Then a sandboxed real run shows what that acceptance costs.
# --------------------------------------------------------------------------
echo "-- Probe 2: huge -j is unbounded (footgun) --"
OUT="$(VINYL_THREADS_SET=1 timeout 5 "$VINYL" -j 999999 --help 2>&1)"; RC=$?
zero_msg="$(VINYL_THREADS_SET=1 timeout 5 "$VINYL" -j 0 --help 2>&1)"
printf '   sentinel-set -j 999999 -> %s\n' "$(printf '%s' "$OUT" | head -n1)"
printf '   sentinel-set -j 0      -> %s\n' "$(printf '%s' "$zero_msg" | head -n1)"
if printf '%s' "$OUT" | grep -q "re-execute twice"; then
  # 999999 reached the sentinel guard => it was NOT rejected as an invalid count.
  # Now show the real cost in an isolated, memory-capped, SIGKILL-bounded shell.
  real="$(
    ulimit -v 1500000 2>/dev/null
    timeout -s KILL 8 "$VINYL" -j 4096 --help >/dev/null 2>"$TMP/big.err"
    echo "rc=$?"
  )"
  bigmsg="$(head -n1 "$TMP/big.err" 2>/dev/null)"
  printf '   sandboxed real -j 4096 -> %s : %s\n' "$real" "${bigmsg:-<no output>}"
  info "large -j is accepted unbounded; a real re-exec sets LEAN_NUM_THREADS to that many workers -> runtime aborts / resource-exhausts (local DoS footgun, LOW value)"
else
  ok "large -j appears bounds-checked/rejected"
fi
echo

# --------------------------------------------------------------------------
# Probe 3: sentinel leak. VINYL_THREADS_SET is the re-exec guard. If it leaks
# into the environment, -j does NOT get silently ignored -- the whole command
# hard-fails with exit 2 and never runs.
# --------------------------------------------------------------------------
echo "-- Probe 3: VINYL_THREADS_SET leak + -j 4 --"
OUT="$(VINYL_THREADS_SET=1 timeout 10 "$VINYL" -j 4 --help 2>&1)"; RC=$?
printf '   exit %s : %s\n' "$RC" "$(printf '%s' "$OUT" | head -n1)"
if [ "$RC" -ne 0 ] && printf '%s' "$OUT" | grep -q "re-execute twice"; then
  info "with the sentinel already set, '-j 4' is NOT silently ignored: the command hard-errors (exit 2) and does not run -- footgun if the env var ever leaks into a parent shell/wrapper"
elif [ "$RC" -eq 0 ]; then
  info "with the sentinel already set, '-j 4' is silently ignored and the command runs -- footgun: requested parallelism is dropped without warning"
else
  info "unexpected sentinel-leak behavior (exit $RC); review manually"
fi
echo

# --------------------------------------------------------------------------
# Probe 4: a normal -j 4 --decode-fast on a valid stream must still succeed.
# --------------------------------------------------------------------------
echo "-- Probe 4: -j 4 --decode-fast on a valid stream --"
if [ -n "$FLAC" ]; then
  run 30 -j 4 --decode-fast "$FLAC" "$TMP/out.pcm"
  osz=$(stat -c%s "$TMP/out.pcm" 2>/dev/null || echo 0)
  printf '   exit %s : %s : decoded %s bytes\n' "$RC" "$(printf '%s' "$OUT" | head -n1)" "$osz"
  if [ "$RC" -eq 0 ] && [ "$osz" -gt 0 ]; then
    ok "-j 4 --decode-fast succeeded on a valid stream"
  else
    bad "-j 4 --decode-fast did NOT succeed on a valid stream"
  fi
else
  info "positive probe skipped (no test FLAC could be built)"
fi
echo

echo "== summary: PASS=$pass FAIL=$fail NOTE=$note =="
[ "$fail" -eq 0 ]
