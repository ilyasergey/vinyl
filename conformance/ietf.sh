#!/usr/bin/env bash
# Rig 2 against the RFC 9639 companion test suite
# (https://github.com/ietf-wg-cellar/flac-test-files):
#   subset/   — the "must decode" set: every file must decode byte-identically
#               to `flac -d` raw output.
#   uncommon/ — edge-case set: report pass/skip per file (not merge-gating;
#               triaged as future completeness work, PLAN.md §9).
# Usage: conformance/ietf.sh <path-to-flac-test-files>
set -uo pipefail
cd "$(dirname "$0")/.."

CORPUS="${1:?usage: ietf.sh <path-to-flac-test-files>}"
command -v flac >/dev/null || { echo "flac CLI required"; exit 1; }
command -v metaflac >/dev/null || { echo "metaflac required"; exit 1; }
lake build vinyl >/dev/null

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

run_set () {
  local dir="$1" gate="$2" pass=0 fail=0 failed=""
  echo "== $dir"
  while IFS= read -r -d '' f; do
    name=$(basename "$f")
    if ! flac -d -s --force-raw-format --sign=signed --endian=little \
        -f -o "$WORK/ref.raw" "$f" 2>/dev/null; then
      echo "skip (flac itself rejects): $name"
      continue
    fi
    if .lake/build/bin/vinyl --decode "$f" "$WORK/got.raw" >/dev/null 2>&1 \
        && cmp -s "$WORK/got.raw" "$WORK/ref.raw"; then
      pass=$((pass+1))
    else
      fail=$((fail+1)); failed="$failed\n  FAIL: $name"
    fi
  done < <(find "$CORPUS/$dir" -name '*.flac' -print0 | sort -z)
  echo "$dir: $pass passed, $fail failed"
  [ -n "$failed" ] && echo -e "$failed"
  if [ "$gate" = gate ] && [ "$fail" -gt 0 ]; then GATE_FAIL=1; fi
}

GATE_FAIL=0
run_set subset gate
run_set uncommon report

if [ "$GATE_FAIL" = 0 ]; then echo "IETF MUST-DECODE: ALL GREEN"; else echo "IETF MUST-DECODE: FAILURES"; exit 1; fi
