#!/usr/bin/env bash
# The merge gate: build, proof hygiene, decoder totality lint, tests.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

echo "== build"
lake build

echo "== proof hygiene: no sorry/axiom in Flac/"
if grep -rn --include='*.lean' -E '\bsorry\b|^axiom |[^_a-zA-Z]axiom ' Flac/; then
  echo "FAIL: sorry/axiom found"; fail=1
else
  echo "ok"
fi

echo "== capstone theorems present (grep-pinned names)"
for thm in "theorem decodeReference_encode " "theorem _root_.Flac.Stream.decodeReference_encode_default" "theorem decode_ok_iff_reference" "theorem decode_encode " "theorem decode_encode_cfg" "theorem decode_encodeChecked" "theorem decodePcm16_encodePcm16" "theorem pushFrame_spec" "theorem emitFast_eq_encode" "theorem decodeBytes_spec"; do
  if ! grep -rq "$thm" Flac/Spec/; then
    echo "FAIL: missing $thm"; fail=1
  fi
done
echo "ok"

echo "== CLI entry points call the functions the capstones are about"
# Statements are pinned by type in FlacTest/Capstones.lean; which function a
# CLI branch *invokes* is not something a type can express, so pin it here.
# Each entry is: <cli flag> <helper or - > <function the capstone names>.
#
# A flag may have several branches (both `--encode` arities do, one per
# argument count) and they may delegate to a shared helper.  Naming the helper
# beats scraping for it: a renamed or newly introduced helper then fails the
# check instead of silently widening it.  The branch count and the delegation
# count must agree, so a second arity cannot appear that skips the helper.
while read -r flag helper fn; do
  [ -z "$flag" ] && continue
  # A flag pattern is `["<flag>",` — the comma matters, or `--encode` also
  # matches the `--encode-slow` branch and inherits whatever *it* calls.
  pat="\"$flag\","
  # the branch bodies run from the first matching `if let [` line to the next
  # `if let [` line for a different flag
  body=$(awk -v f="$pat" '
    index($0, "if let [" f) {inb=1}
    inb {print}
    inb && NR>1 && $0 ~ /^  if let \[/ && !index($0, "if let [" f) {inb=0}' FlacTest/Cli.lean)
  if [ "$helper" != "-" ]; then
    branches=$(printf '%s\n' "$body" | grep -c "if let \[$pat" || true)
    delegations=$(printf '%s\n' "$body" | grep -c -- "$helper" || true)
    if [ "$branches" -eq 0 ] || [ "$branches" -ne "$delegations" ]; then
      echo "FAIL: CLI $flag has $branches branch(es) but $delegations call(s) of $helper"
      fail=1
    fi
    # the helper's body runs from its `def` line to the next top-level `def`
    body=$(awk -v f="$helper" '
      $0 ~ ("^def " f "( |$|\\()") {inb=1; next}
      inb && /^def / {inb=0}
      inb {print}' FlacTest/Cli.lean)
    if [ -z "$body" ]; then
      echo "FAIL: CLI helper $helper is not defined in FlacTest/Cli.lean"; fail=1
    fi
  fi
  if ! printf '%s' "$body" | grep -q -- "$fn"; then
    echo "FAIL: CLI $flag does not call $fn"; fail=1
  fi
done <<'EOF'
--encode encodeFastMain Flac.encodePcm16Fast
--encode-slow encodeSlowMain Flac.encodePcm16Cfg
--decode-pcm16 - Flac.decodePcm16A
--decode-fast - Flac.Decode.decodeBytes
--decode-fast - Flac.Decode.decodeArrays
--decode - Flac.Decode.decodeOption
EOF
echo "ok"

echo "== proof-level trust holes: no native_decide/implemented_by/unsafe/extern in Flac/"
if grep -rn --include='*.lean' -E '\bnative_decide\b|@\[implemented_by|\bunsafe def\b|@\[extern' Flac/; then
  echo "FAIL: proof or compilation trust hole in Flac/"; fail=1
else
  echo "ok"
fi

echo "== decoder totality: no 'partial', no panicking indexing in decode paths"
# decode paths: everything in Flac/ except the encoder-only modules
DECODE_FILES=$(ls Flac/Native/*.lean | grep -v -e Md5.lean -e Heuristics.lean)
if grep -n 'partial def' $DECODE_FILES Flac/Spec/*.lean; then
  echo "FAIL: partial def in decode path"; fail=1
else
  echo "ok: no partial"
fi
if grep -n '\]!\|\[i\]!\|get!\|headD?!' $DECODE_FILES | grep -v '\-\-'; then
  echo "FAIL: panicking access in decode path"; fail=1
else
  echo "ok: no panicking access"
fi

echo "== shipped-binary panic lint: every module a lake exe links"
# The vinyl executable's main is FlacTest/Cli.lean's cliMain (audit finding
# P9: a toNat! panic shipped because this directory sat outside the lint).
# Code reachable from a shipped main gets the no-panic tier no matter which
# directory it lives in; keep this list in step with the [[lean_exe]] roots
# in lakefile.toml and their imports.
BIN_FILES="FlacTest/Cli.lean FlacTest/Capstones.lean FlacTest/Main.lean Vinyl.lean FlacTest.lean"
if grep -n '\]!\|get!\|headD?!\|head!\|tail!\|toNat!\|toInt!\|panic!' $BIN_FILES | grep -v '\-\-'; then
  echo "FAIL: panicking call in a shipped executable's modules"; fail=1
else
  echo "ok: no panicking calls in executable modules"
fi

echo "== unit tests"
lake exe flactest

if [ "$fail" = 0 ]; then echo "CHECK: ALL GREEN"; else echo "CHECK: FAILURES"; exit 1; fi
