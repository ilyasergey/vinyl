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
for thm in "theorem decodeReference_encode " "theorem _root_.Flac.Stream.decodeReference_encode_default" "theorem decode_ok_iff_reference" "theorem decode_encode " "theorem decode_encode_cfg" "theorem decode_encodeChecked" "theorem decodePcm16_encodePcm16" "theorem pushFrame_spec" "theorem emitFast_eq_encode"; do
  if ! grep -rq "$thm" Flac/Spec/; then
    echo "FAIL: missing $thm"; fail=1
  fi
done
echo "ok"

echo "== CLI entry points call the functions the capstones are about"
# Statements are pinned by type in FlacTest/Capstones.lean; which function a
# CLI branch *invokes* is not something a type can express, so pin it here.
# Each entry is: <cli flag> <function the capstone names>
while read -r flag fn; do
  [ -z "$flag" ] && continue
  # the branch body runs from its `if let ["<flag>"` line to the next `if let`
  body=$(awk -v f="\"$flag\"" '
    $0 ~ ("if let \\[" f) {inb=1}
    inb {print}
    inb && NR>1 && $0 ~ /^  if let \[/ && $0 !~ ("if let \\[" f) {inb=0}' FlacTest/Cli.lean)
  if ! printf '%s' "$body" | grep -q -- "$fn"; then
    echo "FAIL: CLI $flag does not call $fn"; fail=1
  fi
done <<'EOF'
--encode Flac.encodePcm16Fast
--encode-slow Flac.encodePcm16Cfg
--decode-pcm16 Flac.decodePcm16A
--decode-fast Flac.Decode.decodeArrays
--decode Stream.decodeReference
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

echo "== unit tests"
lake exe flactest

if [ "$fail" = 0 ]; then echo "CHECK: ALL GREEN"; else echo "CHECK: FAILURES"; exit 1; fi
