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

echo "== stack-shape swaps present (P6: csimp-pinned tail forms)"
# The input-driven frame loops ship in accumulator form via kernel-checked
# @[csimp] equations (docs/06-recursion-shape.md). Pin them by name so a
# refactor cannot silently drop a swap and revert a loop to
# stack-frame-per-frame.  All are tail-recursion (`*TR`) swaps in Flac/Native/.
STACK_SWAPS="readUnary_eq_readUnaryTR readFrames_eq_readFramesTR readFramesB_eq_readFramesBTR
recombine_eq_recombineTR readFramesStepsB_eq_readFramesStepsBTR readRiceSeq_eq_readRiceSeqTR
readSIntSeq_eq_readSIntSeqTR restoreAux_eq_restoreAuxTR bitsToByteList_eq_bitsToByteListTR
chunkChannels_eq_chunkChannelsTR deinterleaveN_eq_deinterleaveNTR diff1_eq_diff1TR
pcm16OfByteList_eq_pcm16OfByteListTR residualAux_eq_residualAuxTR writeFrames_eq_writeFramesTR"
for thm in $STACK_SWAPS; do
  if ! grep -rq "@\[csimp\] theorem $thm" Flac/Native/; then
    echo "FAIL: missing csimp stack-shape swap $thm"; fail=1
  fi
done
echo "ok"

echo "== machine-word kernel swaps present (csimp-pinned, per file)"
# The hot loops ship as Int64/USize kernels behind kernel-checked @[csimp]
# equations.  Pin them so a refactor cannot drop a swap and silently revert a
# loop to boxed arithmetic.  The LPC and fixed restores are both named
# restoreA_eq_restoreFast, so the pins are per file: a repository-wide grep
# would be satisfied by either one alone.
KERNEL_SWAPS='Flac/Native/Lpc.lean restoreA_eq_restoreFast
Flac/Native/Fixed.lean restoreA_eq_restoreFast
Flac/Native/Emit.lean lpcResGo1_eq_fast
Flac/Native/Emit.lean lpcResGo2_eq_fast
Flac/Native/Emit.lean lpcResGo3_eq_fast
Flac/Native/Emit.lean lpcResGo4_eq_fast
Flac/Native/Emit.lean lpcResGo5_eq_fast
Flac/Native/Emit.lean lpcResGo6_eq_fast
Flac/Native/Emit.lean lpcResGo7_eq_fast
Flac/Native/Emit.lean lpcResGo8_eq_fast
Flac/Native/Encode.lean pushRiceRangeF_eq_fast
Flac/Native/Encode.lean channelSegO_eq_fast
Flac/Native/Stereo.lean decodeLSA_eq_fast
Flac/Native/Stereo.lean decodeRSA_eq_fast
Flac/Native/Stereo.lean decodeMSLA_eq_fast
Flac/Native/Stereo.lean decodeMSRA_eq_fast
Flac/Native/Stereo.lean decodeMSA_eq_fast
Flac/Native/Stream.lean pcmStereoGo_eq_fast
Flac/Native/Stream.lean pcmMonoGo_eq_fast
Flac/Native/Crc.lean crc16Range_eq_fast
Flac/Native/Heuristics.lean riceParam_eq_fast
Flac/Spec/PcmBytes.lean decodePcm16_eq_decodePcm16A
Flac/Spec/Emit.lean Unchecked_encode_eq_emitFast'
while read -r file thm; do
  [ -z "$file" ] && continue
  if ! grep -q "@\[csimp\] theorem $thm" "$file"; then
    echo "FAIL: missing csimp swap $thm in $file"; fail=1
  fi
done <<EOF
$KERNEL_SWAPS
EOF
echo "ok"

echo "== every @[csimp] swap in Flac/ is pinned above (closure: the pin list cannot drift behind the code)"
# The two lists above detect a *removed* pin; they cannot detect a *newly added*
# swap that nobody pinned.  Seven tail-form swaps were introduced by later work
# and sat unpinned until this check existed.  Derive the expected set from the
# code and fail on any @[csimp] name not covered by a pin above, so adding a
# swap forces adding its pin rather than silently reverting the gate's coverage.
PINNED=$( { printf '%s\n' $STACK_SWAPS; printf '%s\n' "$KERNEL_SWAPS" | awk '{print $2}'; } | sort -u )
for name in $(grep -rhoE "@\[csimp\] theorem [A-Za-z0-9_.']+" Flac/ | sed -E 's/.*theorem //' | sort -u); do
  if ! printf '%s\n' "$PINNED" | grep -Fxq "$name"; then
    echo "FAIL: @[csimp] swap $name is defined in Flac/ but pinned nowhere in scripts/check.sh"; fail=1
  fi
done
echo "ok"

echo "== residual-reader equalities present (not csimp: they justify the guarded dispatch)"
# readRiceSeqFast and readSIntSeqFast are not @[csimp] swaps: they *are* the
# shipped definitions and dispatch on a decidable domain guard, with every
# branch proven equal to the specification reader.  Pin those equalities by
# name so a branch cannot be added or a guard widened without one.
for thm in "riceRunU_eq" "readRiceSeqFast_eq_scanFast" "scanOneU_toNat" "readRiceSeqScan3_eq" \
           "readSIntSeqU_eq" "readSIntSeqFast_eq_go" "readSIntSeqFast_eq"; do
  if ! grep -rq "theorem $thm" Flac/Spec/Decode.lean; then
    echo "FAIL: missing $thm"; fail=1
  fi
done
echo "ok"

echo "== compiled-path audit: the kernels reach the shipped binary, and the hot loops stay header-free"
# Two properties of the generated C that no theorem can state:
#   positive — each shipped entry point's module calls the kernel it should.
#              A @[csimp] only rewrites code generated after it is declared,
#              and the public Flac.encode/decodePcm16 once did not;
#   negative — the Rice reader, unary scan, byteU, sync scan and MD5 block loop
#              contain no ByteArray-header read.  That load cost ~32% of the
#              16-thread decode wall and is invisible at one thread, so this
#              grep is the only mechanical guard against a repeat.
# Both live in scripts/audit_ir.py, which matches function bodies by brace depth
# so a legitimate header read elsewhere in the same file does not trip it.
python3 scripts/audit_ir.py || fail=1

echo "== kernel generators match the code they generated"
# The per-order kernels are templates instantiated per order; nothing
# regenerates them at build time, so without this they drift and the next
# order added by hand reintroduces the index-arithmetic error class the
# templates exist to prevent.
python3 scripts/gen/check_gen.py || fail=1

echo "== proven-equivalence twin map + encode-side oracle-aliasing guard (E1)"
# fuzz/cov/twins.py: every proven-equivalent implementation side has a live C
# connector and >=1 driving fuzz target, AND -- the half that matters here -- the
# reference writer (Unchecked.encode) and emitFast stay DISTINCT compiled callees in
# the generated FlacTest/Fuzz*.c. An `import` that pulled `@[csimp]
# Unchecked_encode_eq_emitFast` into the exporting module's scope once aliased the two
# @[export] wrappers, so the differential encode oracle compared emitFast to itself and
# every green run was a false negative -- a defect no theorem, build or nm check can
# see. The detector existed but lived only in the fuzz CI; pinning it here makes it a
# merge-gate condition. `lake build` above generates the FlacTest/Fuzz*.c IR the
# disjointness check reads, so an absent IR fails rather than skips.
if twout=$(python3 fuzz/cov/twins.py 2>&1); then
  echo "ok"
else
  echo "$twout"
  echo "FAIL: twins.py (twin routing / oracle aliasing)"; fail=1
fi

echo "== proof-level trust holes: no native_decide/implemented_by/unsafe/extern/dbg_trace in Flac/"
if grep -rn --include='*.lean' -E '\bnative_decide\b|@\[implemented_by|\bunsafe def\b|@\[extern|\bdbg_trace\b' Flac/; then
  echo "FAIL: proof or compilation trust hole in Flac/"; fail=1
else
  echo "ok"
fi

# One token list for both panic lints below, so the decode tier cannot end up
# narrower than the executable tier by omission.  `sed 's|--.*||'` strips Lean
# line comments *from the line* rather than dropping the whole line: discarding
# any line containing `--` would hide a real `a[i]!` that carries a trailing
# comment.
PANIC='\]!\|get!\|set!\|head!\|tail!\|toNat!\|toInt!\|panic!'
panic_grep () { grep -n "$PANIC" "$@" 2>/dev/null | sed 's|--.*||' | grep "$PANIC"; }

echo "== decoder totality: no 'partial', no panicking indexing in decode paths"
# decode paths: everything in Flac/ except the two modules that are deliberately
# outside the tier -- Md5 (tested, not verified) and Heuristics (unverified by
# design; its choices change which valid stream is emitted, never whether the
# round trip holds).
DECODE_FILES=$(ls Flac/Native/*.lean | grep -v -e Md5.lean -e Heuristics.lean)
if grep -n 'partial def' $DECODE_FILES Flac/Spec/*.lean; then
  echo "FAIL: partial def in decode path"; fail=1
else
  echo "ok: no partial"
fi
if panic_grep $DECODE_FILES Flac/Spec/*.lean; then
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
if panic_grep $BIN_FILES; then
  echo "FAIL: panicking call in a shipped executable's modules"; fail=1
else
  echo "ok: no panicking calls in executable modules"
fi

echo "== unit tests"
lake exe flactest

if [ "$fail" = 0 ]; then echo "CHECK: ALL GREEN"; else echo "CHECK: FAILURES"; exit 1; fi
