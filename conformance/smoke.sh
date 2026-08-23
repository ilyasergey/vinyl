#!/usr/bin/env bash
# Conformance smoke test (Rigs 1-2 of PLAN.md §6, M2/M3 profile: mono 16-bit).
#
# Rig 1 (our encoder -> their decoder): every stream we emit must pass
#   `flac -t` (which verifies frame CRCs and the STREAMINFO MD5) and decode
#   via `flac -d` to byte-identical PCM.
# Rig 2 (their encoder -> our decoder): a libFLAC-encoded stream inside our
#   current feature envelope (fixed predictors, no wasted bits) must decode
#   byte-identically with `decodeReference`.
#
# Oracle: flac CLI (libFLAC). Pin: any >= 1.4 works; developed against 1.5.0.
set -euo pipefail
cd "$(dirname "$0")/.."

command -v flac >/dev/null || { echo "SKIP: flac CLI not installed"; exit 0; }

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

lake build flactest >/dev/null
lake exe flactest "$WORK" >/dev/null

fail=0

echo "== Rig 1: vinyl encoder -> libFLAC decoder"
for f in "$WORK"/*.flac; do
  name=$(basename "$f" .flac)
  if ! flac -t -s "$f" 2>/dev/null; then
    echo "FAIL: flac -t rejects $name"; fail=1; continue
  fi
  flac -d -s --force-raw-format --sign=signed --endian=little \
    -f -o "$WORK/$name.raw" "$f" 2>/dev/null
  if cmp -s "$WORK/$name.raw" "$WORK/$name.pcm"; then
    echo "ok: $name"
  else
    echo "FAIL: PCM mismatch on $name"; fail=1
  fi
done

echo "== Rig 2: libFLAC encoder -> vinyl reference decoder"
# parity-mixed noise (no wasted bits; wasted-bits support lands with M4)
python3 - "$WORK/rig2.pcm" <<'EOF'
import struct, sys
vals = [((((i*i*2654435761 + i*40503) % 65536) - 32768) | (i & 1)) for i in range(20000)]
open(sys.argv[1], 'wb').write(b''.join(struct.pack('<h', v & 0xFFFF if (v & 0xFFFF) < 32768 else (v & 0xFFFF) - 65536) for v in vals))
EOF
flac --force-raw-format --sign=signed --endian=little --channels=1 --bps=16 \
  --sample-rate=44100 -l 0 -s -f -o "$WORK/rig2.flac" "$WORK/rig2.pcm" 2>/dev/null
lake exe flactest --decode "$WORK/rig2.flac" "$WORK/rig2.out" >/dev/null
if cmp -s "$WORK/rig2.out" "$WORK/rig2.pcm"; then
  echo "ok: libFLAC(-l 0) stream decodes byte-identically"
else
  echo "FAIL: Rig 2 mismatch"; fail=1
fi

if [ "$fail" = 0 ]; then echo "CONFORMANCE SMOKE: ALL GREEN"; else echo "CONFORMANCE SMOKE: FAILURES"; fi
exit $fail
