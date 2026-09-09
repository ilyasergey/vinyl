#!/usr/bin/env bash
# Conformance smoke test (Rigs 1-2 of PLAN.md §6): mono and stereo 16-bit.
#
# Rig 1 (our encoder -> their decoder): every stream we emit must pass
#   `flac -t` (which verifies frame CRCs and the STREAMINFO MD5) and decode
#   via `flac -d` to byte-identical PCM.
# Rig 2 (their encoder -> our decoder): a libFLAC-encoded stream must decode
#   byte-identically. The `--decode` branch runs `Flac.Decode.decodeOption`,
#   proven pointwise equal to `decodeReference`.
#
# Oracle: flac CLI (libFLAC). Pin: any >= 1.4 works; developed against 1.5.0.
set -euo pipefail
cd "$(dirname "$0")/.."

command -v flac >/dev/null || { echo "SKIP: flac CLI not installed"; exit 0; }

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

lake build flactest >/dev/null
lake exe flactest --samples "$WORK" >/dev/null

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
# parity-mixed noise: the low bit is forced set, so no wasted-bits subframe
# is emitted and this case stays a fixed-predictor test
python3 - "$WORK/rig2.pcm" <<'EOF'
import struct, sys
vals = [((((i*i*2654435761 + i*40503) % 65536) - 32768) | (i & 1)) for i in range(20000)]
open(sys.argv[1], 'wb').write(b''.join(struct.pack('<h', v & 0xFFFF if (v & 0xFFFF) < 32768 else (v & 0xFFFF) - 65536) for v in vals))
EOF
flac --force-raw-format --sign=signed --endian=little --channels=1 --bps=16 \
  --sample-rate=44100 -l 0 -s -f -o "$WORK/rig2.flac" "$WORK/rig2.pcm" 2>/dev/null
lake exe flactest --decode "$WORK/rig2.flac" "$WORK/rig2.out" >/dev/null
if cmp -s "$WORK/rig2.out" "$WORK/rig2.pcm"; then
  echo "ok: libFLAC(-l 0) mono stream decodes byte-identically"
else
  echo "FAIL: Rig 2 mono mismatch"; fail=1
fi

# stereo: libFLAC will pick stereo decorrelation modes on correlated channels
python3 - "$WORK/rig2s.pcm" <<'EOF2'
import struct, sys, math
out = []
for i in range(20000):
    l = int(9000 * math.sin(i * 0.02))
    r = l - l // 8 + ((i * 37) % 5)
    out.append(struct.pack('<hh', l, r))
open(sys.argv[1], 'wb').write(b''.join(out))
EOF2
flac --force-raw-format --sign=signed --endian=little --channels=2 --bps=16 \
  --sample-rate=44100 -l 0 -s -f -o "$WORK/rig2s.flac" "$WORK/rig2s.pcm" 2>/dev/null
lake exe flactest --decode "$WORK/rig2s.flac" "$WORK/rig2s.out" >/dev/null
if cmp -s "$WORK/rig2s.out" "$WORK/rig2s.pcm"; then
  echo "ok: libFLAC(-l 0) stereo stream decodes byte-identically"
else
  echo "FAIL: Rig 2 stereo mismatch"; fail=1
fi

if [ "$fail" = 0 ]; then echo "CONFORMANCE SMOKE: ALL GREEN"; else echo "CONFORMANCE SMOKE: FAILURES"; fi
exit $fail
