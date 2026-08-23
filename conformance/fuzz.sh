#!/usr/bin/env bash
# Rigs 3-5 (PLAN.md §9):
#   Rig 3 — decoder totality fuzz: random bytes and truncations must never
#           crash/hang the decoder (clean accept or clean reject only).
#   Rig 4 — structure-aware fuzz: bit-flipped valid streams must never
#           crash the decoder; CRC checks should reject most corruptions.
#   Rig 5 — runtime round-trip fuzz: random audio through the *compiled*
#           checked encoder and decoder must round-trip byte-identically
#           (the theorem guarantees the functions agree; this rig tests
#           the trusted base: compiler + runtime).
# Usage: conformance/fuzz.sh [iterations-per-rig]  (default 200)
set -uo pipefail
cd "$(dirname "$0")/.."

N="${1:-200}"
VINYL=.lake/build/bin/vinyl
lake build vinyl >/dev/null

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# one valid seed stream for rigs 3 (truncations) and 4 (mutations)
python3 - "$WORK/seed.pcm" <<'EOF'
import math, struct, sys
with open(sys.argv[1], "wb") as f:
    for i in range(20000):
        v = int(12000 * math.sin(i / 37.0) + 800 * math.sin(i / 5.0))
        f.write(struct.pack("<hh", v, v // 2 + 100))
EOF
"$VINYL" --encode "$WORK/seed.pcm" "$WORK/seed.flac" 4096 2 >/dev/null

run_decode () {  # $1 = input file; returns decoder exit code, 124 on timeout
  ( "$VINYL" --decode-fast "$1" "$WORK/out.pcm" >/dev/null 2>&1 ) &
  local pid=$!
  ( sleep 20 && kill -9 $pid 2>/dev/null ) & local watchdog=$!
  wait $pid 2>/dev/null; local rc=$?
  kill $watchdog 2>/dev/null; wait $watchdog 2>/dev/null
  return $rc
}

echo "== Rig 3: totality fuzz ($N random inputs + truncations)"
fail=0
for i in $(seq 1 "$N"); do
  case $((i % 3)) in
    0) head -c $((RANDOM % 4096)) /dev/urandom > "$WORK/fuzz.bin" ;;
    1) { printf 'fLaC'; head -c $((RANDOM % 4096)) /dev/urandom; } > "$WORK/fuzz.bin" ;;
    2) head -c $((RANDOM % $(stat -f%z "$WORK/seed.flac" 2>/dev/null || stat -c%s "$WORK/seed.flac"))) \
         "$WORK/seed.flac" > "$WORK/fuzz.bin" ;;
  esac
  run_decode "$WORK/fuzz.bin"; rc=$?
  if [ "$rc" -ne 0 ] && [ "$rc" -ne 1 ]; then
    fail=$((fail+1)); echo "  CRASH/HANG (rc=$rc) on iteration $i"
    cp "$WORK/fuzz.bin" "$WORK/rig3-fail-$i.bin"
  fi
done
echo "Rig 3: $((N - fail)) clean, $fail crashes/hangs"
R3=$fail

echo "== Rig 4: structure-aware fuzz ($N bit-flipped valid streams)"
fail=0; accepted=0
for i in $(seq 1 "$N"); do
  python3 - "$WORK/seed.flac" "$WORK/fuzz.bin" <<'EOF'
import random, sys
data = bytearray(open(sys.argv[1], "rb").read())
for _ in range(random.randint(1, 8)):
    pos = random.randrange(len(data))
    data[pos] ^= 1 << random.randrange(8)
open(sys.argv[2], "wb").write(bytes(data))
EOF
  run_decode "$WORK/fuzz.bin"; rc=$?
  case "$rc" in
    0) accepted=$((accepted+1)) ;;
    1) : ;;
    *) fail=$((fail+1)); echo "  CRASH/HANG (rc=$rc) on iteration $i"
       cp "$WORK/fuzz.bin" "$WORK/rig4-fail-$i.bin" ;;
  esac
done
echo "Rig 4: $((N - fail)) clean ($accepted mutants still accepted), $fail crashes/hangs"
R4=$fail

echo "== Rig 5: runtime round-trip fuzz ($N random audios)"
fail=0
for i in $(seq 1 "$N"); do
  ch=$((RANDOM % 2 + 1))
  python3 - "$WORK/rt.pcm" "$ch" <<'EOF'
import random, struct, sys
n = random.randint(0, 3000)
mode = random.choice(["uniform", "small", "extreme", "constant", "wasted"])
with open(sys.argv[1], "wb") as f:
    c0 = random.randint(-32768, 32767)
    for i in range(n * int(sys.argv[2])):
        if mode == "uniform":  v = random.randint(-32768, 32767)
        elif mode == "small":  v = random.randint(-40, 40)
        elif mode == "extreme": v = random.choice([-32768, 32767, 0, -1])
        elif mode == "constant": v = c0
        else: v = random.randint(-4096, 4095) * 8
        f.write(struct.pack("<h", v))
EOF
  bs=$((16 + RANDOM % 8000))
  if ! "$VINYL" --encode "$WORK/rt.pcm" "$WORK/rt.flac" "$bs" "$ch" >/dev/null 2>&1; then
    fail=$((fail+1)); echo "  ENCODE REJECTED valid input on iteration $i (bs=$bs ch=$ch)"
    continue
  fi
  if ! "$VINYL" --decode-fast "$WORK/rt.flac" "$WORK/rt.out" >/dev/null 2>&1 \
      || ! cmp -s "$WORK/rt.out" "$WORK/rt.pcm"; then
    fail=$((fail+1)); echo "  ROUND-TRIP MISMATCH on iteration $i (bs=$bs ch=$ch)"
    cp "$WORK/rt.pcm" "$WORK/rig5-fail-$i.pcm"
  fi
done
echo "Rig 5: $((N - fail)) round-tripped, $fail failures"
R5=$fail

if [ "$R3" = 0 ] && [ "$R4" = 0 ] && [ "$R5" = 0 ]; then
  echo "FUZZ: ALL GREEN"
else
  echo "FUZZ: FAILURES (rig3=$R3 rig4=$R4 rig5=$R5)"
  exit 1
fi
