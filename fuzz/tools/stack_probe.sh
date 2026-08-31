#!/usr/bin/env bash
# stack_probe.sh -- measure the ENCODER's non-tail-recursion stack
# threshold. Flac.encodePcm16 = bitsToBytes (writeStream cfg a), and bitsToByteList
# recurses once per OUTPUT byte, so the minimum surviving stack grows with the
# output size. The depth is what overflows, so it must be PROBED, not asserted.
#
# Two sweeps:
#   (1) fixed input, shrinking `ulimit -s`  -> the stack a given input needs.
#   (2) fixed `ulimit -s`, growing input    -> "minimum surviving stack grows with
#       input", the class relationship (fitted line, not a single crash size).
#
# IMPORTANT: this bounds the STACK (ulimit -s), never the address space. Do NOT
# use `ulimit -v` / RLIMIT_AS here -- Lean reserves a large virtual arena per
# thread and an address-space cap kills healthy encodes (see setup.sh notes).
#
#   tools/stack_probe.sh            # both sweeps, default sizes
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
BIN=build/bin/measure_encode
[ -x "$BIN" ] || { echo "build first: make (or make tools) -> $BIN"; exit 1; }

# LEAN_NUM_THREADS=1 so a Task worker's own stack does not confound the main
# thread's recursion depth (P6's note: probe where the code executes).
export LEAN_NUM_THREADS=1

probe() {  # $1 = frames, $2 = stack KB ; prints ok/CRASH
  local frames="$1" stk="$2"
  if ( ulimit -s "$stk" 2>/dev/null; "$BIN" "$frames" >/dev/null 2>&1 ); then
    echo ok
  else
    echo CRASH
  fi
}

echo "== (1) fixed input, shrinking ulimit -s =="
FRAMES=${FRAMES:-131072}
echo "input = $FRAMES frames/channel (slow bitsToByteList path)"
for stk in 65536 32768 16384 8192 4096 2048 1024 512; do
  printf "  ulimit -s %-6s : %s\n" "$stk" "$(probe "$FRAMES" "$stk")"
done

echo
echo "== (2) fixed ulimit -s = 8192 KB, growing input (the class relationship) =="
for frames in 16384 65536 262144 1048576 4194304; do
  printf "  frames=%-9s : %s\n" "$frames" "$(probe "$frames" 8192)"
done

echo
echo "note: the crossover from ok->CRASH is the threshold; that it MOVES with input"
echo "      size (sweep 2) is the finding -- a total function whose stack need grows"
echo "      with output, not a fixed-size bug. bitsToByteList recurses per output byte."
