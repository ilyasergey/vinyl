#!/usr/bin/env python3
"""Paired resource assertion: the Audio-level encoder must scale sub-quadratically.

The August recommendation for the non-tail-recursion class was "run the reproducer under
a small stack limit and assert exit 0". That is necessary and NOT sufficient: a fix for
the stack can spend the time instead. `writeFramesAcc` was O(1) stack and O(n^2) time,
and the frame chunker's emptiness-by-`length` test was separately quadratic (issue 5) —
both passed a stack assertion. The paired bound is stack AND cost; this is the cost half.

Encode the same content at N and 2N frames through `--encode-slow` (the `Audio`-level
path: `chunkChannels` + `writeFrames`), at a small block size so the frame count — and any
quadratic term in it — dominates, and require the growth from N to 2N to stay well under
the ~4x a quadratic produces. Measured here: 2.17x on the fixed branch, 6.88x with the
`chunkChannels` length-test quadratic present, so a 3.5x threshold separates them cleanly.

The oracle is WALL TIME (minimum of repeated runs), not instruction count, on purpose:
this quadratic is cache-bound, not instruction-bound — walking the growing head channel
per frame thrashes cache at large N, so the instruction-count ratio stays near 2x even
when wall time is 7x. Instruction count is deterministic but blind to this class; wall
time sees it, at the cost of load-sensitivity, which the wide threshold absorbs. Skips
(exit 0) rather than failing if it cannot obtain a usable measurement.

    python3 scripts/scaling_assert.py <path-to-vinyl-exe>
"""
import random
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

BLOCK = 16          # small block => many frames => a quadratic-in-frames term dominates
CHANNELS = 8
SIZES = [131072, 262144]   # samples/channel; 2x apart, large enough that the term shows
REPS = 3
WALL_MAX = 3.5      # linear ~2.0, quadratic ~4.0; branch 2.17, quadratic 6.88 when present
MIN_WALL = 0.3      # below this the measurement is dominated by process startup, not work


def make_pcm(path: Path, spc: int) -> None:
    random.seed(7)
    n = spc * CHANNELS
    buf = bytearray(n * 2)
    for i in range(n):
        struct.pack_into("<h", buf, i * 2, random.randint(-2000, 2000))
    path.write_bytes(buf)


def wall_min(vinyl: str, pcm: Path, out: Path) -> float:
    best = float("inf")
    for _ in range(REPS):
        t0 = time.perf_counter()
        r = subprocess.run(["env", "LEAN_NUM_THREADS=1", vinyl, "--encode-slow",
                            str(pcm), str(out), str(BLOCK), str(CHANNELS)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if r.returncode != 0:
            return -1.0
        best = min(best, time.perf_counter() - t0)
    return best


def main() -> int:
    if len(sys.argv) < 2 or not Path(sys.argv[1]).exists():
        print("SKIP: no vinyl exe given"); return 0
    vinyl = sys.argv[1]
    with tempfile.TemporaryDirectory() as d:
        dd = Path(d)
        walls = {}
        for spc in SIZES:
            p = dd / f"p{spc}.raw"
            make_pcm(p, spc)
            w = wall_min(vinyl, p, dd / f"o{spc}.flac")
            if w < 0:
                print(f"SKIP: encode of {spc} samples/ch x {CHANNELS} failed"); return 0
            walls[spc] = w

    lo, hi = walls[SIZES[0]], walls[SIZES[1]]
    if lo < MIN_WALL:
        print(f"SKIP: baseline too fast to time reliably ({lo:.3f}s < {MIN_WALL}s)"); return 0
    ratio = hi / lo
    verdict = "OK" if ratio < WALL_MAX else "FAIL"
    print(f"{verdict}: --encode-slow block {BLOCK}, {SIZES[0]}->{SIZES[1]} samples/ch x "
          f"{CHANNELS}: wall {lo:.2f}s -> {hi:.2f}s, ratio {ratio:.2f} "
          f"(linear ~2.0, quadratic ~4.0, threshold {WALL_MAX})")
    return 0 if ratio < WALL_MAX else 1


if __name__ == "__main__":
    raise SystemExit(main())
