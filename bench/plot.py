#!/usr/bin/env python3
"""Cactus plots from bench/results.csv: per-file compression ratio and
encode throughput, each series sorted independently (SAT-solver style —
curves lower/righter are better on ratio, higher/righter on speed)."""
import csv
import sys
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

results_csv = sys.argv[1] if len(sys.argv) > 1 else "bench/results.csv"
out_png = sys.argv[2] if len(sys.argv) > 2 else "bench/cactus.png"

ratio = defaultdict(list)      # encoder -> [encoded/raw]
speed = defaultdict(list)      # encoder -> [raw MB/s]
with open(results_csv) as f:
    for row in csv.DictReader(f):
        enc = row["encoder"]
        raw = int(row["raw_bytes"])
        if raw == 0:
            continue
        ratio[enc].append(int(row["bytes"]) / raw)
        speed[enc].append(raw / 1e6 / float(row["seconds"]))

STYLE = {
    "vinyl":   dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
    "flac -0": dict(color="#94a3b8", marker="s", lw=1.6),
    "flac -5": dict(color="#64748b", marker="^", lw=1.6),
    "flac -8": dict(color="#334155", marker="v", lw=1.6),
}

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.4), dpi=150)

for enc in STYLE:
    if enc not in ratio:
        continue
    ys = sorted(ratio[enc])
    ax1.plot(range(1, len(ys) + 1), [100 * y for y in ys],
             label=enc, ms=4, **STYLE[enc])
ax1.set_xlabel("files solved (sorted per encoder)")
ax1.set_ylabel("compression ratio, % of raw (lower = better)")
ax1.set_title("Compression ratio cactus")
ax1.grid(alpha=0.25)
ax1.legend()

for enc in STYLE:
    if enc not in speed:
        continue
    ys = sorted(speed[enc])
    ax2.plot(range(1, len(ys) + 1), ys, label=enc, ms=4, **STYLE[enc])
ax2.set_xlabel("files (sorted per encoder)")
ax2.set_ylabel("encode throughput, raw MB/s (higher = better)")
ax2.set_yscale("log")
ax2.set_title("Encode speed cactus")
ax2.grid(alpha=0.25, which="both")
ax2.legend()

fig.suptitle("Vinyl (verified, M3 heuristics) vs libFLAC — synthetic mono 16-bit corpus")
fig.tight_layout()
fig.savefig(out_png)
print(f"wrote {out_png}")
