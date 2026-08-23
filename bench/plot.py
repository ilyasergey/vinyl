#!/usr/bin/env python3
"""Render benchmark figures from bench/results.csv:

- bench/compression.png — per-file ratio cactus + per-category aggregate bars
- bench/performance.png — per-file encode-throughput profile
- bench/summary.md      — the per-category ratio table (pasted into README)
"""
import csv
import os
import sys
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

results_csv = sys.argv[1] if len(sys.argv) > 1 else "bench/results.csv"
out_dir = os.path.dirname(results_csv) or "bench"

CATS = ["tonal", "wave", "noise", "mixed", "degen", "stereo"]

ratio = defaultdict(list)      # encoder -> [encoded/raw]
speed = defaultdict(list)      # encoder -> [raw MB/s per file]
catbytes = defaultdict(lambda: defaultdict(lambda: [0, 0]))  # cat -> enc -> [enc, raw]
with open(results_csv) as f:
    for row in csv.DictReader(f):
        enc = row["encoder"]
        raw = int(row["raw_bytes"])
        if raw == 0:
            continue
        ratio[enc].append(int(row["bytes"]) / raw)
        speed[enc].append(raw / 1e6 / float(row["seconds"]))
        cb = catbytes[row["file"].split("-")[0]][enc]
        cb[0] += int(row["bytes"])
        cb[1] += raw

STYLE = {
    "vinyl":   dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
    "flac -0": dict(color="#94a3b8", marker="s", lw=1.6),
    "flac -5": dict(color="#64748b", marker="^", lw=1.6),
    "flac -8": dict(color="#334155", marker="v", lw=1.6),
}

# ── compression: cactus above, category bars below ──────────────────────
fig, (ax1, ax3) = plt.subplots(2, 1, figsize=(8.5, 9), dpi=150)

for enc in STYLE:
    if enc not in ratio:
        continue
    ys = sorted(ratio[enc])
    ax1.plot(range(1, len(ys) + 1), [100 * y for y in ys],
             label=enc, ms=4, **STYLE[enc])
ax1.set_xlabel("files solved (sorted per encoder)")
ax1.set_ylabel("compression ratio, % of raw (lower = better)")
ax1.set_title("Per-file ratio cactus")
ax1.grid(alpha=0.25)
ax1.legend()

cats = [c for c in CATS if c in catbytes]
width = 0.2
for k, enc in enumerate(STYLE):
    xs = [i + (k - 1.5) * width for i in range(len(cats))]
    ys = [100 * catbytes[c][enc][0] / catbytes[c][enc][1] if catbytes[c].get(enc) else 0
          for c in cats]
    ax3.bar(xs, ys, width=width, label=enc, color=STYLE[enc]["color"])
ax3.set_xticks(range(len(cats)))
ax3.set_xticklabels(cats)
ax3.set_ylabel("aggregate ratio, % of raw (lower = better)")
ax3.set_title("Aggregate ratio by content category")
ax3.grid(alpha=0.25, axis="y")
ax3.legend(ncol=2)

fig.suptitle("Compression — Vinyl (verified) vs libFLAC, synthetic 16-bit corpus")
fig.tight_layout()
fig.savefig(os.path.join(out_dir, "compression.png"))
print("wrote compression.png")

# ── performance: throughput profile ─────────────────────────────────────
fig2, ax2 = plt.subplots(figsize=(7.5, 4.6), dpi=150)
for enc in STYLE:
    if enc not in speed:
        continue
    ys = sorted(speed[enc])
    ax2.plot(range(1, len(ys) + 1), ys, label=enc, ms=4, **STYLE[enc])
ax2.set_xlabel("files (each encoder sorted slowest → fastest)")
ax2.set_ylabel("encode throughput, raw MB/s (higher = faster)")
ax2.set_yscale("log")
ax2.set_title("Encode speed — Vinyl (verified) vs libFLAC")
ax2.grid(alpha=0.25, which="both")
ax2.legend()
fig2.tight_layout()
fig2.savefig(os.path.join(out_dir, "performance.png"))
print("wrote performance.png")

# ── markdown summary table ───────────────────────────────────────────────
with open(os.path.join(out_dir, "summary.md"), "w") as f:
    f.write("| category | vinyl | flac -0 | flac -5 | flac -8 |\n")
    f.write("|---|---|---|---|---|\n")
    for c in cats + ["TOTAL"]:
        if c == "TOTAL":
            row = {e: (sum(catbytes[cc][e][0] for cc in cats),
                       sum(catbytes[cc][e][1] for cc in cats)) for e in STYLE}
        else:
            row = {e: tuple(catbytes[c][e]) for e in STYLE}
        cells = " | ".join(f"{100 * row[e][0] / row[e][1]:.1f}%" for e in STYLE)
        f.write(f"| {c} | {cells} |\n")
print("wrote summary.md")
