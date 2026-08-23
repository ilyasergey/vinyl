#!/usr/bin/env python3
"""Render benchmark figures from bench/results.csv:

- bench/compression.png — per-file ratio cactus + per-category aggregate bars
- bench/performance.png — per-file encode-throughput profile
- bench/summary.md      — the per-category ratio table (pasted into README)
"""
import csv
import math
import os
import statistics
import sys
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter

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
        if "decode" in enc:
            continue
        cb = catbytes[row["file"].split("-")[0]][enc]
        cb[0] += int(row["bytes"])
        cb[1] += raw

STYLE = {
    "vinyl":   dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
    "flac -0": dict(color="#94a3b8", marker="s", lw=1.6),
    "flac -5": dict(color="#64748b", marker="^", lw=1.6),
    "flac -8": dict(color="#334155", marker="v", lw=1.6),
}
DEC_STYLE = {
    "vinyl decode": dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
    "flac decode":  dict(color="#334155", marker="v", lw=1.6),
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

# ── performance: encode + decode throughput profiles ────────────────────
def throughput_panel(ax, styles, kind, gap_pair, gap_note=""):
    """Log-scale profile with readable scalar ticks, medians in the legend,
    and an arrow marking the median gap between the two encoders in
    gap_pair (vinyl vs the libFLAC baseline it should be judged against)."""
    n = 0
    for enc in styles:
        if enc not in speed:
            continue
        ys = sorted(speed[enc])
        n = max(n, len(ys))
        med = statistics.median(ys)
        ax.plot(range(1, len(ys) + 1), ys,
                label=f"{enc} — median {med:.3g} MB/s", ms=4, **styles[enc])
    ax.set_xlabel(f"files (each {kind}r sorted slowest → fastest)")
    ax.set_ylabel(f"{kind} throughput, raw MB/s (higher = faster)")
    ax.set_yscale("log")
    allv = [v for e in styles if e in speed for v in speed[e]]
    ticks = [t for t in (0.05, 0.1, 0.2, 0.5, 1, 2, 3, 5, 7, 10, 15, 20, 30, 50, 70,
                         100, 200)
             if min(allv) * 0.8 <= t <= max(allv) * 1.25]
    ax.set_yticks(ticks)
    ax.set_yticklabels([f"{t:g}" for t in ticks])
    ax.yaxis.set_minor_formatter(NullFormatter())
    lo, hi = gap_pair
    if lo in speed and hi in speed:
        lo_med = statistics.median(speed[lo])
        hi_med = statistics.median(speed[hi])
        for med, enc in ((lo_med, lo), (hi_med, hi)):
            ax.axhline(med, color=styles[enc]["color"], ls="--", lw=1, alpha=0.6)
        x = n * 0.3
        ax.annotate("", xy=(x, hi_med), xytext=(x, lo_med),
                    arrowprops=dict(arrowstyle="<->", color="#111827", lw=1.1))
        ax.text(x + n * 0.03, math.sqrt(lo_med * hi_med),
                f"×{hi_med / lo_med:.1f} median gap\nvs {hi}{gap_note}",
                va="center", fontsize=9, color="#111827")
    ax.set_title(f"{kind.capitalize()} speed")
    ax.grid(alpha=0.25, which="both")
    ax.legend(fontsize=8)

fig2, (ax2, ax4) = plt.subplots(2, 1, figsize=(8.5, 9), dpi=150)
# Encode is judged against `flac -8`: that is the preset whose compression
# Vinyl matches, so it is the like-for-like speed baseline.
throughput_panel(ax2, STYLE, "encode", ("vinyl", "flac -8"),
                 gap_note="\n(matched ratio)")
throughput_panel(ax4, DEC_STYLE, "decode", ("vinyl decode", "flac decode"))
fig2.suptitle("Throughput — Vinyl (verified) vs libFLAC")
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
