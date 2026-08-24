#!/usr/bin/env python3
"""Render the real-audio benchmark figures from bench/real_results.csv:

- bench/real_compression.png — per-unit audio-frame ratio cactus + category bars
- bench/real_performance.png — encode and decode throughput profiles
- bench/real_summary.md      — the tables pasted into the READMEs

Compression is reported on the *audio-frame payload* (whole file minus the
metadata blocks).  libFLAC writes padding, a seektable, and a vendor comment;
Vinyl writes STREAMINFO alone, so whole-file sizes would credit Vinyl with
about 8 kB per unit that has nothing to do with coding.
"""
import csv
import os
import statistics
import sys
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter

results_csv = sys.argv[1] if len(sys.argv) > 1 else "bench/real_results.csv"
out_dir = os.path.dirname(results_csv) or "bench"

# Vinyl carries the one identity hue; the libFLAC presets are a neutral ramp,
# except the thread-matched preset — the honest wall-clock comparator for a
# frame-parallel encoder — which earns its own hue.  Markers repeat the
# identity so nothing is distinguished by colour alone.
def style_for(labels):
    """`flac -8 -jN` carries N from BENCH_THREADS, so bind the styles to the
    labels the run actually produced."""
    parallel = sorted(l for l in labels if l.startswith("flac -8 -j"))
    style = {
        "vinyl":   dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
        "flac -5": dict(color="#64748b", marker="^", lw=1.6),
        "flac -8": dict(color="#1e293b", marker="v", lw=1.6),
    }
    for label in parallel:
        style[label] = dict(color="#0d9488", marker="D", lw=1.8, zorder=4)
    return style, (parallel[0] if parallel else "flac -8")
DEC_STYLE = {
    "vinyl decode": dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
    "flac decode":  dict(color="#1e293b", marker="v", lw=1.6),
}
# Compression curves: -j only changes scheduling, so the multithreaded stream
# is the byte-identical twin of `flac -8` and would draw a duplicate curve.
RATIO_ENCODERS = ["vinyl", "flac -5", "flac -8"]

CATS = ["alignment", "artificial", "single-instrument", "solo-instrument",
        "vocal", "vocal-orchestra", "orchestra", "pop", "speech",
        "speech-clean", "speech-other"]
SUITES = ["sqam", "librispeech-test-clean", "librispeech-test-other"]

ratio = defaultdict(list)     # encoder -> [audio_bytes / raw]
speed = defaultdict(list)     # encoder -> [raw MB/s per unit]
catbytes = defaultdict(lambda: defaultdict(lambda: [0, 0]))   # cat -> enc -> [enc, raw]
filebytes = defaultdict(lambda: [0, 0])                       # enc -> [whole file, raw]
corpus = defaultdict(lambda: defaultdict(lambda: [0.0, 0]))   # suite -> enc -> [s, raw]
threads = {}
units = set()
catunits = defaultdict(set)   # cat -> {unit}

with open(results_csv) as handle:
    for row in csv.DictReader(handle):
        enc = row["encoder"]
        raw = int(row["raw_bytes"])
        seconds = float(row["seconds"])
        if raw == 0 or seconds <= 0:
            continue
        units.add(row["unit"])
        catunits[row["category"]].add(row["unit"])
        threads[enc] = int(row["threads"])
        ratio[enc].append(int(row["audio_bytes"]) / raw)
        speed[enc].append(raw / 1e6 / seconds)
        agg = corpus[row["suite"]][enc]
        agg[0] += seconds
        agg[1] += raw
        if "decode" in enc:
            continue
        cell = catbytes[row["category"]][enc]
        cell[0] += int(row["audio_bytes"])
        cell[1] += raw
        whole = filebytes[enc]
        whole[0] += int(row["bytes"])
        whole[1] += raw

STYLE, PARALLEL_BASELINE = style_for(threads)
cats = [c for c in CATS if c in catbytes]
suites = [s for s in SUITES if s in corpus]
n_units = len(units)


def total(enc, keys=None):
    keys = cats if keys is None else keys
    return (sum(catbytes[c][enc][0] for c in keys),
            sum(catbytes[c][enc][1] for c in keys))


# ── compression: cactus above, category bars below ──────────────────────
fig, (ax1, ax3) = plt.subplots(2, 1, figsize=(9, 9.5), dpi=150)

for enc in RATIO_ENCODERS:
    if enc not in ratio:
        continue
    ys = sorted(ratio[enc])
    num, den = total(enc)
    ax1.plot(range(1, len(ys) + 1), [100 * y for y in ys],
             label=f"{enc} — corpus {100 * num / den:.1f}%", ms=3.5, **STYLE[enc])
ax1.set_xlabel(f"benchmark units ({n_units} total, sorted per encoder)")
ax1.set_ylabel("audio-frame ratio, % of raw PCM (lower = better)")
ax1.set_title("Per-unit compression cactus")
ax1.grid(alpha=0.25)
ax1.legend()

width = 0.26
for k, enc in enumerate(RATIO_ENCODERS):
    xs = [i + (k - 1) * width for i in range(len(cats))]
    ys = [100 * catbytes[c][enc][0] / catbytes[c][enc][1] if catbytes[c].get(enc) else 0
          for c in cats]
    ax3.bar(xs, ys, width=width - 0.02, label=enc, color=STYLE[enc]["color"])
ax3.set_xticks(range(len(cats)))
ax3.set_xticklabels(cats, rotation=30, ha="right")
ax3.set_ylabel("aggregate ratio, % of raw (lower = better)")
ax3.set_title("Aggregate audio-frame ratio by content category")
ax3.grid(alpha=0.25, axis="y")
ax3.legend(ncol=3)

fig.suptitle("Compression — Vinyl (verified) vs libFLAC 1.5.0, real-audio corpora")
fig.tight_layout()
fig.savefig(os.path.join(out_dir, "real_compression.png"))
print("wrote real_compression.png")


# ── performance: encode + decode throughput profiles ────────────────────
def throughput_panel(ax, styles, kind, gap_pair, gap_note=""):
    n = 0
    for enc in styles:
        if enc not in speed:
            continue
        ys = sorted(speed[enc])
        n = max(n, len(ys))
        # `-jN` already names the thread count where it appears in the label;
        # everywhere else spell it out, because a frame-parallel codec beside a
        # single-threaded one is the whole point of the comparison.
        count = threads[enc]
        tag = "" if "-j" in enc else f" · {count} thread{'s' if count > 1 else ''}"
        ax.plot(range(1, len(ys) + 1), ys, ms=3.5, **styles[enc],
                label=f"{enc}{tag} — median {statistics.median(ys):.3g} MB/s")
    ax.set_xlabel(f"benchmark units (each {kind}r sorted slowest → fastest)")
    ax.set_ylabel(f"{kind} throughput, raw MB/s (higher = faster)")
    ax.set_yscale("log")
    allv = [v for e in styles if e in speed for v in speed[e]]
    ticks = [t for t in (5, 10, 15, 20, 30, 50, 70, 100, 150, 200, 300, 500, 700,
                         1000)
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
        # Curves rise left to right, so the arrow goes near the right end,
        # between the two dashed medians.  The caption cannot hang off it —
        # the slowest curve passes through that space — so it sits in the
        # bottom-right of the axes, which every curve has already left.
        x = n * 0.86
        ax.annotate("", xy=(x, hi_med), xytext=(x, lo_med),
                    arrowprops=dict(arrowstyle="<->", color="#111827", lw=1.1))
        ax.text(0.985, 0.03,
                f"×{max(hi_med, lo_med) / min(hi_med, lo_med):.2f} median gap "
                f"vs {hi}{gap_note}",
                transform=ax.transAxes, ha="right", va="bottom",
                fontsize=9, color="#111827",
                bbox=dict(boxstyle="round,pad=0.35", fc="#f8fafc",
                          ec="#cbd5e1", lw=0.8))
    ax.set_title(f"{kind.capitalize()} speed")
    ax.grid(alpha=0.25, which="both")
    ax.legend(fontsize=8, loc="upper left")


fig2, (ax2, ax4) = plt.subplots(2, 1, figsize=(9, 9.5), dpi=150)
# Vinyl's encoder is frame-parallel, so the like-for-like wall-clock baseline
# is libFLAC at the same thread count; the single-threaded `-8` row stays on
# the plot because it is the preset's default and the historical reference.
throughput_panel(ax2, STYLE, "encode", ("vinyl", PARALLEL_BASELINE),
                 gap_note=" (thread-matched)")
throughput_panel(ax4, DEC_STYLE, "decode", ("vinyl decode", "flac decode"))
fig2.suptitle("Throughput — Vinyl (verified) vs libFLAC 1.5.0, real-audio corpora")
fig2.tight_layout()
fig2.savefig(os.path.join(out_dir, "real_performance.png"))
print("wrote real_performance.png")

# ── markdown summary tables ─────────────────────────────────────────────
with open(os.path.join(out_dir, "real_summary.md"), "w") as f:
    f.write("### Compression, audio-frame payload as % of raw PCM\n\n")
    f.write("| category | units | vinyl | flac -5 | flac -8 |\n|---|---:|---|---|---|\n")
    for c in cats:
        cells = " | ".join(
            f"{100 * catbytes[c][e][0] / catbytes[c][e][1]:.1f}%" for e in RATIO_ENCODERS)
        f.write(f"| {c} | {len(catunits[c])} | {cells} |\n")
    cells = " | ".join(f"{100 * total(e)[0] / total(e)[1]:.1f}%" for e in RATIO_ENCODERS)
    f.write(f"| **TOTAL** | {n_units} | {cells} |\n\n")

    f.write("### Whole-file size as % of raw PCM (metadata included)\n\n")
    f.write("| " + " | ".join(RATIO_ENCODERS) + " |\n")
    f.write("|" + "---|" * len(RATIO_ENCODERS) + "\n| ")
    f.write(" | ".join(f"{100 * filebytes[e][0] / filebytes[e][1]:.1f}%"
                       for e in RATIO_ENCODERS) + " |\n\n")

    f.write("### Corpus throughput, total raw MB ÷ total seconds\n\n")
    order = [e for e in list(STYLE) + list(DEC_STYLE) if e in threads]
    f.write("| suite | " + " | ".join(order) + " |\n")
    f.write("|---|" + "---|" * len(order) + "\n")
    for s in suites + ["TOTAL"]:
        keys = suites if s == "TOTAL" else [s]
        cells = []
        for e in order:
            secs = sum(corpus[k][e][0] for k in keys)
            raw = sum(corpus[k][e][1] for k in keys)
            cells.append(f"{raw / 1e6 / secs:.0f} MB/s" if secs else "—")
        label = f"**{s}**" if s == "TOTAL" else s
        f.write(f"| {label} | " + " | ".join(cells) + " |\n")
print("wrote real_summary.md")
