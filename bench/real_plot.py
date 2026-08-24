#!/usr/bin/env python3
"""Render the real-audio benchmark figures from bench/real_results.csv:

- bench/real_compression.png — per-unit audio-frame ratio cactus + category bars
- bench/real_performance.png — encode and decode throughput at the headline
                               thread count
- bench/real_threads.png     — throughput and parallel speedup vs thread count
- bench/real_summary.md      — the tables pasted into the READMEs

Compression is reported on the *audio-frame payload* (whole file minus the
metadata blocks).  libFLAC writes padding, a seektable, and a vendor comment;
Vinyl writes STREAMINFO alone, so whole-file sizes would credit Vinyl with
about 8 kB per unit that has nothing to do with coding.

Every case label carries its thread count as `-jN`, because both codecs are
swept: Vinyl's encoder and decoder are frame-parallel and libFLAC 1.5.0 takes
`-j`.  libFLAC's decoder has no threading option and appears at `-j1` only.
"""
import csv
import math
import os
import re
import statistics
import sys
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.transforms import blended_transform_factory
from matplotlib.ticker import NullFormatter

results_csv = sys.argv[1] if len(sys.argv) > 1 else "bench/real_results.csv"
out_dir = os.path.dirname(results_csv) or "bench"

# Vinyl carries the one identity hue; the libFLAC presets are a neutral ramp,
# except `-8`, the encoder Vinyl is actually being judged against, which earns
# its own hue.  Markers repeat the identity so nothing is colour-alone.
FAMILY = {
    "vinyl":        dict(color="#7c3aed", marker="o", lw=2.2, zorder=5),
    "vinyl decode": dict(color="#7c3aed", marker="s", lw=2.2, zorder=5),
    "flac -5":      dict(color="#64748b", marker="^", lw=1.6),
    "flac -8":      dict(color="#059669", marker="D", lw=1.8, zorder=4),
    "flac decode":  dict(color="#1e293b", marker="v", lw=1.6),
}
# Compression curves: -j changes scheduling only, so one thread count per
# encoder is the whole story.
RATIO_FAMILIES = ["vinyl", "flac -5", "flac -8"]

CATS = ["alignment", "artificial", "single-instrument", "solo-instrument",
        "vocal", "vocal-orchestra", "orchestra", "pop", "speech",
        "speech-clean", "speech-other"]
SUITES = ["sqam", "librispeech-test-clean", "librispeech-test-other"]

# A hue per (implementation, thread count).  Same hue with a different dash
# was not distinguishable in practice, and same hue at two lightnesses cannot
# work on a light surface here: the light step lands at 2.4:1 contrast against
# a 3:1 floor, and the dark step loses enough chroma to read gray.  So the
# single-threaded runs get their own hues.
#
# violet / orange / green pass the palette validator's six checks on every
# pair, worst at ΔE 9.4 deutan and 13.6 tritan.  A blue was tried here first
# and rejected: against the violet it was the weakest pair in the set (ΔE 9.2
# deutan, 3.0 tritan) and read as the same colour.  The fourth series is a
# deliberate near-black neutral — it clears contrast and separates from all
# three hues by lightness, which is also how libFLAC's decoder is drawn.
SINGLE_THREAD_HUE = {
    "vinyl": "#c2410c",
    "vinyl decode": "#c2410c",
    "flac -8": "#1e293b",
}


def job_style(family, count):
    """Style for one (family, thread count) curve."""
    style = dict(FAMILY[family])
    if count != max(threadsets[family]):
        style["color"] = SINGLE_THREAD_HUE.get(family, style["color"])
    return style


JOB = re.compile(r"^(?P<family>.+?) -j(?P<threads>\d+)$")

ratio = defaultdict(list)      # family -> [audio_bytes / raw]  (one thread count)
speed = defaultdict(list)      # (family, threads) -> [raw MB/s per unit]
catbytes = defaultdict(lambda: defaultdict(lambda: [0, 0]))
filebytes = defaultdict(lambda: [0, 0])
corpus = defaultdict(lambda: defaultdict(lambda: [0.0, 0]))   # suite -> job -> [s, raw]
sizes = defaultdict(dict)      # family -> unit -> audio_bytes  (to check -j purity)
catunits = defaultdict(set)
units = set()
threadsets = defaultdict(set)  # family -> {thread counts}

with open(results_csv) as handle:
    for row in csv.DictReader(handle):
        match = JOB.match(row["encoder"])
        if not match:
            raise SystemExit(f"unparseable case label {row['encoder']!r}")
        family, n = match["family"], int(match["threads"])
        raw, seconds = int(row["raw_bytes"]), float(row["seconds"])
        if raw == 0 or seconds <= 0:
            continue
        units.add(row["unit"])
        catunits[row["category"]].add(row["unit"])
        threadsets[family].add(n)
        speed[(family, n)].append(raw / 1e6 / seconds)
        corpus[row["suite"]][(family, n)][0] += seconds
        corpus[row["suite"]][(family, n)][1] += raw
        if "decode" in family:
            continue
        # `-j` must not change the bytes; check rather than assume
        previous = sizes[family].setdefault(row["unit"], int(row["audio_bytes"]))
        if previous != int(row["audio_bytes"]):
            raise SystemExit(
                f"{family}: -j changed the output size on {row['unit']}")
        if n != min(threadsets[family]):
            continue
        ratio[family].append(int(row["audio_bytes"]) / raw)
        catbytes[row["category"]][family][0] += int(row["audio_bytes"])
        catbytes[row["category"]][family][1] += raw
        filebytes[family][0] += int(row["bytes"])
        filebytes[family][1] += raw

cats = [c for c in CATS if c in catbytes]
suites = [s for s in SUITES if s in corpus]
n_units = len(units)
HEAD = max(threadsets["vinyl"])          # the headline thread count


def total(family, keys=None):
    keys = cats if keys is None else keys
    return (sum(catbytes[c][family][0] for c in keys),
            sum(catbytes[c][family][1] for c in keys))


def corpus_speed(job, keys=None):
    keys = suites if keys is None else keys
    seconds = sum(corpus[k][job][0] for k in keys)
    raw = sum(corpus[k][job][1] for k in keys)
    return raw / 1e6 / seconds if seconds else None


# ── compression: cactus above, category bars below ──────────────────────
fig, (ax1, ax3) = plt.subplots(2, 1, figsize=(9, 9.5), dpi=150)

for family in RATIO_FAMILIES:
    if family not in ratio:
        continue
    ys = sorted(ratio[family])
    num, den = total(family)
    ax1.plot(range(1, len(ys) + 1), [100 * y for y in ys],
             label=f"{family} — corpus {100 * num / den:.1f}%", ms=3.5,
             **FAMILY[family])
ax1.set_xlabel(f"benchmark units ({n_units} total, sorted per encoder)")
ax1.set_ylabel("audio-frame ratio, % of raw PCM (lower = better)")
ax1.set_title("Per-unit compression cactus")
ax1.grid(alpha=0.25)
ax1.legend()

width = 0.26
for k, family in enumerate(RATIO_FAMILIES):
    xs = [i + (k - 1) * width for i in range(len(cats))]
    ys = [100 * catbytes[c][family][0] / catbytes[c][family][1]
          if catbytes[c].get(family) else 0 for c in cats]
    ax3.bar(xs, ys, width=width - 0.02, label=family, color=FAMILY[family]["color"])
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


# ── throughput at the headline thread count ─────────────────────────────
def throughput_panel(ax, jobs, kind, gap_pair, gap_note=""):
    n = 0
    for family, count in jobs:
        if (family, count) not in speed:
            continue
        ys = sorted(speed[(family, count)])
        n = max(n, len(ys))
        ax.plot(range(1, len(ys) + 1), ys, ms=3.5, **job_style(family, count),
                label=f"{family}, "
                      f"{'single-threaded' if count == 1 else f'{count} threads'}"
                      f"  —  {statistics.median(ys):.3g} MB/s",
                ls="-" if count == max(threadsets[family]) else "--")
    ax.set_xlabel(f"benchmark units (each {kind}r sorted slowest → fastest)")
    ax.set_ylabel(f"{kind} throughput, raw MB/s (higher = faster)")
    ax.set_yscale("log")
    allv = [v for j in jobs if j in speed for v in speed[j]]
    ticks = [t for t in (5, 10, 15, 20, 30, 50, 70, 100, 150, 200, 300, 500,
                         700, 1000)
             if min(allv) * 0.8 <= t <= max(allv) * 1.25]
    ax.set_yticks(ticks)
    ax.set_yticklabels([f"{t:g}" for t in ticks])
    ax.yaxis.set_minor_formatter(NullFormatter())
    lo, hi = gap_pair
    if lo in speed and hi in speed:
        lo_med = statistics.median(speed[lo])
        hi_med = statistics.median(speed[hi])
        for med, job in ((lo_med, lo), (hi_med, hi)):
            ax.axhline(med, color=job_style(*job)["color"], ls="--", lw=1, alpha=0.6)
        x = n * 0.86
        ax.annotate("", xy=(x, hi_med), xytext=(x, lo_med),
                    arrowprops=dict(arrowstyle="<->", color="#111827", lw=1.1))
        ax.text(0.985, 0.97,
                f"×{max(hi_med, lo_med) / min(hi_med, lo_med):.2f} median gap vs "
                f"{hi[0]}, "
                f"{'single-threaded' if hi[1] == 1 else f'{hi[1]} threads'}"
                f"{gap_note}",
                transform=ax.transAxes, ha="right", va="top",
                fontsize=9, color="#111827",
                bbox=dict(boxstyle="round,pad=0.35", fc="#f8fafc",
                          ec="#cbd5e1", lw=0.8))
    ax.set_title(f"{kind.capitalize()} speed at {HEAD} threads")
    ax.grid(alpha=0.25, which="both")
    # Curves rise left to right, so the legend belongs top-left — but with a
    # thread sweep there are enough entries to sit on the curves.  Give it its
    # own headroom instead, measured in decades of the log axis; that same
    # band is what keeps the top-right corner free for the gap caption.
    plotted = sum(1 for j in jobs if j in speed)
    ncol = 2 if plotted > 4 else 1
    rows = -(-plotted // ncol)
    lo, hi = min(allv) * 0.85, max(allv) * 1.1
    ax.set_ylim(lo, hi * 10 ** (0.085 * rows))
    ax.legend(fontsize=8, loc="upper left", ncol=ncol)


fig2, (ax2, ax4) = plt.subplots(2, 1, figsize=(9, 9.5), dpi=150)
throughput_panel(
    ax2,
    [("vinyl", HEAD), ("vinyl", 1), ("flac -8", HEAD), ("flac -8", 1)],
    "encode", (("vinyl", HEAD), ("flac -8", HEAD)), gap_note=" (thread-matched)")
throughput_panel(
    ax4, [("vinyl decode", HEAD), ("vinyl decode", 1), ("flac decode", 1)],
    "decode", (("vinyl decode", HEAD), ("flac decode", 1)))
fig2.suptitle("Throughput — Vinyl (verified) vs libFLAC 1.5.0, real-audio corpora")
fig2.tight_layout()
fig2.savefig(os.path.join(out_dir, "real_performance.png"))
print("wrote real_performance.png")

# ── scaling with thread count ───────────────────────────────────────────
SCALED = [("vinyl", "encode"), ("flac -8", "encode"), ("vinyl decode", "decode")]


def scaled_label(family, kind):
    """`vinyl decode` already names its direction; `vinyl` does not."""
    return family if kind in family else f"{family} ({kind})"

counts = sorted(threadsets["vinyl"])

fig3, (ax5, ax6) = plt.subplots(1, 2, figsize=(11, 5), dpi=150)
for family, kind in SCALED:
    ns = [n for n in sorted(threadsets[family]) if (family, n) in speed]
    ys = [corpus_speed((family, n)) for n in ns]
    ax5.plot(ns, ys, ms=6, label=scaled_label(family, kind), **FAMILY[family],
             ls="-" if kind == "encode" else "--")
# libFLAC's decoder cannot be swept, so it is a reference level, not a curve
flac_dec = corpus_speed(("flac decode", 1))
if flac_dec:
    ax5.axhline(flac_dec, color=FAMILY["flac decode"]["color"], ls=":", lw=1.6)
    # Left end: the curves all start low there, so the space above the level
    # is clear.  x in axes fraction (inset from the spine), y in data units so
    # the label stays pinned to the line it names.
    ax5.annotate(f"flac decode, 1 thread (no -j) — {flac_dec:.0f} MB/s",
                 xy=(0.02, flac_dec),
                 xycoords=blended_transform_factory(ax5.transAxes, ax5.transData),
                 xytext=(0, 4), textcoords="offset points",
                 ha="left", va="bottom", fontsize=8,
                 color=FAMILY["flac decode"]["color"])
ax5.set_xscale("log", base=2)
ax5.set_xticks(counts)
ax5.set_xticklabels([str(c) for c in counts])
ax5.xaxis.set_minor_formatter(NullFormatter())
ax5.set_xlabel("threads")
ax5.set_ylabel("corpus throughput, raw MB/s (higher = faster)")
ax5.set_title("Throughput vs threads")
ax5.grid(alpha=0.25, which="both")
ax5.legend(fontsize=8, loc="upper left")

for family, kind in SCALED:
    ns = [n for n in sorted(threadsets[family]) if (family, n) in speed]
    base = corpus_speed((family, ns[0]))
    ax6.plot(ns, [corpus_speed((family, n)) / base for n in ns], ms=6,
             label=scaled_label(family, kind), **FAMILY[family],
             ls="-" if kind == "encode" else "--")
ax6.plot(counts, counts, color="#94a3b8", ls=":", lw=1.4, label="ideal (linear)")
ax6.set_xscale("log", base=2)
ax6.set_yscale("log", base=2)
ax6.set_xticks(counts)
ax6.set_xticklabels([str(c) for c in counts])
ax6.set_yticks(counts)
ax6.set_yticklabels([f"{c}×" for c in counts])
ax6.xaxis.set_minor_formatter(NullFormatter())
ax6.yaxis.set_minor_formatter(NullFormatter())
ax6.set_xlabel("threads")
ax6.set_ylabel(f"speedup vs {counts[0]} thread")
ax6.set_title("Parallel speedup")
ax6.grid(alpha=0.25, which="both")
ax6.legend(fontsize=8, loc="upper left")

fig3.suptitle("Scaling with thread count — real-audio corpora, "
              f"{n_units} units / total corpus time")
fig3.tight_layout()
fig3.savefig(os.path.join(out_dir, "real_threads.png"))
print("wrote real_threads.png")

# ── markdown summary tables ─────────────────────────────────────────────
with open(os.path.join(out_dir, "real_summary.md"), "w") as f:
    f.write("### Compression, audio-frame payload as % of raw PCM\n\n")
    f.write("| category | units | vinyl | flac -5 | flac -8 |\n|---|---:|---|---|---|\n")
    for c in cats:
        cells = " | ".join(
            f"{100 * catbytes[c][e][0] / catbytes[c][e][1]:.1f}%" for e in RATIO_FAMILIES)
        f.write(f"| {c} | {len(catunits[c])} | {cells} |\n")
    cells = " | ".join(f"{100 * total(e)[0] / total(e)[1]:.1f}%" for e in RATIO_FAMILIES)
    f.write(f"| **TOTAL** | {n_units} | {cells} |\n\n")

    f.write("### Whole-file size as % of raw PCM (metadata included)\n\n")
    f.write("| " + " | ".join(RATIO_FAMILIES) + " |\n")
    f.write("|" + "---|" * len(RATIO_FAMILIES) + "\n| ")
    f.write(" | ".join(f"{100 * filebytes[e][0] / filebytes[e][1]:.1f}%"
                       for e in RATIO_FAMILIES) + " |\n\n")

    f.write(f"### Corpus throughput at {HEAD} threads, total raw MB ÷ total seconds\n\n")
    head = [("vinyl", HEAD), ("flac -5", 1), ("flac -8", 1), ("flac -8", HEAD),
            ("vinyl decode", HEAD), ("flac decode", 1)]
    head = [j for j in head if j in speed]
    f.write("| suite | " + " | ".join(f"{fam} -j{n}" for fam, n in head) + " |\n")
    f.write("|---|" + "---|" * len(head) + "\n")
    for s in suites + ["TOTAL"]:
        keys = suites if s == "TOTAL" else [s]
        cells = [f"{corpus_speed(j, keys):.0f} MB/s" for j in head]
        label = f"**{s}**" if s == "TOTAL" else s
        f.write(f"| {label} | " + " | ".join(cells) + " |\n")

    f.write("\n### Scaling with thread count, corpus throughput\n\n")
    f.write("| threads | " + " | ".join(f"{fam} ({kind})" for fam, kind in SCALED)
            + " | flac decode |\n")
    f.write("|---:|" + "---|" * (len(SCALED) + 1) + "\n")
    for n in counts:
        cells = []
        for family, _ in SCALED:
            value = corpus_speed((family, n)) if (family, n) in speed else None
            cells.append(f"{value:.0f} MB/s" if value else "—")
        cells.append(f"{flac_dec:.0f} MB/s" if n == 1 and flac_dec else "no `-j`")
        f.write(f"| {n} | " + " | ".join(cells) + " |\n")
    f.write("\nSpeedup at %d threads: " % counts[-1] + ", ".join(
        f"{fam} {corpus_speed((fam, counts[-1])) / corpus_speed((fam, counts[0])):.2f}×"
        for fam, _ in SCALED if (fam, counts[-1]) in speed) + ".\n")
print("wrote real_summary.md")
