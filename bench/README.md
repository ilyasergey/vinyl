# Benchmarks

Vinyl vs libFLAC 1.5.0, measured on the 37-file synthetic 16-bit corpus
of [`gen_corpus.py`](gen_corpus.py) — six content categories (tonal,
waveforms, noise, tonal+noise mixes, degenerate signals, stereo pairs).

Regenerate everything with:

```sh
./bench/run.sh        # times both codecs, writes results.csv (verifies every vinyl output with flac -t)
python3 bench/plot.py # renders compression.png / performance.png, summary.md
```

`corpus/`, `out/`, `results.csv`, `summary.md`, and the two PNGs are all
generated artifacts.

All percentages are compression ratios: encoded size as a fraction of
the raw PCM. 0% would mean the file vanished, 100% means no compression
at all — lower is better.

## Compression

**Top** — per-file cactus: each encoder's ratios sorted ascending; a
curve that stays lower compresses better. **Bottom** — aggregate ratio
(total encoded bytes ÷ total raw bytes) per content category:

![Compression vs libFLAC](compression.png)

| category | vinyl | flac -0 | flac -5 | flac -8 |
|---|---|---|---|---|
| tonal | **19.7%** | 40.2% | 22.3% | 20.1% |
| wave | **39.2%** | 44.5% | 43.9% | 40.9% |
| noise | **77.5%** | 77.9% | 77.5% | 77.5% |
| mixed | 72.0% | 72.6% | 71.0% | **70.9%** |
| degen | **22.1%** | 46.6% | 22.9% | 22.9% |
| stereo | 27.2% | 31.8% | 26.7% | **26.6%** |
| **TOTAL** | **39.5%** | 49.4% | 40.9% | 39.8% |

With the certified heuristics (Levinson–Durbin LPC, wasted-bit
detection, stereo-mode decision, adaptive Rice partitioning), the
verified encoder's overall ratio **beats `flac -8`** on this corpus
(39.5% vs 39.8% of raw), winning tonal/waveform/degenerate content and
trailing slightly on noisy mixes and stereo.

## Speed

Per-file throughput (log scale), sorted slowest→fastest per codec; a
curve that sits higher is faster. Left: encode. Right: decode (the
shipped buffered decoder):

![Throughput vs libFLAC](performance.png)

Honest reading: Vinyl encodes at ~0.16 MB/s (median; the checked encoder
re-validates every heuristic certificate) and decodes at ~1.5 MB/s,
vs libFLAC's ~30–37 MB/s for both. The encoder still runs on the
proof-oriented `List Bool` bit model and does exhaustive searches;
performance work is deliberately deferred to M6, *after* the capstone
makes optimization safe: any faster implementation must re-prove the
same simulation theorems.
