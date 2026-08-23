# Benchmarks

Vinyl vs libFLAC 1.5.0, measured on the 37-file synthetic 16-bit corpus
of [`gen_corpus.py`](gen_corpus.py) — six content categories (tonal,
waveforms, noise, tonal+noise mixes, degenerate signals, stereo pairs).

Regenerate everything with:

```sh
./bench/run.sh        # five measured runs per case by default
BENCH_RUNS=9 ./bench/run.sh
python3 bench/plot.py # re-render plots/tables from an existing results.csv
```

`corpus/`, `out/`, `results.csv`, `summary.md`, and the two PNGs are all
generated artifacts. Each case receives an untimed warmup. The measured
encode/decode commands are then shuffled with a fixed seed, and
`results.csv` records their median wall time. Correctness checks (`flac -t`
and a byte-for-byte PCM comparison) run outside the timed intervals.

Timing is deliberately owned by one persistent Python parent process. The
original shell harness launched `python3` separately for every timestamp;
the startup of the second timestamp process added roughly 19–22 ms to every
codec invocation. That fixed surcharge was especially large beside
libFLAC's 7–10 ms work on these mostly 1 MB files, so the old dashboard
substantially understated the relative gap. Results produced by the old
harness must not be compared with results produced by the current one.

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
| noise | 77.8% | 77.9% | **77.5%** | **77.5%** |
| mixed | 72.0% | 72.6% | 71.0% | **70.9%** |
| degen | **22.1%** | 46.6% | 22.9% | 22.9% |
| stereo | 27.2% | 31.8% | 26.7% | **26.6%** |
| **TOTAL** | **39.6%** | 49.4% | 40.9% | 39.8% |

With the certified heuristics (Levinson–Durbin LPC, wasted-bit
detection, stereo-mode decision, adaptive Rice partitioning), the
encoder's overall ratio **beats `flac -8`** on this corpus
(39.6% vs 39.8% of raw), winning tonal/waveform/degenerate content and
trailing slightly on noise, noisy mixes, and stereo.

## Speed

Per-file throughput (log scale), sorted slowest→fastest per codec; a
curve that sits higher is faster. Dashed lines mark each codec's median
and the arrow labels the median gap. **Top** — encode. **Bottom** —
decode (the shipped buffered decoder):

![Throughput vs libFLAC](performance.png)

Current five-run medians (2026-08-23): Vinyl encode 24.5 MB/s and Vinyl
decode 79.2 MB/s, versus 108.7 MB/s for `flac -5` encode, 75.1 MB/s for
`flac -8` encode, and 125.1 MB/s for libFLAC decode. That is a
**1.58× decode gap** and a 4.4× encode gap against `flac -5` — **3.1×
against `flac -8`, the level whose compression Vinyl matches**.

Progress this session, all with the capstones unchanged and no proof debt:

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| corrected-timer baseline | 13.9 MB/s | 30.6 MB/s | 5.2× | 4.0× |
| allocation-free CRC ranges | 13.9 MB/s | 30.6 MB/s | 5.2× | 4.0× |
| array-typed decoder core | 15.3 MB/s | 40.3 MB/s | 4.8× | 3.1× |
| frame-parallel decoding | 18.6 MB/s | 67.4 MB/s | 4.0× | 1.8× |
| parallel PCM serialization | 18.5 MB/s | 73.9 MB/s | 4.0× | 1.68× |
| decode task granularity 8 | 18.8 MB/s | 78.0 MB/s | 3.9× | **1.58×** |
| channel-major deinterleave | 21.4 MB/s | 78.6 MB/s | 3.5× | 1.59× |
| unboxed `FloatArray` search | 21.9 MB/s | 78.3 MB/s | 3.4× | 1.60× |
| deinterleave in the workers | 23.8 MB/s | 79.3 MB/s | 3.15× | 1.59× |
| parallel certificate serialize | 24.5 MB/s | 79.2 MB/s | **3.06×** | 1.58× |

Two structural changes did the work. First, the decoder used to convert
every decoded sample from its `Array Int` into a `List Int` (the type the
theorems are phrased over) and then the serializer rebuilt the very same
arrays; `Flac.Decode.decodeArrays` is now the decoder core, with
`decodeOption` defined as that plus the conversion, so consumers that
want bytes skip the round-trip (`pcmBytesA_eq`, `pcm16FastA_eq`,
`decodePcm16A_eq`).

Second, frames now decode in parallel. FLAC frames are byte-aligned and
self-contained and `BitReader` reads a shared immutable `ByteArray` at an
absolute bit position, so decoding the frame at position `p` on a worker
runs *literally the call the serial loop runs there*. Each worker result
carries the frame reader's own equation as a proof field, so consuming
one trusts neither the thread nor the sync-code scan that guessed the
position — a wrong guess costs work, never correctness. `readFramesFast_eq`
collapses the whole parallel path back to the serial loop, leaving
`decodeOption_eq_reference` and every capstone untouched.

Serialization then became the decoder's serial bottleneck (150 ms of a
480 ms 40 MB decode), so interleaved PCM is now written one task per
64Ki-sample window — the interleaved layout is sample-major, so windows
serialize independently and concatenate.

On the encode side, four things landed. The fast encoder is certified per
call by decoding its own output with the verified decoder, so it inherits
every decoder gain directly. Deinterleaving moved from a per-sample
`Array.modify` over the outer array of channels into the frame workers
themselves, which read their own sample window out of the shared
immutable PCM bytes — that removed a serial pass worth 17% of encode plus
a second full copy per frame. The float search now holds block-sized data
in an unboxed `FloatArray` rather than an `Array Float` that boxed every
element. And the certificate's own re-serialization, which was 10% of
encode and serial, now runs one task per sample window.

What remains of the encode gap is not algorithmic. Profiling puts about
three quarters of encode in the parallel frame workers, and roughly a
third of that in exactly costing the five or six candidate LPC orders —
Lean `Int` multiply–accumulate against libFLAC's `int32` SIMD, with
`Array Int64` being *worse* in Lean (boxed per element), so the current
representation is already the best available in pure Lean. Scoring fewer
candidates closes part of the gap but gives up compression: measured on
this corpus, keeping the best two candidates by Levinson estimate runs
~1.3× faster at 40.0% instead of 39.6%, which would forfeit the win over
`flac -8`. That tradeoff is recorded rather than taken. The one remaining
change that would improve encode without trading compression or adding
trusted code is retiring the runtime certificate (~20% of encode) in
favour of the statically verified emitter — milestone M6b.

The important correction is methodological: libFLAC did not suddenly get
faster, and Vinyl also measures faster without the timestamp surcharge.
Removing a fixed ~20 ms error simply benefits the shorter libFLAC commands
much more. Compare medians only *within the same run*; machine load and
thermal state still move absolute throughput, which is why the figure plots
both codecs together and interleaves their measurements.

Both Vinyl paths retain zero proof debt: decoder fast paths are proved equal
to their specifications, while the production encoder currently certifies
each call by decoding its own output with the verified decoder and comparing
it with the input (falling back to the verified encoder on mismatch).
