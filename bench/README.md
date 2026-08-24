# Benchmarks

Vinyl vs libFLAC 1.5.0, in two suites that answer different questions:

| suite | material | units | raw PCM | what it is for |
|---|---|---:|---:|---|
| [**Part 1 — real audio**](#part-1--real-audio-benchmarks) | EBU SQAM + LibriSpeech recordings | 143 | 1.73 GiB | the headline numbers |
| [**Part 2 — synthetic micro-benchmarks**](#part-2--synthetic-micro-benchmarks) | 37 generated 1 MB signals | 37 | 37 MB | per-category coverage, regression detection |
| [**Part 3 — optimization history**](#part-3--optimization-history) | a 32 MB probe | 1 | 32 MB | what each tuning stage bought |

All percentages are compression ratios: encoded size as a fraction of the raw
PCM, so 100% means no compression and **lower is better**. All throughputs are
raw PCM MB/s of wall time, so **higher is faster**.

Read Part 1 for what the codec does on audio someone would actually encode.
Read Part 2 for which *content categories* a change moved — its 1 MB files are
sized for compression coverage, not throughput. **Never quote a number from one
suite against a baseline from the other**, and never against a dashboard
produced by the pre-2026-08-23 shell harness (see
[the timing note](#the-timing-note-that-invalidates-older-dashboards)).

---

## Part 1 — Real-audio benchmarks

### What the real benchmarks are

The synthetic corpus in Part 2 is 37 *generated* signals — sine sweeps, square
waves, white and brown noise, deliberately degenerate cases like pure silence
and samples with three wasted low bits. It is good at what it is for: each file
isolates one property of the format, so a compression regression can be
attributed to a content category. What it is not is *audio*, and two conclusions
this repository drew from it turned out to be artifacts of that (see
[what the real corpus settled](#what-the-real-corpus-settled)).

The real-audio suite encodes actual recordings — instruments, voices, orchestra,
pop mixes, read speech in clean and noisy conditions — at sizes where a codec
invocation measures the codec rather than process startup.

#### The corpora

| corpus | selector | archive | prepared PCM | native format | licence |
|---|---|---:|---:|---|---|
| **EBU SQAM** (Tech 3253) | `sqam` (default) | 167.4 MiB | 620 MB, 70 tracks | 2ch 44.1 kHz S16 | R&D use; no other commercial use |
| **LibriSpeech `test-clean`** | `librispeech-test-clean` | 330.6 MiB | 622 MB, 2,620 utterances | 1ch 16 kHz S16 | CC BY 4.0 |
| **LibriSpeech `test-other`** | `librispeech-test-other` | 313.5 MiB | 615 MB, 2,939 utterances | 1ch 16 kHz S16 | CC BY 4.0 |

**SQAM** is the European Broadcasting Union's sound-quality assessment material:
70 short tracks chosen to *stress* codecs, categorised by Tech 3253 into
alignment tones, artificial signals, 36 single instruments, solo instruments,
vocals, speech, vocal-orchestra, orchestra, and pop. It is already in Vinyl's
native encoder format, and it is deliberately harder than a music library —
single instruments recorded dry have far less to correlate away than a mix.

**LibriSpeech** is read English audiobook speech from LibriVox, 16 kHz mono. The
two `test` splits are the standard held-out sets: `test-clean` is the
higher-recording-quality half, `test-other` the harder half. Speech at 16 kHz is
the least compressible material in this suite (about 55% of raw, against 27% for
single instruments), and it exercises a sample rate and channel count that SQAM
does not.

#### Why these two, and not the others

[`CORPORA.md`](CORPORA.md) also records identities and fetch commands for
FSD50K evaluation audio (6.2 GB), MUSDB18-HQ (22.7 GB), and MAESTRO v3 (101 GB).
Those are deliberately **not** part of this suite: at 1.73 GiB the two corpora
here already run six measured passes in about fifteen minutes, and adding an
order of magnitude of audio buys resolution the comparison does not need — the
gaps being measured are 3× and 5%, not 2%. They remain documented for anyone who
wants a music-mixture or general-audio corpus later.

#### What a benchmark unit is

`real_fetch.py` writes one canonical S16LE PCM file per source recording.
That is the right granularity for SQAM, whose tracks are 2.6–46.9 MB. It is not
the right granularity for LibriSpeech, whose utterances average 0.22 MB: at that
size a codec invocation is dominated by process startup, which is a real cost
but not the one being measured here.

[`real_units.py`](real_units.py) therefore builds the benchmark units:

- **SQAM** — one unit per track, benchmarked in place. 70 units, median 5.9 MB.
- **LibriSpeech** — one unit per *speaker*, concatenating that speaker's
  utterances in sorted order into a single stream. 73 units (40 clean, 33
  other), 5.1–19.8 MB. Concatenation is raw-PCM only: no resampling, no gain,
  no reordering, and both codecs receive byte-identical input. Speaker is the
  coarsest grouping the corpus labels, which keeps the streams large without
  mixing voices inside a unit.

`units.csv` records each unit's format, byte count, source-file count, and
SHA-256, so a run is reproducible against a specific set of streams.

#### Reproducing it

```sh
python3 bench/real_fetch.py --list                  # what is available
python3 bench/real_fetch.py --accept-ebu-terms      # SQAM (review EBU terms first)
python3 bench/real_fetch.py --corpus librispeech    # both LibriSpeech test splits
./bench/real_run.sh                                 # units, measure, plot
```

[`CORPORA.md`](CORPORA.md) has the category selectors, licence restrictions,
checksums and prepared-corpus layout; [`real_corpora.lock.json`](real_corpora.lock.json)
pins the exact archives these numbers were produced from, with locally observed
SHA-256 digests.

`BENCH_RUNS` sets measured repetitions (default 5), `BENCH_THREADS` the thread
count both codecs get for their multithreaded rows (default: all cores),
`BENCH_SUITES` restricts to a comma-separated subset, and `BENCH_LIMIT` caps the
unit count for a smoke run. Audio, prepared PCM, streams and encoder output all
live under ignored directories; nothing in this section is committed except the
scripts, the figures, `real_results.csv` and `real_summary.md`.

### How the real suite is measured

Timing is the same instrument as Part 2: one persistent Python parent holding a
`perf_counter_ns`, one untimed warmup per case, then `BENCH_RUNS` measured runs
whose order is shuffled with a fixed seed so no implementation keeps the same
thermal and cache position. The reported number is the median. Correctness
checks run outside every timed interval.

Three things differ from the synthetic suite, each because real audio made them
measurable:

**1. Sizes are recorded twice.** libFLAC writes 8,826 bytes of padding,
seektable and vendor comment per file at its defaults; Vinyl writes STREAMINFO
alone, 42 bytes. `real_results.csv` therefore carries both `bytes` (whole file)
and `audio_bytes` (the coded frames, found by walking the metadata block headers
— [`flacsize.py`](flacsize.py)). Only the payload column can support a
compression claim. On these units the distinction is cosmetic — 8.8 kB against a
15 MB stream — which is exactly why it had to be measured here: it is *not*
cosmetic on Part 2's 1 MB files.

**2. libFLAC is measured at both thread counts.** libFLAC 1.5.0 takes `-j`, and
Vinyl's encoder is frame-parallel, so the default single-threaded row alone
would compare 8 Vinyl threads against 1 libFLAC thread. Both are recorded:
`flac -8` at its default one thread, and `flac -8 -j8` at the same count Vinyl
uses. `-j` changes scheduling only — the two produce byte-identical output on
**143/143** units, verified from the recorded sizes. libFLAC's *decoder* has no
threading option, so the decode comparison is unavoidably 8 threads against 1
and is labelled as such on the figure.

**3. Every unit is cross-decoded.** Per unit, outside the timed intervals: `flac
-t` accepts Vinyl's stream and its MD5 signature; Vinyl's `--decode-fast`
reproduces the input exactly; and **Vinyl's decoder reproduces libFLAC's `-8`
stream exactly**. All three passed on all 143 units — the harness aborts on the
first mismatch. The third is the interesting one: 1.73 GiB of libFLAC-encoded
real audio, at the preset that uses the widest search, decoded byte-for-byte by
the verified decoder. That is interoperability evidence, not a theorem, which is
why it is tested.

### Compression

**Top** — per-unit cactus: each encoder's audio-frame ratios sorted ascending, so
a curve that stays lower compresses better. **Bottom** — aggregate ratio (total
coded bytes ÷ total raw bytes) per content category. `flac -8 -j8` is omitted
from both: it is byte-identical to `flac -8` and would draw a duplicate curve.

![Compression vs libFLAC on real audio](real_compression.png)

| category | units | vinyl | flac -5 | flac -8 |
|---|---:|---|---|---|
| alignment | 2 | 22.0% | 22.0% | **20.9%** |
| artificial | 5 | 7.6% | 7.8% | **7.4%** |
| single-instrument | 36 | 29.0% | 27.4% | **27.1%** |
| solo-instrument | 6 | 32.4% | 30.8% | **30.5%** |
| vocal | 5 | 34.9% | 33.2% | **32.6%** |
| vocal-orchestra | 4 | 41.3% | 39.6% | **39.3%** |
| orchestra | 4 | 34.1% | 32.2% | **32.1%** |
| pop | 2 | 40.4% | 38.9% | **38.4%** |
| speech | 6 | 31.9% | 30.8% | **30.4%** |
| speech-clean | 40 | 57.5% | 55.9% | **55.2%** |
| speech-other | 33 | 55.2% | 53.6% | **52.9%** |
| **TOTAL** | **143** | 47.6% | 46.1% | **45.5%** |

**`flac -8` compresses real audio better than Vinyl in every category**, and so
does `flac -5`. Per unit, Vinyl's payload is smaller than `flac -8`'s on
**1 of 143** units and smaller than `flac -5`'s on **3 of 143**; the median unit
is **4.7% larger** than `flac -8`'s (range −8.5% to +12.9%) and **3.1% larger**
than `flac -5`'s (range −23.7% to +8.6%).

Including metadata does not change this — whole-file totals are 47.6% / 46.1% /
45.6% — because 8.8 kB is nothing against a 15 MB unit. That equality is the
point: it is the control that shows the metadata correction in Part 2 is real
rather than an accounting preference.

### Speed

Per-unit throughput, log scale, sorted slowest→fastest per implementation; a
curve that sits higher is faster. Dashed lines mark the two medians the arrow
spans. Thread counts are on every legend entry, because a frame-parallel codec
beside a single-threaded one is the whole comparison. **Top** — encode.
**Bottom** — decode (the shipped buffered decoder).

![Throughput vs libFLAC on real audio](real_performance.png)

Corpus throughput — total raw MB ÷ total seconds, which weights by size rather
than by unit and so is the number to quote for aggregate speed:

| suite | vinyl | flac -5 | flac -8 | flac -8 -j8 | vinyl decode | flac decode |
|---|---|---|---|---|---|---|
| | 8 threads | 1 thread | 1 thread | 8 threads | 8 threads | 1 thread |
| sqam | 101 MB/s | 122 MB/s | 62 MB/s | **256 MB/s** | **214 MB/s** | 197 MB/s |
| librispeech-test-clean | 95 MB/s | 153 MB/s | 89 MB/s | **374 MB/s** | **207 MB/s** | 187 MB/s |
| librispeech-test-other | 88 MB/s | 151 MB/s | 86 MB/s | **355 MB/s** | **195 MB/s** | 183 MB/s |
| **TOTAL** | 94 MB/s | 140 MB/s | 77 MB/s | **319 MB/s** | **205 MB/s** | 189 MB/s |

Three separate comparisons, all of which need stating:

- **Against thread-matched libFLAC, encode is 3.4× behind** (94 vs 319 MB/s
  corpus; ×3.21 on per-unit medians). Vinyl is faster on **0 of 143** units.
  This is the honest wall-clock encode number.
- **Against single-threaded `flac -8`, encode is 1.22× ahead** (94 vs 77 MB/s;
  faster on 129 of 143 units). This is the preset's default configuration and
  the historical reference in Part 3, but it is 8 threads against 1.
- **Against single-threaded `flac -5`, encode is 1.49× behind** (94 vs
  140 MB/s; faster on 5 of 143 units) — and `flac -5` also compresses better.
  So there is no libFLAC preset here that Vinyl beats on both axes.

**Decode is 1.08× ahead** (205 vs 189 MB/s corpus, ×1.11 on medians; faster on
120 of 143 units) — with 8 threads against libFLAC's 1, because libFLAC has no
multithreaded decoder to match. Per core the verified decoder is well behind;
per invocation on a multicore machine it is ahead. Total CPU time is not
recorded, so the per-core figure is not quantified here.

The SQAM column is where the two encoders diverge most: `flac -8` drops to
62 MB/s on stereo 44.1 kHz material against 86–89 MB/s on mono speech, while
Vinyl runs slightly *faster* on SQAM (101 MB/s) than on LibriSpeech. Stereo
costs libFLAC's `-8` an exhaustive mid/side decision that Vinyl's certified
heuristic decides directly.

### What the real corpus settled

Two claims this repository carried from the synthetic corpus do not survive.

**"Vinyl's compression beats `flac -8`."** It does not, and it never did — the
comparison was whole-file. libFLAC's 8,826 bytes of metadata are about 2.2% of
the ~400 kB it emits for a 1 MB synthetic file, four times the 0.5% relative
difference the claim rested on. Re-measured on coded frames, the synthetic corpus
gives Vinyl 39.6% against `flac -8`'s **39.0%** (Part 2), and real audio gives
47.6% against 45.5%. `flac -8` was ahead on both corpora all along. The old
`bench/README.md` flagged this as unresolved and said the real-corpus run must
settle it before a speed baseline was chosen; this is that run, and it settles it
the other way.

**"Encode is at parity with `flac -8`."** At one thread each it would be — but
libFLAC 1.5.0 has `-j` and Vinyl has been frame-parallel since session 6, so
parity against the single-threaded default was measuring a thread count, not a
codec. Thread-matched, the gap is 3.4×.

What holds up:

- **Decode is genuinely competitive**, 1.08× ahead of libFLAC on real audio at
  8 threads against 1 — and that is the direction where the proofs are deepest
  (every decoder fast path is proven equal to its bit-level specification,
  frame-parallel decoding and serialization included).
- **Interoperability is solid.** 143/143 units round-trip through Vinyl, pass
  `flac -t`, and — in the other direction — libFLAC's `-8` output decodes
  byte-exactly under the verified decoder.
- **The ratio is close, not competitive.** 4.7% behind `flac -8` on the median
  unit is a search-quality gap, not a format gap:
  `Flac.Heuristics.lpcCandidates` carries the measured tradeoff curve, and
  [where the remaining encode gap is](#where-the-remaining-encode-gap-is)
  describes what libFLAC's `-8` buys with several apodization windows that Vinyl
  does not have.

### Known gaps in this suite

- **No CPU-time accounting.** Every number is wall clock. The thread counts are
  labelled everywhere, but a per-core comparison would need `rusage` per
  invocation, which the harness does not record yet.
- **`flac -0` is not measured on real audio**, so Vinyl's ratio is bracketed
  from above by `flac -5` but not from below.
- **16-bit only, two sample rates.** Both corpora are S16; the codec and the
  theorems cover depths 1–32. No 24-bit or 96 kHz material is benchmarked.
- **SQAM may not be redistributed.** The fetcher verifies publisher identity and
  records hashes, but the audio stays local; a third party reproducing these
  numbers must accept the EBU terms themselves.

---

## Part 2 — Synthetic micro-benchmarks

Thirty-seven generated 16-bit signals from [`gen_corpus.py`](gen_corpus.py) in
six content categories — tonal, waveforms, noise, tonal+noise mixes, degenerate
signals, stereo pairs — at 1 MB each. Each file isolates one property of the
format, which is what makes this suite useful for attributing a compression
change to a category. It is a **micro-benchmark**, not a proxy for audio: for
that, read [Part 1](#part-1--real-audio-benchmarks).

Regenerate everything with:

```sh
./bench/run.sh          # five measured runs per case by default
BENCH_RUNS=15 ./bench/run.sh
python3 bench/plot.py   # re-render plots/tables from an existing results.csv
```

`corpus/`, `out/`, `results.csv`, `summary.md`, and the two PNGs are all
generated artifacts.

### The timing note that invalidates older dashboards

Timing is owned by one persistent Python parent process. The original shell
harness launched `python3` separately for every timestamp; the startup of the
second timestamp process added roughly 19–22 ms to every codec invocation. That
fixed surcharge was especially large beside libFLAC's 7–10 ms of work on these
1 MB files, so the old dashboard substantially understated the relative gap.
**Results produced by the pre-2026-08-23 harness must not be compared with
results produced by the current one.**

### Read the corpus numbers with the file size in mind

These files are 1 MB each by design: `gen_corpus.py` sizes them for compression
coverage, not throughput. At that size **process startup is a third of the
measurement** — 3.1 ms of Lean runtime init against libFLAC's 2.7 ms, on an
8–9 ms decode — and only 0.09 ms of Vinyl's share is this project's own module
initialization (a trivial Lean binary also takes 3.10 ms; the binary is already
statically linked against Lean, so there is no dynamic-loading cost to remove).

### Compression

Ratios are the **audio-frame payload**, metadata excluded. This matters far more
here than in Part 1: libFLAC's default 8,826 bytes of padding, seektable and
vendor comment are about 2.2% of the ~400 kB it emits for a 1 MB file, several
times the difference between the encoders being compared.

**Top** — per-file cactus: each encoder's ratios sorted ascending; a curve that
stays lower compresses better. **Bottom** — aggregate ratio per content
category:

![Compression vs libFLAC](compression.png)

| category | vinyl | flac -0 | flac -5 | flac -8 |
|---|---|---|---|---|
| tonal | 19.8% | 39.4% | 21.5% | **19.3%** |
| wave | **39.2%** | 43.7% | 43.1% | 40.1% |
| noise | 77.8% | 77.1% | **76.7%** | **76.7%** |
| mixed | 72.0% | 71.7% | 70.2% | **70.0%** |
| degen | 22.1% | 45.8% | **22.0%** | **22.0%** |
| stereo | 27.2% | 31.4% | 26.3% | **26.2%** |
| **TOTAL** | 39.6% | 48.6% | 40.2% | **39.0%** |

`flac -8` is ahead overall and in five of six categories; Vinyl wins `wave` and
sits between `flac -5` and `flac -8` on the total. Whole-file totals — the
accounting this dashboard used until 2026-08-24 — are 39.6% / 49.4% / 40.9% /
39.8%, which is where the retracted "beats `flac -8`" claim came from. The
0.2-point whole-file lead was smaller than the metadata difference producing it.
See [what the real corpus settled](#what-the-real-corpus-settled).

### Speed

**Top** — encode. **Bottom** — decode (the shipped buffered decoder). Per-file
throughput on a log scale, sorted slowest→fastest per implementation; dashed
lines mark the two medians the arrow spans.

![Throughput vs libFLAC](performance.png)

Fifteen-run medians, 2026-08-24:

| | Vinyl (8 threads) | libFLAC (1 thread) | gap |
|---|---|---|---|
| decode | 124.9 MB/s | 125.6 MB/s | 1.01× |
| encode | 75.0 MB/s | 74.9 MB/s (`flac -8`) | 1.00× |
| encode | 75.0 MB/s | 107.6 MB/s (`flac -5`) | 1.44× |

**These are 8 threads against 1.** libFLAC 1.5.0 takes `-j`, which this
dashboard does not exercise; on real audio the thread-matched encode gap is
3.4× ([Part 1](#speed)). Read the `flac -8` row as continuity with the stage
tables in Part 3, not as a parity claim.

Run-to-run spread differs by direction: repeating the whole run moves the
*decode* gap by ~1% but the *encode* gap by ~5% (1.02–1.07× across six passes).
Encoding is `Task`-parallel, so at 1 MB it is far more sensitive to whatever
else the machine is doing than single-threaded libFLAC is. Quote these gaps to
two significant figures, only ever against baselines from the same run — and
prefer the size sweep below, or the 32 MB probe in Part 3, for judging a change.

### Throughput against file size

Same material, medians, single-threaded libFLAC throughout:

| PCM | Vinyl decode | libFLAC | gap | Vinyl encode | `flac -8` | gap |
|---|---|---|---|---|---|---|
| 1 MB | 104.4 MB/s | 121.7 MB/s | 1.17× | 70.9 MB/s | 70.7 MB/s | 1.00× |
| 2 MB | 140.3 MB/s | 150.9 MB/s | 1.08× | 82.3 MB/s | 81.8 MB/s | 0.99× |
| 4 MB | 178.8 MB/s | 168.7 MB/s | 0.94× | 89.6 MB/s | 87.0 MB/s | 0.97× |
| 8 MB | 198.7 MB/s | 178.6 MB/s | 0.90× | 94.8 MB/s | 89.4 MB/s | 0.94× |
| 16 MB | 209.7 MB/s | 185.9 MB/s | 0.89× | 95.9 MB/s | 90.5 MB/s | 0.94× |
| 32 MB | 217.2 MB/s | 189.6 MB/s | 0.87× | 97.0 MB/s | 91.6 MB/s | 0.94× |

Both directions overtake *single-threaded* libFLAC once startup stops
dominating: encode from 2 MB, decode from 4 MB. Each row is the better of two
passes, which is the least-contended estimate a working machine allows. Part 1
measures the same effect on real units of the same size and reaches the same
place for decode (205 vs 189 MB/s) — and the opposite place for encode, once
libFLAC is given the same threads.

---

## Part 3 — Optimization history

Where each tuning stage got its speed, kept for anyone pushing further. Two
things to know before reading the tables:

- **Ratios quoted inside these stage tables are whole-file**, the accounting in
  use at the time. Statements like "still ahead of `flac -8`" are superseded by
  [Part 1](#what-the-real-corpus-settled); what the ratio columns still
  establish is what each stage did *not* change, which is what they were for.
- **Gap columns are against single-threaded `flac -8`.** They are stage-to-stage
  measurements, not a codec comparison; for that, see Part 1.

### Sessions 6–7: parallelism and the array-typed decoder

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| corrected-timer baseline | 13.9 MB/s | 30.6 MB/s | 5.2× | 4.0× |
| array-typed decoder core | 15.3 MB/s | 40.3 MB/s | 4.8× | 3.1× |
| frame-parallel decoding | 18.6 MB/s | 67.4 MB/s | 4.0× | 1.8× |
| parallel PCM serialization | 18.5 MB/s | 73.9 MB/s | 4.0× | 1.68× |
| decode task granularity | 18.8 MB/s | 78.0 MB/s | 3.9× | 1.58× |
| channel-major deinterleave | 21.4 MB/s | 78.6 MB/s | 3.5× | 1.59× |
| unboxed `FloatArray` search | 21.9 MB/s | 78.3 MB/s | 3.4× | 1.60× |
| deinterleave in the workers | 23.8 MB/s | 79.3 MB/s | 3.15× | 1.59× |
| parallel certificate serialize | 24.5 MB/s | 79.2 MB/s | 3.06× | 1.58× |

### Sessions 8–9: exact float arithmetic, and not allocating

Measured on the 32 MB probe (mono, 4096-sample blocks), so not comparable
with the corpus medians above — only with each other.

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| session 7 end | 26.7 MB/s | 108.8 MB/s | 3.53× | 1.85× |
| float candidate searches | 33.3 MB/s | — | 2.90× | — |
| bit writer without tuples | 42.8 MB/s | — | 2.27× | — |
| unboxed PCM serialization | 43.5 MB/s | 117.2 MB/s | 2.24× | 1.76× |
| parallel sync-code scan | 44.6 MB/s | 126.5 MB/s | 2.18× | 1.65× |
| fused fixed-order search | 47.1 MB/s | 127.5 MB/s | 2.07× | 1.59× |
| frame-parallel serialization | 46.6 MB/s | 220.7 MB/s | 2.07× | **0.96×** |
| certificate via the byte path | 57.7 MB/s | 222.2 MB/s | 1.67× | 0.94× |
| three-byte Rice window | 58.5 MB/s | 246.2 MB/s | 1.63× | **0.83×** |
| MD5 off the critical path | 64.9 MB/s | 244.3 MB/s | 1.48× | 0.85× |
| three LPC orders, not five | 71.7 MB/s | 246.2 MB/s | 1.34× | 0.84× |
| float residual for emission | 73.7 MB/s | 244.3 MB/s | 1.32× | 0.85× |
| three autocorrelation lags per pass | 75.5 MB/s | 244.3 MB/s | **1.27×** | 0.85× |

Every stage but one kept the corpus ratio at 39.580% and the output
byte-identical to the verified encoder's; "three LPC orders" moved it to
39.634%, still ahead of `flac -8`'s 39.784%.

### Session 10: proving the encoder, and retiring its certificate

Same 32 MB probe, `flac -8` at 92.3 MB/s on it. Every row is
byte-identical to the previous one — the whole project was a proof project,
and the only changes to what the encoder *computes* were forced by what can
be proven at all.

| stage | encode | decode | encode gap (`-8`) |
|---|---|---|---|
| session 9 end | 75.3 MB/s | 199.3 MB/s | 1.23× |
| `Int` residual emission | 69.2 MB/s | 214.9 MB/s | 1.33× |
| plan sanitisation | 68.6 MB/s | 213.0 MB/s | 1.35× |
| stage 3 complete | 68.8 MB/s | 214.7 MB/s | 1.34× |
| self-certifying payloads | 68.5 MB/s | 215.0 MB/s | 1.35× |
| **certificate retired** | 97.7 MB/s | 215.8 MB/s | **0.94×** |

The whole cost of provability was 10% — `Int` residual emission 8%, plan
sanitisation and the rest under 1% each — and retiring the certificate paid
30% back. Encode ends *ahead of* `flac -8` on this probe, at unchanged
compression, which is what M6b was for.

The one change that was not free is worth naming: residual bits used to
come off the search's `FloatArray`s, and `lpcResidualArrF`'s own doc
asserted the unprovable step ("every value is an exact integer, so the
bytes emitted from it are the bytes an `Int` residual would emit"). That is
precisely what the certificate was covering. `Float` is opaque in Lean —
its operations are compiler intrinsics with no axiomatization — so a float
in the *bytes* can never be reasoned about, and emission had to move to the
exact `Int` residual first. Costing candidates in `Float` stays free,
because a search that picks the wrong candidate loses compression, never
correctness.

**Exact float arithmetic in the searches — and now in emission.** A search
only *chooses* a subframe, and every value it computes is an integer well
inside 2^53 (for 16-bit input: samples below 2^17, quantized coefficients
below 2^11, order at most 8, so prediction sums below 2^32, residuals
below 2^19, 4096-sample partition sums below 2^32). IEEE-754 doubles
represent those exactly, so an unboxed `FloatArray` search picks the *same
subframe bit for bit* at one hardware `fmul`/`fadd` per tap instead of
`lean_int_mul`/`lean_int_add` on a boxed `Array Int`. The same holds for
the residual that gets *emitted*, so the `Int` residual path is gone
entirely and `pushRiceRange` folds the zigzag magnitude straight off the
float. A differential test pins all of it against the verified encoder on
LPC, FIXED, noise, wasted-bit, constant and stereo material.

Two Lean codegen facts drove the tuning, and both cost real time to find.
`Float`-typed `let mut` variables carried across a `for` loop are **boxed
once per iteration** — an order-8 residual fold went 84 ms → 255 ms when
its accumulators moved from tail-recursion parameters into ten mutable
locals — so every accumulator here is a tail-recursion parameter. And
`Prod`'s fields are polymorphic, so a returned tuple **boxes any scalar in
it**: `BitWriter.flushGo` returned `ByteArray × UInt64 × Nat`, three heap
allocations per *bit push*, which put about a quarter of all encode work in
the allocator beneath it. Both dropped components were recoverable without
the tuple.

**Frame-parallel serialization.** Turning decoded samples into interleaved
PCM bytes was 46% of decode wall time and none of it was decoding:
`recombineA` concatenated every frame's channel arrays into whole-file
arrays (41 ms, serial) and `pcmBytesA` walked those again (61 ms — its task
fan-out bought nothing, because marking the shared `Array Int` channels
multi-threaded cost about what the parallelism saved). A frame covers a
contiguous sample range, so a frame *is* a serialization window; each
worker now emits its own frame's bytes, and a `ByteArray` is O(1) to mark
where `Array Int` channels are O(samples). `Flac/Spec/PcmBytes.lean` proves
it rather than asserting it.

**Three autocorrelation lags per pass.** Nine lags meant nine passes over
the windowed block, each re-reading both operands of every product.
`acorr3` reads `w[i]` and `w[i-lag]` and carries `w[i-lag-1]`/`w[i-lag-2]`
in registers, so a (lag, sample) pair costs two thirds of a load instead
of two; each lag still accumulates ascending in `i` from `+0.0`, so the
sums stay bit-identical. Worth 6% of encode.

**MD5 off the critical path.** The STREAMINFO digest is chained and cannot
be split across workers, but it does not have to be *first*: it was 62 ms
of a 550 ms encode, computed before the first frame task started. Spawned
alongside them, it overlaps work that was already saturating the cores.

**Measured and discarded.** A libFLAC-style *windowed* bit reader — cached
64-bit word plus a leading-zero count — was prototyped and came out **5.7×
slower** (207 ms vs 36 ms on a 2M-sample Rice run): Lean boxes `UInt64`
values carried across control flow, so refills and `clz` cost far more
than the scalar `Nat` path they replace. What survives of that idea is the
three-byte extraction window (1.35×). Also neutral or worse: unrolling the
float dot product with four accumulator chains (155 ms vs 83 ms — the
per-tap `Nat` index arithmetic costs more than the shortened dependency
chain saves), splitting it into two chains, a sliding register window,
holding the coefficients in a `FloatArray` walked by a counter instead of
a `List Float` walked structurally (a wash at order 4, *worse* at order 8),
`>>>3`/`&&&7` in place of `/8`/`%8` (identical), a constructor-level
`unzigzag` (identical), and lowering the sync-scan window below 1 MB. The
LPC dot product has now resisted five different attempts; treat ~5 cycles
per tap as the floor.

### Where the remaining encode gap is

On a large file the encoder is 6% ahead of *single-threaded* `flac -8`;
thread-matched on real audio it is 3.4× behind, and 4.7% behind on ratio
([Part 1](#speed)). So the gap is real, and this is where it lives, for
anyone pushing further.

1. **The runtime certificate is gone.** It was ~30% of encode wall:
   decoding the encoder's own output to check it. Milestone M6b replaced it
   with a proof (`Flac.Encode.encodePcm16_eq`), and `ARCHITECTURE.md` walks
   the chain. What was never in the way is the searches — a chooser's
   output carries a decidable validity certificate by construction, so the
   round-trip theorem already held for every chooser, `Float` included; and
   `Float` did not block the *emission* theorem either, because a search
   and the chooser the reference is instantiated with need only be the same
   function on equal inputs.
2. **The candidate search: ~37% of encode work** (`lpcDotFf` 24%,
   autocorrelation 6%, the partition folds the rest). libFLAC's `-8`
   evaluates
   exactly one LPC order per apodization window and one fixed order
   (`compression_levels_` and `process_subframe_` in
   `src/libFLAC/stream_encoder.c` — `do_exhaustive_model_search` is false
   at every level), buying its ratio with several *windows* instead. Vinyl
   uses one window and costs three LPC orders plus all five fixed orders
   exactly. `Flac.Heuristics.lpcCandidates` carries the measured curve.

Below those, per-operation cost is at the floor pure Lean offers.
libFLAC's inner loops are `int32` SIMD; `Array Int64` would be *worse*
than `Array Int` in Lean (boxed per element), and `FloatArray` — already
used everywhere it is exact — is the only unboxed numeric array Lean has
besides `ByteArray`.

### Where the remaining decode gap is

There is none above 4 MB. Below it the residual is Lean's fixed process
init, not decoding. Decode work now divides as: the Rice reader ~43%
(`readRiceSeqScan3` 38%, `scanOne` 5%), predictor restoration ~29%
(`Lpc.dotAGo` 23% — `Int` multiply-accumulate that must stay `Int`,
because it is the proven path and `Int → Int64` conversion per tap would
cost what it saves), `crc16` 6%, serialization ~9%, array pushes ~3%.

Compare medians only *within the same run*; machine load and thermal state
move absolute throughput, which is why every figure plots both codecs
together and interleaves their measurements. And never against a dashboard
from the pre-2026-08-23 harness — see
[the timing note](#the-timing-note-that-invalidates-older-dashboards).

Both Vinyl paths retain zero proof debt. Decoder fast paths are proved equal
to their bit-level specifications, and since M6b the production *encoder* is
proved too: `Flac.Encode.encodePcm16_eq` shows it computes
`Flac.Stream.encode` at the configuration its own search denotes, so the
byte-level round trip follows from the reference capstone with no runtime
decode and no fallback.
