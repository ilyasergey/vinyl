# Benchmarks

Vinyl vs libFLAC 1.5.0, measured on the 37-file synthetic 16-bit corpus
of [`gen_corpus.py`](gen_corpus.py) — six content categories (tonal,
waveforms, noise, tonal+noise mixes, degenerate signals, stereo pairs).

## Real-audio corpus: fetched, not timed yet

The next benchmark suite uses real recordings rather than generated proxy
signals.  [`real_fetch.py`](real_fetch.py) defaults to the compact 167.4 MiB
EBU SQAM corpus; the 644.1 MiB LibriSpeech test pair and multi-gigabyte
FSD50K, MUSDB18-HQ, and MAESTRO corpora are explicit opt-ins.  Audio and
prepared PCM remain under ignored `bench/real_data/`; the committed fetcher
verifies publisher identities and writes a per-file hash/format/licence
manifest.

```sh
python3 bench/real_fetch.py --list
python3 bench/real_fetch.py --accept-ebu-terms  # default: SQAM only
```

No timing or compression results have been recorded for these corpora yet.
See [`CORPORA.md`](CORPORA.md) for category selectors, exact optional-download
commands and checksums, licence restrictions, native-format caveats, and the
prepared-corpus layout.  [`real_corpora.lock.json`](real_corpora.lock.json)
pins the exact SQAM and LibriSpeech archives fetched in this session.

## Synthetic regression dashboard

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

These are the complete files emitted by the current commands, not comparable
audio-frame payloads.  libFLAC's files include its default 8,192-byte padding,
seektable, and vendor comment; Vinyl emits only STREAMINFO.  Across files this
small, that metadata is larger than the displayed 0.2-point difference.
Consequently the table does **not** establish that Vinyl beats or
compression-matches `flac -8`.  The real-audio run must use minimal metadata
and compare frame payload sizes before selecting a speed baseline.

## Speed

Per-file throughput (log scale), sorted slowest→fastest per codec; a
curve that sits higher is faster. Dashed lines mark the two medians the
arrow spans, and the arrow names the baseline it is drawn against.  The
encode panel retains **`flac -8` as a historical reference**, not as an
established compression match; the decode panel uses libFLAC's decoder.
All four encoder curves are plotted regardless, with medians in the legend,
so the `-0`/`-5` presets stay visible for context.
**Top** — encode. **Bottom** — decode (the shipped buffered decoder):

![Throughput vs libFLAC](performance.png)

Current fifteen-run medians (2026-08-24, after M6b): Vinyl encode 70.7 MB/s
and Vinyl decode 123.6 MB/s, versus 108.4 MB/s for `flac -5` encode,
74.7 MB/s for `flac -8` encode, and 124.9 MB/s for libFLAC decode. That is
a **1.01× decode gap** and a 1.53× encode gap against `flac -5` — **1.06×
against the `flac -8` reference**, from 1.27× before the runtime certificate
was retired. On files large enough that process startup does not dominate,
encode is *ahead* of `flac -8` (0.94× at 32 MB; see the size sweep below).
Neither encode gap should be called compression-matched until the
metadata-normalized real-corpus frontier has been measured.

Repeating the whole run moves these medians, and by different amounts in
the two directions: across six passes the *decode* gap held within 1%
(1.01–1.03×) while the *encode* gap ranged 1.02–1.07×. Encoding is
`Task`-parallel, so at 1 MB it loses more to whatever else the machine is
running than single-threaded libFLAC does — measure it on an otherwise idle
machine, or don't quote the third digit. This is why the gaps are quoted to
two significant figures and why the stage tables further down use a 32 MB
probe instead: a single large file resolves a 5% change, where the corpus
medians do not.

### Read the corpus medians with the file size in mind

These files are 1 MB each, by design: `gen_corpus.py` sizes them for
*compression* coverage, not throughput. At that size **process startup is
a third of the measurement** — 3.1 ms of Lean runtime init against
libFLAC's 2.7 ms, on an 8–9 ms decode — and only 0.09 ms of Vinyl's share
is this project's own module initialization (a trivial Lean binary also
takes 3.10 ms; the binary is already statically linked against Lean, so
there is no dynamic-loading cost to remove).

Same material, medians against file size:

| PCM | Vinyl decode | libFLAC | gap | Vinyl encode | `flac -8` | gap |
|---|---|---|---|---|---|---|
| 1 MB | 104.4 MB/s | 121.7 MB/s | 1.17× | 70.9 MB/s | 70.7 MB/s | **1.00×** |
| 2 MB | 140.3 MB/s | 150.9 MB/s | 1.08× | 82.3 MB/s | 81.8 MB/s | **0.99×** |
| 4 MB | 178.8 MB/s | 168.7 MB/s | **0.94×** | 89.6 MB/s | 87.0 MB/s | **0.97×** |
| 8 MB | 198.7 MB/s | 178.6 MB/s | **0.90×** | 94.8 MB/s | 89.4 MB/s | **0.94×** |
| 16 MB | 209.7 MB/s | 185.9 MB/s | **0.89×** | 95.9 MB/s | 90.5 MB/s | **0.94×** |
| 32 MB | 217.2 MB/s | 189.6 MB/s | **0.87×** | 97.0 MB/s | 91.6 MB/s | **0.94×** |

Both directions overtake libFLAC once startup stops dominating: encode from
2 MB, decode from 4 MB, settling ~6% and ~13% faster. Each row is the
better of two passes, which is the least-contended estimate a working
machine allows. The 32 MB probe below is the instrument for judging a
*change*.

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

There is no longer an encode *gap* on a large file — the encoder is 6%
ahead of `flac -8` from 8 MB up — so what follows is where the remaining
*work* is, for anyone pushing further.

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

Compare medians only *within the same run*; machine load and thermal
state move absolute throughput, which is why the figure plots both codecs
together and interleaves their measurements. And do not compare against
any dashboard produced by the pre-2026-08-23 shell harness, which charged
a fixed ~20 ms timestamp-process startup to every codec invocation and so
understated the gaps (see the timing note above).

Both Vinyl paths retain zero proof debt: decoder fast paths are proved equal
to their specifications, while the production encoder currently certifies
each call by decoding its own output with the verified decoder and comparing
it with the input (falling back to the verified encoder on mismatch).
