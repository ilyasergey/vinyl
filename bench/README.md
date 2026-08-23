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
curve that sits higher is faster. Dashed lines mark the two medians the
arrow spans, and the arrow names the baseline it is drawn against: the
encode panel is measured against **`flac -8`**, the preset whose
compression ratio Vinyl matches, and the decode panel against libFLAC's
decoder. All four encoder curves are plotted regardless, with medians in
the legend, so the `-0`/`-5` presets stay visible for context.
**Top** — encode. **Bottom** — decode (the shipped buffered decoder):

![Throughput vs libFLAC](performance.png)

Current five-run medians (2026-08-24): Vinyl encode 38.8 MB/s and Vinyl
decode 82.7 MB/s, versus 109.9 MB/s for `flac -5` encode, 75.1 MB/s for
`flac -8` encode, and 126.2 MB/s for libFLAC decode. That is a
**1.53× decode gap** and a 2.83× encode gap against `flac -5` — **1.94×
against `flac -8`, the level whose compression Vinyl matches**.

These corpus files are 1 MB each, so process startup is charged to every
measurement and compresses the apparent gaps. A 32 MB probe, where
startup is negligible, is the better instrument for a *change*: it puts
the gaps at 1.6× decode and 2.1× encode, and it is the yardstick the
stage tables below use.

### Sessions 6–7: parallelism and the array-typed decoder

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| corrected-timer baseline | 13.9 MB/s | 30.6 MB/s | 5.2× | 4.0× |
| allocation-free CRC ranges | 13.9 MB/s | 30.6 MB/s | 5.2× | 4.0× |
| array-typed decoder core | 15.3 MB/s | 40.3 MB/s | 4.8× | 3.1× |
| frame-parallel decoding | 18.6 MB/s | 67.4 MB/s | 4.0× | 1.8× |
| parallel PCM serialization | 18.5 MB/s | 73.9 MB/s | 4.0× | 1.68× |
| decode task granularity 8 | 18.8 MB/s | 78.0 MB/s | 3.9× | 1.58× |
| channel-major deinterleave | 21.4 MB/s | 78.6 MB/s | 3.5× | 1.59× |
| unboxed `FloatArray` search | 21.9 MB/s | 78.3 MB/s | 3.4× | 1.60× |
| deinterleave in the workers | 23.8 MB/s | 79.3 MB/s | 3.15× | 1.59× |
| parallel certificate serialize | 24.5 MB/s | 79.2 MB/s | 3.06× | 1.58× |

### Session 8: exact float arithmetic, and not allocating per bit

Measured on the 32 MB probe (mono, 4096-sample blocks), so these numbers
are not comparable with the corpus medians above — only with each other.
Every stage left the corpus ratio at 39.580% and kept the output
byte-identical to the verified encoder's.

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| session 7 end | 26.7 MB/s | 108.8 MB/s | 3.53× | 1.85× |
| float candidate searches | 33.3 MB/s | — | 2.90× | — |
| bit writer without tuples | 42.8 MB/s | — | 2.27× | — |
| unboxed PCM serialization | 43.5 MB/s | 117.2 MB/s | 2.24× | 1.76× |
| parallel sync-code scan | 44.6 MB/s | 126.5 MB/s | 2.18× | 1.65× |
| fused fixed-order search | 47.1 MB/s | 127.5 MB/s | **2.07×** | **1.59×** |

Four changes, and the two largest were not about algorithms.

**Exact float arithmetic in the searches.** A candidate search only
*chooses* a subframe; the bytes are always emitted from the exact `Int`
path. Every value a search computes is an integer well inside 2^53 — for
16-bit input, samples below 2^17, quantized coefficients below 2^11, order
at most 8, so prediction sums below 2^32, residuals below 2^19, and
4096-sample partition sums below 2^32 — and IEEE-754 doubles represent
those exactly. So the searches run over unboxed `FloatArray` at one
hardware `fmul`/`fadd` per tap instead of `lean_int_mul`/`lean_int_add` on
a boxed `Array Int`, and choose the *same subframe bit for bit*. A
differential test pins that: `Flac.Encode`'s float searches and
`Flac.Heuristics`' `Int`/list searches emit byte-identical streams on
LPC, FIXED, noise, wasted-bit, constant, and stereo material.

Two shapes mattered for the measured 2.5× on the inner loops, and both
are worth remembering. `Float`-typed `let mut` variables carried across a
`for` loop get **boxed once per iteration**, which costs more than the
arithmetic saves — an order-8 residual fold went from 84 ms to 255 ms
when its accumulators moved from tail-recursion parameters into ten
mutable locals. So every accumulator here is a tail-recursion parameter,
and the `for` loops carry only heap objects and `Nat` counters. And exact
integer sums re-associate freely, which is what makes per-partition folds
independent. (Two things that did *not* help: unrolling the dot product
with four accumulator chains — the per-tap `Nat` index arithmetic costs
more than the shortened dependency chain saves — and splitting it into two
chains, which measured neutral. The generated inner loop is already
`ldr`/`ldr`/`fmul`/`fadd` with `Float.floor` inlined to a single
`frintm`.)

**A bit writer that does not allocate.** `BitWriter.flushGo` returned
`ByteArray × UInt64 × Nat`: three heap allocations per call — two `Prod`
cells plus a boxed `UInt64`, because `Prod`'s fields are polymorphic and
so always boxed. `push` runs twice per residual sample, which made the
bit writer the encoder's largest single allocator: the profile put about
a quarter of all encode work in `mi_malloc_small`/`mi_free`/
`lean_dec_ref_cold` beneath it, more than the LPC search itself. Both
dropped components are recoverable without the tuple — the new pending
count is `n % 8`, and `acc` needs no masking because `toUInt8` truncates
on the way out and no bit at or above position `n` is ever read back — so
`flushBytes` returns the buffer alone. The residual loop then threads
`buf`/`acc`/`n` as three parameters through a tail recursion, building one
`BitWriter` per partition instead of two per sample.

**Serializing PCM through the `UInt64` lane.** `Int → Int64 → UInt64`
with unboxed shifts, instead of `Int` addition then `Int.toNat` then `Nat`
masking: one runtime conversion per sample instead of three plus two
`Nat` division-family calls, measured at 2.5× on a 4M-sample block
(266 → 666 MB/s). Serializing decoded samples had been ~27% of decode.
`pcmBytesA_eq` cancels only the array/list conversion, so this arithmetic
carries no proof obligation at all.

**Scanning for sync codes in parallel.** The scan was the decoder's
largest serial phase — one pass over the whole compressed stream on the
driver thread before any frame worker could start. It is a pure guess
(every use is validated by the step's own `Step.ok`), so it may be
computed any way at all: concatenating ascending windows stays ascending,
which is all `findStep`'s binary search needs, and a sync code straddling
a boundary is still found by the window owning its first byte.

**Fusing the fixed-order search.** The order-`ord` fixed residual is the
`ord`-th finite difference, so one traversal carrying the difference
ladder produces all five residual streams: one array read per sample
instead of five, and no block-sized difference array at any order. (An
earlier session measured a fused *`Int`* fixed search as slower, because
juggling five-element `Array` state per sample cost more than the
allocations it saved. Unboxed float parameters are what make the fused
shape win.)

### Where the remaining encode gap is

Two items, measured on the 32 MB probe at 4.09 CPU-seconds total:

1. **The runtime certificate: 1.12 CPU-seconds, 27%.** The fast encoder
   is unverified by design, so every call decodes its own output with the
   verified decoder and compares against the input — which is exactly
   what makes `decodePcm16_encodePcm16Fast` hypothesis-free. Retiring it
   in favour of the statically verified emitter (M6b: `emitFast_eq_encode`
   already exists; what blocks shipping it is that the heuristics it calls
   still run on lists, so array-izing the searches with equality proofs is
   the actual work) would take encode to roughly 1.6× on the probe,
   trading nothing at all.
2. **The candidate search, ~27%.** libFLAC's preset table
   (`compression_levels_` in `src/libFLAC/stream_encoder.c`) sets
   `do_exhaustive_model_search` to false at **every** level including
   `-8`, and `process_subframe_` acts on that: it evaluates exactly one
   LPC order per apodization window (`guess_lpc_order`) and exactly one
   fixed order (`guess_fixed_order`), buying its ratio with several
   *windows* instead (`subdivide_tukey(3)`, max order 12). Vinyl uses one
   window and costs five or six LPC orders plus all five fixed orders
   exactly. `Flac.Heuristics.lpcCandidates` now carries
   the measured tradeoff curve: pruning buys 6–22% encode speed for
   0.05–0.92 percentage points of ratio, and the two sets that beat the
   current one on ratio both cost speed. Raising the order ceiling to 12
   with `[1,2,4,8,12]` reaches 39.450% (0.33 points better than
   `flac -8`) at 0.94× the speed, if ratio is what is wanted.

Beyond those, per-operation cost is at the floor pure Lean offers.
libFLAC's inner loops are `int32` SIMD; `Array Int64` would be *worse*
than `Array Int` in Lean (boxed per element), and `FloatArray` — already
used everywhere it is exact — is the only unboxed numeric array Lean has
besides `ByteArray`.

### Where the remaining decode gap is

Decode is 1.02 CPU-seconds for the 32 MB probe against 0.25 s of wall
time, so it is running about 4× parallel on 4 performance plus 4
efficiency cores, and roughly 40% of the *critical path* is serial.
Remaining work, by profile share: the Rice reader (~22%, and the one
change that would move it is a libFLAC-style windowed bit reader with a
cached word, which needs a simulation proof against `readRiceSeqScan`),
`lean_byte_array_push`/`lean_array_push` (~26%, two pushes per sample —
the floor of the `ByteArray` API), `lean_mark_mt` (~14%, marking decoded
sample arrays as shared when they cross into serialization workers), and
LPC/fixed restoration (~11%, `Int` multiply–accumulate that must stay
`Int` because it is the proven path).

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
