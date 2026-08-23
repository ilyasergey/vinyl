# Vinyl

**A formally verified FLAC codec in pure Lean 4.**

Vinyl implements a FLAC ([RFC 9639](references/rfc9639.txt)) encoder
and decoder with no FFI, together with machine-checked proofs. The main
correctness theorem — kernel-certified losslessness — is
[`Flac.Stream.decodeReference_encode`](Flac/Spec/Stream.lean#L278):

```lean
/-- decodeReference ∘ encode = id over the full option space: every
    well-formed audio, every block size 16–65535, both numbering
    strategies, and every valid channel-assignment heuristic. -/
theorem Flac.Stream.decodeReference_encode (cfg : EncoderCfg) (a : Audio)
    (hwf : a.WellFormed)
    (hbs1 : 16 ≤ cfg.blockSize) (hbs2 : cfg.blockSize ≤ 65535)
    (hsr : a.sampleRate < 2 ^ 20) (htot : a.numSamples < 2 ^ 36)
    (hchooser : /- the heuristic returns valid configurations -/) :
    decodeReference (encode cfg a) = some a.channels
```

quantified over *all* well-formed audio (1–8 channels, bit depth 1–32) and
*all* encoder settings — block size, stereo-decorrelation mode, wasted
bits, LPC/fixed/constant/verbatim subframe choices, Rice parameters and
partitions, numbering strategy — so every heuristic knob is
correctness-irrelevant by construction. With the shipped search heuristics
plugged in, the hypothesis-light corollary is
[`Flac.Stream.decodeReference_encode_default`](Flac/Spec/Heuristics.lean#L314).
The methodology mirrors [`lean-zip`](https://github.com/kim-em/lean-zip)
(verified DEFLATE): verified reference decoder, round-trip theorem as the
merge ratchet, reference→production transfer proof, and differential
fuzzing against libFLAC/ffmpeg for interoperability.

## Status

Milestones M0–M4 are complete (see `PLAN.md §8` for the roadmap and
`PROGRESS.md` for the session log): the **reference capstone** above is
proven, and the emitted streams — including stereo-decorrelated and
wasted-bits streams — pass `flac -t` (CRCs + MD5) and decode
byte-identically with libFLAC, while libFLAC-encoded streams inside the
current feature envelope decode byte-identically with `decodeReference`
(`conformance/smoke.sh`).

- [x] **M0** — bit-level I/O with round-trip proofs, CRC-8/CRC-16,
      extended-UTF-8 coded numbers with round-trip proof, pure-Lean MD5
      (RFC 1321 suite green)
- [x] **M1** — Rice/zigzag/escape coding + partitioned-residual proofs
      with divisibility certificates
- [x] **M2** — CONSTANT/VERBATIM/FIXED subframes, CRC-verified frames,
      stream layer; `decodeReference ∘ encode = id` on the mono profile;
      first libFLAC interop (both directions)
- [x] **M3** — LPC subframes with the L3-LPC restore proof; certified
      default heuristic (Welch-windowed Levinson–Durbin LPC + fixed-order
      search, exact Rice bit costs)
- [x] **M4** — 1–8 channels, stereo decorrelation (L/S, R/S, M/S with the
      b+1-bit side channel), wasted bits, both numbering strategies;
      **reference capstone** over the full option space
- [ ] **M5** — production decoder + accept-set transfer; **shipped capstone**
- [ ] **M6** — performance work under the ratchet
- [ ] **M7** — (stretch) two-sided verification against RFC 9639

## Benchmarks

Measured on the 37-file synthetic 16-bit corpus of `bench/gen_corpus.py`
— six content categories (tonal, waveforms, noise, tonal+noise mixes,
degenerate signals, stereo pairs) — against libFLAC 1.5.0; regenerate
with `./bench/run.sh`. **Top left** — compression cactus: each encoder's
per-file ratios sorted ascending; a curve that stays lower compresses
better. **Top right** — throughput profile: per-file encode throughput
(log scale), each encoder's files sorted slowest→fastest; higher is
faster. **Bottom** — aggregate compression per content category:

![Compression and speed vs libFLAC](bench/cactus.png)

| category | vinyl | flac -0 | flac -5 | flac -8 |
|---|---|---|---|---|
| tonal | **19.7%** | 40.2% | 22.3% | 20.1% |
| wave | **39.2%** | 44.5% | 43.9% | 40.9% |
| noise | **77.5%** | 77.9% | 77.5% | 77.5% |
| mixed | 72.0% | 72.6% | 71.0% | **70.9%** |
| degen | **22.1%** | 46.6% | 22.9% | 22.9% |
| stereo | 27.2% | 31.8% | 26.7% | **26.6%** |
| **TOTAL** | **39.5%** | 49.4% | 40.9% | 39.8% |

With the M4 heuristics (Levinson–Durbin LPC, wasted-bit detection,
stereo-mode decision, adaptive Rice partitioning), the verified encoder's
overall ratio **beats `flac -8`** on this corpus (39.5% vs 39.8% of raw),
winning tonal/waveform/degenerate content and trailing slightly on noisy
mixes and stereo. Encode speed is ~0.2 MB/s vs libFLAC's ~30 MB/s: the
encoder still runs on the proof-oriented bit model and does an exhaustive
partition search; performance work is deliberately deferred to M6, *after*
the capstone makes optimization safe (PLAN.md §7).

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain
(Lean 4.33.0) is pinned in `lean-toolchain`. No external Lean dependencies.

```sh
lake build          # library + proofs (no sorry, no axioms in Flac/Spec/)
lake exe flactest   # golden-vector unit tests
```

## Command-line usage

`lake build vinyl` produces `.lake/build/bin/vinyl`, a small CLI over the
verified codec (`vinyl --help` lists the commands). It reads and writes
raw interleaved **signed 16-bit little-endian** PCM:

```sh
# generate sample .flac/.pcm pairs to play with
lake exe vinyl --samples /tmp/vinyl-samples
ls /tmp/vinyl-samples          # sine, stereo, wasted-bits, constant, …

# the .flac files are real FLAC — any player/tool accepts them
flac -t /tmp/vinyl-samples/stereo-corr.flac      # verifies CRCs + MD5
ffplay /tmp/vinyl-samples/sine-fixed.flac        # plays (mono 44.1 kHz)

# encode raw PCM (blockSize 4096, 2 channels) with the verified encoder
lake exe vinyl --encode input.pcm out.flac 4096 2

# decode any in-envelope FLAC with the verified reference decoder
lake exe vinyl --decode out.flac roundtrip.pcm
cmp input.pcm roundtrip.pcm                      # byte-identical, by theorem

# make a raw PCM input from any audio file with ffmpeg…
ffmpeg -i song.mp3 -f s16le -acodec pcm_s16le -ac 2 -ar 44100 input.pcm
# …or from a FLAC file with the reference flac tool
flac -d --force-raw-format --sign=signed --endian=little -o input.pcm song.flac
```

A larger corpus of synthetic test signals (tones, sweeps, noise, stereo
pairs, …) can be generated with `python3 bench/gen_corpus.py /tmp/corpus`.

## Reading guide

- [`ARCHITECTURE.md`](ARCHITECTURE.md) — how the repository is organized
  and why (the trusted/tested split, the theorem layering L0–L6).
- [`PLAN.md`](PLAN.md) — the complete working plan: capstone statement,
  scope, theorem stack, known hard points, fuzzing/conformance rigs,
  milestones.
- [`CLAUDE.md`](CLAUDE.md) — contributor/agent workflow rules.
- [`PROGRESS.md`](PROGRESS.md) — per-session development log.
