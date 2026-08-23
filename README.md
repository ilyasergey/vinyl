# Vinyl

**A formally verified FLAC codec in pure Lean 4.**

Vinyl implements a FLAC ([RFC 9639](references/rfc9639.txt)) encoder and
decoder with no FFI, together with machine-checked proofs. The main
correctness theorem — kernel-certified losslessness of the shipped
encoder/decoder pair — is
[`Flac.decode_encode`](Flac/Spec/Decode.lean#L1750):

```lean
/-- Decoding an encoded stream recovers the audio exactly,
    for every well-formed input. -/
theorem Flac.decode_encode (a : Audio) (h : a.WellFormed) :
    decode (encode a) = .ok a
```

Here [`Audio.WellFormed`](Flac/Native/Stream.lean#L210) says exactly
"representable as FLAC" — 1–8 equal-length channels, bit depth 1–32,
samples in range for the bit depth, and the STREAMINFO field bounds — and
it is **decidable**, so the precondition can be tested at runtime. The
checked encoder [`Flac.encodeChecked`](Flac/Native/Codec.lean#L24) does
exactly that, which turns the runtime check itself into the theorem's
premise ([`Flac.decode_encodeChecked`](Flac/Spec/Decode.lean#L1757)):

```lean
/-- If the checked encoder returns bytes at all, decoding them
    recovers the audio. No hypotheses. -/
theorem Flac.decode_encodeChecked
    (h : encodeChecked a = some bytes) : decode bytes = .ok a
```

At the byte level the same guarantee holds for raw PCM files
([`Flac.decodePcm16_encodePcm16`](Flac/Spec/Decode.lean#L1951)): if
`encodePcm16 ch bytes` turns a raw interleaved signed 16-bit
little-endian PCM `ByteArray` into a FLAC file, then `decodePcm16`
returns **exactly the input bytes** — again with no hypotheses. (The
"16" is only the byte layout of this front end; the codec and the
theorems above cover bit depths 1–32.)

The statements quantify over every encoder knob: block size, numbering
strategy, stereo-decorrelation mode, wasted bits, subframe types, Rice
parameters and partitions
([`Flac.decode_encode_cfg`](Flac/Spec/Decode.lean#L1738)). The encoder
validates each heuristic choice against a decidable certificate and falls
back to VERBATIM when the check fails, so **arbitrary — even
adversarial — heuristics cannot break correctness**: they only choose
*which* valid stream is emitted.

The proof is layered: a verified *reference* decoder over a `List Bool`
bit model carries the round-trip proof
([`Flac.Stream.decodeReference_encode`](Flac/Spec/Stream.lean#L315)); the
shipped *production* decoder (a buffered `ByteArray` reader) is proven to
compute exactly the same function on every input
([`decodeOption_eq_reference`](Flac/Spec/Decode.lean), accept-set
transfer [`decode_ok_iff_reference`](Flac/Spec/Decode.lean#L1728)); and
both are *total* — no `partial`, no panics — so the decoder terminates on
arbitrary bytes. Interoperability with the real world is established
separately by differential testing against libFLAC (below).

## Status

Milestones M0–M5 are complete (see `PLAN.md §8` for the roadmap and
`PROGRESS.md` for the session log); M6 (performance under the theorem
ratchet) is next.

- [x] **M0** — bit-level I/O with round-trip proofs, CRC-8/CRC-16,
      extended-UTF-8 coded numbers with round-trip proof, pure-Lean MD5
      (RFC 1321 suite green)
- [x] **M1** — Rice/zigzag/escape coding + partitioned-residual proofs
      with divisibility certificates
- [x] **M2** — CONSTANT/VERBATIM/FIXED subframes, CRC-verified frames,
      stream layer; `decodeReference ∘ encode = id` on the mono profile;
      first libFLAC interop (both directions)
- [x] **M3** — LPC subframes with the LPC restore proof; certified
      default heuristic (Welch-windowed Levinson–Durbin LPC + fixed-order
      search, exact Rice bit costs)
- [x] **M4** — 1–8 channels, stereo decorrelation (L/S, R/S, M/S with the
      b+1-bit side channel), wasted bits, both numbering strategies;
      **reference capstone** over the full option space
- [x] **M5** — buffered production decoder, simulation proof against the
      reference, accept-set transfer; **shipped capstone**
      `decode (encode a) = .ok a` and its byte-level PCM corollary;
      IETF conformance-corpus gate
- [ ] **M6** — performance work under the ratchet
- [ ] **M7** — (stretch) two-sided verification against RFC 9639

## What of RFC 9639 is covered

Everything needed to *decode the "streamable subset"* of FLAC and to
*encode within it*. Concretely:

**Supported (decode, with the equivalence proof; encode where noted):**

| feature | decode | encode |
|---|---|---|
| `fLaC` marker + STREAMINFO; all other metadata blocks (padding, application, seektable, Vorbis comment, cuesheet, picture, …) | ✓ (parsed / skipped) | STREAMINFO only |
| block sizes: all codes incl. explicit 8/16-bit (192, 576·2ᵏ, 256·2ᵏ, arbitrary 1–65536) | ✓ | 16–65535, explicit code |
| both frame-numbering strategies (fixed / variable block size) | ✓ | ✓ |
| sample rates: STREAMINFO up to 2²⁰−1 Hz; all frame-header codes incl. explicit 8/16-bit | ✓ | STREAMINFO code |
| bit depths 1–32; per-frame bit-depth codes (8/12/16/20/24/32 + STREAMINFO) | ✓ | STREAMINFO code, 1–32 |
| channels 1–8 independent; stereo decorrelation left/side, right/side, mid/side (b+1-bit side) | ✓ | ✓ |
| subframes: CONSTANT, VERBATIM, FIXED orders 0–4, LPC orders 1–32 (any precision 1–15, shift 0–15) | ✓ | ✓ |
| wasted bits (any count < bit depth) | ✓ | ✓ (detected) |
| residuals: 4-bit Rice, 5-bit Rice2, escaped partitions, partition orders 0–15 | ✓ | ✓ |
| CRC-8 (frame header) and CRC-16 (frame) verification | ✓ (checked, by theorem) | ✓ (emitted) |
| MD5 signature of the unencoded data | emitted by encoder | emitted |
| coded frame numbers (extended UTF-8, up to 36 bits) | ✓ | ✓ |

**Not supported (decode rejects with an error rather than guessing):**

- streams that do not begin with `fLaC` + STREAMINFO — e.g. files
  starting mid-stream at a frame header, or with leading garbage/ID3
  tags (RFC 9639 makes STREAMINFO mandatory; resynchronization is a
  player feature, not part of the format);
- reserved codes anywhere (block-size code 0, sample-rate code 15,
  bit-depth code 3, channel codes 11–15, reserved header bits ≠ 0) —
  rejected, as the RFC requires;
- MD5 *verification* on decode (the decoder is exact by theorem on
  every stream it accepts; MD5 is validated in differential tests);
- metadata *content* (Vorbis comments, seek tables, pictures …) is
  skipped, not surfaced to the caller;
- the encoder always emits the streamable subset: it does not produce
  uncommon block sizes/rates requiring explicit frame-header codes.

On the [IETF FLAC conformance corpus](https://github.com/ietf-wg-cellar/flac-test-files),
the **must-decode `subset/` set passes 61/61** files that the `flac` CLI
itself can compare against raw output (the remaining 3 are 12/20-bit
files the reference *CLI* refuses to emit as raw; Vinyl decodes them
too). Of the `uncommon/` edge set, everything comparable passes except
the deliberately headerless "file starting at frame header".

## Differential testing

Three rigs run against libFLAC 1.5.0 (`conformance/`):

- `smoke.sh` — both directions on synthetic signals: every Vinyl stream
  passes `flac -t` (CRC-8/16 + MD5) and decodes byte-identically with
  libFLAC; libFLAC-encoded streams decode byte-identically with Vinyl.
- `ietf.sh` — the RFC 9639 companion test-file corpus (results above);
  the `subset/` set is a merge gate.
- `scripts/check.sh` — the ratchet: full build, **zero `sorry`/`axiom`**,
  grep-pinned capstone theorems present, decoder-totality lint (no
  `partial`, no panicking indexing), 71-check unit suite.

## Benchmarks

Measured on the 37-file synthetic 16-bit corpus of `bench/gen_corpus.py`
— six content categories (tonal, waveforms, noise, tonal+noise mixes,
degenerate signals, stereo pairs) — against libFLAC 1.5.0; regenerate
with `./bench/run.sh`. All percentages are compression ratios: encoded
size as a fraction of the raw PCM. 0% would mean the file vanished,
100% means no compression at all — lower is better.

### Compression

**Top** — per-file cactus: each encoder's ratios sorted ascending; a
curve that stays lower compresses better. **Bottom** — aggregate ratio
(total encoded bytes ÷ total raw bytes) per content category:

![Compression vs libFLAC](bench/compression.png)

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

### Speed

Per-file throughput (log scale), sorted slowest→fastest per codec; a
curve that sits higher is faster. Left: encode. Right: decode (the
shipped buffered decoder):

![Throughput vs libFLAC](bench/performance.png)

Honest reading: Vinyl encodes at ~0.16 MB/s (median; the checked encoder
re-validates every heuristic certificate) and decodes at ~1.5 MB/s,
vs libFLAC's ~30–37 MB/s for both. The encoder still runs on the
proof-oriented `List Bool` bit model and does exhaustive searches;
performance work is deliberately deferred to M6, *after* the capstone
makes optimization safe: any faster implementation must re-prove the
same simulation theorems.

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain
(Lean 4.33.0) is pinned in `lean-toolchain`. No external Lean
dependencies.

```sh
lake build          # library + proofs (no sorry, no axioms in Flac/)
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

# encode raw PCM (blockSize 4096, 2 channels) with the verified encoder;
# if this succeeds, the round-trip is guaranteed by theorem
lake exe vinyl --encode input.pcm out.flac 4096 2

# decode any in-coverage FLAC (bit depths 1-32) — reference or fast decoder
lake exe vinyl --decode out.flac roundtrip.pcm         # reference decoder
lake exe vinyl --decode-fast out.flac roundtrip.pcm    # shipped decoder
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
