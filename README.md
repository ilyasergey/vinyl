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
([`Flac.decodePcm16_encodePcm16`](Flac/Spec/Decode.lean#L1951)):

```lean
/-- If encoding a raw 16-bit PCM byte array succeeds at all,
    decoding the resulting FLAC file returns exactly the input
    bytes. No hypotheses. -/
theorem Flac.decodePcm16_encodePcm16
    (h : encodePcm16 ch bytes = some flac) : decodePcm16 flac = .ok bytes
```

This matters because `decode_encode` speaks about the structured
`Audio` value, while what a user actually holds is a flat interleaved
signed 16-bit little-endian PCM `ByteArray` (a `.wav` payload, a sound
card buffer). The corollary extends the sample-level capstone across
the remaining conversion glue — channel deinterleaving and byte
packing, proved to round-trip as well — so **no unverified code sits
between the user's bytes and the guarantee**: it is the end-to-end
contract for the file-level API (and the `vinyl` CLI), and the single
hypothesis-free statement to audit if that is the interface you use.
(The "16" is only the byte layout of this front end; the codec and the
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

Milestones M0–M5 are complete and M6 (performance under the theorem
ratchet) has largely landed: every decoder fast path is proven equal to
its bit-level specification, and the frame-parallel encoder is certified
per call by the verified decoder — the remaining step is a statically
verified fast emitter to retire that runtime certificate. M7 (two-sided
verification against RFC 9639) is a stretch goal. See [`PLAN.md`](PLAN.md) §8 for the milestone-by-milestone
roadmap and [`PROGRESS.md`](PROGRESS.md) for the session log. In short:
bit-level I/O, CRCs, MD5, Rice coding, all subframe types (CONSTANT /
VERBATIM / FIXED / LPC), 1–8 channels with stereo decorrelation, wasted
bits, and the buffered production decoder are all done and under the
capstone theorems above.

## What of RFC 9639 is covered

Everything needed to *decode the "streamable subset"* of FLAC and to
*encode within it*: all subframe types (LPC orders 1–32), Rice/Rice2
residuals with escapes, 1–8 channels with all three stereo-decorrelation
modes, wasted bits, both numbering strategies, CRC-8/CRC-16, and MD5.
The full feature-by-feature table — and the explicit list of what decode
*rejects* (headerless streams, reserved codes, …) — is in
[`COVERAGE.md`](COVERAGE.md). On the
[IETF conformance corpus](https://github.com/ietf-wg-cellar/flac-test-files)
the must-decode `subset/` set passes **61/61** comparable files.

## Differential testing

The theorems prove encoder and decoder agree with *each other*;
agreement with the rest of the world is tested against libFLAC 1.5.0.
[`conformance/`](conformance/README.md) holds the rigs: `smoke.sh`
(both directions on synthetic signals), `ietf.sh` (the RFC 9639 corpus;
merge gate), and `fuzz.sh` (decoder-totality, bit-flip, and compiled
round-trip fuzzing). `scripts/check.sh` is the ratchet: full build,
**zero `sorry`/`axiom`**, grep-pinned capstones, totality lint, unit
suite. To run the cross-check yourself on one file, see
[Cross-checking against libFLAC](#cross-checking-against-libflac) below.

## Benchmarks

On the 37-file synthetic corpus of `bench/gen_corpus.py`, the encoder's
overall compression ratio **beats `flac -8`** (39.6% vs 39.8% of raw) —
the certified heuristics choose well. A corrected-timer smoke pass measured
approximately 12.0 MB/s encode and 30.6 MB/s decode for Vinyl, against
106.3 MB/s for `flac -5` encode and 121.3 MB/s for libFLAC decode: gaps of
about 8.9× and 4.0×. These replace the previously reported 4.4×/2.4×
figures, which were biased downward because the old harness charged roughly
20 ms of Python timestamp-process startup to every command. The current
harness warms every case, interleaves implementations, and records five-run
medians from one persistent timer process. Every decoder fast path is proven
equal to its bit-level specification; the frame-parallel encoder is certified
per call by the verified decoder. See [`bench/README.md`](bench/README.md)
for the methodology, provisional status, and regeneration instructions.

Compression, per file (sorted; lower is better) and aggregated per
content category:

![Compression vs libFLAC](bench/compression.png)

Throughput per file (log scale; higher is faster), encode and decode:

![Throughput vs libFLAC](bench/performance.png)

Per-category tables, how to read the plots in detail, and how to
regenerate them: [`bench/README.md`](bench/README.md).

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
raw interleaved **signed 16-bit little-endian** PCM.

Generate sample `.flac`/`.pcm` pairs to play with (the directory must
exist; the `.flac` files are real FLAC — any player or tool accepts
them, e.g. `flac -t` or `ffplay`):

```sh
mkdir -p /tmp/vinyl-samples
lake exe vinyl --samples /tmp/vinyl-samples
```

Encode raw PCM (block size 4096, 2 channels) with the verified encoder —
if this succeeds, the round-trip is guaranteed by theorem — then decode
(`--decode` is the reference decoder, `--decode-fast` the shipped one)
and compare:

```sh
lake exe vinyl --encode input.pcm out.flac 4096 2
lake exe vinyl --decode-fast out.flac roundtrip.pcm
cmp input.pcm roundtrip.pcm
```

To make a raw PCM input from any audio file, use ffmpeg or the
reference `flac` tool:

```sh
ffmpeg -i song.mp3 -f s16le -acodec pcm_s16le -ac 2 -ar 44100 input.pcm
flac -d --force-raw-format --sign=signed --endian=little -o input.pcm song.flac
```

A larger corpus of synthetic test signals (tones, sweeps, noise, stereo
pairs, …) can be generated with `python3 bench/gen_corpus.py /tmp/corpus`.

## Cross-checking against libFLAC

To see with your own eyes that Vinyl and the reference implementation
(the `flac` CLI / libFLAC) do the same thing, run the same PCM bytes
through both codecs, in both directions, and compare byte-for-byte.
First produce a test signal:

```sh
mkdir -p /tmp/demo
lake exe vinyl --samples /tmp/demo
```

**Direction A** — Vinyl encodes; libFLAC verifies the stream
(`flac -t` checks CRC-8/16 and the MD5 signature), decodes it, and the
output must equal the input:

```sh
lake exe vinyl --encode /tmp/demo/stereo-corr.pcm A.flac 4096 2
flac -t A.flac
flac -d -f --force-raw-format --sign=signed --endian=little -o A-libflac.pcm A.flac
cmp /tmp/demo/stereo-corr.pcm A-libflac.pcm && echo byte-identical
```

**Direction B** — libFLAC encodes the same signal; Vinyl decodes it,
and the output must equal the input:

```sh
flac -f -8 --force-raw-format --sign=signed --endian=little \
     --channels=2 --bps=16 --sample-rate=44100 -o B.flac /tmp/demo/stereo-corr.pcm
lake exe vinyl --decode-fast B.flac B-vinyl.pcm
cmp /tmp/demo/stereo-corr.pcm B-vinyl.pcm && echo byte-identical
```

The two directions check different things. A shows libFLAC accepts and
agrees with Vinyl's *encoder* output; B shows Vinyl's *decoder* agrees
with libFLAC's encoder on a stream Vinyl did not produce. Neither is
covered by the theorems — they establish interoperability, which is
exactly why they are tested, not proved. (The Vinyl-encode →
Vinyl-decode leg in the middle *is* the part guaranteed by
`decodePcm16_encodePcm16`.) The automated version of this walkthrough,
run over a batch of signals, is
[`conformance/smoke.sh`](conformance/smoke.sh).

## Reading guide

- [`ARCHITECTURE.md`](ARCHITECTURE.md) — how the repository is organized
  and why (the trusted/tested split, the theorem layering L0–L6).
- [`PLAN.md`](PLAN.md) — the complete working plan: capstone statement,
  scope, theorem stack, known hard points, fuzzing/conformance rigs,
  milestones.
- [`COVERAGE.md`](COVERAGE.md) — feature-by-feature RFC 9639 coverage
  and conformance-corpus results.
- [`conformance/README.md`](conformance/README.md) — the differential
  testing and fuzzing rigs against libFLAC.
- [`bench/README.md`](bench/README.md) — compression and speed
  benchmarks vs libFLAC, with plots.
- [`CLAUDE.md`](CLAUDE.md) — contributor/agent workflow rules.
- [`PROGRESS.md`](PROGRESS.md) — per-session development log.
