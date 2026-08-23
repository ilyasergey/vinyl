# Repository structure

Vinyl is a formally verified FLAC codec in pure Lean 4. This document
explains how the repository is organized and *why* — the layering is the
methodology (see `PLAN.md` for the full technical plan, milestones, and
theorem stack).

## The idea in one paragraph

The deliverable is a pure-Lean FLAC encoder/decoder pair together with a
kernel-checked **round-trip theorem**: `Flac.decode (Flac.encode a) = .ok a`
for every well-formed input — and, one level up, its runtime-checked and
byte-level corollaries (`decode_encodeChecked`, `decodePcm16_encodePcm16`),
which carry the guarantee with *no hypotheses at all*. Everything in the
tree is positioned relative to that theorem: code that the theorem
quantifies over lives in `Flac/Native/`, the theorems themselves live in
`Flac/Spec/`, and everything that merely *tests* the result against the
outside world (libFLAC, fuzzers, benchmarks) lives outside the trusted
base in `conformance/` and `bench/`.

## Directory map

```
vinyl/
├── PLAN.md              # the complete working plan (normative for agents)
├── CLAUDE.md            # workflow rules: no sorry on master, logging, commits
├── PROGRESS.md          # per-session log: what landed, what's blocked, next
├── ARCHITECTURE.md      # this file
├── lean-toolchain       # pinned Lean version (4.33.0)
├── lakefile.toml        # lake package: lib Flac, lib FlacTest, exe flactest
├── references/
│   └── rfc9639.txt      # the normative FLAC specification (IETF, Dec 2024)
├── Flac.lean            # library root; imports the public modules
├── Flac/
│   ├── Native/          # executable code — what actually ships
│   │   ├── Bits.lean       # MSB-first bit model: readBits/writeBits, unary,
│   │   │                   #   signed ints, alignment, bytes, withConsumed
│   │   ├── Crc.lean        # CRC-8 (poly 0x07) and CRC-16 (poly 0x8005)
│   │   ├── Utf8Num.lean    # extended-UTF-8 coded numbers (≤36 bits)
│   │   ├── Md5.lean        # pure-Lean MD5 for the STREAMINFO PCM checksum
│   │   ├── Rice.lean       # zigzag, Rice/RICE2, escaped + partitioned residuals
│   │   ├── Fixed.lean      # fixed predictors = iterated finite differences
│   │   ├── Lpc.lean        # quantized LPC, history-passing style
│   │   ├── Stereo.lean     # left/side, right/side, mid/side transforms
│   │   ├── Subframe.lean   # all four subframe types + wasted bits
│   │   ├── Frame.lean      # multichannel frames, CRC-verified decode
│   │   ├── Stream.lean     # STREAMINFO, Audio, encode/decodeReference
│   │   ├── Heuristics.lean # LPC/fixed/stereo search (sanitized at use)
│   │   ├── Reader.lean     # BitReader: buffered ByteArray bit reader
│   │   │                   #   (word-level fast paths proven = the spec)
│   │   ├── Decode.lean     # the shipped production decoder, Flac.decode
│   │   ├── Encode.lean     # the fast encoder (arrays/Task-parallel frames;
│   │   │                   #   unverified by design — certified per call)
│   │   └── Codec.lean      # Flac.encode, checked + certified-fast encoders,
│   │                       #   PCM16 pipeline
│   └── Spec/               # ALL theorems; no sorry, no axioms, ever
│       ├── Bits.lean       # L0 round-trips, packing, withConsumed_spec
│       ├── Utf8Num.lean    # coded-number round-trip (n < 2^36)
│       ├── Rice.lean       # L1–L2 incl. readResidual_writeResidual
│       ├── Fixed.lean      # L3-fixed: restore_residual
│       ├── Lpc.lean        # L3-LPC: restore_residual (hypothesis-free)
│       ├── Stereo.lean     # L4: per-mode round-trips + width facts
│       ├── Subframe.lean   # subframe round-trip incl. wasted bits
│       ├── Frame.lean      # multichannel frame round-trip
│       ├── Stream.lean     # the reference capstone: decodeReference_encode
│       ├── Heuristics.lean # chooser certificates + default corollary
│       ├── Reader.lean     # BitReader simulates the List Bool model
│       └── Decode.lean     # production ≡ reference; the shipped capstones
├── FlacTest.lean, FlacTest/
│   ├── Cli.lean         # unit tests + the vinyl CLI (encode/decode)
│   └── Main.lean        # entry point
├── conformance/
│   ├── smoke.sh         # Rigs 1–2 vs `flac` CLI, both directions
│   └── ietf.sh          # RFC 9639 companion test-file corpus (merge gate)
├── scripts/
│   └── check.sh         # the ratchet: build + hygiene + pins + tests
└── bench/               # corpus generator, runner, plots (see README)
```

## The layering discipline

Three kinds of code, three different obligations:

1. **`Flac/Native/`** — production code. Total by construction on decode
   paths (no `partial`, no panicking `!` indexing); heuristic choices
   (LPC order search, apodization, partition search — `Heuristics.lean`,
   from M3) are *unverified by design*: they only pick **which** valid
   stream is emitted, never whether the round-trip holds, so once the
   capstone is proven the entire heuristic layer is free optimization
   territory.

2. **The reference decoder** (`Stream.decodeReference` and the readers it
   is built from) — written over the `List Bool` bit model for clean
   induction rather than speed. The capstone is first proven against it,
   then transferred to the shipped decoder via the equivalence
   `decodeOption_eq_reference` / `decode_ok_iff_reference`
   (`Flac/Spec/Decode.lean`).

3. **`Flac/Spec/`** — the theorem stack, proven bottom-up (PLAN.md §4):
   - **L0** bit I/O round-trips (done),
   - **L1** primitive codes: zigzag, Rice/RICE2, escapes, coded numbers (done),
   - **L2** residual partitions with divisibility certificates (done),
   - **L3** fixed and quantized-LPC predictors (done),
   - **L4** stereo decorrelation and wasted bits (done),
   - **L5** subframe/frame composition with width bookkeeping (done),
   - **L6** the stream capstone — `decodeReference_encode` over the full
     option space, and the *shipped* capstones: `Flac.decode_encode`,
     the hypothesis-free `decode_encodeChecked`, and the byte-level
     `decodePcm16_encodePcm16`.

Each layer's round-trip lemma is stated so the layer above uses it opaquely.

## Key representation choice (current)

The bit-level model is `List Bool`, MSB-first (`Flac.BitStream`). Writers
are pure functions returning bit lists; readers are structural-recursive
consumers returning `Option (value × rest)`. This makes every L0/L1 proof a
clean induction. The shipped decoder instead reads bits from a `ByteArray`
at a bit cursor (`BitReader`); every primitive is proven to simulate the
model (`Flac/Spec/Reader.lean`), and the whole decoder is proven
extensionally equal to the reference (`Flac/Spec/Decode.lean`). That is
the ratchet pattern for M6 — optimize only what a theorem already pins
down — and it is now exercised throughout the decoder: bit extraction is
byte-at-a-time (`extractBitsFast_eq`), `2^k` is a table (`p2_eq`),
Rice/verbatim runs are read at raw bit positions into arrays
(`readRiceSeqFast_eq`, `readSIntSeqFast_eq`), both predictor restores run
on arrays (`Fixed.restoreA_toList`, `Lpc.restoreA_toList`), and the
byte-level PCM16 serializer is a fused indexed pass (`pcm16Fast_eq`) —
each fast path proven equal to its specification, so every simulation
lemma and capstone keeps its statement.

The fast *encoder* (`Flac/Native/Encode.lean`) uses the other sound
pattern: it is unverified by design, like the heuristics, and each call
is **certified at runtime** — `Flac.encodePcm16Fast` decodes the produced
bytes with the *verified* decoder and compares them with the input,
falling back to the fully verified encoder on any mismatch. The byte-level
round-trip theorem (`Flac.decodePcm16_encodePcm16Fast`) therefore holds
with no hypotheses and no new trusted code, while the encoder itself is
free to use mutable arrays, a scalar bit accumulator, and a `Task` per
frame (frames are byte-aligned and independent; outputs are concatenated
in order and remain byte-identical to the serial verified encoder under
the default heuristics — which differential tests check on every corpus
file).

One more by-construction safety device: heuristic outputs carry decidable
validity certificates, and the encoder (`EncoderCfg.safeChooser`) checks
each choice at runtime, falling back to VERBATIM if the check fails. This
is why the capstone needs no hypothesis about the heuristics at all.

## Trusted vs. tested

Trusted (PLAN.md §10): the Lean kernel and compiler, plus our reading of
RFC 9639. Tested but not verified: MD5 (a conformance checksum, not part of
the losslessness claim — validated against the RFC 1321 suite) and CRC-8/16
(the encoder writes them by construction, the decoder recomputes the same
function, so the round-trip theorem needs no CRC math; correctness against
the standard is covered by golden vectors and, later, the conformance rigs).

## Working on this repo

- Build: `lake build` · Tests: `lake exe flactest`
- Read `CLAUDE.md` before contributing; the short version: no `sorry`
  reaches `master`, log every session in `PROGRESS.md`, commit per
  self-contained unit, and where PLAN.md disagrees with RFC 9639 the RFC
  wins (then fix PLAN.md).
