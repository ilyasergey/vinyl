# Repository structure

Soundproof is a formally verified FLAC codec in pure Lean 4. This document
explains how the repository is organized and *why* — the layering is the
methodology (see `PLAN.md` for the full technical plan, milestones, and
theorem stack).

## The idea in one paragraph

The deliverable is a pure-Lean FLAC encoder/decoder pair together with a
kernel-checked **round-trip theorem**: `Flac.decode (Flac.encode pcm opts) =
.ok pcm` for every well-formed input and every encoder configuration
(PLAN.md §1). Everything in the tree is positioned relative to that theorem:
code that the theorem quantifies over lives in `Flac/Native/`, the
proof-oriented reference semantics lives in `Flac/Reference/`, the theorems
themselves live in `Flac/Spec/`, and everything that merely *tests* the
result against the outside world (libFLAC, ffmpeg, fuzzers, benchmarks)
lives outside the trusted base in `conformance/` and `bench/`.

## Directory map

```
soundproof/
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
│   │   ├── Bits.lean    # MSB-first bit model: readBits/writeBits, unary,
│   │   │                #   byte alignment, ByteArray packing
│   │   ├── Crc.lean     # CRC-8 (poly 0x07) and CRC-16 (poly 0x8005)
│   │   ├── Utf8Num.lean # extended-UTF-8 coded frame/sample numbers (≤36 bits)
│   │   └── Md5.lean     # pure-Lean MD5 for the STREAMINFO PCM checksum
│   ├── Reference/       # (from M2) verified reference decoder over ℤ,
│   │                    #   structured for proofs, not speed
│   └── Spec/            # ALL theorems; no sorry, no axioms, ever
│       ├── Bits.lean    # L0: bit-I/O round-trips, packing, alignment
│       └── Utf8Num.lean # coded-number round-trip (n < 2^36)
├── FlacTest.lean, FlacTest/
│   └── Main.lean        # golden-vector unit tests (`lake exe flactest`)
├── conformance/         # (from M3–M4) separate lake package: differential
│                        #   rigs vs `flac`/ffmpeg, decoder fuzzing, corpora
└── bench/               # (post-M5) throughput/ratio benchmarks vs libFLAC
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

2. **`Flac/Reference/`** — a second decoder over unbounded `Int`, written
   for clean induction rather than speed. The capstone is first proven
   against it (M4), then transferred to the shipped decoder via an
   accept-set equivalence `decode_ok_iff_reference` (M5).

3. **`Flac/Spec/`** — the theorem stack, proven bottom-up (PLAN.md §4):
   - **L0** bit I/O round-trips (`Spec/Bits.lean`, done),
   - **L1** primitive codes: zigzag, Rice/RICE2, escapes, coded numbers
     (`Spec/Utf8Num.lean` done; Rice with M1),
   - **L2** residual partitions (with divisibility certificates),
   - **L3** fixed and quantized-LPC predictors — the load-bearing lemmas,
   - **L4** stereo decorrelation and wasted bits,
   - **L5** subframe/frame composition and width bookkeeping,
   - **L6** the stream capstone `Flac.decode_encode`.

Each layer's round-trip lemma is stated so the layer above uses it opaquely.

## Key representation choice (current)

The bit-level model is `List Bool`, MSB-first (`Flac.BitStream`). Writers
are pure functions returning bit lists; readers are structural-recursive
consumers returning `Option (value × rest)`. This makes every L0/L1 proof a
clean induction. Buffered, word-at-a-time production bit I/O is deliberately
deferred to M5/M6, where it is proven equivalent to this model — the
lean-zip "ratchet" pattern: optimize only what a theorem already pins down.

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
