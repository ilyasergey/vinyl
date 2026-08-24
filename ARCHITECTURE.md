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

The decoder also stops *at* arrays. `Decode.decodeArrays` is the core, and
`decodeOption` is defined as that plus the `Array → List` conversion the
theorem statements are phrased over, so consumers that want bytes never
pay for the round-trip (`pcmBytesA_eq`, `pcm16FastA_eq`,
`decodePcm16A_eq`). Before that split, decoding allocated a cons cell per
sample only for the serializer to rebuild the very same arrays.

And it no longer stops at samples for callers that want bytes.
`Decode.decodeBytes` has each frame worker serialize *its own frame*, and
`decodeBytes_spec` says a `some` result is exactly `Stream.pcmBytesRange`
of what `decodeArrays` returns. The property that licenses it is that **a
frame is a serialization window**: the interleaved layout is sample-major,
serializing `l₁ + l₂` samples is serializing `l₁` then `l₂`
(`pcmModel_split`), and samples before/after a frame boundary come from
that frame alone (`pcmModel_left`, `pcmModel_right`), so serializing the
recombined whole-file channels is serializing each frame and concatenating
(`recombineA_model`). Together those removed 46% of decode wall time —
`recombineA`'s serial array concatenation and a whole second pass over the
samples — and they *narrowed* the trusted surface, because the window
concatenation `Stream.pcmBytesA` performs was previously asserted in prose
and unprovable (it reasons through `Task`).

## Parallelism under the ratchet

Both directions now use a `Task` per unit of work, and on the decode side
that parallelism is *proven*, not trusted. Two facts make it possible.
FLAC frames are byte-aligned and self-contained, and `BitReader` reads a
**shared immutable** `ByteArray` at an absolute bit position — so decoding
the frame at position `p` on a worker runs literally the call the serial
loop would run there. There is no shared mutable state to reason about,
and the result does not depend on scheduling.

One route would be to reason about the tasks directly. `Task` is a plain
structure whose `get` is a field, and `Task.spawn`'s logical model is
`⟨fn ()⟩` (the `@[extern "lean_task_spawn"]` implementation is what
actually spawns a thread), so `(Task.spawn f).get = f ()` holds by `rfl`,
axiom-free. That route is available and sound; it just trades the trust
in `@[extern]` models that Lean programs already accept.

Vinyl takes a different route: each worker's payload carries its own
proof.

```lean
structure Step (b0 : Nat) (d : ByteArray) where
  pos : Nat
  chs : List (Array Int)
  next : Nat
  ok : readFrameAt b0 d pos = some (chs, next)   -- erased at runtime
```

A worker builds a `Step` by pattern-matching on its own call, so the
equation is discharged by the match itself, and the field is erased at
runtime. The consumer then takes an *arbitrary* list of `Step`s — however
they were produced — checks the cheap scalar part (does this step record
the position I want?), and uses `ok` for the rest; anything unmatched or
missing it decodes on the spot.

Two things fall out, and they are the reason for the choice. First the
equality theorem is unconditional in the payload, so the *producer* never
has to be characterized at all: `stepFor_eq`, `readFramesSteps_eq` and
`readFramesFast_eq` collapse the parallel path back to the serial loop
without a single lemma about task lists, candidate scans, or window
tilings, leaving `decodeOption_eq_reference` and every capstone untouched.
That matters because frame *starts* are only guessed (a sync-code scan)
and the guess is deliberately not on the proof path — a wrong guess costs
work, never correctness. `pcm16FastPar_eq` does the same for the parallel
PCM serializer via a `PcmChunk`, whose windows are likewise a heuristic
tiling.

`ByteStep` is the same device pushed one step further: it carries
`∃ chs, readFrameAt b0 d pos = some (chs, next) ∧ … ∧ bytes = …`, with the
channel arrays *existentially quantified*. Proof fields are erased, so
those arrays never exist at runtime and never cross the thread boundary —
which is the point, because marking a `ByteArray` shared is O(1) where
marking `Array Int` channels is O(samples), and that marking cost was
what made the old per-window serialization fan-out worthless.

Second, no proof here mentions `Task` at all, so none of them depends on
the `@[extern]` task model matching the runtime. A well-typed `Step`
cannot lie either: its `ok` field proves a proposition that is false for
any other frame content, so no worker — however scheduled, however
buggy — can construct a `Step` that misdecodes a frame. What remains
trusted is exactly what every compiled Lean program already trusts, the
compiler and runtime including type safety across `Task.get`, and
specifically *not* the scheduler, the thread count, or the sync-scan
heuristic.

The writer-side ratchet now exists as well. `Flac.Emit.emitFast` writes a
complete stream into a byte buffer, and `Flac.Emit.emitFast_eq_encode` proves
byte-for-byte equality with `Stream.encode`; the proof stack covers the bit
writer, residuals, subframes, CRC-bearing frames, STREAMINFO, frame sequences,
and the full stream. This path is deliberately not the public PCM16 fast path
yet, and the reason is its *plumbing*, not its emission: `W.pushFrames`
folds serially over `Stream.chunkChannels cfg.blockSize a.channels`, and
`Stream.Audio` carries `List (List Int)` channels, so driving it means
materializing the whole file as cons cells. That is exactly what
`--encode-slow` does, and it measures **113× slower** than the fast
encoder on the same input for byte-identical output (7.89 s vs 0.07 s on
4 MB) — roughly 7× from the missing frame parallelism and ~16× from
lists-and-`Int` instead of arrays-and-`Float`.

The fast *encoder* (`Flac/Native/Encode.lean`) uses the other sound
pattern: it is unverified by design, like the heuristics, and each call
is **certified at runtime** — `Flac.encodePcm16Fast` decodes the produced
bytes with the *verified* decoder and compares them with the input,
falling back to the fully verified encoder on any mismatch. That decode
runs `Decode.decodeBytes`, the frame-parallel byte path, which
`pcm16FastA_eq_range` licenses to stand in for `decodePcm16`'s
serializer. The byte-level
round-trip theorem (`Flac.decodePcm16_encodePcm16Fast`) therefore holds
with no hypotheses and no new trusted code, while the encoder itself is
free to use mutable arrays, a scalar bit accumulator, and a `Task` per
frame (frames are byte-aligned and independent; outputs are concatenated
in order and remain byte-identical to the serial verified encoder under
the default heuristics — which differential tests check on every corpus
file).

Retiring that runtime decode is now in progress, by a different route than
the one this document used to describe. Rather than array-izing the *proven*
emitter, `Flac/Native/Encode.lean` is being proven directly. The project
owner chose that trade explicitly, accepting that a proof stack pinned to
the fast encoder will be invalidated by future performance passes; in
exchange it carries less performance risk, since the code being proven is
already measured at 1.27× rather than hoped to reach it.

**Not in the way: the searches.** They need no verification at all. A
chooser's *output* carries a decidable validity certificate by
construction (`riceCfg`, `fixedCfg`, `lpcCfg` clamp order, precision,
shift, coefficients and Rice parameters into legal range), and
`EncoderCfg.safeChooser` checks it at runtime with a VERBATIM fallback.
So the round-trip theorem already holds for *every* chooser — including
one computing in `Float`, which is unprovable in Lean (its operations are
compiler intrinsics with no axiomatization). Search quality is a
compression question, never a correctness one.

Nor does `Float` block the *emission* theorem, for a reason worth stating
precisely: `Float` operations are opaque but **deterministic**. A search and
the chooser it instantiates need only be the same function applied to equal
inputs, and `f x = f x` requires no lemma about `f`. What `Float` does
forbid is a `Float` value reaching the *bytes*.

**Which it was doing.** Until session 10 the encoder's residual bits came
from `FloatArray`s: `pushResidual`/`pushRiceRange` folded float values into
the stream, and `lpcResidualArrF`'s doc asserted the unprovable step
outright — "every value is an exact integer, so the bytes emitted from it
are the bytes an `Int` residual would emit". True, and exactly the claim the
runtime certificate existed to cover; unprovable, because there are no
equations to reason from. So emission moved to the exact `Int` residual
(`Emit.fixedResA`/`lpcResA`), costing 5.6% of encode, and the Float
emission path was deleted. Searches still run on `Float`: they only choose.

**In the way, and now discharged: the writers.** `Flac/Spec/Encode.lean`
relates the shipped `BitWriter` (a `UInt64` accumulator whose bits at or
above the pending count are deliberately stale) to `Flac.Emit.W` (a `Nat`
accumulator, masked at every step) by `Sim`: same bytes, same pending
count, same pending bits. `Simulates` lifts that to writer transformers and
composes, so each primitive is one structural induction. The simulation now
reaches `Emit.W.pushFrame` — a whole frame including both CRCs, which line
up because `sim_push_buf` says a value read off the writer's own buffer is
the same on both sides *when the buffers are*.

Two shapes made that possible, both free. `BitWriter.accPush` is one
accumulator step shared by `push` and the hot residual loop, so the loop —
which carries `buf`/`acc`/`n` unpacked to avoid allocating per sample — is
*definitionally* pushing rather than inlining something to be discharged.
And emission mirrors `Emit.W`'s recursion shapes, so no proof argues about
`Std.Range.forIn`.

**Still in the way.** Three things: a byte→array input bridge for
`frameChannels`; the chooser correspondence (`planOf`, `SubPrep.Denotes`,
`SubPlan.EmitOk`), whose real work is a fast array-side validity decider,
since today's `Decidable` instances re-materialize residual lists; and
stream assembly with the per-frame `Task` collapse, for which
`pushFrame_spec` (emission only appends) is the same locality argument that
licensed per-frame serialization on the decode side.

The payoff is measured, not estimated: the certificate is 31% of encode on
a 47 MB stereo probe, and `Int` emission cost 6.6%, so retiring it lands at
≈0.75× today's encode — about 0.95× libFLAC. Until the chain closes, master
keeps the certificate: the proven path is being built alongside it, and only
the final commit flips `--encode` and deletes `pcm16Certified`.
`Flac.encodePcm16Fast` keeps its signature and
`Flac.Stream.decodePcm16_encodePcm16Fast` keeps its exact statement — the
`Option` survives for the input well-formedness guard — so `pin_encode_fast`
never moves.

A smaller stage remains on `Flac.Emit.W`'s own bit writer: `W.flushGo`
returns `ByteArray × Nat × Nat` (two `Prod` cells per bit push, plus a boxed
scalar) and multiplies by `p2 k` where the fast writer shifts a `UInt64`.
That only matters for `--encode-slow`, which is no longer on the shipping
path's critical route.

One more by-construction safety device: heuristic outputs carry decidable
validity certificates, and the encoder (`EncoderCfg.safeChooser`) checks
each choice at runtime, falling back to VERBATIM if the check fails. This
is why the capstone needs no hypothesis about the heuristics at all.

## Is the thing you ran the thing that was proved?

The theorems name specific functions; the `vinyl` binary calls specific
functions; nothing about Lean forces those to be the same functions. That
linkage is therefore pinned two ways, both in the merge gate.

`FlacTest/Capstones.lean` restates each capstone in full and discharges it
with the real theorem, so a statement that drifts while keeping its name
fails `lake build` (grep-by-name, which `scripts/check.sh` also does,
cannot notice that). `scripts/check.sh` then greps each CLI branch for the
function its capstone is about, because which function a `do` block invokes
is not something a type can express:

| CLI mode | calls | covered by |
|---|---|---|
| `--encode` | `Flac.encodePcm16Fast` | `decodePcm16_encodePcm16Fast` — hypothesis-free |
| `--encode-slow` | `Flac.encodePcm16Cfg` | `decodePcm16_encodePcm16Cfg` |
| `--decode-pcm16` | `Flac.decodePcm16A` | `decodePcm16A_eq` → the byte-level capstone |
| `--decode-fast` | `Decode.decodeBytes` (fallback `decodeArrays` + `Stream.pcmBytesRange`) | `decodeBytes_spec` → samples **and** byte layout |
| `--decode` | `Stream.decodeReference` + `Stream.pcmBytes` | samples yes, byte layout **no** (below) |

Both negative tests are checked to fire: repointing `--encode` at the
uncertified `Flac.Encode.encodePcm16` fails the gate, and weakening
`pin_encode_fast` fails the build.

What is trusted regardless. The proofs rest on Lean's kernel and, per
`#print axioms`, only on `propext`, `Classical.choice` and `Quot.sound`.
The executable rests additionally on Lean's compiler and runtime — but
*not* on any second implementation of this code: `Flac/` contains no
`native_decide` (which would put the compiler inside a proof), no
`@[implemented_by]`, no `@[extern]`, no `unsafe`, and no `partial def`, so
the compiled code is generated from the very definitions the kernel
checked. The gate greps for all of these. The primitives underneath —
`Nat`/`Int` arithmetic on GMP, `ByteArray`, `FloatArray`, `Task` — are
core Lean's `@[extern]` implementations, trusted as by any Lean program.

And the honest gap, now one mode narrower than it was.
`Flac/Spec/PcmBytes.lean` pins the serialization loops of
`Flac/Native/Stream.lean` to a model (`pcmBytesRange_eq`) and proves the
frame-window property above, so **`--decode-fast`** — the mode the
benchmark's decode column measures — has its byte layout covered by
`decodeBytes_spec`, not merely tested. `--decode` still writes through
`Stream.pcmBytes`, whose *windowing* (one `Task` per 64Ki-sample window)
is unprovable as written, so for that mode the decoded samples are covered
by `decodeOption_eq_reference` while the byte layout is established
against libFLAC by differential testing plus the golden vectors of
`pcmBytesTests`. The other fully proved byte-level path is
`--decode-pcm16` (`decodePcm16A_eq`).

The two serializers are also now tied together: `pcm16FastA_eq_range`
proves `Flac.pcm16Row`'s `(x % 65536)` byte split equals the `UInt64`-lane
split of `pcmBytesRange` for *every* `Int`, because `Int.toInt64` is
reduction mod `2^64` and `2^16` divides `2^64`. That is what lets the
encoder's runtime certificate run the frame-parallel byte decoder in place
of a decode followed by a serial serialization.

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
