# Repository structure

Vinyl is a formally verified FLAC codec in pure Lean 4. This document
explains how the repository is organized and *why* — the layering is the
methodology (see `PLAN.md` for the full technical plan, milestones, and
theorem stack).

## The idea in one paragraph

The deliverable is a pure-Lean FLAC encoder/decoder pair together with a
kernel-checked **round-trip theorem**: whenever the shipped encoder
returns bytes at all, decoding them recovers the audio —
`Flac.encode a = some bytes → Flac.decode bytes = .ok a`
(`decode_encode`, hypothesis-free: since the P7 hardening round the
public `encode` checks its decidable precondition at runtime, and the
raw total encoder lives under `Flac.Unchecked`). Its byte-level
corollary (`decodePcm16_encodePcm16`) carries the same guarantee for
raw PCM files. Everything in the
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
├── lakefile.toml        # lake package: libs Flac/FlacTest, exes flactest/vinyl
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
│   │   ├── Stream.lean     # STREAMINFO, Audio, Unchecked.encode,
│   │   │                   #   decodeReference
│   │   ├── Heuristics.lean # LPC/fixed/stereo search (sanitized at use)
│   │   ├── Reader.lean     # BitReader: buffered ByteArray bit reader
│   │   │                   #   (word-level fast paths proven = the spec)
│   │   ├── Decode.lean     # the shipped production decoder, Flac.decode
│   │   ├── Emit.lean       # the byte-buffer stream writer (Emit.emitFast)
│   │   ├── Encode.lean     # the fast encoder (arrays/Task-parallel frames);
│   │   │                   #   proven to compute Stream.Unchecked.encode
│   │   └── Codec.lean      # Flac.encode (checked) + Unchecked + fast,
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
│       ├── Emit.lean       # emitFast writes the reference encoder's bytes
│       ├── Encode.lean     # the shipped encoder computes the reference one
│       ├── PcmBytes.lean   # the serialization loops and decodeBytes_spec
│       ├── Reader.lean     # BitReader simulates the List Bool model
│       └── Decode.lean     # production ≡ reference; the shipped capstones
├── FlacTest.lean, FlacTest/
│   ├── Cli.lean         # unit tests + the vinyl CLI (encode/decode)
│   ├── Capstones.lean   # each capstone restated in full, discharged
│   ├── FuzzGen.lean     # generators for the round-trip fuzz rig
│   └── Main.lean        # entry point
├── conformance/
│   ├── smoke.sh         # Rigs 1–2 vs `flac` CLI, both directions
│   ├── ietf.sh          # RFC 9639 companion test-file corpus (merge gate)
│   └── fuzz.sh          # Rigs 3–5: totality, bit-flip, round-trip
├── scripts/
│   ├── check.sh         # the ratchet: build + hygiene + pins + tests
│   ├── audit_ir.py      # what the generated C must and must not contain
│   └── gen/             # per-order kernel templates + drift check
├── docs/                # hardening notes, one per audit finding (see README)
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

2. **The reference decoder** (`Stream.decodeReference` in
   `Flac/Native/Stream.lean`, and the readers it is built from) — written over
   the `List Bool` bit model for clean induction rather than speed. The
   capstone is first proven against it,
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
byte-for-byte equality with `Stream.Unchecked.encode`; the proof stack covers the bit
writer, residuals, subframes, CRC-bearing frames, STREAMINFO, frame sequences,
and the full stream. This path is deliberately not the public PCM16 fast path
yet, and the reason is its *plumbing*, not its emission: `W.pushFrames`
folds serially over `Stream.chunkChannels cfg.blockSize a.channels`, and
`Stream.Audio` carries `List (List Int)` channels, so driving it means
materializing the whole file as cons cells. That is exactly what
`--encode-slow` does, and at one thread it measures **~40× slower** than the
fast encoder for byte-identical output (2.01 s against 0.05 s on 4 MB) — all
of it lists-and-`Int` against arrays-and-`Float`, since neither side is
parallel in that comparison. It also costs **≈47× the input in resident
memory**, so it is not an option on large files: 4 MB of PCM peaks at 203 MB,
128 MB at 6.1 GB. The channel representation is what does that, not the
emitter.

The fast *encoder* (`Flac/Native/Encode.lean`) used the other sound
pattern until session 10: unverified by design, like the heuristics, with
each call **certified at runtime** by decoding its own output with the
verified decoder. That is gone. The encoder is now *proven*.

**The capstone.** `Flac.Encode.encodePcm16_eq` says the shipped encoder
computes the reference encoder:

```
encodePcm16 blockSize ch sr bytes
  = Stream.Unchecked.encode ⟨blockSize, false, fastChooser 16⟩
      ⟨deinterleave ch (pcm16OfByteList bytes.data.toList), 16, sr⟩
```

so `Flac.Stream.decodePcm16_encodePcm16Fast` follows from
`decodePcm16_encodePcm16Cfg` with no runtime decode, no fallback, and no
trust in `Flac.Encode`. Its statement did not change by a character — the
`Option` survives for the input guard — so the grep-pinned capstone never
moved. Retiring the certificate was worth 30% of encode on the 32 MB mono
probe the bench history uses (68.5 → 97.7 MB/s, taking encode from 1.35×
*single-threaded* `flac -8` to **0.94×**; thread-matched on real audio the
encoder is 1.6× behind — see [`bench/README.md`](bench/README.md)) and
23% on a 47 MB stereo one (0.564 s → 0.434 s). Compression is unchanged: the
output is byte-identical.

**Why `Float` was never in the way.** Float operations are opaque but
*deterministic*. A search and the chooser the reference is instantiated
with need only be the same function applied to equal inputs, and
`f x = f x` requires no lemma about `f`. So the searches appear on *both*
sides of every equation in the chain and are only ever applied. What
`Float` does forbid is a float reaching the **bytes** — and until session
10 one did: `pushResidual` folded values straight off the search's
`FloatArray`s, and `lpcResidualArrF`'s own doc asserted the unprovable
step ("every value is an exact integer, so the bytes emitted from it are
the bytes an `Int` residual would emit"). That was precisely the claim the
certificate existed to cover. Emission now goes through the exact `Int`
residual (`Emit.fixedResA`/`lpcResA`), at 8% of encode — the whole cost of
provability was 10%, against the 30% the certificate gave back.

**The chain, bottom to top** (all in `Flac/Spec/Encode.lean`):

- `Sim` relates the shipped `BitWriter` — a `UInt64` accumulator whose bits
  at or above the pending count are deliberately stale — to `Flac.Emit.W`,
  by "same bytes, same pending count, same pending bits". `Simulates` lifts
  it to writer transformers and composes, so each primitive is one
  structural induction. `flush_sim` discharges the fast writer's
  sloppiness: it never masks because every byte it emits is bits
  `[n-8, n)` and nothing at or above `n` is read.
- `sim_pushRiceRange` covers the per-sample loop, which carries
  `buf`/`acc`/`n` unpacked to avoid allocating. It stays provable because
  it goes through the same accumulator step `push` does
  (`BitWriter.accPush`), making each of its pushes *definitionally* a push.
- `sim_pushFrameOf` reaches a whole frame, both CRCs included: a value read
  off the writer's own buffer is the same on both sides *because* the
  buffers are (`sim_push_buf`).
- `frameChannels_eq` is the input bridge: the window a worker deinterleaves
  out of the shared PCM bytes is the reference's frame.
- `SubPlan.sanitize` clamps the search's scalars (Rice parameters to 14,
  fixed order to 4, coefficients to the 12-bit field, shift to 15,
  partition order to a legal one) so `Subframe.SubCfg.Valid` holds *by
  construction* — no scan. Every clamp is a no-op on what the searches
  return, so output is byte-identical, at 0.2%. `wastedDetectF_dvd` is the
  one non-scalar clause, and it too is a proof.
- `chooseFrame_asg_valid` lifts that to `Frame.ChannelAsg.Valid`, so
  `orVerbatim` — which the reference wraps every chooser in — is the
  identity on the fast encoder's choices (`safeChooser_fastChooser`). The
  VERBATIM fallback never fires, and nothing checks that it doesn't.
- `sim_frame` joins search and emission; `pushFrames_concat` joins the
  reference's fold to the shipped concatenation, resting on
  `pushFrame_buf_append` — emission only *appends*, the same locality
  argument that licensed per-frame serialisation on the decode side.

**`Task` stayed out of every proof**, as on the decode side. Each frame
worker returns a `FrameStep`: its bytes plus the erased proof that they are
`frameBytesPcm`'s output for that index, discharged by `rfl` at
construction. *Any* value of that type carries the equation, so the
consumer needs no fact about how the worker ran; it checks the recorded
index and rebuilds the frame otherwise, so a wrong payload costs work,
never correctness. `Md5Step` does the same for the digest worker. And
`Stream.pcmBytesA` — which split serialisation into windows, one `Task`
each, and "carried no theorem, because it reasons through `Task`" — is now
the plain range, which is what let the STREAMINFO digest become a proven
function of the samples. Nothing on a shipped fast path used it.

**What the encoder still checks at run time** is a handful of O(1)
guards, exactly the conditions the certificate silently covered plus the
two the audit added: the shared `Pcm16ShapeOk` shape guard — `0 < ch ≤ 8`,
the byte count a multiple of `2·ch`, and a nonzero sample rate on
nonempty input (P8/P11) — then `sampleRate < 2^20`, the sample count
below `2^36`, and `16 ≤ blockSize ≤ 4608`. Everything else
`Stream.Unchecked.encode` checks — `Audio.WellFormed` in full — is
discharged by `Flac.Encode.audio_wellFormed`.

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
| `--decode` | `Flac.Decode.decodeOption` + `Stream.pcmBytes` | `decodeOption_eq_reference` — pointwise the reference decoder; byte layout **no** (below) |

Both negative tests are checked to fire: repointing `--encode` at the
uncertified `Flac.Encode.encodePcm16` fails the gate, and weakening
`pin_encode_fast` fails the build.

**Kernel swaps have the same problem one level down, and the same answer.**
Most hot loops ship as a `@[csimp]` equation: a kernel-checked theorem
`f = fFast` that leaves every statement about `f` alone and changes only what
the compiler emits. Two things follow, and the gate checks both.

*Where the equality lives.* A swap must be co-located with the definition it
replaces, so `Flac/Native/` now holds equalities as well as code (the LPC and
fixed restores, the Rice writer, the stereo decorrelations, the serializers,
the CRC). That is not a break in the layering discipline: these theorems are
about two definitions in the same module and prove nothing about the codec —
`Flac/Spec/` remains where every statement *about the format* lives.

*Where the swap applies.* A `@[csimp]` only rewrites code generated after it
is elaborated, so a swap proved in `Flac/Spec/` reaches importers but not the
module that defined the function. Two shipped entry points sat on the wrong
side of that line for months (`Flac.encode` compiled to the `List Bool`
reference writer, `Flac.decodePcm16` to the list decoder, both with the fast
equality proven and unused). So the rule is: **a swap is either co-located with
a Native-provable equality, or accompanied by a compiled-path audit of every
caller module** — `scripts/check.sh` greps the generated C in
`.lake/build/ir/` for the kernel symbols the shipped entry points must call. A
theorem cannot state that; the generated C can be read.

*Not every kernel is a swap, and the difference is worth naming.* Four
mechanisms put a fast path on the shipped binary and they carry different
guarantees. **(a)** A `@[csimp]` swap, as above. **(b)** A *guarded dispatch*:
the shipped definition itself branches on a decidable domain guard, with every
branch proven equal to the specification reader — that is what
`readRiceSeqFast` (on `RiceRunOk`) and `readSIntSeqFast` (on `SIntRunOk`) are,
and the guarantee is as strong as (a), with `riceRunU_eq` / `readSIntSeqU_eq`
pinned by name instead of a swap. **(c)** *Tested, not verified*: MD5 has no
equality theorem and no second implementation; RFC 1321 vectors and corpus
digests are what check it, and it sits outside the decoder-totality lint for
the same reason. **(d)** *Proof-free by construction*: the sync scan only
guesses frame offsets, and `stepAt` builds a `Step` by matching on
`readFrameAt`'s own result, so a `Step` exists only where a frame really
parsed. A wrong guess therefore costs a failed parse and never a wrong result;
what bounds the *work* it costs is separate, the candidate-density floor and
the task cap. Documentation that calls all four "csimp swaps" overstates (c)
and (d), which is a claim about the trusted base, not a wording preference.

*The audit has a negative half too.* Several hot loops carry the input
buffer's size as an erased-proof parameter specifically so that `uget` needs no
size load — that word shares a cache line with the object's reference count, so
reading it per byte turns into repeated coherence invalidations once several
decode workers hold the same input. It cost ≈32% of the sixteen-thread decode
wall. The pathology is **invisible at one thread**, where the line is L1-hot,
so no timing gate and no single-thread profile can catch a regression.
`scripts/audit_ir.py` therefore also requires that the generated bodies of the
Rice reader, the unary scan, `byteU`, the sync scan, the fixed-width reader and
MD5's block loop contain no `lean_sarray_size`/`lean_byte_array_size` at all.

What is trusted regardless. The proofs rest on Lean's kernel and, per
`#print axioms`, only on `propext`, `Classical.choice` and `Quot.sound`.
The executable rests additionally on Lean's compiler and runtime — but
*not* on any second implementation of this code: `Flac/` contains no
`native_decide` (which would put the compiler inside a proof), no
`@[implemented_by]`, no `@[extern]`, no `unsafe`, and no `partial def`, so
the compiled code is generated from the very definitions the kernel
checked. The gate greps for all of these — and, since the audit
hardening rounds ([`docs/README.md`](docs/README.md)), it also lints
every module the shipped executables link for panicking calls (P9), and
pins by name the `@[csimp]` equations that keep the frame loops in
constant stack (P6). The primitives underneath —
`Nat`/`Int` arithmetic on GMP, `ByteArray`, `FloatArray`, `Task` — are
core Lean's `@[extern]` implementations, trusted as by any Lean program.

And the honest gap, now one mode narrower than it was.
`Flac/Spec/PcmBytes.lean` pins the serialization loops of
`Flac/Native/Stream.lean` to a model (`pcmBytesRange_eq`) and proves the
frame-window property above, so **`--decode-fast`** — the mode the
benchmark's decode column measures — has its byte layout covered by
`decodeBytes_spec`, not merely tested. `--decode` still writes through
`Stream.pcmBytes` — serial since the windowed serializer was retired,
but its byte arithmetic (the `UInt64` lane) is deliberately outside the
theorems — so for that mode the decoded samples are covered by
`decodeOption_eq_reference` (which is also why, since the P6 round, the
branch *runs* `Flac.Decode.decodeOption` rather than executing the
`List Bool` reference pipeline on untrusted input) while the byte layout
is established against libFLAC by differential testing plus the golden
vectors of `pcmBytesTests`. The other fully proved byte-level path is
`--decode-pcm16` (`decodePcm16A_eq`).

The two serializers are also now tied together: `pcm16FastA_eq_range`
proves `Flac.pcm16Row`'s `(x % 65536)` byte split equals the `UInt64`-lane
split of `pcmBytesRange` for *every* `Int`, because `Int.toInt64` is
reduction mod `2^64` and `2^16` divides `2^64`. That is what lets the
decoder's `--decode-fast` path serialize inside its frame workers, and it
is how the STREAMINFO digest the reference writes is tied to the input
bytes (`Flac.Encode.pcmBytes_deinterleave`).

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
