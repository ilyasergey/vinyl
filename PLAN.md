# Vinyl — PLAN.md

Lean version: 4.33
Github repository to sync with:
Make suitable .gitignore
Log your progress and commit regularly - make this into CLAUD.md

**A formally verified FLAC codec in pure Lean 4.**

This document is the complete working plan. It is written to be handed to a
coding agent (or a swarm of them) with no other context. Read it fully before
writing code. The methodology deliberately mirrors
[`lean-zip`](https://github.com/kim-em/lean-zip) (verified DEFLATE): a pure-Lean
encoder/decoder pair, a kernel-checked round-trip theorem as the merge ratchet,
a reference→production transfer proof, and differential fuzzing against the
incumbent C implementation for standards interoperability. Study lean-zip's
`Zip/Spec/` layout, its `DeflateRoundtripProduction.lean` capstone, and its
`conformance/` package before starting; reuse its proof patterns (BitReader
invariants, `CopyWithin`-style array lemmas, accept-set transfer) wherever they
fit.

Normative format reference: **RFC 9639** (FLAC, IETF, Dec 2024). Keep a copy in
`references/`. Where this plan and the RFC disagree, the RFC wins — then fix
this plan.

---

## 1. Goal and capstone theorem

Deliverable: a pure-Lean (no FFI) FLAC encoder and decoder such that the Lean
kernel certifies losslessness:

```lean
/-- **Capstone.** Decoding the output of `encode` returns the original audio,
    for every well-formed input and every encoder configuration. -/
theorem Flac.decode_encode (pcm : Audio) (opts : EncoderOptions)
    (hwf : pcm.WellFormed) (hopts : opts.WellFormed pcm) :
    Flac.decode (Flac.encode pcm opts) = .ok pcm
```

with

```lean
/-- Interleaved multichannel PCM. `samples[c][i] : Int` is sample `i` of
    channel `c`. -/
structure Audio where
  channels      : Array (Array Int)
  bitsPerSample : Nat        -- 4..32
  sampleRate    : Nat        -- 1..1048575 (0 reserved out of scope for v1)

def Audio.WellFormed (a : Audio) : Prop :=
  1 ≤ a.channels.size ∧ a.channels.size ≤ 8 ∧
  4 ≤ a.bitsPerSample ∧ a.bitsPerSample ≤ 32 ∧
  (∀ c ∈ a.channels, c.size = a.channels[0]!.size) ∧
  (∀ c ∈ a.channels, ∀ s ∈ c,
     -(2^(a.bitsPerSample-1)) ≤ s ∧ s < 2^(a.bitsPerSample-1))
```

`EncoderOptions` must cover, and the capstone must quantify over: block size,
max fixed/LPC order, LPC coefficient precision, Rice partition order limit,
stereo-decorrelation mode policy, and apodization/order-selection heuristics.
The lean-zip lesson applies verbatim: **every heuristic knob is
correctness-irrelevant by construction** (it changes *which* valid stream is
emitted, never whether the round-trip holds), so once the capstone is in place,
the entire search/heuristic layer is free optimization territory for agents.

Secondary certified statements (required, not stretch):

```lean
/-- Decoder totality: decoding never panics; every input yields .ok or a
    diagnostic .error. Enforced by construction (no partial defs, no `!`
    indexing in the decoder) and exercised by fuzzing. -/

/-- Accept-set transfer (mirrors lean-zip's inflate_ok_iff_reference):
    the shipped decoder accepts exactly the streams the verified reference
    decoder accepts, with equal outputs. -/
theorem Flac.decode_ok_iff_reference (s : ByteArray) :
    Flac.decode s = .ok a ↔ Flac.decodeReference s = .ok a
```

Stretch (Section 9): a declarative RFC 9639 stream relation and two-sided
decoder soundness/completeness against it. Do not block v1 on this.

### Why the round-trip theorem is the right spec

Same argument as lean-zip: it is *endogenous* (no external model in the trusted
statement), it quantifies over all inputs and all knobs, and it is exactly the
property users mean by "lossless". Interop with the rest of the world (libFLAC,
ffmpeg) is a conformance concern, handled by the differential-testing rig in
Section 6 — outside the kernel, by design.

---

## 2. Scope

**v1 (the verified core, milestones M0–M5):**
- Native FLAC container: `fLaC` marker, STREAMINFO, PADDING; frames with
  CRC-8 header / CRC-16 footer.
- All block sizes 16–65535 (last frame may be shorter), all sample rates
  encodable in the frame header, 4–32 bits per sample, 1–8 channels.
- Subframes: CONSTANT, VERBATIM, FIXED (orders 0–4), LPC (orders 1–32,
  coefficient precision 1–15 bits, non-negative quantization shift).
- Wasted-bits flag (decoder: full support; encoder: emits it when detected —
  detection is deterministic, so it stays inside the capstone quantifier).
- Stereo decorrelation: independent, left/side, right/side, mid/side.
- Residuals: Rice partitions, both 4-bit (RICE) and 5-bit (RICE2) parameter
  variants, including the escape code (verbatim residuals).
- Frame numbering: fixed- and variable-blocksize strategies, UTF-8-style coded
  numbers up to 36 bits.
- MD5 of the unencoded PCM in STREAMINFO (implemented in Lean; *tested*, not
  verified — see trusted base).

**Deferred (explicitly out of v1):** SEEKTABLE, VORBIS_COMMENT, CUESHEET,
PICTURE, APPLICATION metadata (decoder skips them by length; encoder emits
none); Ogg encapsulation; streaming/push APIs; sample rate 0 ("get from
metadata") edge cases. None of these interact with the capstone.

---

## 3. Repository layout

```
lean-flac/
  Flac.lean                    -- public API re-exports
  Flac/
    Native/                    -- executable code (production)
      BitReader.lean           -- MSB-first reader (FLAC is big-endian/MSB-first;
      BitWriter.lean           --   port lean-zip's pattern, flip bit order)
      Crc.lean                 -- CRC-8 (poly 0x07), CRC-16 (poly 0x8005)
      Md5.lean                 -- pure-Lean MD5 (tested against RFC 1321 vectors)
      Utf8Num.lean             -- extended-UTF-8 coded frame/sample numbers (≤36 bits)
      Rice.lean                -- zigzag + Rice/RICE2 + escape partitions
      Fixed.lean               -- fixed predictors, orders 0–4
      Lpc.lean                 -- quantized-LPC residual/restore (Int64 arithmetic)
      Stereo.lean              -- mid/side, left/side, right/side transforms
      Subframe.lean            -- subframe encode/decode incl. wasted bits
      Frame.lean               -- frame assembly, header/footer, CRCs
      Stream.lean              -- fLaC marker, STREAMINFO, top-level encode/decode
      Heuristics.lean          -- order selection, apodization, partition search,
                               --   stereo-mode decision (UNVERIFIED BY DESIGN;
                               --   only output-format lemmas may depend on it)
    Reference/                 -- verified reference decoder over ℤ (unbounded),
                               --   structured for proofs, not speed
    Spec/                      -- all theorems; NO sorry, NO axioms; one file per
                               --   lemma cluster, lean-zip style
  FlacTest/                    -- unit + golden tests
  conformance/                 -- separate lake package (like lean-zip's):
    DiffLibFlac.lean           --   differential rig vs `flac` CLI and ffmpeg
    FuzzDecode.lean            --   decoder totality fuzzing
    FuzzRoundtrip.lean         --   structured round-trip fuzzing
    corpus/                    --   IETF test files + generated corpus
  references/                  -- RFC 9639; ietf-wg-cellar/flac-test-files notes
  bench/                       -- vs libFLAC/ffmpeg (Section 7)
  PLAN.md                      -- this file
  PROGRESS.md                  -- per-session logs, lean-zip convention
```

Toolchain: current stable Lean 4; depend on Std only (no mathlib in `Native/`;
mathlib allowed in `Spec/` only if it demonstrably shortens proofs — prefer
self-contained lemmas, again the lean-zip convention).

---

## 4. Theorem stack

Prove bottom-up. Each layer's round-trip lemma should be stated so that the
layer above uses it opaquely. Signatures below are the contract; adjust names,
keep shapes.

**L0 — Bit I/O.** Port lean-zip's BitWriter/BitReader correctness pattern,
MSB-first:
```lean
theorem readBits_writeBits (w : BitWriter) (n : Nat) (v : Nat) (hn : n ≤ 32)
    (hv : v < 2^n) : -- reader positioned at writer's pre-write position
    ...
theorem bitReader_align_pad ...   -- byte alignment before CRC-16 footer
```
Also: unary read/write inverse (needed by Rice and wasted-bits).

**L1 — Primitive codes.**
```lean
theorem unzigzag_zigzag (x : Int) : unzigzag (zigzag x) = x
theorem riceDecode_riceEncode (k : Nat) (hk : k ≤ 30) (xs : Array Int) : ...
theorem escapeDecode_escapeEncode (bits : Nat) (xs : Array Int)
    (hb : ∀ x ∈ xs, fits bits x) : ...
theorem utf8NumDecode_encode (n : Nat) (h : n < 2^36) : ...
theorem crc8_encoderOutput_valid / crc16_encoderOutput_valid
    -- decoder recomputes and compares; encoder writes by construction
```

**L2 — Residual partitions.** Partition order `po` requires
`2^po ∣ blockSize` and `blockSize / 2^po > predictorOrder` for the first
partition rule; encode these as hypotheses produced by the encoder's partition
chooser and consumed here:
```lean
theorem partitionsDecode_encode (po : Nat) (ord : Nat) (bs : Nat)
    (hdiv : 2^po ∣ bs) (hfirst : ord < bs / 2^po) (res : Array Int) : ...
```

**L3 — Predictors.** The load-bearing lemmas. Reference forms over `Int`
(no overflow, clean induction), production forms over `Int64` with explicit
range lemmas (see Section 5).
```lean
-- Fixed, orders 0–4 (coefficients are the alternating binomials):
theorem restoreFixed_residualFixed (ord : Fin 5) (xs : Array Int)
    (h : ord.val ≤ xs.size) :
    restoreFixed ord (xs.take ord) (residualFixed ord xs) = xs

-- Quantized LPC. Prediction p n = (Σ i, c[i] * out[n-1-i]) >>> shift
-- (arithmetic shift). Key induction: decoded prefix = original prefix,
-- hence decoder's prediction ≡ encoder's prediction, hence
-- out[n] = p n + (xs[n] - p n) = xs[n].
theorem restoreLpc_residualLpc (c : Array Int) (shift : Nat)
    (hc : 1 ≤ c.size ∧ c.size ≤ 32) (xs : Array Int) (h : c.size ≤ xs.size) :
    restoreLpc c shift (xs.take c.size) (residualLpc c shift xs) = xs
```
Note the proof does **not** care where `c` came from — Levinson-Durbin,
windowing, and quantization live in `Heuristics.lean` and never enter the
kernel. The only obligation they carry is emitting `c.size`, precision, and
shift within header-encodable ranges.

**L4 — Sample transforms.**
```lean
theorem stereoRestore_stereoApply (m : StereoMode) (l r : Array Int)
    (h : l.size = r.size) : stereoRestore m (stereoApply m l r) = (l, r)
-- mid/side: mid = (l+r) >>> 1, side = l - r; recover via parity of side.
-- side channel needs bps+1 bits — this fact feeds the L5 width bookkeeping.

theorem wastedRestore_wastedShift (k : Nat) (xs : Array Int)
    (h : ∀ x ∈ xs, 2^k ∣ x) : ...
theorem wastedDetect_sound (xs) : ∀ x ∈ xs, 2^(wastedDetect xs) ∣ x
```

**L5 — Subframe and frame round-trips.** Composition layers; mostly plumbing
plus width bookkeeping (which subframe sees bps, bps+1 for the side channel,
minus wasted bits). Then:
```lean
theorem frameDecode_frameEncode (fr : FrameData) (opts) (hwf) : ...
```

**L6 — Stream capstone.** STREAMINFO consistency (min/max block size, min/max
frame size, total samples, MD5), frame concatenation, sync-code non-emulation
*not required* (the decoder is positional after the header: it reads frames by
structure, not by hunting for sync codes — hunting/resync is a robustness
feature deferred with streaming). Conclude `Flac.decodeReference_encode`, then
transfer via `decode_ok_iff_reference` to the production decoder, yielding the
capstone `Flac.decode_encode`.

Rough proof-mass estimate, calibrated against lean-zip (32k lines for DEFLATE
incl. Huffman + LZ77): FLAC has no Huffman and no match-finder, so expect
**6–12k lines** across `Spec/`, dominated by L3 and the L5 width bookkeeping.

---

## 5. Known hard points (read before estimating anything)

1. **Integer widths.** Side channel is bps+1 bits (up to 33). LPC accumulator:
   32 coefficients × 15-bit precision × 33-bit samples ⇒ ≤ 33+15+5 = 53-bit
   partial sums — fits Int64, but *prove it*: production `Lpc.lean` needs a
   `noOverflow` lemma family, and the reference/production transfer at L3 is
   where `Int` meets `Int64`. Budget real time here; it is the FLAC analogue
   of lean-zip's word-at-a-time comparator proofs.
2. **Arithmetic shift on negatives.** `>>>` on `Int` (floor toward −∞) must
   match the production Int64 arithmetic-shift semantics exactly. Write the
   bridging lemmas once, in one file, and reuse.
3. **Mid/side parity.** `l+r` and `l−r` share parity; reconstruction uses
   side's low bit. Easy to state, easy to get off-by-one wrong — make it a
   standalone lemma with exhaustive small-int tests before proving.
4. **Rice escape + partition rules.** The `2^po ∣ blockSize` and first-partition
   size conditions must be carried as hypotheses, not rediscovered mid-proof.
   Design the encoder's partition chooser to *return* the certificates.
5. **Last-frame short block** interacts with fixed/variable blocksize
   numbering and with STREAMINFO min/max block size. Handle it in L5, not as a
   special case smeared across layers.
6. **Wasted bits** change the effective bps *per subframe* after stereo
   decorrelation. The width bookkeeping in L5 is the single most bug-prone
   composition; write the width function once and prove its monotonicity
   lemmas early.
7. **Decoder totality.** No `partial`, no panicking indexing anywhere in
   `Native/` decode paths. Structural or fuel-based recursion with explicit
   error returns. Fuel bounds derivable from input size (a FLAC frame cannot
   encode more than its bit budget of samples — state this as the
   loop-bounds lemma, mirroring lean-zip's `InflateLoopBounds`).

---

## 6. Fuzzing and conformance plan

All of this lives in `conformance/` (separate lake package) and in CI. None of
it is in the trusted base; all of it gates merges.

**C oracles:** official `flac` CLI (libFLAC) and `ffmpeg`. Pin versions in
`conformance/README`.

**Corpora:**
- `ietf-wg-cellar/flac-test-files` (the RFC 9639 companion test suite) —
  vendored into `conformance/corpus/`, both the "must decode" and
  "uncommon/edge" sets.
- Generated PCM battery: silence, DC offsets, full-scale square waves
  (clipping-adjacent values ±2^(bps−1)), sines at rates that stress each fixed
  order, white noise, alternating ±max (worst case for prediction), per-channel
  divergent content (stresses stereo-mode decision), lengths that force short
  last frames, and every (bps, channels) corner: bps ∈ {4, 8, 12, 16, 20, 24,
  32}, channels ∈ {1, 2, 3, 8}.

**Rig 1 — Encoder conformance (our encoder → their decoders).** For every
corpus PCM × a matrix of `EncoderOptions`: encode with lean-flac; require
(a) `flac -t` passes, (b) `flac -d` output is byte-identical PCM, (c) ffmpeg
decode matches, (d) STREAMINFO MD5 verifies. This is the interop statement the
kernel doesn't give us; it must be green from M4 onward.

**Rig 2 — Decoder conformance (their encoder → our decoder).** Encode corpus
PCM with `flac` across `-0`..`-8`, `-e`, `-p`, `-A` variants, `--lax`, forced
stereo modes, and odd block sizes; require lean-flac decodes byte-identically.
This exercises regions of the format our encoder never emits (e.g. exotic
partition orders, precision choices) — exactly the gap a round-trip theorem
leaves open.

**Rig 3 — Decoder totality fuzz.** lean-zip-style harness
(`FuzzDecode.lean`, cf. `ZipFuzzInflate.lean`): PRNG byte mutation of valid
files + pure-random buffers; the decoder must return `.error` gracefully, never
panic, never exceed the declared output bound, within a wall-clock/fuel budget.
Run a fixed-seed smoke set in CI; long runs nightly.

**Rig 4 — Structure-aware fuzz.** Generate random *valid* frame structures
directly at the subframe/residual layer (random orders, partition orders,
Rice params incl. escapes, wasted bits), byte-serialize, decode with both
lean-flac and libFLAC; outputs must agree whenever both accept. Disagreement =
spec-reading bug; file an issue with the minimized frame.

**Rig 5 — Property round-trip fuzz.** Random `(pcm, opts)` through
`decode ∘ encode` at runtime. Post-capstone this can never fail — keep it
anyway as a canary for `native_decide`-style discrepancies between compiled
and kernel semantics, and run it *before* the capstone lands as the guide for
which lemma to prove next (a counterexample is a proof-priority signal).

**CI gates (merge-blocking):** `lake build` with zero `sorry`/`axiom` in
`Spec/`; capstone theorem present and referenced from CI (grep-pinned name);
Rigs 1–2 full pass; Rig 3–5 smoke pass; bench regression check (Section 7)
advisory-only.

---

## 7. Benchmarking

`bench/` with hyperfine drivers, lean-zip style. Metrics: encode MB/s and
compression ratio vs libFLAC `-0`..`-8` and ffmpeg, decode MB/s, on the corpus
plus a few CC-licensed full-length tracks (do not commit audio; fetch script
with checksums). Publish the ratio/throughput frontier the way lean-zip's
dashboard does. Performance work begins **only after M5** — the entire point
of the methodology is that the capstone makes aggressive optimization safe to
delegate.

---

## 8. Milestones and agent workflow

Each milestone is a mergeable state with green CI. Suggested single-agent-day
granularity; parallelize where files are disjoint.

- **M0** — Skeleton, BitReader/BitWriter + L0 proofs, CRC-8/16 + test vectors,
  Utf8Num + round-trip proof, MD5 + RFC 1321 vectors. (Heavy pattern reuse
  from lean-zip; start here even if it feels like typing.)
- **M1** — Rice/zigzag/escape + L1–L2 proofs, incl. partition certificates.
- **M2** — CONSTANT/VERBATIM/FIXED subframes end-to-end for 16-bit mono;
  L3-fixed + subframe round-trip; first `decodeReference ∘ encode` theorem on
  the restricted profile. *First demo moment.*
- **M3** — LPC over ℤ + L3-LPC proof; Heuristics.lean initial (Levinson-Durbin,
  one window); Rig 1 turns on for the mono profile.
- **M4** — Stereo modes, wasted bits, full width bookkeeping, frame/stream
  assembly, STREAMINFO/MD5; **reference capstone** over the full v1 option
  space; Rigs 1–2 full matrix.
- **M5** — Production decoder (Int64, buffered) + overflow lemmas +
  `decode_ok_iff_reference`; **shipped capstone**; Rigs 3–5 on.
- **M6** — Performance under the ratchet: better windows, exhaustive order
  search, partition-order search, precision search, block-size heuristics —
  all free territory. Bench dashboard.
- **M7 (stretch)** — Section 9.

Workflow rules (copy of lean-zip's, keep them): agents work in their own git
worktrees; one issue = one PR; PRs cannot merge unless CI (incl. the capstone)
is green; every session appends to `PROGRESS.md` (what was attempted, what's
blocked, exact lemma names); no `sorry` reaches `master`, ever — a stuck proof
becomes an issue with a minimized statement, not a hole.

---

## 9. Stretch: two-sided verification against RFC 9639

Define a declarative relation `Flac.Spec.Encodes : ByteArray → Audio → Prop`
(bitstream grammar as an inductive predicate, no algorithm), then prove:
`decode s = .ok a ↔ Encodes s a` (decoder soundness **and completeness**) and
`Encodes (encode pcm opts) pcm` (encoder soundness). The capstone becomes a
corollary, and libFLAC-interop stops being purely empirical. Completeness is a
different sport — every valid stream must decode, including ones our encoder
never emits — which is exactly why it's a stretch goal and why Rig 2/Rig 4
disagreements should be triaged as *future completeness counterexamples* and
archived, not just fixed.

---

## 10. Trusted base and non-goals

Trusted: Lean kernel + compiler; our reading of RFC 9639 (mitigated by Rigs
1–4); MD5 (tested against vectors, not verified — it's a conformance checksum,
not part of the losslessness claim); the conformance oracles themselves
(libFLAC/ffmpeg bugs would show up as unexplainable rig disagreements —
investigate, don't auto-trust either side).

Non-goals for v1: Ogg-FLAC, streaming push API, seeking, metadata editing,
resync-after-corruption, sample-rate-0 files, encoder bit-for-bit
compatibility with libFLAC output (only *validity* and losslessness are
claimed).

---

## 11. Definition of done (v1)

1. `Flac.decode_encode` type-checks on master, `sorry`-free, over the full
   Section 2 option space, and CI greps for it by name.
2. `decode_ok_iff_reference` links the shipped decoder to the verified one.
3. Rigs 1–2: 100% pass on the full matrix incl. the IETF test files
   (must-decode set); Rig 3: no panics over the standing nightly budget.
4. Decoder totality holds by construction (no `partial`, no panicking access
   in decode paths) — enforced by a lint script in CI.
5. Bench page exists with honest numbers vs libFLAC, even if we lose —
   losing fast is fine at v1; M6 is where the lean-zip performance story gets
   its sequel.
