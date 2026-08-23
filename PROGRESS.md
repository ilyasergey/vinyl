# PROGRESS

Per-session log, newest entry last. Each entry: what was attempted, what
landed, what is blocked (exact lemma names), next step.

---

## 2026-08-23 — Session 1: bootstrap + M0

**Attempted:** repository bootstrap and milestone M0 (skeleton, bit I/O +
L0 proofs, CRC-8/16 + vectors, Utf8Num + round-trip proof, MD5 + RFC 1321
vectors).

**Landed:** (updated as the session progresses)

- Toolchain pinned to Lean 4.33.0; lake package `vinyl` with lib `Flac`,
  test lib `FlacTest`, test exe `flactest`. `.gitignore`, `CLAUDE.md`.
- **M0 complete.** `Flac/Native/Bits.lean` (MSB-first bit model, unary,
  alignment, byte packing, signed two's-complement ints) with all L0
  round-trip theorems in `Flac/Spec/Bits.lean` (`readBits_writeBits`,
  `readUnary_writeUnary`, `readSInt_writeSInt`, `bytesToBits_bitsToBytes`,
  `alignToByte_dvd`). CRC-8/CRC-16 with golden vectors. Extended-UTF-8 coded
  numbers with `Utf8Num.read_write` round-trip for `n < 2^36` (incl. the RFC
  §9.1.5 worked example as a test). Pure-Lean MD5, RFC 1321 suite green.
- **M1 complete.** `Flac/Native/Rice.lean`: zigzag, Rice/RICE2, escaped
  partitions, partitioned coded residual (RFC 9639 §9.2.7) with per-partition
  choices as explicit heuristic inputs. `Flac/Spec/Rice.lean`:
  `unzigzag_zigzag`, `readRice_writeRice`, `readSIntSeq_writeSIntSeq`,
  `readPart_writePart`, `readParts_writeParts`, and the L2 keystone
  `readResidual_writeResidual` — the partition-order constraints
  (`2^po ∣ bs`, `ord < bs/2^po`) are carried as a `ResidualCfg.Valid`
  certificate exactly as PLAN.md §5.4 prescribes. 55 unit checks green.

**Proof-engineering notes (for future sessions):**

- `omega` handles `Int.toNat`, casts, `min`, and literal powers, but NOT
  symbolic `2^k` products: introduce `∃ k, 2^po = k+1`, rewrite with
  `Nat.mul_succ`/`Nat.mul_comm` until nonlinear atoms coincide syntactically,
  then `omega` (see `partSizes_sum`).
- After `rw [readBits_writeBits ...]` a surrounding `match` does NOT
  iota-reduce; use `simp only [lemma]` instead of `rw` so simp reduces the
  match on the resulting literal scrutinee.
- Literal-condition `if`s (e.g. the 0xFE case in `Utf8Num.read`) may be
  pre-reduced to `if True` by elaboration — `rw [if_pos rfl]` then fails;
  use `if_pos trivial` / plain `simp`.
- No mathlib: `ring_nf` unavailable — write tiny `digit_step`-style rewrite
  lemmas instead.

**Design decisions:**

- Bit-level reference model is `List Bool` (MSB-first), in
  `Flac/Reference/Bits.lean`. Writers are pure functions returning bit lists;
  readers are structural-recursive consumers returning `Option (α × List Bool)`.
  All L0 round-trip proofs are over this model. Production (ByteArray-buffered)
  bit I/O and its transfer proofs arrive with M5 per PLAN.md; until then the
  encoder assembles the model directly and packs to bytes at the end.
  Rationale: keeps every proof by clean structural induction; performance is
  post-capstone territory (PLAN.md §7, §8/M6).

- **M2 complete.** Fixed predictors as iterated finite differences
  (`Flac/Native/Fixed.lean`) with the L3-fixed keystone
  `Fixed.restore_residual`. Subframes (CONSTANT/VERBATIM/FIXED, RFC 9639
  §9.2) with `Subframe.read_write`. Frames (mono, fixed-blocksize
  numbering) with CRC-8/CRC-16 recomputed by the decoder over consumed
  bits via the `Bits.withConsumed` combinator — CRC checks discharge
  definitionally in `Frame.read_write`. Stream layer (STREAMINFO,
  metadata skipping, fuel-bounded frame loop) with the M2 keystone
  **`Stream.decodeReference_encode`**: kernel-checked decode∘encode = id
  for mono, bps 1–32, block size 16–65535, quantified over every valid
  subframe heuristic.
- **M3 started.** `Heuristics.defaultChooser` (constant detection,
  fixed-order 0–4 search by exact Rice bit cost, mean-based Rice
  parameter, verbatim fallback). `fixedCfg` clamps order/parameter so
  `defaultChooser_valid` never reasons about the search. Corollary
  **`Stream.decodeReference_encode_default`** — the keystone with no
  chooser hypothesis.
- **Conformance (early Rigs 1–2 smoke, `conformance/smoke.sh`):** all
  emitted streams pass `flac -t` (CRCs + STREAMINFO MD5 verified by
  libFLAC 1.5.0) and `flac -d` output is byte-identical; a libFLAC
  `-l 0` stream decodes byte-identically with `decodeReference`.
  Wasted-bits streams are correctly rejected until M4 (that was the one
  gap found by differential testing — libFLAC emits the wasted-bits flag
  whenever a block's samples share low zero bits).
- **Bench (`bench/run.sh`, cactus plot in README):** overall ratio 47.1%
  of raw vs flac -0's 43.7% / -8's 37.7%; beats -0 on tonal/trivial
  content, loses where LPC matters. Speed 0.42 MB/s vs ~14 (List-based
  bit model; M6 territory).
- 63 unit checks green. Project renamed **Vinyl** mid-session (package +
  docs; the on-disk folder is still `soundproof`).

**Blocked:** nothing.

**Next (M3 continuation):** LPC over ℤ (`Native/Lpc.lean` +
`restoreLpc_residualLpc` — note PLAN.md §5.2's arithmetic-shift bridging
lemmas); Levinson–Durbin + windowing in Heuristics; then M4 (stereo,
wasted bits, multichannel frames, variable blocksize numbering).

---

## 2026-08-23 — Session 2: M3 (LPC) + M4 complete (reference capstone)

**Landed:**

- **M3 complete.** `Flac/Native/Lpc.lean` in history-passing style makes
  `Lpc.restore_residual` a hypothesis-free one-line induction (the decoder's
  history provably equals the encoder's, so predictions coincide for *any*
  coefficients/shift). LPC subframes end-to-end (4-bit precision−1 with
  0b1111 rejected, 5-bit signed non-negative shift, big-endian signed
  coefficients). Heuristics: Welch window, autocorrelation,
  Levinson–Durbin (orders 1–8), libFLAC-style error-feedback quantization
  at 12 bits, exact-Rice-cost comparison vs fixed and verbatim. `lpcCfg`
  clamps everything so `defaultChooser_valid` never inspects the Float
  search.
- **M4 complete — the reference capstone.**
  `Flac.Stream.decodeReference_encode`: decode∘encode = id for every
  well-formed `Audio` (1–8 equal-length channels, bps 1–32), block sizes
  16–65535, fixed- and variable-blocksize numbering, and every valid
  channel-assignment heuristic. Pieces: wasted bits (`SubCfg` wrapper,
  content coded at `b − w`, certified `wastedDetect`); stereo
  decorrelation (`Flac/Native/Stereo.lean`, L4 round-trips; mid/side via
  the parity lemma `two_mul_sar_one`); multichannel frames
  (`ChannelAsg`, `subframePlan`, decoder dispatch on the channel code,
  side subframes at `b+1` bits); joint channel chunking + recombination
  at the stream layer; `defaultAsgChooser` (sum-of-magnitudes stereo
  decision) certified, giving the hypothesis-light corollary
  `decodeReference_encode_default`.
- **Conformance:** smoke rig extended to stereo — all our streams
  (incl. mid/side and wasted-bits) verify and decode byte-identically
  under libFLAC 1.5.0; libFLAC `-l 0` mono and stereo streams decode
  byte-identically under `decodeReference`. The wasted-bits gap found by
  differential testing in session 1 is closed.
- **Bench:** corpus expanded to ~39 files with category prefixes
  (tonal/wave/noise/mixed/degen/stereo); per-category aggregate-ratio
  bars + summary table; throughput profile panel.
- Housekeeping: project renamed to Vinyl on GitHub
  (`ilyasergey/vinyl`); Lean sources no longer reference PLAN.md or
  milestone names (docs only); README now quotes the actual proven
  capstone with source links; 71 unit checks.

**Proof-engineering notes (new):**

- `omega` does not see through `Int.ofNat` (use `↑`-casts) and only
  matches `%`/`/` notation, not `.emod`/`.ediv` applications.
- `fun_induction` on well-founded defs both unfolds the goal per-case and
  auto-folds recursive occurrences — do not `rw [f]`/`rw [← f.eq_def]`
  around it. Lambdas over the decreasing argument get `attach`-wrapped in
  termination goals; hide them behind tiny named defs (`dropAll`,
  `tailAll`) to keep `decreasing_by` sane.
- `simp only [lemma-with-_-args]` fails where `rw` succeeds: explicit
  arguments (e.g. fuel) must be given for use as a simp rule.
- `split` on a match-in-goal may generalize the scrutinee with an `heq`
  rather than case on an inner match; prefer `rcases h : innerFn` and
  `simp only [h]`.
- Anonymous-constructor `exact ⟨…⟩` works under definitional match
  reduction only after the scrutinee is a literal constructor.

**Blocked:** nothing.

**Next (M5):** production decoder (Int64 arithmetic, ByteArray-buffered
bit reader) + overflow lemma family (PLAN.md §5.1) +
`decode_ok_iff_reference` accept-set transfer ⇒ shipped capstone
`Flac.decode_encode`; then Rigs 3–5 (fuzzing) and the M6 performance
work (adaptive Rice partitions, block-size search, faster bit I/O).

---

## 2026-08-23 — Session 3: M5 complete (shipped capstone) + byte-level guarantee

**Attempted:** M5 — buffered production decoder with the equivalence
proof, accept-set transfer, shipped capstone; then, on review feedback,
strengthening the theorem statement (no heuristic hypothesis, identity
form, runtime-checkable premise, byte-level PCM round-trip); IETF
conformance corpus; documentation + benchmarks refresh.

**Landed:**

- **M5 complete.** `Flac/Native/Reader.lean` (`BitReader`: MSB-first bit
  cursor over `ByteArray`, indexing the array directly — `.data` copies!)
  and `Flac/Native/Decode.lean` (production decoder mirroring the
  reference function-for-function; CRCs recomputed over `sliceBytes` =
  `ByteArray.extract`). `Flac/Spec/Reader.lean` proves every reader
  primitive simulates the `List Bool` model
  (`readBits_sim`/`readUnary_sim`/`readSInt_sim` + `_spec` position
  lemmas); `Flac/Spec/Decode.lean` lifts this through every layer
  (subframes, frames incl. CRC slices via `sliceBytes_eq`, metadata,
  frame sequence) to `decodeOption_eq_reference` — the production decoder
  computes *exactly* the reference function on every input — and
  `decode_ok_iff_reference`.
- **Theorem strengthening** (user review): (1) heuristic hypothesis
  eliminated — all `Valid` certificates are now `Decidable`, and the
  encoder (`EncoderCfg.safeChooser` / `ChannelAsg.orVerbatim`) checks
  each heuristic choice at runtime, falling back to VERBATIM, so the
  capstone quantifies over *arbitrary* choosers; (2) STREAMINFO bounds
  folded into `Audio.WellFormed` (now `Decidable`); (3) both decoders
  return the full `Audio`, making the capstone the literal identity
  `Flac.decode_encode : decode (encode a) = .ok a`; (4) hypothesis-free
  runtime-checked forms `decode_encodeChecked`/`decode_encodeCheckedCfg`;
  (5) byte-level PCM pipeline `encodePcm16`/`decodePcm16` with
  `decodePcm16_encodePcm16` — raw interleaved 16-bit LE PCM bytes round-trip
  exactly, no hypotheses (verified interleave/deinterleave + PCM16
  (de)serialization). CLI `--encode` runs the checked byte path;
  `--decode-fast` is the shipped decoder (~2× the reference decoder).
- **IETF conformance corpus** (`conformance/ietf.sh`, merge gate):
  must-decode `subset/` 61/61 comparable files pass byte-identically
  (3 skipped only because the `flac` CLI can't emit 12/20-bit raw);
  `uncommon/` 4/5, failing only the headerless
  "file starting at frame header" (out of scope by design).
- Docs: README rewritten around the new capstones with an explicit
  RFC 9639 coverage table (supported / not supported); ARCHITECTURE.md
  updated for the new modules; benchmarks re-run with decode-speed
  measurements added (see README).

**Proof-engineering notes:**

- `Decidable` instances for match-defined `Prop`s: tactic-mode
  `unfold X.Valid; rcases ... <;> exact inferInstance` iota-reduces each
  branch; structure-Props via `decidable_of_iff` with an ∧-chain.
- Literal-struct projections (`(⟨bytes, 0⟩ : BitReader).pos`) are opaque
  to `omega` — normalize with `have : br1.pos = 32 := p1` (defeq) first.
- `ByteArray.toList` is a loop, NOT defeq to `.data.toList` — use
  `.data.toList` in definitions meant for proofs.
- Structure eta closes `some ⟨a.channels, a.bps, a.sampleRate⟩ = some a`
  by `rfl` — returning the whole record costs nothing in proofs.
- Two-at-a-time list recursion: state the theorem as a recursive
  definition with `[]`/`[_]`/`a :: b :: rest` patterns rather than
  fighting `fun_induction`'s wildcard case hypotheses.
- `omega` cannot commute symbolic products: `ch * m` and `m * ch` are
  different atoms — `rw [Nat.mul_comm]`/`Nat.mul_left_comm` first.

**Next:** M6 performance under the ratchet (word-at-a-time `BitReader`
under the same simulation lemmas; encoder off the `List Bool` model),
Rigs 3–5 fuzz harnesses, uncommon-corpus completeness triage.

## 2026-08-23 — Session 4: documentation restructure

Docs-only session; no Lean changes (`lake build` / `flactest` untouched).

- README: quoted `decodePcm16_encodePcm16` statement with a "why it
  matters" paragraph (end-to-end contract for the file-level API — no
  unverified glue between the user's bytes and the guarantee).
- README slimmed into an overview with links; moved out:
  - `COVERAGE.md` — RFC 9639 feature table, not-supported list,
    IETF conformance-corpus results;
  - `bench/README.md` — plots, per-category tables, regeneration steps;
  - `conformance/README.md` — rigs, now documenting `fuzz.sh`
    (rigs 3–5) which the README never mentioned.
- README: new "Cross-checking against libFLAC" walkthrough (verified
  end-to-end on flac 1.5.0, both directions byte-identical); code
  blocks kept free of inline `#` comments — interactive zsh without
  `interactive_comments` passes them as arguments (user-hit failure).
- `.gitignore`: root-anchored `/*.flac`, `/*.pcm` for walkthrough
  scratch files.
- CLI: malformed/unknown arguments now print the usage text to stderr
  and exit 2 instead of falling through to samples mode (the old
  catch-all treated `--encode` + wrong arity as a samples directory);
  bare-directory samples invocation removed (`--samples` only,
  `smoke.sh` updated), `--decode-fast` added to the usage text.
  `lake exe flactest` (71 checks) and `smoke.sh` green.

**Next:** unchanged — M6 performance under the ratchet.

## 2026-08-23 — Session 5: M6 performance under the ratchet

**Attempted:** M6 — close the throughput gap to libFLAC on both codec
directions without weakening a single theorem statement.

**Landed (decode, fully verified — every fast path proven equal to its
specification, so `Spec/Decode`'s simulation statements and the capstones
are unchanged):**

- Word-level bit extraction (`extractBitsFast`, byte-at-a-time via
  `accBytes`) and shift/mask single-bit reads (`bitFast`), proven equal to
  the bit-recursive specs (`extractBitsFast_eq`, `bitFast_eq`).
- `p2` power table + `p2_eq`: the Lean runtime evaluates `Nat.pow` AND
  `Nat.shiftLeft` through GMP even for word-sized values (only `>>>`,
  `&&&`, `+`, `*` have scalar fast paths) — every hot `2^k` now goes
  through the table (`readRiceNat`, `readSInt`, `shiftUp`, masks).
- Residual layer on arrays: `readRiceSeqA`/`readSIntSeqA`/`readPartA`/
  `readPartsA`/`readResidualA` accumulate one `Array Int` across all
  partitions (accumulator-normalization + model-simulation lemmas per
  function; PosOK family rebuilt).
- Fused position-based sequence readers (`readRiceSeqGo`/`readSIntSeqGo`):
  unary + remainder read at raw bit positions, no `Option (_ × BitReader)`
  chain per sample; proven equal via positional unrollings `readRice_pos`/
  `readSInt_pos` (`readRiceSeqFast_eq`, `readSIntSeqFast_eq`).
- Array predictor restores: `Fixed.restoreA` (prefix-sum `undiffA` folds),
  `Lpc.restoreA` (decoded prefix indexed from the end, allocation-free
  `dot`/`dotA`); bridges `restoreA_toList` in `Spec/Fixed`/`Spec/Lpc`,
  `dot_eq_zip_foldl` pins the RFC prediction sum.
- Frame layer on arrays end-to-end: subframes, wasted-bits scaling, stereo
  undo (`Stereo.decode*A` + toList bridges), channel reassembly by
  amortized left fold (`recombineA`, proven equal to `Stream.recombine`
  via `zipApp_toList`/`zipApp_assoc`). Lists materialize once per channel
  at the `Audio` boundary.
- Verified fused PCM16 serializer `pcm16Fast` (+ `pcm16Fast_eq`) inside
  `decodePcm16` — the byte-level pipeline now runs at raw decode speed.
- Table-driven CRC-8/16 (same function on both codec sides, so round-trip
  proofs unaffected; shift-register definitions kept as reference with
  exhaustive/sampled agreement tests).

**Landed (encode):**

- `Flac/Native/Encode.lean` — fast encoder on arrays/`ByteArray`:
  `UInt64` bit accumulator, fused zigzag+partition sums (O(1) per
  partition off nested finest-level sums), estimate-first model selection
  (LPC order from Levinson per-order errors via `levinsonErrs`/
  `pickLpcOrder`, orders 1–8; fixed order from difference-level sums —
  only the chosen candidates get residuals), `Task`-parallel frame
  encoding (frames are byte-aligned and independent; concatenated in
  order). Byte-identical to the verified encoder on the whole corpus
  (differential-tested every run).
- **Certified per call, zero proof debt**: `Flac.encodePcm16Fast` decodes
  its own output with the *verified* decoder and compares with the input,
  falling back to the verified encoder on mismatch —
  `Flac.decodePcm16_encodePcm16Fast` holds with no hypotheses. The
  heuristics changes (sum-estimated partition costs, estimate-first
  orders, extern-only Float conversions — `Float.ofNat/ofInt/literals`
  compile to `Float.ofScientific`, which re-parses a big-integer constant
  per call!) apply to the verified encoder too (19 s → 13 s / 10 MB).

**Numbers (10 MB mono tonal probe; corpus medians in bench/README.md):**
decode 2.1 → 25 MB/s; certified encode 0.16 → 12 MB/s (raw fast encode
~0.4 s wall, certification ≈ one decode + compare); stereo decode
22 MB/s. Compression unchanged within 0.1% (still ahead of `flac -8`
overall on the corpus).

**Conformance:** IETF must-decode 61/61 comparable ALL GREEN (rig now
decodes with the production decoder — justified by
`decodeOption_eq_reference`); uncommon 4/5 (same known out-of-scope
headerless case); smoke + fuzz rigs 3–5 green; `scripts/check.sh` ALL
GREEN (no sorry/axiom, capstones pinned, totality lint, 73 checks).

**Proof-engineering notes:**

- Runtime perf: `Nat.pow`/`Nat.shiftLeft` are GMP calls even for scalar
  values; `>>>`/`&&&`/`+`/`*`/`|||`/`^^^` have scalar fast paths. `Float`
  literals and `Float.ofNat/ofInt` call the Lean-implemented
  `Float.ofScientific` whose compiled body re-parses a big-int constant
  per call — use `Float.ofBits`/`UInt64.toFloat`/`Int64.toFloat`.
  `Array Float` boxes every element; per-lag accumulator loops beat
  fused `set!` loops.
- `rw [if_pos h]` fails when `dsimp` normalized the Prop but not the
  `Decidable` instance inside the `ite`; `simp only [h, if_true/if_false]`
  is instance-agnostic.
- Accumulator functions want two lemmas each: an acc-normalization
  (`f acc = (f #[]).map (acc ++ ·)`) and a `#[]`-sim against the model;
  callers then rewrite with both.
- `subst h` when `h : a = b` eliminates `b` — later references must use
  `_` for the eliminated variable.
- IDE diagnostics after editing an imported file are stale until `lake
  build`; trust the build, not the hover.

**Blocked:** nothing.

**Next (M6b — designed, not started): the verified fast encoder.**
Replace the runtime certificate by a statically verified fast emitter:
(1) `BitWriter` simulation against the `List Bool` writer model, lifted
writer-by-writer (Rice → residual → subframe → frame → stream) to
`emitFast cfg a = Stream.encode cfg a` — the writer-side mirror of M5;
(2) fast validity deciders proven equal to the `Decidable` instances
(today's instances re-materialize residual lists just to check lengths);
(3) heuristics stay unverified choosers (the capstone already quantifies
over them), shared between fast and reference paths. Then
`decode (emitFast cfg a) = .ok a` follows by rewriting — no per-call
decode, no fallback. Also open: frame-parallel *verified* emission needs
`(Frame.write …).length % 8 = 0` + `bitsToBytes`-append lemmas.

## 2026-08-23 — Session 6: corrected benchmark and second M6 pass

**Attempted:** continue M6 toward a ≤1.1× median throughput gap to
libFLAC, complete the M6b writer proof, and profile the corrected remaining
gaps without weakening totality or any capstone.

**Benchmark correction (commit `05b3033`, narrative `3e36c77`):** the old
shell harness launched `python3` once per timestamp. The second timestamp
startup (roughly 19–22 ms) was inside every measured interval, which
disproportionately slowed libFLAC's 7–10 ms commands on the mostly 1 MB
corpus. `bench/run.py` now owns timing in one persistent process, warms every
case, shuffles a fixed-seed schedule, records the median (five repetitions by
default), and keeps `flac -t`/PCM byte comparisons outside timing. The first
corrected one-sample smoke pass measured:

- Vinyl encode 11.995 MB/s versus `flac -5` 106.281 MB/s: 8.86× gap.
- Vinyl decode 30.649 MB/s versus libFLAC decode 121.325 MB/s: 3.96× gap.
- Compression remained 39.6% overall (Vinyl) versus 39.8% (`flac -8`).

These are provisional correction-run numbers, not the final default-five-run
dashboard. The previous published 4.4×/2.4× gaps were measurement-biased
and have been removed from both READMEs. Lean CLI startup itself was only
about 1.6 ms slower than `flac`, so executable startup is not the main gap.

**Landed, green, and committed:**

- `29ef364` — scalar unary `scanOne` plus the allocation-free fused Rice
  sequence reader, with `scanOne_spec` and `readRiceSeqScan_eq`. The
  representative Rice-heavy decode fell from about 43.45 ms to 33.62 ms
  (~1.29×); all existing decoder equivalence/capstone statements remain.
- `75609f3` — streaming MD5: direct proof-indexed block reads, 64 unrolled
  rounds, and at most 128 bytes of tail padding instead of copying the whole
  input. 1 MB and 50 MB probes improved by about 5.2× (11.45→2.16 ms and
  570.28→109.94 ms). MD5 remains tested rather than trusted for losslessness.
- `eaa2fc5` — tail-recursive proof-indexed LPC restore dot product. The
  order-8 microbenchmark improved 1420→1074 ms (24.4%); representative
  end-to-end LPC decodes improved 7–16% depending on content.
- `f55b305` — LPC candidates fold residuals directly into partition sums,
  allocate no block-sized losing residuals, and carry the winning residual
  into emission. All 37 corpus outputs (16,227,607 encoded bytes) remained
  byte-identical. Interleaved corpus median encode throughput improved
  11.883→13.764 MB/s (1.153×); aggregate CPU time fell 12.42→9.32 s.
- `68321f1` — full verified byte emitter. `pushFrame_spec` is lifted through
  `emits_pushStreamInfo`, `pushFrames_spec`, `pushStream_spec`, and `encode_eq`
  to the public capstone `Flac.Emit.emitFast_eq_encode`. No public encoder
  switch was made: the serial/list-safe path was 1.91–4.32× slower than the
  current UInt64/array emitter.
- `93162d9` — allocation-free `crc8Range`/`crc16Range`, with general
  `ByteArray.foldl_start_stop` and `crc*Range_eq_extract` proofs for all
  endpoints. The isolated frame-range probe gained a modest 1–3% and removed
  the temporary slice. Call sites are intentionally left for the next unit.

**Measured and discarded (working tree restored):**

- Selecting separate `k = 0`/positive Rice loops per partition regressed an
  interleaved representative median from 33.62 to 34.05 ms. A proof-carrying
  byte cursor and alternate bitwise unzigzag/masked extraction also regressed.
- Tail-accumulating decoded frames was fully proved (`readFramesGoA_eq`,
  `readFramesA_eq`) but neutral: mixed 41.089→41.034 ms, tonal
  37.723→37.773 ms, stereo 66.827→67.244 ms. It was reverted.
- Grouping eight frames per encoder task was neutral (raw speed ratios
  0.990–1.007×); task setup is not a dominant cost. Replacing the short LPC
  coefficient list with an array loop regressed raw encode by 5–9%.
- Fused autocorrelation/shared Levinson snapshots, a typed recursive CRC
  loop, and several extraction micro-rewrites were neutral or slower and were
  reverted rather than retained as complexity.

**Current profile and honest status:** the ≤1.1× target is not reached.
After correcting the timer, the target is substantially harder than the old
dashboard suggested. Decode is dominated by the fused Rice loop (~31% in the
latest sample), LPC restore (~21%), array pushes/allocations, bit extraction,
and CRC/memory copies. Raw encode workers are dominated by repeated LPC
candidate scoring, then fixed residual scans/differences, allocation, and bit
emission; the production CLI additionally spends roughly one verified decode
on its runtime certificate.

**Exact takeover path:**

1. Wire `crc8Range`/`crc16Range` into decoder, verified emitter, and raw
   encoder call sites, rewriting proofs with `crc8Range_eq_extract` and
   `crc16Range_eq_extract`.
2. Prototype a guarded `USize` Rice cursor (fallback to the proved Nat path
   when buffer/quotient arithmetic could wrap), then prove it equal to
   `readRiceSeqScan` only if an interleaved benchmark shows a clear win.
3. Test the intended libFLAC-style speed/ratio tradeoff of scoring only the
   Levinson-selected LPC order instead of selected + `{1,2,4,6,8}`; record
   corpus compression delta before changing both shared heuristics.
4. To remove encode's runtime decode, build the array validity/sanitization
   bridge (`validResidualA` → subframe → channel assignment), preserve
   prepared residuals and task-parallel emission, and prove array chunking plus
   PCM16/MD5 correspondence. Do not substitute the existing list-safe emitter;
   its measured regression defeats the objective.
5. After each retained unit run `scripts/check.sh`; once code settles, run
   `BENCH_RUNS=5 ./bench/run.sh`, replace the provisional artifacts/narrative,
   and evaluate the ≤1.1× target against the same-run medians.

**Handoff state:** all speculative decoder/encoder changes were reverted;
only green committed units and the explicitly provisional corrected benchmark
artifacts remain. `scripts/check.sh` is ALL GREEN: the 73-job build succeeds,
proof hygiene finds no `sorry`/`axiom`, capstones are pinned, decoder totality
and indexing lints pass, and all 73 executable checks pass.

## 2026-08-23 — Session 7: M6 third pass — parallel decoding closes the decode gap

**Attempted:** continue M6 from Session 6's handoff toward a ~1.5×
throughput gap against libFLAC, keeping every capstone and all proofs
sorry-free, benchmarking and republishing `bench/` after each stage.

**Result:** decode reached **1.58×** of libFLAC (30.6 → 79.2 MB/s median,
2.59× faster this session); encode reached **3.06×** of `flac -8`
(13.9 → 24.5 MB/s, 1.76× faster). Compression is byte-for-byte unchanged
(39.58% overall, still ahead of `flac -8`'s 39.8%). `scripts/check.sh` is
ALL GREEN throughout; no capstone statement changed. The decode target is
met; the encode gap and why it is representational rather than
algorithmic are analysed at the end of this entry.

**Landed, green, committed and pushed:**

- `fc02a46` — wired `crc8Range`/`crc16Range` into the decoder header and
  footer checks, the verified emitter, and the fast encoder, removing a
  slice allocation per frame. Proof deltas `crc8Slice_eq`/`crc16Slice_eq`
  plus a range-form `pushFrame_spec`. Throughput-neutral, so this is now
  purely an allocation cleanup (Session 6 had left the call sites unwired).
- `37a4fd7` — **array-typed decoder core.** `decodeOption` used to
  `.map (·.toList)` over every decoded sample, and `pcmBytes` immediately
  rebuilt the very same arrays. `Flac.Decode.decodeArrays` is now the
  core, `decodeOption` is that plus the conversion the *theorem
  statements* are phrased over, and byte consumers use the arrays
  directly (`pcmBytesA_eq`, `pcm16FastA_eq`, `decodePcm16A_eq`).
  Decode 30.6 → 40.3 MB/s.
- `59595a2` — **frame-parallel decoding, proven equal to the serial
  loop.** The key observation is that `BitReader` reads a shared
  immutable `ByteArray` at an absolute bit position, so decoding the
  frame at position `p` on a worker runs *literally the call the serial
  loop runs there*. A worker returns a `Step` carrying the frame reader's
  own equation (`Step.ok`), so consuming one trusts neither the thread
  nor the sync-code scan that guessed the position: a step is used only
  when its recorded position matches, and positions the scan missed are
  decoded on the spot. Proof chain `readFramesAt_eq` → `stepFor_eq` →
  `readFramesSteps_eq` → `readFramesFast_eq`. Decode 40.3 → 67.4 MB/s.
- `40a161f` — **parallel PCM serialization.** With frames decoding in
  parallel, interleaved-PCM serialization was the serial bottleneck
  (150 ms of a 480 ms 40 MB decode). The layout is sample-major, so
  `pcmBytesA` now runs one task per 64Ki-sample window. It carries no
  theorem (the verified byte path is `decodePcm16`/`pcm16FastA`), and
  output is byte-identical on the 40 MB probe and all 37 corpus files
  against libFLAC. Decode 67.4 → 73.9 MB/s.
- `66dfbfb` — parallel-decode task granularity 24 → 8 candidates
  (measured 8/12/24/48). Decode 73.9 → 78.0 MB/s.
- `db5c65b` — **channel-major deinterleave.** The sample-major loop
  updated the outer array of channels once per sample (`Array.modify`),
  making deinterleaving 17% of encode and all of it serial. Corpus encode
  2.12 → 1.87 s.
- `28d9019` — **unboxed float search.** A generic `Array Float` boxes
  every element, so windowing a block cost one heap allocation per sample
  per subframe; `welchF`/`autocorrF` hold block-sized data in a
  `FloatArray` and perform the same operations in the same order, so the
  searches make identical choices. The boxed `welch`/`autocorr` are gone.
  1.87 → 1.79 s.
- `a9abf15` — **deinterleave inside the frame workers.** Each worker now
  reads its own sample window out of the shared immutable PCM
  `ByteArray`, which removes both the remaining serial deinterleave pass
  and the per-frame `Array.extract` that copied every sample a second
  time (`frameBytes`/`encodeArrays`/`pcm16Channels` deleted as dead).
  1.79 → 1.64 s.
- `34e4a22` — **parallel certificate serialization, with proof.** The
  certificate re-serializes the decoded output to compare against the
  input; that was 10% of encode and serial. `pcm16FastPar` runs one task
  per sample window using the same self-certifying arrangement as the
  frame decoder — a `PcmChunk` carries the equation for the window it
  actually serialized. Proofs `pcm16Row_app`, `pcm16Go_app`,
  `pcm16Go_split`, `pcm16Chunks_eq`, `pcm16FastPar_eq`. 1.64 → 1.57 s;
  40 MB probe 1.97 → 1.63 s.

**Correction to two of this session's commit messages** (`59595a2`,
`34e4a22`) and to the first draft of the notes above: they justified the
self-certifying payloads by claiming `Task.spawn`/`Task.get` are `opaque`,
so that a worker "cannot be assumed" to have computed what was asked.
That is **wrong** for this toolchain. `Task` is a plain structure whose
`get` is a field and `Task.spawn`'s logical model is `⟨fn ()⟩`, so
`(Task.spawn f).get = f ()` holds by `rfl` and `#print axioms` reports no
axioms; reasoning about tasks directly is available and sound, trading
only the `@[extern]`-model trust that Lean programs already accept. The
payload design is therefore a *choice*, and its real justifications are
the two in `ARCHITECTURE.md`: the consumer's equality theorem is
unconditional in the payload, so the heuristic producers (the sync-code
candidate scan, the window tiling) never need characterizing at all —
which is what kept these proofs small — and no proof in the parallel path
mentions `Task`, so none of them leans on the task model matching the
runtime.
- `9921c43`, `2ebc9f9`, `3e7a410`, and one refresh per stage after — the
  benchmark dashboard was regenerated (five runs, plots,
  `bench/README.md` narrative) after every committed stage.

**Measured and discarded (working tree restored):**

- **LPC candidate pruning by Levinson estimate** — the biggest single
  encode item is exactly costing the five or six candidate orders
  (`lpcDotF` 19% + `lpcPartitionSearchF` 17% of raw encode). Keeping only
  the best `k` by `lpcEstCost` measured, on the full corpus:
  `k=6` 39.580%/3.05 s, `k=4` 39.674%/2.92 s, `k=3` 39.870%/2.83 s,
  `k=2` 40.016%/2.33 s. Only `k=2` is meaningfully faster and it forfeits
  the win over `flac -8` (39.8%), so the tradeoff was recorded, not taken.
  This is the one lever that would move encode materially without new
  proof work — it is a product decision, not an engineering one.
- **Fused fixed-predictor search** (libFLAC's difference-ladder: one pass
  carrying all five difference orders into their partition sums, no
  block-sized difference arrays). Byte-identical output but *slower*
  (2.28 s vs 2.12 s): juggling five-element `Array` state per sample costs
  more than the allocations it saves.
- **Unrolled LPC dot products** for orders 1/2/4/6/8 (straight-line
  arithmetic, erased index proofs, no cons walk). Byte-identical and
  exactly neutral (2.12 s) — the cost is the `Int` multiply/add calls, not
  the list walk.
- **Shift-based bit addressing** (`>>>3`/`&&&7` for `/8`/`%8`). A compiled
  microbenchmark showed `Nat` division by 8 and shifting are the same
  speed (239 ms per 100M iterations either way), so the change was never
  made.
- **`pcmBytesA` mono/stereo specialization** (channel arrays hoisted out
  of the sample loop): neutral (30.74 vs 31.20 ms mono, stereo unchanged),
  reverted rather than retained as complexity.

**Profiling notes (macOS `sample`, 40 MB probes):**

- Decode after this session: `readRiceSeqScan` ~23%, `Lpc.dotAGo` ~19%,
  `accBytes` ~11%, `crc16` 8%, serialization 8%, array pushes and
  allocator ~10%. The list round-trip items (`lengthTR`,
  `array_to_list`, `toArrayAux`) are gone.
- Raw encode: `lpcDotF` 19%, `lpcPartitionSearchF` 17%,
  `partitionSearchF` 9.5%, allocator ~20%, `autocorr` 6%, bit writer 7%.
  `wastedDetectF` never appears — the early-exit on an odd sample makes
  libFLAC's OR+ctz trick unnecessary here.
- Parallelism: encode 10.1 s user / 3.0 s real (3.4×); decode was 1.01/1.09
  (serial) before this session and 1.58/0.45 after. The sync-code scan
  finds 6488 candidates for 4883 real frames (1.33×); false candidates are
  rejected by the header CRC-8, so the residual overhead is Lean's
  cross-thread refcounting and allocator traffic, not wasted decoding.

**Encode phase breakdown (40 MB probe, after this session).** Raw encode
1255 ms (parallel frame workers, 77%), certificate decode 281 ms (17%),
certificate re-serialize ~50 ms (3%, was 169 ms), MD5 75 ms (4.6%,
inherently serial — the hash is chained). Before this session the same
probe additionally spent 372 ms in a serial deinterleave.

**Honest assessment of the remaining gap.** Decode is at the target.
Encode is not, and the reason is representational rather than
algorithmic: the hot loops are `Int` multiply–accumulate over `Array Int`
against libFLAC's `int32` SIMD, and `Array Int64` would be *worse* in
Lean (boxed per element), so the current representation is already the
best available in pure Lean. Three levers remain, in order of value:

1. **Remove the runtime certificate** (~20% of encode, now that both its
   decode and its serialization are parallel): the designed M6b path — array-side validity/sanitization bridge
   so the statically verified emitter can ship, instead of decoding every
   encode to certify it. Note the verified emitter already exists and is
   proven (`Flac.Emit.emitFast_eq_encode`); what blocks shipping it is
   that the *heuristics* it calls still run on lists, so array-izing the
   searches with equality proofs is the actual work.
2. **Match libFLAC's search *shape*, not just its budget.** libFLAC's
   preset table (`FLAC/stream_encoder.h`, installed with the CLI — no
   implementation sources are available locally) sets `exhaustive model
   search` to false at *every* level including `-8`: it estimate-picks a
   single LPC order per apodization window, and `-8` earns its ratio with
   several *windows* (`subdivide_tukey(3)`, max order 12) rather than by
   exactly costing several orders. Vinyl does the opposite — one Welch
   window, five or six orders costed exactly. So the pruning experiment
   above (one order, one window, 40.016%) is not the right comparison:
   the untested design point is *one order per window × two or three
   windows*, which would cost roughly half of today's LPC work and might
   compress as well or better. This is now the most promising encode
   lever, ahead of the flat compression/speed tradeoff (~1.3×, 0.44 pp),
   which remains a decision for the project owner rather than a
   recommendation.
3. A windowed bit reader (cached word + count, libFLAC-style) for the
   ~34% of decode in the Rice reader; would need a simulation proof
   against `readRiceSeqScan`, and decode is already at target.

**Blocked:** nothing.

**Next:** M6b item 1 above (certificate removal) is the only remaining
change that improves encode without trading compression or adding trusted
code.
