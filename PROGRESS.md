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

---

## 2026-08-24 — Session 8: M6 fourth pass — exact float search, allocation-free bit writer

**Attempted:** close the remaining decode and encode gaps against libFLAC
1.5.0, target 1.1× on both, without giving up the compression win over
`flac -8` (39.580% vs 39.784% on the 37-file corpus) and with the ratchet
green throughout.

**Landed** (32 MB mono probe, 4096-sample blocks; every stage kept the
corpus ratio at 39.580% and the output byte-identical to the verified
encoder's):

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| session 7 end | 26.7 MB/s | 108.8 MB/s | 3.53× | 1.85× |
| `a08d9d5` float candidate searches | 33.3 MB/s | — | 2.90× | — |
| `c5bd00c` bit writer without tuples | 42.8 MB/s | — | 2.27× | — |
| unboxed PCM serialization | 43.5 MB/s | 117.2 MB/s | 2.24× | 1.76× |
| parallel sync-code scan | 44.6 MB/s | 126.5 MB/s | 2.18× | 1.65× |
| `33bb86b` fused fixed-order search | 47.1 MB/s | 127.5 MB/s | **2.07×** | **1.59×** |

Five-run corpus medians moved 24.5 → 38.8 MB/s encode (gap 3.06× → 1.94×)
and 79.2 → 82.7 MB/s decode (gap 1.58× → 1.53×); the corpus files are 1 MB
each, so process startup damps both the absolute figures and the deltas.

1. **Exact float arithmetic in the candidate searches**
   (`Flac/Native/Encode.lean`). A search only *chooses* a subframe; the
   bytes always come from the exact `Int` path. Every value a search
   computes is an integer well inside 2^53 (16-bit samples < 2^17,
   quantized coefficients < 2^11, order ≤ 8 ⇒ prediction sums < 2^32,
   residuals < 2^19, 4096-sample partition sums < 2^32), so doubles
   represent them exactly and the subframe chosen is bit-identical, at one
   hardware `fmul`/`fadd` per tap instead of `lean_int_mul`/`lean_int_add`
   on a boxed `Array Int`. `Flac/Native/Heuristics.lean` keeps its `Int`
   list search for the verified encoder, and a new differential test
   (`fastMirrorTests` in `FlacTest/Cli.lean`) pins the two to
   byte-identical output on LPC/FIXED/noise/wasted-bit/constant/stereo
   material. No theorem touched — `Flac/Native/Encode.lean` carries no
   proof obligation, and `Flac/Spec/Heuristics.lean` never mentions the
   search internals.
2. **The bit writer stopped allocating per bit push.**
   `BitWriter.flushGo` returned `ByteArray × UInt64 × Nat` — three heap
   allocations per call (two `Prod` cells plus a boxed `UInt64`, `Prod`'s
   fields being polymorphic) — and `push` runs twice per residual sample.
   The profile attributed ~25% of *all* encode work to
   `mi_malloc_small`/`mi_free`/`lean_dec_ref_cold` beneath it, more than
   the LPC search. `flushBytes` now returns the buffer alone: the new
   pending count is `n % 8`, and `acc` needs no masking because `toUInt8`
   truncates and no bit at or above position `n` is read back. The
   residual loop (`pushRiceRange`) threads `buf`/`acc`/`n` as three
   parameters, one `BitWriter` per partition rather than two per sample.
   This was the single largest win of the session.
3. **PCM serialization through the `UInt64` lane**
   (`Stream.pcmBytesRange`, with mono/stereo specializations). `Int →
   Int64 → UInt64` plus unboxed shifts instead of `Int` addition,
   `Int.toNat` and `Nat` masking: 2.5× on a 4M-sample block
   (266 → 666 MB/s). `pcmBytesA_eq` cancels only the array/list
   conversion, so this arithmetic carries no proof obligation. Out-of-range
   samples now wrap in two's complement instead of clamping at zero, which
   is what RFC 9639 §8.2 asks for and what `Flac.pcm16Row` already did.
4. **The sync-code scan runs in parallel windows** (`Decode.syncCandidates`)
   — it was the decoder's largest serial phase, one pass over the whole
   compressed stream on the driver thread before any frame worker could
   start. It is a pure guess validated by `Step.ok` at every use, so it
   carries no proof obligation; ascending windows concatenate ascending
   (all `findStep` needs), and a sync code straddling a boundary is still
   found by the window owning its first byte.
5. **The fixed-order search is one fused pass** (`fixedPartitionSums`).
   The order-`ord` residual is the `ord`-th finite difference, so one
   traversal carrying the ladder yields all five streams: one array read
   per sample instead of five, no block-sized difference array at any
   order.
6. **`riceParam` carries `n · 2^k` and doubles it** instead of a `p2`
   lookup plus a multiply per step (it is called 127 times per candidate).
7. **`lpcMaxOrder`/`lpcCandidates` factored into one place** that both the
   verified chooser and the fast encoder read — which is what keeps them
   byte-identical when either is tuned — with the measured tradeoff curve
   in the docstring.
8. **Two new test groups** (suite 73 → 88 checks). `fastMirrorTests` pins
   the float searches to the verified encoder's `Int`/list searches,
   byte-for-byte — the load-bearing invariant of item 1, and not a theorem
   (the fast encoder is unverified by design). `pcmBytesTests` gives
   `Stream.pcmBytesRange` golden vectors at 8/16/24 bits, across
   mono/stereo/three-channel interleaving, and pins it against the
   verified `Flac.pcm16Fast` on the same samples — it is deliberately
   outside every theorem, so item 3 needed vectors rather than a proof.

Conformance is green throughout: `conformance/smoke.sh` (both directions
against libFLAC 1.5.0) and `conformance/fuzz.sh 150` (totality,
bit-flip, compiled round-trip) after the serialization change.

**Two shapes worth remembering** (both cost real time before they were
found):

- A `Float`-typed `let mut` carried across a `for` loop is **boxed once
  per iteration**. An order-8 residual fold went 84 ms → 255 ms when its
  accumulators moved from tail-recursion parameters into ten mutable
  locals. Every float accumulator in `Flac/Native/Encode.lean` is
  therefore a tail-recursion parameter, and the `for` loops carry only
  heap objects and `Nat` counters.
- `Prod` fields are polymorphic, so a returned tuple boxes any scalar in
  it. Returning `ByteArray × UInt64 × Nat` from a per-sample helper is
  three allocations; unpacking the state into parameters is zero.

**Measured and discarded (working tree restored):**

- **Unrolling the float dot product.** Four accumulator chains with
  explicit `xs[n-1-j]` loads: 155 ms vs 83 ms — the per-tap `Nat` index
  arithmetic costs more than the shortened dependency chain saves. A
  sliding register window (one load per sample, nine mutable locals):
  255 ms, the boxing effect above. Two accumulator chains via
  pattern-matching two taps at a time: neutral to 2% *slower*
  (47.1 → 46.0 MB/s). Disassembly explains why there is nothing left: the
  inner loop is `ldr`/`ldr`/`fmul`/`fadd` plus loop control, with
  `Float.floor` inlined to a single `frintm` and `foldF` branchless
  (`fcmp`/`fcsel`).
- **Pruning the LPC candidate set.** Full curve now recorded in
  `Heuristics.lpcCandidates`. Corpus ratio / probe encode speed:
  `[1,2,4,6,8]` max 8 = 39.580% / 1.00×; `[2,4,8]` 39.634% / 1.06×;
  `[4,8]` 39.876% / 1.11×; `[8]` 40.072% / 1.16×; estimate-only (libFLAC's
  own rule) 40.504% / 1.22×. At max order 12: `[2,4,12]` 39.571% / 1.00×,
  `[2,12]` 39.701% / 1.04×, `[1,2,4,8,12]` 39.450% / 0.94×. Pruning buys
  little speed for real ratio, and the two sets that beat the current one
  on ratio both cost speed — so the set is unchanged.
- **Serial vs parallel PCM serialization.** Now that serialization is
  2.5× faster, the task fan-out's `lean_mark_mt` of the decoded sample
  arrays costs about what the parallelism saves: 128 MB probe, serial
  1.00 s wall / 3.93 CPU-s versus parallel 0.99 s / 4.11 CPU-s. Kept
  parallel (better wall time), but it is no longer load-bearing.
- **`LEAN_NUM_THREADS`** at 8/12/16: no effect on either direction.

**Profiling notes (macOS `sample`, 128 MB probes).** Encode, of 4.09
CPU-seconds for the 32 MB probe: runtime certificate 1.12 s (27%, measured
directly as `--decode-pcm16` on the encoder's own output), LPC candidate
search ~27% (`lpcDotFf` 15%, `acorrGo` 5%, `lpcFoldRange` 3%, `riceParam`
2%), emission ~11%, fixed search ~5%, `lean_mark_mt` 5%. Decode, 1.02
CPU-seconds against 0.25 s wall (≈4× parallel on 4 P + 4 E cores, ~40% of
the critical path serial): Rice reader ~22% (`readRiceSeqScan` 14%,
`accBytes` 6%, `scanOne` 2%), `lean_byte_array_push` +
`lean_array_push` ~26%, `lean_mark_mt` ~14%, LPC/fixed restoration ~11%,
serialization arithmetic ~9%, `crc16` 3%.

**Honest assessment of the remaining gap.** Neither direction is at 1.1×
and neither will get there by tuning; what is left is two structural items
and a hard floor.

1. **Retire the runtime certificate — encode 2.07× → ≈1.6×, trading
   nothing.** Measured, not estimated: the certificate is 1.12 of encode's
   4.09 CPU-seconds. This is milestone M6b as designed. The verified
   emitter already exists and is proven (`Flac.Emit.emitFast_eq_encode`);
   what blocks shipping it is that the heuristics it calls still run on
   lists, so array-izing the searches *with equality proofs* is the actual
   work — the array-side validity/sanitization bridge.
2. **A windowed bit reader — decode ~22% of work.** libFLAC-style cached
   word plus a leading-zero count, replacing the per-bit `bitFast` walk in
   `scanOne` and the per-sample `Nat` `accBytes` chain in
   `extractBitsFast`. Needs a simulation proof against `readRiceSeqScan`
   with an invariant relating `(word, avail, bytePos)` to `pos` — the
   largest single proof obligation left on the perf path, and the reason
   it was not attempted this session alongside the rest.
3. **Below that is a floor, not a backlog.** Two `ByteArray`/`Array`
   pushes per sample (~26% of decode) is what the API costs; `lean_mark_mt`
   (~14% of decode) is what sharing `Array Int` across threads costs and
   would only go away if the decoder produced bytes rather than samples,
   which the CLI/capstone pinning deliberately prevents; and the proven
   LPC/fixed restoration must stay `Int` multiply–accumulate against
   libFLAC's `int32` SIMD. `Array Int64` is *worse* than `Array Int` in
   Lean (boxed per element), and `FloatArray` — now used everywhere it is
   exact — is the only other unboxed numeric array Lean has. Per-operation
   cost in the proven decode path is therefore at its pure-Lean minimum.

**Blocked:** nothing.

**Next:** M6b item 1 above — array-izing the heuristics with equality
proofs so the statically verified emitter can ship and the runtime
certificate can be retired. That is the only remaining change that
improves encode without trading compression, adding trusted code, or
taking on a bit-level simulation proof.

---

## 2026-08-24 — Session 9: M6 fifth pass — decode past libFLAC, encode to 1.3×

**Attempted:** the user's escalating targets, in order — get within 1.1× of
libFLAC on both directions, then make *decode faster than libFLAC*, then
push encode toward 1.1× — without giving up the compression win over
`flac -8` and with the ratchet green throughout.

**Landed** (32 MB mono probe; corpus five-run medians in brackets):

| stage | encode | decode | encode gap (`-8`) | decode gap |
|---|---|---|---|---|
| session 8 end | 47.1 MB/s | 127.5 MB/s | 2.07× | 1.59× |
| `bcdcaaf` frame-parallel serialization | 46.6 | 220.7 | 2.07× | **0.96×** |
| `74739a0` certificate via the byte path | 57.7 | 222.2 | 1.67× | 0.94× |
| `3732892` three-byte Rice window | 58.5 | 246.2 | 1.63× | **0.83×** |
| `9104522` MD5 off the critical path | 64.9 | 244.3 | 1.48× | 0.85× |
| `8a4888d` three LPC orders, not five | 71.7 | 246.2 | 1.34× | 0.84× |
| `86ff281` float residual for emission | 73.7 | 244.3 | 1.32× | 0.85× |
| three autocorrelation lags per pass | 75.5 | 244.3 | **1.27×** | **0.85×** |

Corpus medians moved 38.8 → 58.4 MB/s encode (gap 1.94× → **1.27×**) and
82.7 → 123.7 MB/s decode (1.53× → **1.01×**); repeating the whole run
moves these by 2–3%. Ratio 39.580% → 39.634%,
still ahead of `flac -8`'s 39.784%. Against file size, encode settles
around **1.24×** and decode at **0.88×** from 8 MB up.

**Decode is now faster than libFLAC above ~4 MB** — 0.96× at 4 MB, 0.89×
(11% faster) from 8 MB up. Below that the residual is *process init*, not
decoding: 3.1 ms of Lean runtime setup against libFLAC's 2.7 ms on an
8–9 ms measurement, of which only 0.09 ms is this project's own module
initialization (a trivial Lean binary also takes 3.10 ms, and the binary
is already statically linked, so there is no dynamic-loading cost to
remove). The size-scaling table is in `bench/README.md`.

1. **Frame-parallel serialization, with proof** (`Flac/Spec/PcmBytes.lean`,
   613 lines). Turning decoded samples into interleaved PCM bytes was 46%
   of decode wall time and none of it was decoding: `recombineA`
   concatenated every frame's channels into whole-file arrays (41 ms,
   serial) and `pcmBytesA` walked those again (61 ms — its task fan-out
   bought nothing, because `lean_mark_mt` on the shared `Array Int`
   channels cost about what the parallelism saved). A frame covers a
   contiguous sample range, so **a frame is a serialization window**:
   `pcmBytesRange_eq` pins all three serialization loops to a list model,
   `pcmModel_split` splits it along the sample index, `pcmModel_left`/
   `pcmModel_right` split it at a frame boundary, `recombineA_model` is the
   keystone, and `decodeBytes_spec` the capstone — a `some` result is
   exactly `pcmBytesRange` of what `decodeArrays` returns. `ByteStep`
   carries the frame reader's equation with the channel arrays
   *existentially quantified*, so they are erased and never cross the
   thread boundary; a `ByteArray` is O(1) to mark. Nothing mentions
   `Task`. This **narrowed** the trusted surface: `--decode-fast`
   previously wrote `Stream.pcmBytesA`, whose window concatenation was
   asserted in prose and unprovable.
2. **The certificate runs the same byte path** (~27% of encode). Needed a
   bridge, since the certificate must imply `decodePcm16 out = .ok bytes`
   and `decodePcm16` serializes with `Flac.pcm16Row`:
   `pcm16FastA_eq_range` proves the two serializers agree for *every*
   `Int`, because `Int.toInt64` is reduction mod `2^64` and `2^16` divides
   `2^64` (`lane_lo`, `lane_hi`, off `Int64.toBitVec_ofInt` and
   `Int.emod_emod_of_dvd`). `pcm16Certified_ok` unchanged in statement.
3. **Three-byte Rice window** (`extractBits3`, `extractBits3_eq`).
   `extractBitsFast` computed its byte count with two `Nat` divisions, ran
   `accBytes` as a loop, and rebuilt `2^n - 1` per call; for `n ≤ 17`
   (every RICE parameter) three straight-line byte loads against a hoisted
   mask compute the same value. 1.35× on a 2M-sample Rice run.
4. **MD5 off the critical path.** Chained, so unsplittable, but it does not
   have to be *first*: 62 ms of a 550 ms encode, computed before the first
   frame task. Spawned alongside them it overlaps work that already
   saturated the cores.
5. **Three LPC orders instead of five.** The estimate winner is listed
   first and takes ties, so dropping an order costs far less than it looks
   — dropping order 1 is *free* (identical ratio, 4.5% faster), and
   `[2,4,8]` gives 10% for 0.054 points, keeping a 0.15-point margin over
   `flac -8`. Whole curve in the `lpcCandidates` docstring, including the
   two points deliberately not taken.
6. **Emission off the float array.** The search already computes every
   residual exactly in `Float`; emission recomputed the winner's in `Int`.
   `lpcResidualArrF`/`diffArrFf` replace that, and `pushRiceRange` folds
   the zigzag magnitude straight off the float. One whole duplicate
   arithmetic path left the file.
7. **Three autocorrelation lags per pass** (`acorr3`, shared by both
   encoders). Nine lags meant nine passes each re-reading both operands;
   the fused pass reads `w[i]` and `w[i-lag]` and carries the two older
   history values in registers, so a (lag, sample) pair costs two thirds
   of a load instead of two. Each lag still accumulates ascending in `i`
   from `+0.0`, so the sums are bit-identical — confirmed by the corpus
   ratio not moving. A/B: 71.0 → 75.5 MB/s, 6% of encode.

**Measured and discarded (working tree restored):**

- **A libFLAC-style windowed bit reader** — cached 64-bit word plus
  leading-zero count — **5.7× slower** (207 ms vs 36 ms on a 2M-sample
  Rice run). Lean boxes `UInt64` values carried across control flow, so
  refills and `clz` cost far more than the scalar `Nat` path they replace.
  **This was the top item on session 8's "next" list; it should not be
  attempted again.** The three-byte window is what survives of it.
- **`>>>3`/`&&&7` for `/8`/`%8`** in the Rice loop: identical (27 ms
  either way), confirming the session-5 microbenchmark.
- **A constructor-level `unzigzag`** (`Int.negSucc` + `&&&1` instead of
  `%`/`/` and `Int.neg`): identical.
- **Coefficients in a `FloatArray`** walked by an increasing counter
  against a decreasing sample index, instead of a `List Float` walked
  structurally: a wash at order 4, *worse* at order 8 (93 ms vs 86 ms).
  With the earlier unrolling, two-accumulator and sliding-window attempts
  that makes **five** failed approaches to `lpcDotFf`; ~5 cycles per tap
  is the floor and the next session should not spend time there.
- **Decode task granularity** re-swept for the byte-emitting workers
  (1/2/4/8/16): 2 is best at both 1 MB and 32 MB, spread under 3%.
- **Sync-scan window** below 1 MB (64K/16K/4K): no effect; the serial scan
  was not the small-file fixed cost.
- **Serial vs parallel PCM serialization** (before the fusion): a wash —
  128 MB probe, serial 1.00 s / 3.93 CPU-s versus parallel 0.99 s / 4.11
  CPU-s. Superseded by moving it into the frame workers.
- **`LEAN_NUM_THREADS`** 8/12/16: no effect.

**Profiling notes (macOS `sample`, 512 MB decode / 128 MB encode probes).**
Decode, 43% Rice reader (`readRiceSeqScan3` 38%, `scanOne` 5%), 29%
predictor restoration (`Lpc.dotAGo` 23%), `crc16` 6%, serialization 9%,
array pushes 3% — `lean_mark_mt` has disappeared entirely. Encode, of 3.23
CPU-seconds: certificate ~35% of work (0.119 s of 0.434 s wall), candidate
search ~31% (`lpcDotFf` 18%, `acorrGo` 8%), emission ~18%, fixed search
~7%.

**Honest assessment.** Decode is done: faster than libFLAC wherever
process startup is not a third of the measurement, and the per-operation
cost of what remains is at the pure-Lean floor (`Lpc.dotAGo` must stay
`Int` — it is the proven path, and converting `Int → Int64` per tap would
cost what it saves).

Encode is at 1.27× (1.30× on the corpus medians, ~1.24× at large sizes)
and the path to 1.1× is **one project, not a list**:
retire the runtime certificate in favour of the statically verified
emitter. Measured, that alone lands at ~0.93×. What is *not* in the way is
the searches — a chooser's output carries a decidable validity certificate
by construction and `safeChooser` checks it, so the round-trip theorem
already holds for every chooser, `Float` included, and nothing about the
search needs proving. What *is* in the way is the emitter's plumbing:
`W.pushFrames` folds serially over `Stream.chunkChannels`, and
`Stream.Audio` carries `List (List Int)` channels, so driving it means
materializing the file as cons cells — which is exactly `--encode-slow`,
measured **113× slower** than the fast encoder for byte-identical output
(7.89 s vs 0.07 s on 4 MB).

**Blocked:** nothing.

**Next:** M6b, in four stages, in this order:
1. De-tuple `Flac.Emit.W`'s bit writer (`flushGo` returns
   `ByteArray × Nat × Nat` — two `Prod` cells per bit push — and multiplies
   by `p2 k` where the fast writer shifts a `UInt64`); its `Emits` lemmas
   need the same treatment `flushBytes` got this session.
2. A byte→array input pipeline proven equal to
   `deinterleave ∘ pcm16OfByteList`.
3. Array-side chunking proven equal to `Stream.chunkChannels`.
4. Parallel frame emission proven equal to the serial `pushFrames`. This
   one is already well-supported: `pushFrame_spec` says emission only
   *appends* (`(pushFrame … w).bits = w.bits ++ Frame.write …`), which is
   the same locality argument that licensed per-frame serialization on the
   decode side this session.

---

## 2026-08-24 — Session 10: M6b — proving the fast encoder, route changed

**Attempted:** the user chose to retire the runtime certificate by proving
`Flac/Native/Encode.lean` *directly*, explicitly accepting that a proof stack
pinned to the fast encoder will be invalidated by future performance passes.
That replaces the recorded M6b plan (array-ize the already-proven
`Flac.Emit` emitter). Tagged `certified-encoder-stable` at `a163b25` first.

**Why the direct route is defensible.** It shares stages with the recorded
plan (input pipeline, parallel frames) and differs only in proving the *fast*
writer rather than speeding up the *proven* one — which carries strictly less
performance risk, since the code being proven is already measured at 1.27×.
And `Float` does not block it: Float operations are opaque but
*deterministic*, so a search and the chooser it instantiates need only be the
same function on equal inputs. `f x = f x` needs no Float lemma.

**The finding that changed the cost.** The file's own header claimed "the
bytes are always emitted from the exact `Int` path below". They were not:
`pushResidual`/`pushRiceRange` took a `FloatArray` and folded its values
into the stream, so *every residual bit was Float-derived*.
`lpcResidualArrF`'s doc asserted the unprovable part outright — "every value
is an exact integer, so the bytes emitted from it are the bytes an `Int`
residual would emit". That is precisely the claim the runtime certificate was
covering, and it can never be proven: Lean's `Float` operations are compiler
intrinsics with no axiomatization, so there is nothing to reason from. Any
emission theorem therefore *required* moving emission to `Int` first.

**Landed** (47 MB stereo SQAM probe, `bench/real_data/pcm/sqam/33.pcm`,
9-run interleaved medians; byte-identical output on all 37 corpus files at
every step):

| commit | change | vs tag |
|---|---|---|
| `9655cbd` | search/emission split (`chooseSub`/`chooseFrame` vs `pushSubframeOf`/`pushFrameOf`) | −0.5% |
| `7f39546` | emit from `Emit.fixedResA`/`lpcResA`, delete the Float emission path | +5.6% |
| `f1cec08` | emission reshaped to mirror `Emit.W` recursion for recursion | +6.9% |
| `d573ed1` | shared `BitWriter.accPush`; hot-loop masks restored | +6.5% |
| `ee44cab` | list-shaped partition loop | +6.6% |

The +6.6% buys provable emission. The certificate it unblocks measures
**31% of encode** on the same probe (0.201 s of 0.647 s), so retiring it
still lands at ≈0.75× today's encode — about **0.95× libFLAC**, against the
0.93× projected before this finding.

`Flac/Spec/Encode.lean` (new, 571 lines, 34 theorems, no sorry/axioms):
`Sim` relates `BitWriter` (UInt64 accumulator, stale bits above the pending
count) to `Emit.W` (Nat accumulator, masked every step); `Simulates` lifts it
to writer transformers and composes. `flush_sim` discharges the fast
writer's deliberate sloppiness — it never masks, because every byte it emits
is bits `[n-8, n)` and nothing at or above `n` is read. `sim_push` is the
central step; `push_key` is factored out so the hot loop reuses it. Then all
primitives, the sequence writers, `sim_pushRiceRange` (the per-sample loop),
partitions, residuals, subframes, and `sim_pushFrameOf` — a whole frame,
including both CRCs, via `sim_push_buf`: a value read off the writer's own
buffer is the same on both sides *because* the buffers are.

Two code changes were made purely to make statements provable, both free:
- `BitWriter.accPush`, one accumulator step shared by `push` and the hot
  residual loop, so the loop's two pushes are *definitionally* pushes rather
  than an inlining to be discharged (re-adding the masks it drops cost
  nothing measurable: +6.5% vs +6.7%);
- emission reshaped to `Emit.W`'s recursion shapes, so every proof is a
  structural induction instead of an argument about `Std.Range.forIn`.

**Blocked:** nothing.

**Next**, in order:
1. **Input bridge** — `frameChannels bytes ch lo hi` equals the matching
   window of `deinterleave ∘ pcm16OfByteList` composed with
   `Stream.chunkChannels`. Shared with the abandoned plan.
2. **Chooser correspondence** — `chooseFrame` produces a `FramePrep` with
   `planOf qs = Emit.W.planA b asg chs`, `SubPrep.Denotes`, and
   `SubPlan.EmitOk`. Note `EmitOk` should be *derivable*, not separately
   checked: `(Rice.partSizes bs po ord).sum = bs - ord` under
   `ResidualCfg.Valid`'s `dvd`/`ord_lt`, and `Valid.len` gives
   `res.length = bs - ord`, while `k ≤ 32` follows from `Partition.Valid`'s
   `k < m.escapeCode = 15`. So the existing certificate `safeChooser`
   already checks implies everything emission needs — but the fast encoder
   must run that check, and today's `Decidable` instances re-materialize
   residual *lists*. A fast array-side decider proven equal to them is the
   real work here.
3. **Stream assembly and the Task collapse** — STREAMINFO prefix, then
   per-frame concatenation. `pushFrame_spec` (emission only appends) is the
   locality argument; `(Task.spawn f).get = f ()` holds by `rfl`, or a
   `ByteStep`-style erased payload avoids even that.
4. **Flip and delete** — only in the final commit: point `--encode` at the
   proven path and drop `pcm16Certified`. `Flac.encodePcm16Fast` keeps its
   signature and `Flac.Stream.decodePcm16_encodePcm16Fast` keeps its exact
   statement; the `Option` survives for the input well-formedness guard, so
   `pin_encode_fast` is untouched. Until then master keeps the certificate,
   so the ratchet never regresses.

**Toolchain note for future sessions:** no mathlib means no `set`,
`conv_lhs`, `norm_num`, `ring`. Core `conv` provides `lhs`/`rhs`/`zeta`.
`simp only [f]` zeta-reduces where `unfold f` leaves `have`s in the way, but
loops on well-founded recursive definitions — `rw [f]` then `simp only []`
unfolds exactly once.

### Session 10, continued — stages 2 and 3

**Landed** (same probe and method; byte-identical on all 37 corpus files at
every step, `degen-wasted3.pcm` included):

| commit | change | vs tag |
|---|---|---|
| `1f8e3ef` | `frameChannels` structural (`channelSeg`/`frameChannelsGo`), mono/stereo specialisations dropped | +0.5% |
| `2450dbc` | the input bridge, proven | — |
| `8d533b7` | `SubPlan.sanitize`: O(1) clamps in place of a validity scan | +0.2% |
| `9208292` | the sanitised plan is valid; `EmitOk` derived | — |
| `f08ad39` | `wastedDetectF` structural (`tzGo`/`wastedGo`) and proven sound | +7.2% total |

**Stage 2 — the input bridge.** `frameChannels_eq`: the window each frame
worker deinterleaves out of the shared PCM bytes is exactly the reference's
frame — `deinterleave ∘ pcm16OfByteList`, dropped to `lo`, taken to `len`,
which is what `Stream.chunkChannels` hands the verified emitter. Chain:
`getD_toList`, `sampleAt_eq`, `getD_pcm16OfByteList` (valid at every index
because an even byte count leaves no trailing byte — exactly what
`encodePcm16`'s guard enforces), `getD_deinterleaveN`,
`length_getD_deinterleaveN`, then `channelSeg_eq` / `frameChannelsGo_eq`.
`Flac.length_deinterleaveN` is no longer private, and neither is
`Encode.sampleAt`.

**Stage 3 — the validity check is free, and the earlier note about needing a
fast decider was wrong.** Everything `Subframe.SubCfg.Valid` asks of the
search's output is *scalar*, so clamping at the plan boundary makes each
bound hold by construction, with no reasoning about `Float`:

- `riceChoices` clamps each Rice parameter to 14, so `Partition.Valid`'s
  `k < 15` is immediate. `parts_valid` then follows from the clamp *alone*,
  because `Partition.Valid` for a Rice choice ignores its samples — which is
  what removes the apparent need to materialise `chunkBySizes` of a residual
  list, the thing that made the `Decidable` instances look expensive.
- `safePo` keeps the searched partition order only when
  `bs % 2^po = 0 ∧ ord < bs / 2^po ∧ po ≤ 6` — exactly what `partitionMaxF`
  already checks — else 0.
- `SubPlan.sanitize` clamps the fixed order to 4, the coefficient list to 32,
  each coefficient to the 12-bit field, and the shift to 15.

Every clamp is a no-op on what the searches return (`Heuristics.riceParam`
stops at 14 by construction; `partitionMaxF` checks divisibility; the
quantizer already clamps to 12 bits), so output is byte-identical, at +0.2%.

`subCfgOf_sanitize_valid` then proves the sanitised plan's reference
configuration valid given only that the samples fit the bit depth and
`choosePlanF`'s own constant-block guard. `partSizes_sum` shows a legal
configuration's partitions cover the residual exactly, so `emitOk_sanitize`
discharges `SubPlan.EmitOk` unconditionally and the emission simulation needs
no side condition.

Consequence: the fast encoder needs **no validity scan** to match
`ChannelAsg.orVerbatim` — the sanitised choice is always valid, so
`orVerbatim` is the identity on it. That is what keeps certificate removal
free, and it supersedes this session's earlier "the real work here is a fast
array-side decider".

The one non-scalar obligation, wasted-bit divisibility, is also a proof:
`wastedDetectF` is now `tzGo`/`wastedGo` (structural), and
`wastedDetectF_dvd_mem` shows every sample is divisible by `2 ^ w`, with
`wastedDetectF_lt` giving `w < b`.

`Flac/Spec/Encode.lean`: 66 theorems, 1093 lines, no sorry, no axioms beyond
`propext`/`Classical.choice`/`Quot.sound`.

**Blocked:** nothing.

**Next**, what is left of the chain:
1. `chooseSub_denotes` — `SubPrep.Denotes`, which should be nearly `rfl`:
   the fast code scales by `(· / ((p2 wa : Nat) : Int))` and
   `Flac.Bits.shiftDown w x` *is* `x / ((2 ^ w : Nat) : Int)`.
2. The frame-level chooser: define the reference `EncoderCfg.chooser` as the
   translation of `chooseFrame`'s decisions (`⟨p.wasted, subCfgOf p.plan⟩`
   per subframe), then prove `planOf qs = Emit.W.planA b asg chs` branch by
   branch — the stereo cases need `sd`/`md` to be `Stereo.sideA`/`midA`,
   which they are syntactically — and `asg.code chs.length = fp.chCode`.
   `ChannelAsg.Valid` at that level needs the per-channel width facts:
   `Flac.Spec.Stereo.side_fits`/`mid_fits` for the `b+1` channels, and the
   16-bit input bound (via the input bridge) for the rest.
3. Stream assembly: the STREAMINFO prefix, then per-frame concatenation.
   `pushFrame_spec` (emission only appends) is the locality argument;
   `(Task.spawn f).get = f ()` holds by `rfl`, or a `ByteStep`-style erased
   payload avoids even that.
4. Flip and delete, in one commit, as before.

### Session 10, continued — stage 3 complete

**Landed** (same probe and method; byte-identical on all 37 corpus files at
every step). Cumulative encode cost of the whole project so far: **+6.8%**
over the tag, against the 31% the certificate gives back.

| commit | change |
|---|---|
| `e5c76e5` | `StereoMode` inductive; `FramePrep.subs` pairs each decision with its block |
| `4289be0` | `sim_frame` — the shipped frame *is* the verified frame |
| `86ac02b` | `chooseSub_cfg_valid` — one decision carries its certificate |
| `bb9ac08` | `chooseFrame_asg_valid` — the frame's decisions are valid |
| `f4c92d6` | `safeChooser_fastChooser` — `orVerbatim` is the identity on them |

**The frame level is closed, end to end.** `Flac.Encode.sim_frame` has no
hypotheses at all:

    Simulates (fun bw => pushFrameOf bw b strat num (chooseFrame b chs))
              (Emit.W.pushFrame b strat num (chooseFrame b chs).asg chs.toList)

The shipped encoder's frame — its own `Float` search, its own unpacked
writers — emits exactly what the verified emitter emits for the channel
assignment those decisions denote. Nothing in the chain reasons about a
`Float`: the searches appear on *both* sides of every equation and are only
ever applied.

**And the chooser side is closed too.** `fastChooser` is the
`EncoderCfg.chooser` to instantiate `Stream.encode` with, and
`safeChooser_fastChooser` shows the `orVerbatim` wrapper the reference puts
around every chooser is the identity on it, so the VERBATIM fallback never
fires. That needed `chooseFrame_asg_valid`, whose per-mode cases rest on
`Spec.Stereo.side_fits`/`mid_fits` for the `b + 1` side channels.

Two lessons worth keeping:
- `chooseFrame_shape` had to be proven as an *equation* before validity could
  be attacked: inside `ChannelAsg.Valid`, `split` targets `Valid`'s own match
  rather than `chooseFrame`'s branches. Both independent branches (two
  channels coded independently, and more than two) share the description
  `subs = chs.toList.map fun c => (chooseSub b c, c)`, which keeps the case
  analysis to four.
- Neither `set`, `conv_lhs`, `by_contra` nor `repeat'` exists without
  mathlib. For a guarded definition, `rw [f] at h; split at h` gives the
  guard directly — no `by_contra` needed.

`Flac/Spec/Encode.lean`: 93 theorems, 1529 lines, warning-free, no sorry, and
only `propext`/`Classical.choice`/`Quot.sound`.

**Blocked:** nothing.

**Next — stage 4, the last one before the flip.**
1. A byte-level append corollary of `Emit.W.pushFrame_spec` (emission only
   appends): `(W.pushFrame … w).buf = w.buf ++ (W.pushFrame … empty).buf` for
   byte-aligned `w`. `Spec.Emit.aligned_buf_of_bits` is the existing bridge
   from a bits equality to a buffer equality.
2. `Sim (BitWriter.empty c₁) (Emit.W.empty c₂)` — needs
   `ByteArray.emptyWithCapacity c₁ = emptyWithCapacity c₂`, which `encode_eq`
   already proves by `ByteArray.ext`.
3. Then the frame fold: the fast encoder concatenates per-frame buffers,
   each produced from an *empty* writer, where `W.pushFrames` folds one
   writer through. (1) + (2) + `sim_frame` closes that, and the `Task`
   collapse is `(Task.spawn f).get = f ()` by `rfl` — or a `ByteStep`-style
   erased payload if the `@[extern]` task model is to be kept out.
4. The STREAMINFO prefix (`pushStreamPrefix` versus the fast encoder's
   header pushes, plus MD5, which is already outside the losslessness claim).
5. Flip and delete, in one commit: point `--encode` at the proven path, drop
   `pcm16Certified`. `encodePcm16Fast` keeps its signature and
   `decodePcm16_encodePcm16Fast` its exact statement.

### Session 10, continued — stage 4, and M6b is done

**The runtime certificate is retired.** `Flac.Encode.encodePcm16_eq`:

    encodePcm16 blockSize ch sr bytes
      = Stream.encode ⟨blockSize, false, fastChooser 16⟩
          ⟨deinterleave ch (pcm16OfByteList bytes.data.toList), 16, sr⟩

so `Flac.Stream.decodePcm16_encodePcm16Fast` follows from
`decodePcm16_encodePcm16Cfg`. `encodePcm16Fast` is now
`some (Encode.encodePcm16 …)` under O(1) guards; `pcm16Certified`,
`pcm16CertifiedSlow` and `encodePcm16FastGo` are deleted with their proofs.
The capstone's statement did not change by a character, so `pin_encode_fast`
never moved, and it still rests on exactly `propext`, `Classical.choice`,
`Quot.sound`.

**Measured** (same machine as the `certified-encoder-stable` tag):

| probe | certified | proven | |
|---|---|---|---|
| 47 MB stereo | 0.564 s | 0.434 s | 1.30× faster |
| 32 MB stereo | 0.416 s | 0.327 s | 1.27× faster |

Corpus medians after a full `bench/run.sh`: encode 74.3 MB/s against
`flac -8`'s 74.9 (**1.01×**, was 1.30×), decode 121.2 against 125.6
(1.04×), compression unchanged at 39.6% versus 39.8% — output is
byte-identical, so only the throughput figures moved. Against file size,
same material, the encoder is now *ahead of* `flac -8` at every size
measured (0.99× at 1 MB, 0.95× at 32 MB) and the decoder from 4 MB up.

**Stage 4's pieces.** `pushFrame_buf_append` (emission only appends, so a
worker can build its frame from an empty writer), `sim_empty`,
`pushFrames_concat` (the reference's fold is the shipped concatenation),
`sim_prefix` (marker and STREAMINFO in `pushStreamPrefix`'s exact shape —
the digest as one 128-bit field rather than sixteen bytes, so it is
literally the reference's push), `pcmBytes_deinterleave` (the reference's
digest is a digest of the *input*), `chunkChannels_getD` and
`chunkChannels_length` (frame `k` is frame `k`), `frameBytesPcm_eq`,
`audio_wellFormed`, `encodePcm16Cfg_fast`.

**Two `Task` boundaries were closed the sound way**, not by trusting the
`@[extern]` task model:
- `FrameStep`/`Md5Step` — a worker's payload is its bytes plus the erased
  proof that they are what the fast function computes for that index,
  `rfl` at construction. Any value of the type carries the equation, so
  `concatFrames` is characterised without a word about `Task`; it checks the
  recorded index and rebuilds the frame otherwise, so a wrong payload costs
  work, never correctness. Exactly `Flac.Decode.ByteStep`'s pattern.
- `Stream.pcmBytesA` split serialisation into windows, one `Task` each, and
  "carried no theorem, because it reasons through `Task`" (its own comment).
  It is now the plain `pcmBytesRange`. That is what made the digest
  provable. Nothing on a shipped fast path used it — `--decode-fast`
  serialises via `Decode.decodeBytes` — and it costs only `--decode`, which
  is already 297× slower than `--decode-fast` on the same file.

**Five guards replaced the certificate's silent coverage**: `0 < ch ≤ 8`,
byte count a multiple of `2·ch`, `sampleRate < 2^20`, sample count `< 2^36`,
`16 ≤ blockSize ≤ 65535`. All were cases where the old path fell through to
`encodePcm16Cfg` and returned `none` anyway, so behaviour is unchanged;
rejecting a block size below 16 is also what RFC 9639 §9.1 requires.

`Flac/Spec/Encode.lean` ended the session at 124 theorems / 2114 lines,
warning-free, no sorry, axioms `propext`/`Classical.choice`/`Quot.sound`.

**Cost of provability, cumulative and measured**: `Int` residual emission
+6%, plan sanitisation +0.2%, the general deinterleave +0.5%, everything
else free. Against the 23% the certificate gave back.

**Blocked:** nothing.

**Next.** M6b is complete; the remaining ideas are compression and speed
rather than proof:
1. Match libFLAC's search *shape* — one LPC order per apodisation window
   across two or three windows, instead of one window with several orders
   costed exactly. Roughly half today's LPC work, possibly the same ratio.
   Still the most promising encode lever.
2. A windowed bit reader (cached word + count) for the ~34% of decode in
   the Rice reader; needs a simulation proof against `readRiceSeqScan`.
3. De-tuple `Flac.Emit.W`'s bit writer, which only matters for
   `--encode-slow` now.
4. M7: two-sided verification against RFC 9639.

### Session 10, addendum — benchmarks rerun, figures and docs refreshed

The figures in the entries above came from single passes on a machine that
was not idle. Rerun properly (desktop apps closed, `BENCH_RUNS=15`, six
passes for the corpus medians and two for the size sweep), and the picture
is the same but the numbers are firmer:

**Corpus medians** (committed `bench/results.csv`, the canonical pass):
encode 70.7 MB/s against `flac -8`'s 74.7 (**1.06×**, from 1.27× at the
tag), decode 123.6 against 124.9 (**1.01×**), `flac -5` 108.4 (1.53×).
Compression unchanged at 39.6% versus `flac -8`'s 39.8% — the output is
byte-identical, so only throughput could move.

**Methodology correction.** `bench/README.md` claimed run-to-run spread of
2–3% on these medians. That holds for decode (1.01–1.03× across six passes)
but *not* for encode, which ranged 1.02–1.07×. Encoding is `Task`-parallel,
so at 1 MB it loses far more to background load than single-threaded
libFLAC does; a first attempt at these medians, taken with the desktop at
load ~10, put Vinyl 8% low while libFLAC moved 1%. Both READMEs now say so,
and point at the size sweep and the 32 MB probe for judging a change.

**The 32 MB probe** (mono, 4096-sample blocks, `flac -8` at 92.3 MB/s) is
the honest instrument, and it is now in `bench/README.md` as the session-10
stage table:

| stage | encode | gap (`-8`) |
|---|---|---|
| session 9 end | 75.3 MB/s | 1.23× |
| `Int` residual emission | 69.2 MB/s | 1.33× |
| plan sanitisation | 68.6 MB/s | 1.35× |
| stage 3 complete | 68.8 MB/s | 1.34× |
| self-certifying payloads | 68.5 MB/s | 1.35× |
| **certificate retired** | 97.7 MB/s | **0.94×** |

So the whole cost of provability was **10%** and the certificate paid
**30%** back — and encode ends *ahead of* `flac -8` on a large file. The
earlier "23%" figure was the 47 MB stereo probe; both are now quoted where
they belong.

**Size sweep**, same material, best of two passes per row: encode overtakes
`flac -8` from 2 MB (0.99×) and settles at 0.94×; decode overtakes libFLAC
from 4 MB and settles at 0.87×.

Docs brought current: `README.md` (both tables, the spread caveat, the
certificate narrative), `bench/README.md` (headline medians, size sweep,
session-10 stage table, the "where the remaining work is" section — there is
no encode *gap* on a large file any more), `ARCHITECTURE.md` (file tree,
the 30%/23% figures), `COVERAGE.md` (the PCM16 entry point's runtime
preconditions, which now match the block-size and channel rows it already
claimed). `bench/performance.png` regenerated; `bench/compression.png`
unchanged, as it must be for byte-identical output.

---

## 2026-08-24 — Session 11: real-audio benchmarks, and two retractions

**Attempted:** retrieve the real-audio corpora that `real_fetch.py` already
knew how to fetch but that had never been timed, benchmark Vinyl against
`flac -8` on them, and publish the result. The old `bench/README.md` had said
this run "must use minimal metadata and compare frame payload sizes before
selecting a speed baseline"; it does, and it changes two headline claims.

**Landed:**

- **Corpora prepared** — the two in the tens-to-hundreds-of-MB band. EBU SQAM
  (167.4 MiB archive → 620 MB PCM, 70 tracks, 2ch 44.1 kHz) was already
  fetched; LibriSpeech `test-clean` + `test-other` (644.1 MiB → 1.24 GB,
  5,559 utterances, 1ch 16 kHz) prepared from the local archives with
  `real_fetch.py --corpus librispeech --offline`. The multi-gigabyte options
  in `CORPORA.md` (FSD50K 6.2 GB, MUSDB18-HQ 22.7 GB, MAESTRO 101 GB) were
  deliberately skipped — at 1.73 GiB the suite already resolves the gaps
  being measured.
- **`bench/real_units.py`** — turns prepared PCM into 143 benchmark units:
  SQAM tracks in place (median 5.9 MB), LibriSpeech concatenated per *speaker*
  in sorted utterance order (73 streams, 5.1–19.8 MB), because 0.22 MB
  utterances measure process startup rather than throughput. `units.csv`
  records format, size, source count and SHA-256 per unit.
- **`bench/real_run.py`, `bench/real_plot.py`, `bench/real_run.sh`** — same
  timing instrument as the synthetic harness (one persistent
  `perf_counter_ns`, one untimed warmup, fixed-seed shuffled repetitions,
  median), plus three things real audio made measurable: payload-only sizes,
  libFLAC measured at both 1 and 8 threads, and a per-unit cross-decode.
- **`bench/flacsize.py`** — the audio-frame payload parser (walk the metadata
  block headers per RFC 9639 §8), now shared by both harnesses. `bench/run.py`
  records an `audio_bytes` column too, so both dashboards use one accounting.
- **Encode CLI takes a sample rate** (`FlacTest/Cli.lean`), optional and
  defaulting to 44100. Without it LibriSpeech could only be encoded with
  16 kHz audio behind 44.1 kHz metadata. `encodePcm16Fast` already accepted
  any rate below 2^20 and the round-trip theorem is stated at every one, so
  the guarantee is unchanged. Both `--encode` arities delegate to
  `encodeFastMain`; `--encode-slow` likewise to `encodeSlowMain`.
- **`scripts/check.sh` tightened**, not loosened, to follow that delegation.
  The CLI pin table now names the helper, and requires the branch count to
  equal the delegation count — so a second arity cannot appear that skips the
  proven encoder. This also fixed a pre-existing prefix bug: the scrape for
  `--encode` matched the `--encode-slow` branch too and could have been
  satisfied by *its* call. Both failure modes verified by negative test.

**Results, 143 units / 1.73 GiB, five measured runs, Apple M2 (8 cores):**

| | Vinyl | libFLAC | gap |
|---|---|---|---|
| decode | 205 MB/s (8 thr) | 189 MB/s (1 thr) | **0.92×** |
| encode vs `flac -8 -j8` | 94 MB/s (8 thr) | 319 MB/s (8 thr) | 3.40× |
| encode vs `flac -8` | 94 MB/s (8 thr) | 77 MB/s (1 thr) | 0.82× |
| encode vs `flac -5` | 94 MB/s (8 thr) | 140 MB/s (1 thr) | 1.49× |

Compression, audio-frame payload: Vinyl 47.6%, `flac -5` 46.1%, `flac -8`
45.5%. Vinyl's payload is smaller than `flac -8`'s on 1 of 143 units and
smaller than `flac -5`'s on 3; the median unit is 4.7% larger than `flac -8`'s.

**Two retractions.**

1. **"Vinyl's compression beats `flac -8`" is false**, and was false on the
   synthetic corpus too. The comparison was whole-file, and libFLAC's default
   8,826 bytes of padding/seektable/vendor comment are ~2.2% of the ~400 kB it
   emits for a 1 MB file — four times the 0.5% relative difference claimed.
   Re-measured on coded frames, the synthetic corpus gives Vinyl 39.6% against
   `flac -8`'s **39.0%** (was reported as 39.8%). Real audio gives 47.6% vs
   45.5%. `flac -8` was ahead on both corpora all along.
2. **"Encode is at parity with `flac -8`" was measuring a thread count.**
   libFLAC 1.5.0 takes `-j`; Vinyl has been frame-parallel since session 6.
   Thread-matched, encode is 3.4× behind. `-j` changes scheduling only — the
   two libFLAC streams are byte-identical on 143/143 units.

**What holds up.** Decode is genuinely ahead per invocation (1.08×, faster on
120 of 143 units), which is also where the proofs are deepest. And
interoperability is now tested at real scale: on all 143 units, outside the
timed intervals, `flac -t` accepts Vinyl's stream and its MD5, Vinyl's decoder
reproduces the input exactly, and **Vinyl's decoder reproduces libFLAC's
`flac -8` output byte-for-byte** — 1.73 GiB of real audio at libFLAC's widest
search, no mismatch.

**Docs restructured.** `bench/README.md` is now three parts: Part 1 real-audio
benchmarks (what the corpora are, what a unit is, how it is measured, results,
what the corpus settled, known gaps), Part 2 the synthetic micro-benchmarks
retitled as such and re-tabulated on payload, Part 3 the optimization history
with a header noting its ratios are whole-file and its gaps single-threaded.
`README.md`'s benchmark section leads with the real corpus and carries the
retraction. `ARCHITECTURE.md`'s 0.94× figure now says *single-threaded*.
Earlier PROGRESS entries are left as written — they are an accurate record of
what was measured at the time, under the accounting in use then.

**Not blocked; no proof debt.** `scripts/check.sh` green: build, zero
`sorry`/`axiom`, capstones pinned, CLI pins, totality lint, 102 unit checks.

**Next steps.**

1. **Record CPU time per invocation** (`os.wait4` rusage) so the decode result
   can be stated per core as well as per invocation. Every number here is wall
   clock, and the decode comparison is unavoidably 8 threads against 1.
2. **Measure `flac -0` on real audio**, to bracket Vinyl's ratio from below as
   well as above.
3. **Close the 4.7% ratio gap**, which is a search-quality gap: libFLAC's `-8`
   buys its ratio with several apodization windows where
   `Flac.Heuristics.lpcCandidates` uses one. On synthetic signals one window
   nearly kept up; on real audio it does not.
4. **24-bit and non-44.1/16 kHz material** — both corpora are S16 at two
   rates, while the codec and theorems cover depths 1–32.

---

## 2026-08-24 — Session 12: a thread flag, and thread-matched numbers everywhere

**Attempted:** session 11 reported an encode gap "3.4× thread-matched" and a
decode result "1.08× ahead", both against libFLAC's `-j`. Vinyl had no
equivalent knob, so those were the machine's core count against a chosen
libFLAC setting rather than a controlled comparison. Give Vinyl the knob,
sweep both codecs over thread counts on **both** suites, and republish.

**Landed:**

- **`vinyl -j <n>`** (also `--threads <n>`, `--threads=<n>`), in
  `FlacTest/Cli.lean`. Lean sizes its task pool from `LEAN_NUM_THREADS` when
  the runtime starts, which is before `main` is entered, so a flag cannot
  resize its own process's pool: the flag re-executes the binary once with the
  variable set and returns the child's exit code. Measured cost ~3 ms; all
  three spellings agree with the variable to within noise (0.4947 / 0.4976 /
  0.4978 s against 0.4917 s at one thread). Bad input is rejected with exit 2.
- **The knob is the runtime pool, not the codec.** Parallelism is one
  `Task.spawn` per frame, so capping workers inside `encodePcm16` would mean
  regrouping frames and reproving `encodePcm16_eq` for nothing. Nothing under
  `Flac/` changed.
- **Both harnesses sweep.** `BENCH_THREAD_SWEEP` (default `1,2,4,8`, clamped to
  the core count) drives Vinyl encode, Vinyl decode and `flac -8` at every
  count in `bench/run.py` *and* `bench/real_run.py`; `-0`/`-5` stay at one
  thread as ratio context. Case labels carry `-jN`, and both plot scripts
  *check* that `-j` never changes the coded bytes rather than assuming it.
- **`flac -d` takes no threads.** `-j` is documented under encoding options,
  and `flac -d -j8` is silently accepted and ignored — 0.0448 s against
  0.0445 s on the same file, exit 0 either way. So every decode row is one
  libFLAC thread by necessity, and the figures draw it as a dotted reference
  level rather than a curve.
- **New figures** `bench/threads.png` and `bench/real_threads.png`: corpus
  throughput against thread count, and parallel speedup against the ideal
  line.

**Results.** Corpus throughput, total raw MB ÷ total seconds:

| threads | vinyl enc | `flac -8` enc | gap | vinyl dec | `flac` dec | gap |
|---:|---|---|---|---|---|---|
| *synthetic, 37 × 1 MB* | | | | | | |
| 1 | 18.5 | 72.0 | 3.90× | 49.2 | 130.2 | 2.64× |
| 8 | 77.9 | 172.3 | **2.21×** | 124.4 | no `-j` | **1.05×** |
| *real audio, 143 units* | | | | | | |
| 1 | 18.2 | 77.3 | 4.24× | 46.2 | 189.6 | 4.11× |
| 8 | 100.8 | 335.0 | **3.32×** | 216.9 | no `-j` | **0.87×** |

Speedup 1→8 threads: Vinyl encode 4.22× (synthetic) / 5.53× (real), `flac -8`
2.39× / 4.33×, Vinyl decode 2.53× / 4.70×.

**What this revises from session 11.**

1. **Per thread, Vinyl is ~4× behind in *both* directions** — encode 4.2×,
   decode 4.1× on real audio. Session 11 could not state the decode figure at
   all ("total CPU time is not recorded, so the per-core figure is not
   quantified here"); this quantifies it, and it is much worse than the
   wall-clock result suggested. That the factor is the *same* both ways is the
   informative part: it is per-operation cost, not a structural problem in one
   path.
2. **"Decode is ahead" survives but shrinks in meaning.** 1.14× ahead at eight
   threads is real and is Vinyl's only wall-clock win, but the decode curve
   only crosses libFLAC's single-threaded level at about **six threads**.
3. **Vinyl parallelises better than libFLAC** — the one clearly favourable
   finding, and it holds on both corpora. It is also the part the proofs cover:
   frame-parallel decode and serialization are proven equal to their bit-level
   specifications, so the scaling is not bought with trust.
4. **The synthetic suite scales worse for both codecs** (Vinyl 4.22×, libFLAC
   2.39×) because 1 MB files carry a fixed per-file cost that cannot be
   parallelised away. Read scaling off the real corpus.

**Docs.** `bench/README.md` restructured again on request: a
"Where Vinyl stands against libFLAC" ratio block **first**, then Part 1
synthetic micro-benchmarks (moved ahead of the real-audio suite), Part 2
real audio, Part 3 optimization history — with the thread-scaling figure and a
scaling table in both suites, and every cross-reference renumbered.
`README.md`'s benchmark section now leads with the same ratio block and keeps
only the three general points: same-thread slowdown, scaling trends, and that
decode overtakes libFLAC as threads are added; it also documents `-j`.

**Not blocked; no proof debt.** `scripts/check.sh` green.

**Next steps.**

1. **`rusage` per invocation**, to separate oversubscription and
   efficiency-core effects on this asymmetric-core machine (Apple M2: four
   performance, four efficiency) — the likeliest reason neither codec scales
   linearly past four threads.
2. **Close the ~4× per-operation gap**, which is where the whole distance now
   lives. Part 3's "where the remaining encode gap is" is the map.
3. **`flac -0` on real audio**, to bracket Vinyl's ratio from below.
4. **24-bit and non-44.1/16 kHz material.**

## 2026-08-24 — Session 13: main README shows one benchmark figure

**Docs only; no Lean touched.** On request, `README.md`'s benchmark section no
longer carries the thread-scaling material: the per-thread throughput table
(both suites), `bench/threads.png`, `bench/real_threads.png`, and the
scaling/asymmetric-core commentary are gone from the main README. In their place
is a single figure — `bench/real_performance.png`, the real-audio per-unit
throughput cactus — under a new "Real-audio throughput" heading, with commentary
on what the curves actually show: the gap is a flat multiplicative factor across
143 units of very different material (×3.4 encode at eight threads, ×4.7 at
one), decode at eight threads is the one place Vinyl leads on wall clock (×1.15
median, 217 vs 190 MB/s corpus totals), and the per-core distance is the same
~4× in both directions.

Kept deliberately: the thread-matched ratio table and the compression table at
the top of the section, since dropping either would reintroduce one of the two
accounting errors retracted in Session 11 (payload-only sizes, matched threads).
The removed figures and tables still live in `bench/README.md`, which the
section's closing pointer now names explicitly.

**Not blocked; no proof debt.** Next steps unchanged from Session 12.
