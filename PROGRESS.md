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
