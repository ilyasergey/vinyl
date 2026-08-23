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
