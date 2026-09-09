import Flac.Native.Bits

/-!
# Quantized linear prediction (RFC 9639 §9.2.6)

Prediction for sample `n` is `(Σᵢ cs[i] · x[n-1-i]) >>> shift` — the first
coefficient multiplies the most recent sample, and the shift is an
*arithmetic* right shift (floor division by `2^shift`).

Both coder and decoder are written in history-passing style: they carry
the reversed prefix of already-processed samples. That makes the L3-LPC
round-trip (`Flac.Spec.Lpc.restore_residual`) a one-line induction — the
decoder's history provably equals the encoder's, so the predictions
coincide and `residual + prediction = sample` — independent of what the
prediction function actually computes. Where the coefficients come from
(Levinson–Durbin, windowing, quantization) never enters the kernel.
-/

namespace Flac.Lpc

open Flac.Bits (sar)

/-- Dot product over two lists directly — no intermediate `zip`
    allocation per sample. Pinned to the folded-zip formulation by
    `Flac.Spec.Lpc.dot_eq_zip_foldl`. -/
def dot : List Int → List Int → Int
  | c :: cs, h :: hs => c * h + dot cs hs
  | _, _ => 0

/-- Dot product of coefficients with the reversed history (most recent
    sample first), then the quantization shift. -/
def predict (cs : List Int) (shift : Nat) (hist : List Int) : Int :=
  sar (dot cs hist) shift

/-- Residuals of `ys`, given the reversed history `hist` of preceding
    samples. -/
def residualAux (cs : List Int) (shift : Nat) (hist : List Int) :
    List Int → List Int
  | [] => []
  | x :: ys => (x - predict cs shift hist) :: residualAux cs shift (x :: hist) ys

/-- `residualAux` with the residuals accumulated, so the recursive call is in
    tail position: the residual length is the block size (unbounded via the
    unchecked encoder), so the cons-after-return form kept one native stack frame
    per sample (audit finding C04, the LPC residual analogue —
    `fuzz/findings/encoder-stack-overflow-CONFIRMED`). -/
def residualAuxAcc (cs : List Int) (shift : Nat) (acc : List Int) :
    (hist : List Int) → List Int → List Int
  | _, [] => acc.reverse
  | hist, x :: ys =>
    residualAuxAcc cs shift ((x - predict cs shift hist) :: acc) (x :: hist) ys

theorem residualAuxAcc_eq (cs : List Int) (shift : Nat) (acc hist : List Int)
    (ys : List Int) :
    residualAuxAcc cs shift acc hist ys = acc.reverse ++ residualAux cs shift hist ys := by
  induction ys generalizing acc hist with
  | nil => simp [residualAuxAcc, residualAux]
  | cons x ys ih =>
    rw [residualAuxAcc, residualAux, ih ((x - predict cs shift hist) :: acc) (x :: hist)]
    simp

def residualAuxTR (cs : List Int) (shift : Nat) (hist : List Int)
    (ys : List Int) : List Int :=
  residualAuxAcc cs shift [] hist ys

/-- Swap the compiled `residualAux` for the tail form; theorems keep the
    structural definition via the kernel. -/
@[csimp] theorem residualAux_eq_residualAuxTR : @residualAux = @residualAuxTR := by
  funext cs shift hist ys
  unfold residualAuxTR
  rw [residualAuxAcc_eq]
  simp

/-- LPC residual: the first `cs.length` samples are warmup, the rest are
    prediction residuals. -/
def residual (cs : List Int) (shift : Nat) (xs : List Int) : List Int :=
  residualAux cs shift (xs.take cs.length).reverse (xs.drop cs.length)

/-- Sample reconstruction, wrapped to `b`-bit two's complement *inside*
    the recurrence: the wrapped sample is what enters the prediction
    history, exactly as in a fixed-width decoder. Without the wrap a
    crafted subframe (large coefficient, shift 0) diverges geometrically
    and the exact-ℤ samples exhaust memory — the wrap bounds every
    reconstructed sample by construction
    (`Flac.Spec.Bits.fitsSInt_wrapSInt`), and is the identity on every
    stream the encoder produced (`Flac.Spec.Lpc.restore_residual`
    carries the hypothesis). -/
def restoreAux (b : Nat) (cs : List Int) (shift : Nat) (hist : List Int) :
    List Int → List Int
  | [] => []
  | r :: res =>
    let x := Bits.wrapSInt b (r + predict cs shift hist)
    x :: restoreAux b cs shift (x :: hist) res

/-- `restoreAux` with the samples accumulated, so the recursive call is in tail
    position. The structural `restoreAux` recurses once per residual sample (depth =
    block size), so the List-Bool reference decoder overflowed the stack on a
    malformed frame declaring a huge block (fz_proven_pairs, 2026-09-02); this is the
    decode-side twin of `residualAuxTR`. -/
def restoreAuxAcc (b : Nat) (cs : List Int) (shift : Nat) (acc : List Int) :
    (hist : List Int) → List Int → List Int
  | _, [] => acc.reverse
  | hist, r :: res =>
    restoreAuxAcc b cs shift (Bits.wrapSInt b (r + predict cs shift hist) :: acc)
      (Bits.wrapSInt b (r + predict cs shift hist) :: hist) res

theorem restoreAuxAcc_eq (b : Nat) (cs : List Int) (shift : Nat) (acc hist : List Int)
    (res : List Int) :
    restoreAuxAcc b cs shift acc hist res = acc.reverse ++ restoreAux b cs shift hist res := by
  induction res generalizing acc hist with
  | nil => simp [restoreAuxAcc, restoreAux]
  | cons r res ih =>
    rw [restoreAuxAcc, restoreAux, ih]
    simp

def restoreAuxTR (b : Nat) (cs : List Int) (shift : Nat) (hist res : List Int) : List Int :=
  restoreAuxAcc b cs shift [] hist res

/-- Swap the compiled `restoreAux` for the tail form; theorems keep the structural
    definition via the kernel (value-equal). -/
@[csimp] theorem restoreAux_eq_restoreAuxTR : @restoreAux = @restoreAuxTR := by
  funext b cs shift hist res
  unfold restoreAuxTR
  rw [restoreAuxAcc_eq]
  simp

/-- Restore samples from warmup and residual at bit depth `b`. -/
def restore (b : Nat) (cs : List Int) (shift : Nat) (warmup res : List Int) : List Int :=
  warmup ++ restoreAux b cs shift warmup.reverse res

/-! ### Array forms (the production decoder's hot path)

The decoded prefix lives in one growing array; the prediction indexes it
from the end instead of consing a reversed history per sample. Proven
equal to the list forms in `Flac.Spec.Lpc` (`restoreA_toList`). -/

/-- Tail-recursive dot product against the final `n` elements of `out`,
    newest first. The bound is proof-only, so each tap uses direct array
    indexing without a dynamic `getD` check. -/
def dotAGo (out : Array Int) :
    (cs : List Int) → (n : Nat) → n ≤ out.size → Int → Int
  | [], _, _, acc => acc
  | _ :: _, 0, _, acc => acc
  | c :: cs, n + 1, hn, acc =>
    have hi : n < out.size := Nat.lt_of_succ_le hn
    dotAGo out cs n (Nat.le_of_lt hi) (acc + c * out[n])

/-- The original total `getD` behavior for the cold case where the supplied
    starting index is outside the array. -/
private def dotAGetD : List Int → Array Int → Nat → Int
  | [], _, _ => 0
  | c :: _, out, 0 => c * out.getD 0 0
  | c :: cs, out, i + 1 => c * out.getD (i + 1) 0 + dotAGetD cs out i

/-- `dot cs hist` where the history is `out[i], out[i-1], …, out[0]` —
    the decoded prefix walked from the end, most recent first (stopping at
    index 0 exactly like `dot`'s zip truncation). The decoder's in-bounds
    path is a tail loop with one proof-erased direct lookup per tap. -/
@[inline] def dotA (cs : List Int) (out : Array Int) (i : Nat) : Int :=
  match cs with
  | [] => 0
  | _ :: _ =>
    if h : i < out.size then
      dotAGo out cs (i + 1) (Nat.succ_le_iff.mpr h) 0
    else
      dotAGetD cs out i

/-! ### Straight-line dot products

`dotAGo` walks a `List Int` once per sample: two dependent loads per
tap on top of the multiply-accumulate. On the emission path that was the
largest single cost in encode.

Two earlier shapes were measured and rejected. Dispatching a
specialisation *per sample* walks the same cons cells it removes (27.0 →
25.3 MB/s), and a chain of `dotAGo{k}` functions passing `out`, k taps,
`n`, `hn` and `acc` spills at nine arguments on arm64 (27.7 → 26.7). What
works is what `Flac.Encode.lpcFold{n}` already did on the search side: a
self-recursive loop with the taps loop-invariant and a straight-line
body. These are the bodies; `Flac.Emit.lpcResGo{k}` are the loops. -/

/-- `dotA` at 1 tap, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 1` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot1At_eq`. -/
@[inline] def dot1At (xs : Array Int) (c0 : Int) : Nat → Int
  | m + 1 =>
    if h : m + 1 ≤ xs.size then 0 + c0 * xs[m]'(by omega)
    else dotA [c0] xs (m)
  | i => dotA [c0] xs (i - 1)

/-- `dotA` at 2 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 2` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot2At_eq`. -/
@[inline] def dot2At (xs : Array Int) (c0 c1 : Int) : Nat → Int
  | m + 2 =>
    if h : m + 2 ≤ xs.size then 0 + c0 * xs[m + 1]'(by omega) + c1 * xs[m]'(by omega)
    else dotA [c0, c1] xs (m + 1)
  | i => dotA [c0, c1] xs (i - 1)

/-- `dotA` at 3 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 3` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot3At_eq`. -/
@[inline] def dot3At (xs : Array Int) (c0 c1 c2 : Int) : Nat → Int
  | m + 3 =>
    if h : m + 3 ≤ xs.size then 0 + c0 * xs[m + 2]'(by omega) + c1 * xs[m + 1]'(by omega) + c2 * xs[m]'(by omega)
    else dotA [c0, c1, c2] xs (m + 2)
  | i => dotA [c0, c1, c2] xs (i - 1)

/-- `dotA` at 4 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 4` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot4At_eq`. -/
@[inline] def dot4At (xs : Array Int) (c0 c1 c2 c3 : Int) : Nat → Int
  | m + 4 =>
    if h : m + 4 ≤ xs.size then 0 + c0 * xs[m + 3]'(by omega) + c1 * xs[m + 2]'(by omega) + c2 * xs[m + 1]'(by omega) + c3 * xs[m]'(by omega)
    else dotA [c0, c1, c2, c3] xs (m + 3)
  | i => dotA [c0, c1, c2, c3] xs (i - 1)

/-- `dotA` at 5 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 5` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot5At_eq`. -/
@[inline] def dot5At (xs : Array Int) (c0 c1 c2 c3 c4 : Int) : Nat → Int
  | m + 5 =>
    if h : m + 5 ≤ xs.size then 0 + c0 * xs[m + 4]'(by omega) + c1 * xs[m + 3]'(by omega) + c2 * xs[m + 2]'(by omega) + c3 * xs[m + 1]'(by omega) + c4 * xs[m]'(by omega)
    else dotA [c0, c1, c2, c3, c4] xs (m + 4)
  | i => dotA [c0, c1, c2, c3, c4] xs (i - 1)

/-- `dotA` at 6 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 6` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot6At_eq`. -/
@[inline] def dot6At (xs : Array Int) (c0 c1 c2 c3 c4 c5 : Int) : Nat → Int
  | m + 6 =>
    if h : m + 6 ≤ xs.size then 0 + c0 * xs[m + 5]'(by omega) + c1 * xs[m + 4]'(by omega) + c2 * xs[m + 3]'(by omega) + c3 * xs[m + 2]'(by omega) + c4 * xs[m + 1]'(by omega) + c5 * xs[m]'(by omega)
    else dotA [c0, c1, c2, c3, c4, c5] xs (m + 5)
  | i => dotA [c0, c1, c2, c3, c4, c5] xs (i - 1)

/-- `dotA` at 7 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 7` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot7At_eq`. -/
@[inline] def dot7At (xs : Array Int) (c0 c1 c2 c3 c4 c5 c6 : Int) : Nat → Int
  | m + 7 =>
    if h : m + 7 ≤ xs.size then 0 + c0 * xs[m + 6]'(by omega) + c1 * xs[m + 5]'(by omega) + c2 * xs[m + 4]'(by omega) + c3 * xs[m + 3]'(by omega) + c4 * xs[m + 2]'(by omega) + c5 * xs[m + 1]'(by omega) + c6 * xs[m]'(by omega)
    else dotA [c0, c1, c2, c3, c4, c5, c6] xs (m + 6)
  | i => dotA [c0, c1, c2, c3, c4, c5, c6] xs (i - 1)

/-- `dotA` at 8 taps, straight-line.

    The taps are parameters, so after inlining into a residual loop they are
    loop-invariant and stay in registers; matching `i` as `m + 8` keeps the
    hot path free of `Nat` subtraction. Equal to `dotA` by
    `Flac.Spec.Lpc.dot8At_eq`. -/
@[inline] def dot8At (xs : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 : Int) : Nat → Int
  | m + 8 =>
    if h : m + 8 ≤ xs.size then 0 + c0 * xs[m + 7]'(by omega) + c1 * xs[m + 6]'(by omega) + c2 * xs[m + 5]'(by omega) + c3 * xs[m + 4]'(by omega) + c4 * xs[m + 3]'(by omega) + c5 * xs[m + 2]'(by omega) + c6 * xs[m + 1]'(by omega) + c7 * xs[m]'(by omega)
    else dotA [c0, c1, c2, c3, c4, c5, c6, c7] xs (m + 7)
  | i => dotA [c0, c1, c2, c3, c4, c5, c6, c7] xs (i - 1)

/-- `predict` against the tail of the decoded prefix. -/
@[inline] def predictA (cs : List Int) (shift : Nat) (out : Array Int) : Int :=
  sar (dotAGo out cs out.size (Nat.le_refl _) 0) shift

/-- `restore` with the residual (and result) as arrays: the array is both
    the accumulating output and the prediction history. Callers guarantee
    `cs.length ≤ warmup.length` (the subframe grammar always does). The
    per-sample wrap is two comparisons on the in-range path — noise next
    to the prediction dot product. -/
def restoreA (b : Nat) (cs : List Int) (shift : Nat) (warmup : List Int) (res : Array Int) :
    Array Int :=
  res.foldl (fun out r => out.push (Bits.wrapSInt b (r + predictA cs shift out)))
    ((Array.emptyWithCapacity (warmup.length + res.size)) ++ warmup.toArray)

/-! ### The machine-word restore kernel

`restoreA` above is what the theorems read; what the decoder *runs* is
`restoreFast` below, swapped in by `restoreA_eq_restoreFast` (`@[csimp]`).

The boxed fold costs ~660 instructions per sample at order 8: every tap is
a tagged `Int` multiply-add with a 32-bit range check, the shift is a
`match` on the `Int` constructor, and the wrap compares boxed values. On
24-bit audio every tap product leaves the scalar range and allocates a
bignum.

The kernel does the same arithmetic on `Int64`. It is exact wherever the
*true* prediction sum fits a machine word, which the guard
(`RestoreFastOk`) secures once per subframe: at most 32 taps, coefficients
below `2^15` in magnitude, warmup samples below `2^33`, and every restored
sample wrapped to at most 33 bits — so `|Σ cᵢ·xᵢ| < 2^53`. Intermediate
overflow is harmless: `Int64` is exact arithmetic mod `2^64`, so only the
final sum has to fit (`dot64_toInt`).

The residual is *not* bounded (a Rice quotient is attacker-controlled), and
neither is `r + p`. The kernel adds the residual mod `2^64` and tests the
result against `∓2^(b-1)`: in range, it *is* the wrap (`wrapSInt` is the
balanced residue mod `2^b`, and `2^b ∣ 2^64`); out of range — never on a
stream the encoder wrote — it hands the exact `Int` sum to `wrapSInt`.
Everything outside the guard runs the boxed fold unchanged.

Orders 1–12 get straight-line steps with the taps as unboxed parameters and
the history read at fixed `USize` offsets (`restoreStep{K}`); the generic
`restoreStep` walks the tap list. The output array size is bounded by the
guard (`< 2^32`) so the `USize` index arithmetic is exact. -/

/-- `dotAGo` on machine words: the same walk, `acc + c * out[n]` in `Int64`.
    Its value is the exact sum reduced mod `2^64` (`dot64_toInt`). -/
def dot64 (out : Array Int) :
    (cs : List Int) → (n : Nat) → n ≤ out.size → Int64 → Int64
  | [], _, _, acc => acc
  | _ :: _, 0, _, acc => acc
  | c :: cs, n + 1, hn, acc =>
    have hi : n < out.size := Nat.lt_of_succ_le hn
    dot64 out cs n (Nat.le_of_lt hi) (acc + c.toInt64 * (out[n]).toInt64)

/-- One restored sample on machine words. `sh` is the quantization shift,
    `negP`/`P` the wrap bounds `∓2^(b-1)`, all hoisted by the caller. -/
@[inline] def restoreStep (b : Nat) (cs : List Int) (sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  let p := dot64 out cs out.size (Nat.le_refl _) 0 >>> sh
  let x := r.toInt64 + p
  if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)

/-- `i < out.usize` puts `i` inside the array on every platform: the
    machine-word size is the true size reduced mod the word, never more. -/
theorem toNat_lt_of_lt_usize {out : Array Int} {i : USize} (h : i < out.usize) :
    i.toNat < out.size := by
  have := USize.lt_iff_toNat_lt.1 h
  simp only [Array.usize, Nat.toUSize_eq, USize.toNat_ofNat'] at this
  exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)

/-- History sample `out[i]` as a machine word, read behind a word-sized
    bounds test (`histAt_eq`), so the specialised steps carry no index
    proofs at every tap. -/
@[inline] def histAt (out : Array Int) (i : USize) : Int64 :=
  if h : i < out.usize then (out.uget i (toNat_lt_of_lt_usize h)).toInt64 else 0

/-- `restoreStep` at 1 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep1_eq`. -/
@[inline] def restoreStep1 (b : Nat) (c0 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 1 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 1
    let p := (c0 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt] sh negP P out r

/-- The fold at 1 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold1 (b : Nat) (c0 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep1 b c0 sh negP P out r)) init

/-- `restoreStep` at 2 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep2_eq`. -/
@[inline] def restoreStep2 (b : Nat) (c0 c1 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 2 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 2
    let p := (c0 * histAt out (m + USize.ofNat 1) + c1 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt] sh negP P out r

/-- The fold at 2 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold2 (b : Nat) (c0 c1 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep2 b c0 c1 sh negP P out r)) init

/-- `restoreStep` at 3 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep3_eq`. -/
@[inline] def restoreStep3 (b : Nat) (c0 c1 c2 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 3 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 3
    let p := (c0 * histAt out (m + USize.ofNat 2) + c1 * histAt out (m + USize.ofNat 1) + c2 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt] sh negP P out r

/-- The fold at 3 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold3 (b : Nat) (c0 c1 c2 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep3 b c0 c1 c2 sh negP P out r)) init

/-- `restoreStep` at 4 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep4_eq`. -/
@[inline] def restoreStep4 (b : Nat) (c0 c1 c2 c3 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 4 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 4
    let p := (c0 * histAt out (m + USize.ofNat 3) + c1 * histAt out (m + USize.ofNat 2) + c2 * histAt out (m + USize.ofNat 1) + c3 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt] sh negP P out r

/-- The fold at 4 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold4 (b : Nat) (c0 c1 c2 c3 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep4 b c0 c1 c2 c3 sh negP P out r)) init

/-- `restoreStep` at 5 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep5_eq`. -/
@[inline] def restoreStep5 (b : Nat) (c0 c1 c2 c3 c4 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 5 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 5
    let p := (c0 * histAt out (m + USize.ofNat 4) + c1 * histAt out (m + USize.ofNat 3) + c2 * histAt out (m + USize.ofNat 2) + c3 * histAt out (m + USize.ofNat 1) + c4 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt] sh negP P out r

/-- The fold at 5 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold5 (b : Nat) (c0 c1 c2 c3 c4 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep5 b c0 c1 c2 c3 c4 sh negP P out r)) init

/-- `restoreStep` at 6 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep6_eq`. -/
@[inline] def restoreStep6 (b : Nat) (c0 c1 c2 c3 c4 c5 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 6 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 6
    let p := (c0 * histAt out (m + USize.ofNat 5) + c1 * histAt out (m + USize.ofNat 4) + c2 * histAt out (m + USize.ofNat 3) + c3 * histAt out (m + USize.ofNat 2) + c4 * histAt out (m + USize.ofNat 1) + c5 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt] sh negP P out r

/-- The fold at 6 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold6 (b : Nat) (c0 c1 c2 c3 c4 c5 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep6 b c0 c1 c2 c3 c4 c5 sh negP P out r)) init

/-- `restoreStep` at 7 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep7_eq`. -/
@[inline] def restoreStep7 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 7 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 7
    let p := (c0 * histAt out (m + USize.ofNat 6) + c1 * histAt out (m + USize.ofNat 5) + c2 * histAt out (m + USize.ofNat 4) + c3 * histAt out (m + USize.ofNat 3) + c4 * histAt out (m + USize.ofNat 2) + c5 * histAt out (m + USize.ofNat 1) + c6 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt, c6.toInt] sh negP P out r

/-- The fold at 7 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold7 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep7 b c0 c1 c2 c3 c4 c5 c6 sh negP P out r)) init

/-- `restoreStep` at 8 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep8_eq`. -/
@[inline] def restoreStep8 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 8 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 8
    let p := (c0 * histAt out (m + USize.ofNat 7) + c1 * histAt out (m + USize.ofNat 6) + c2 * histAt out (m + USize.ofNat 5) + c3 * histAt out (m + USize.ofNat 4) + c4 * histAt out (m + USize.ofNat 3) + c5 * histAt out (m + USize.ofNat 2) + c6 * histAt out (m + USize.ofNat 1) + c7 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt, c6.toInt, c7.toInt] sh negP P out r

/-- The fold at 8 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold8 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P out r)) init

/-- `restoreStep` at 9 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep9_eq`. -/
@[inline] def restoreStep9 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 9 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 9
    let p := (c0 * histAt out (m + USize.ofNat 8) + c1 * histAt out (m + USize.ofNat 7) + c2 * histAt out (m + USize.ofNat 6) + c3 * histAt out (m + USize.ofNat 5) + c4 * histAt out (m + USize.ofNat 4) + c5 * histAt out (m + USize.ofNat 3) + c6 * histAt out (m + USize.ofNat 2) + c7 * histAt out (m + USize.ofNat 1) + c8 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt, c6.toInt, c7.toInt, c8.toInt] sh negP P out r

/-- The fold at 9 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold9 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P out r)) init

/-- `restoreStep` at 10 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep10_eq`. -/
@[inline] def restoreStep10 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 10 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 10
    let p := (c0 * histAt out (m + USize.ofNat 9) + c1 * histAt out (m + USize.ofNat 8) + c2 * histAt out (m + USize.ofNat 7) + c3 * histAt out (m + USize.ofNat 6) + c4 * histAt out (m + USize.ofNat 5) + c5 * histAt out (m + USize.ofNat 4) + c6 * histAt out (m + USize.ofNat 3) + c7 * histAt out (m + USize.ofNat 2) + c8 * histAt out (m + USize.ofNat 1) + c9 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt, c6.toInt, c7.toInt, c8.toInt, c9.toInt] sh negP P out r

/-- The fold at 10 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold10 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P out r)) init

/-- `restoreStep` at 11 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep11_eq`. -/
@[inline] def restoreStep11 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 11 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 11
    let p := (c0 * histAt out (m + USize.ofNat 10) + c1 * histAt out (m + USize.ofNat 9) + c2 * histAt out (m + USize.ofNat 8) + c3 * histAt out (m + USize.ofNat 7) + c4 * histAt out (m + USize.ofNat 6) + c5 * histAt out (m + USize.ofNat 5) + c6 * histAt out (m + USize.ofNat 4) + c7 * histAt out (m + USize.ofNat 3) + c8 * histAt out (m + USize.ofNat 2) + c9 * histAt out (m + USize.ofNat 1) + c10 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt, c6.toInt, c7.toInt, c8.toInt, c9.toInt, c10.toInt] sh negP P out r

/-- The fold at 11 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold11 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P out r)) init

/-- `restoreStep` at 12 taps held as machine words: the history reads are
    independent loads at fixed offsets from the end of `out`. Equal to
    `restoreStep` at `[c0, …]` by `restoreStep12_eq`. -/
@[inline] def restoreStep12 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P : Int64)
    (out : Array Int) (r : Int) : Int :=
  if 12 ≤ out.size then
    let m : USize := out.size.toUSize - USize.ofNat 12
    let p := (c0 * histAt out (m + USize.ofNat 11) + c1 * histAt out (m + USize.ofNat 10) + c2 * histAt out (m + USize.ofNat 9) + c3 * histAt out (m + USize.ofNat 8) + c4 * histAt out (m + USize.ofNat 7) + c5 * histAt out (m + USize.ofNat 6) + c6 * histAt out (m + USize.ofNat 5) + c7 * histAt out (m + USize.ofNat 4) + c8 * histAt out (m + USize.ofNat 3) + c9 * histAt out (m + USize.ofNat 2) + c10 * histAt out (m + USize.ofNat 1) + c11 * histAt out m) >>> sh
    let x := r.toInt64 + p
    if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
  else restoreStep b [c0.toInt, c1.toInt, c2.toInt, c3.toInt, c4.toInt, c5.toInt, c6.toInt, c7.toInt, c8.toInt, c9.toInt, c10.toInt, c11.toInt] sh negP P out r

/-- The fold at 12 taps. A separate definition so the taps reach the loop
    as unboxed machine words (a closure would re-unbox them per sample). -/
def restoreFold12 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P : Int64) (res init : Array Int) : Array Int :=
  res.foldl (fun out r => out.push (restoreStep12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P out r)) init

/-! ### The history in registers

`restoreFold{K}` reads the `K` history taps back out of the output array on
every sample — a bounds check, a load and an `Int64` conversion per tap.
`restoreWin{K}` carries the last `K` outputs as machine-word parameters
(oldest first) and shifts them along, so a sample costs one residual load,
one conversion and the multiply-adds. `restoreRoll{K}` loads the window from
the warmup and hands short warmups to the fold. Equal to the fold by
`restoreRoll{K}_eq_fold`.

Orders 1–12 are all worth specialising, which is not obvious from the
per-order micro numbers (2.6 / 2.9 / 3.5 / 4.3 ns at orders 1 / 4 / 8 / 12 —
order 12 looks only marginally worse than order 8). Those compare
specialisations with each other; the alternative is the generic
`restoreStep` walk, and it is much slower. Dropping 9–12 to it costs **1.71×**
on an order-12 stream and **1.40×** on `flac -8` material, whose orders run up
to 12. Twelve is where libFLAC's `-8` stops, so this is the common case, not
an edge. -/

/-- `restoreFold1` with the last 1 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 1
    history loads. -/
def restoreWin1 (b : Nat) (c0 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin1 b c0 sh negP P res (i + 1) v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll1 (b : Nat) (c0 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 1 ≤ init.size then
    restoreWin1 b c0 sh negP P res 0 (init.getD (init.size - 1) 0).toInt64 init
  else restoreFold1 b c0 sh negP P res init

/-- `restoreFold2` with the last 2 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 2
    history loads. -/
def restoreWin2 (b : Nat) (c0 c1 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h1 + c1 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin2 b c0 c1 sh negP P res (i + 1) h1 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll2 (b : Nat) (c0 c1 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 2 ≤ init.size then
    restoreWin2 b c0 c1 sh negP P res 0 (init.getD (init.size - 2) 0).toInt64 (init.getD (init.size - 2 + 1) 0).toInt64 init
  else restoreFold2 b c0 c1 sh negP P res init

/-- `restoreFold3` with the last 3 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 3
    history loads. -/
def restoreWin3 (b : Nat) (c0 c1 c2 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h2 + c1 * h1 + c2 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin3 b c0 c1 c2 sh negP P res (i + 1) h1 h2 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll3 (b : Nat) (c0 c1 c2 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 3 ≤ init.size then
    restoreWin3 b c0 c1 c2 sh negP P res 0 (init.getD (init.size - 3) 0).toInt64 (init.getD (init.size - 3 + 1) 0).toInt64 (init.getD (init.size - 3 + 2) 0).toInt64 init
  else restoreFold3 b c0 c1 c2 sh negP P res init

/-- `restoreFold4` with the last 4 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 4
    history loads. -/
def restoreWin4 (b : Nat) (c0 c1 c2 c3 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h3 + c1 * h2 + c2 * h1 + c3 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin4 b c0 c1 c2 c3 sh negP P res (i + 1) h1 h2 h3 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll4 (b : Nat) (c0 c1 c2 c3 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 4 ≤ init.size then
    restoreWin4 b c0 c1 c2 c3 sh negP P res 0 (init.getD (init.size - 4) 0).toInt64 (init.getD (init.size - 4 + 1) 0).toInt64 (init.getD (init.size - 4 + 2) 0).toInt64 (init.getD (init.size - 4 + 3) 0).toInt64 init
  else restoreFold4 b c0 c1 c2 c3 sh negP P res init

/-- `restoreFold5` with the last 5 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 5
    history loads. -/
def restoreWin5 (b : Nat) (c0 c1 c2 c3 c4 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h4 + c1 * h3 + c2 * h2 + c3 * h1 + c4 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin5 b c0 c1 c2 c3 c4 sh negP P res (i + 1) h1 h2 h3 h4 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll5 (b : Nat) (c0 c1 c2 c3 c4 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 5 ≤ init.size then
    restoreWin5 b c0 c1 c2 c3 c4 sh negP P res 0 (init.getD (init.size - 5) 0).toInt64 (init.getD (init.size - 5 + 1) 0).toInt64 (init.getD (init.size - 5 + 2) 0).toInt64 (init.getD (init.size - 5 + 3) 0).toInt64 (init.getD (init.size - 5 + 4) 0).toInt64 init
  else restoreFold5 b c0 c1 c2 c3 c4 sh negP P res init

/-- `restoreFold6` with the last 6 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 6
    history loads. -/
def restoreWin6 (b : Nat) (c0 c1 c2 c3 c4 c5 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h5 + c1 * h4 + c2 * h3 + c3 * h2 + c4 * h1 + c5 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin6 b c0 c1 c2 c3 c4 c5 sh negP P res (i + 1) h1 h2 h3 h4 h5 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll6 (b : Nat) (c0 c1 c2 c3 c4 c5 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 6 ≤ init.size then
    restoreWin6 b c0 c1 c2 c3 c4 c5 sh negP P res 0 (init.getD (init.size - 6) 0).toInt64 (init.getD (init.size - 6 + 1) 0).toInt64 (init.getD (init.size - 6 + 2) 0).toInt64 (init.getD (init.size - 6 + 3) 0).toInt64 (init.getD (init.size - 6 + 4) 0).toInt64 (init.getD (init.size - 6 + 5) 0).toInt64 init
  else restoreFold6 b c0 c1 c2 c3 c4 c5 sh negP P res init

/-- `restoreFold7` with the last 7 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 7
    history loads. -/
def restoreWin7 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 h6 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h6 + c1 * h5 + c2 * h4 + c3 * h3 + c4 * h2 + c5 * h1 + c6 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll7 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 7 ≤ init.size then
    restoreWin7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res 0 (init.getD (init.size - 7) 0).toInt64 (init.getD (init.size - 7 + 1) 0).toInt64 (init.getD (init.size - 7 + 2) 0).toInt64 (init.getD (init.size - 7 + 3) 0).toInt64 (init.getD (init.size - 7 + 4) 0).toInt64 (init.getD (init.size - 7 + 5) 0).toInt64 (init.getD (init.size - 7 + 6) 0).toInt64 init
  else restoreFold7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res init

/-- `restoreFold8` with the last 8 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 8
    history loads. -/
def restoreWin8 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 h6 h7 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h7 + c1 * h6 + c2 * h5 + c3 * h4 + c4 * h3 + c5 * h2 + c6 * h1 + c7 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll8 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 8 ≤ init.size then
    restoreWin8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res 0 (init.getD (init.size - 8) 0).toInt64 (init.getD (init.size - 8 + 1) 0).toInt64 (init.getD (init.size - 8 + 2) 0).toInt64 (init.getD (init.size - 8 + 3) 0).toInt64 (init.getD (init.size - 8 + 4) 0).toInt64 (init.getD (init.size - 8 + 5) 0).toInt64 (init.getD (init.size - 8 + 6) 0).toInt64 (init.getD (init.size - 8 + 7) 0).toInt64 init
  else restoreFold8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res init

/-- `restoreFold9` with the last 9 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 9
    history loads. -/
def restoreWin9 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h8 + c1 * h7 + c2 * h6 + c3 * h5 + c4 * h4 + c5 * h3 + c6 * h2 + c7 * h1 + c8 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll9 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 9 ≤ init.size then
    restoreWin9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res 0 (init.getD (init.size - 9) 0).toInt64 (init.getD (init.size - 9 + 1) 0).toInt64 (init.getD (init.size - 9 + 2) 0).toInt64 (init.getD (init.size - 9 + 3) 0).toInt64 (init.getD (init.size - 9 + 4) 0).toInt64 (init.getD (init.size - 9 + 5) 0).toInt64 (init.getD (init.size - 9 + 6) 0).toInt64 (init.getD (init.size - 9 + 7) 0).toInt64 (init.getD (init.size - 9 + 8) 0).toInt64 init
  else restoreFold9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res init

/-- `restoreFold10` with the last 10 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 10
    history loads. -/
def restoreWin10 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h9 + c1 * h8 + c2 * h7 + c3 * h6 + c4 * h5 + c5 * h4 + c6 * h3 + c7 * h2 + c8 * h1 + c9 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll10 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 10 ≤ init.size then
    restoreWin10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res 0 (init.getD (init.size - 10) 0).toInt64 (init.getD (init.size - 10 + 1) 0).toInt64 (init.getD (init.size - 10 + 2) 0).toInt64 (init.getD (init.size - 10 + 3) 0).toInt64 (init.getD (init.size - 10 + 4) 0).toInt64 (init.getD (init.size - 10 + 5) 0).toInt64 (init.getD (init.size - 10 + 6) 0).toInt64 (init.getD (init.size - 10 + 7) 0).toInt64 (init.getD (init.size - 10 + 8) 0).toInt64 (init.getD (init.size - 10 + 9) 0).toInt64 init
  else restoreFold10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res init

/-- `restoreFold11` with the last 11 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 11
    history loads. -/
def restoreWin11 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h10 + c1 * h9 + c2 * h8 + c3 * h7 + c4 * h6 + c5 * h5 + c6 * h4 + c7 * h3 + c8 * h2 + c9 * h1 + c10 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll11 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 11 ≤ init.size then
    restoreWin11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res 0 (init.getD (init.size - 11) 0).toInt64 (init.getD (init.size - 11 + 1) 0).toInt64 (init.getD (init.size - 11 + 2) 0).toInt64 (init.getD (init.size - 11 + 3) 0).toInt64 (init.getD (init.size - 11 + 4) 0).toInt64 (init.getD (init.size - 11 + 5) 0).toInt64 (init.getD (init.size - 11 + 6) 0).toInt64 (init.getD (init.size - 11 + 7) 0).toInt64 (init.getD (init.size - 11 + 8) 0).toInt64 (init.getD (init.size - 11 + 9) 0).toInt64 (init.getD (init.size - 11 + 10) 0).toInt64 init
  else restoreFold11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res init

/-- `restoreFold12` with the last 12 outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of 12
    history loads. -/
def restoreWin12 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P : Int64) (res : Array Int) (i : Nat)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := (c0 * h11 + c1 * h10 + c2 * h9 + c3 * h8 + c4 * h7 + c5 * h6 + c6 * h5 + c7 * h4 + c8 * h3 + c9 * h2 + c10 * h1 + c11 * h0) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 v.toInt64 (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll12 (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P : Int64) (res init : Array Int) : Array Int :=
  if 12 ≤ init.size then
    restoreWin12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res 0 (init.getD (init.size - 12) 0).toInt64 (init.getD (init.size - 12 + 1) 0).toInt64 (init.getD (init.size - 12 + 2) 0).toInt64 (init.getD (init.size - 12 + 3) 0).toInt64 (init.getD (init.size - 12 + 4) 0).toInt64 (init.getD (init.size - 12 + 5) 0).toInt64 (init.getD (init.size - 12 + 6) 0).toInt64 (init.getD (init.size - 12 + 7) 0).toInt64 (init.getD (init.size - 12 + 8) 0).toInt64 (init.getD (init.size - 12 + 9) 0).toInt64 (init.getD (init.size - 12 + 10) 0).toInt64 (init.getD (init.size - 12 + 11) 0).toInt64 init
  else restoreFold12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res init

/-- The domain on which the kernel is exact (decided once per subframe). -/
def RestoreFastOk (b : Nat) (cs : List Int) (shift : Nat) (warmup : List Int)
    (res : Array Int) : Prop :=
  0 < b ∧ b ≤ 33 ∧ shift < 64 ∧ cs.length ≤ 32 ∧ warmup.length + res.size < Bits.p2 32 ∧
    (∀ c ∈ cs, Bits.FitsSInt 16 c) ∧ (∀ w ∈ warmup, Bits.FitsSInt 34 w)

instance (b : Nat) (cs : List Int) (shift : Nat) (warmup : List Int) (res : Array Int) :
    Decidable (RestoreFastOk b cs shift warmup res) := by
  unfold RestoreFastOk; exact inferInstance

/-- `restoreA` with the machine-word kernel on its domain. -/
def restoreFast (b : Nat) (cs : List Int) (shift : Nat) (warmup : List Int)
    (res : Array Int) : Array Int :=
  let init : Array Int := (Array.emptyWithCapacity (warmup.length + res.size)) ++ warmup.toArray
  if RestoreFastOk b cs shift warmup res then
    let P : Int64 := Int64.ofNat (Bits.p2 (b - 1))
    let negP : Int64 := -P
    let sh : Int64 := Int64.ofNat shift
    match cs with
    | [c0] => restoreRoll1 b c0.toInt64 sh negP P res init
    | [c0, c1] => restoreRoll2 b c0.toInt64 c1.toInt64 sh negP P res init
    | [c0, c1, c2] => restoreRoll3 b c0.toInt64 c1.toInt64 c2.toInt64 sh negP P res init
    | [c0, c1, c2, c3] => restoreRoll4 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4] => restoreRoll5 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5] => restoreRoll6 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5, c6] => restoreRoll7 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5, c6, c7] => restoreRoll8 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5, c6, c7, c8] => restoreRoll9 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] => restoreRoll10 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] => restoreRoll11 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 c10.toInt64 sh negP P res init
    | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] => restoreRoll12 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 c10.toInt64 c11.toInt64 sh negP P res init
    | _ => res.foldl (fun out r => out.push (restoreStep b cs sh negP P out r)) init
  else
    res.foldl (fun out r => out.push (Bits.wrapSInt b (r + predictA cs shift out))) init

/-! #### The kernel computes the fold -/

theorem dotAGo_acc (out : Array Int) :
    ∀ (cs : List Int) (n : Nat) (hn : n ≤ out.size) (acc : Int),
      dotAGo out cs n hn acc = acc + dotAGo out cs n hn 0 := by
  intro cs
  induction cs with
  | nil => intro n hn acc; simp [dotAGo]
  | cons c cs ih =>
    intro n hn acc
    match n with
    | 0 => simp [dotAGo]
    | n + 1 =>
      simp only [dotAGo]
      rw [ih n _ (acc + c * out[n]), ih n _ (0 + c * out[n])]
      omega

theorem dotAGo_unfold1 (out : Array Int) (c0 : Int) (m : Nat)
    (h : m + 1 ≤ out.size) (acc : Int) :
    dotAGo out [c0] (m + 1) h acc = acc + c0 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold2 (out : Array Int) (c0 c1 : Int) (m : Nat)
    (h : m + 2 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1] (m + 2) h acc = acc + c0 * out[m + 1]'(by omega) + c1 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold3 (out : Array Int) (c0 c1 c2 : Int) (m : Nat)
    (h : m + 3 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1, c2] (m + 3) h acc = acc + c0 * out[m + 2]'(by omega) + c1 * out[m + 1]'(by omega) + c2 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold4 (out : Array Int) (c0 c1 c2 c3 : Int) (m : Nat)
    (h : m + 4 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1, c2, c3] (m + 4) h acc = acc + c0 * out[m + 3]'(by omega) + c1 * out[m + 2]'(by omega) + c2 * out[m + 1]'(by omega) + c3 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold5 (out : Array Int) (c0 c1 c2 c3 c4 : Int) (m : Nat)
    (h : m + 5 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1, c2, c3, c4] (m + 5) h acc = acc + c0 * out[m + 4]'(by omega) + c1 * out[m + 3]'(by omega) + c2 * out[m + 2]'(by omega) + c3 * out[m + 1]'(by omega) + c4 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold6 (out : Array Int) (c0 c1 c2 c3 c4 c5 : Int) (m : Nat)
    (h : m + 6 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1, c2, c3, c4, c5] (m + 6) h acc = acc + c0 * out[m + 5]'(by omega) + c1 * out[m + 4]'(by omega) + c2 * out[m + 3]'(by omega) + c3 * out[m + 2]'(by omega) + c4 * out[m + 1]'(by omega) + c5 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold7 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 : Int) (m : Nat)
    (h : m + 7 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1, c2, c3, c4, c5, c6] (m + 7) h acc = acc + c0 * out[m + 6]'(by omega) + c1 * out[m + 5]'(by omega) + c2 * out[m + 4]'(by omega) + c3 * out[m + 3]'(by omega) + c4 * out[m + 2]'(by omega) + c5 * out[m + 1]'(by omega) + c6 * out[m]'(by omega) := by
  simp only [dotAGo]

theorem dotAGo_unfold8 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (m : Nat)
    (h : m + 8 ≤ out.size) (acc : Int) :
    dotAGo out [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) h acc = acc + c0 * out[m + 7]'(by omega) + c1 * out[m + 6]'(by omega) + c2 * out[m + 5]'(by omega) + c3 * out[m + 4]'(by omega) + c4 * out[m + 3]'(by omega) + c5 * out[m + 2]'(by omega) + c6 * out[m + 1]'(by omega) + c7 * out[m]'(by omega) := by
  simp only [dotAGo]

/-- `|Σ| ≤ taps · 2^48` on the guarded domain. -/
theorem dotAGo_bound (out : Array Int) (hout : ∀ x ∈ out, Bits.FitsSInt 34 x) :
    ∀ (cs : List Int) (n : Nat) (hn : n ≤ out.size) (acc : Int),
      (∀ c ∈ cs, Bits.FitsSInt 16 c) →
      (dotAGo out cs n hn acc).natAbs ≤ acc.natAbs + cs.length * 2 ^ 48 := by
  intro cs
  induction cs with
  | nil => intro n hn acc _; simp [dotAGo]
  | cons c cs ih =>
    intro n hn acc hc
    match n with
    | 0 => simp [dotAGo]
    | n + 1 =>
      simp only [dotAGo]
      have hi : n < out.size := Nat.lt_of_succ_le hn
      have hx := hout out[n] (Array.getElem_mem hi)
      have hcc := hc c (List.mem_cons_self ..)
      have hprod : (c * out[n]).natAbs ≤ 2 ^ 48 := by
        rw [Int.natAbs_mul]
        have h1 : c.natAbs ≤ 2 ^ 15 := by
          obtain ⟨a, b⟩ := hcc
          simp only [Nat.reducePow] at a b ⊢
          omega
        have h2 : (out[n]).natAbs ≤ 2 ^ 33 := by
          obtain ⟨a, b⟩ := hx
          simp only [Nat.reducePow] at a b ⊢
          omega
        calc c.natAbs * (out[n]).natAbs ≤ 2 ^ 15 * 2 ^ 33 := Nat.mul_le_mul h1 h2
          _ = 2 ^ 48 := by decide
      have := ih n (Nat.le_of_lt hi) (acc + c * out[n]) (fun d hd => hc d (List.mem_cons_of_mem _ hd))
      have hadd := Int.natAbs_add_le acc (c * out[n])
      simp only [List.length_cons]
      have : (cs.length + 1) * 2 ^ 48 = cs.length * 2 ^ 48 + 2 ^ 48 := by
        rw [Nat.succ_mul]
      omega

/-- `dotAGo_bound` needing only the samples the walk reads. -/
theorem dotAGo_bound_range (out : Array Int) :
    ∀ (cs : List Int) (n : Nat) (hn : n ≤ out.size) (acc : Int),
      (∀ c ∈ cs, Bits.FitsSInt 16 c) →
      (∀ (j : Nat) (hj : j < out.size), n ≤ j + cs.length → j < n → Bits.FitsSInt 34 out[j]) →
      (dotAGo out cs n hn acc).natAbs ≤ acc.natAbs + cs.length * 2 ^ 48 := by
  intro cs
  induction cs with
  | nil => intro n hn acc _ _; simp [dotAGo]
  | cons c cs ih =>
    intro n hn acc hc hout
    match n with
    | 0 => simp [dotAGo]
    | n + 1 =>
      simp only [dotAGo]
      have hi : n < out.size := Nat.lt_of_succ_le hn
      have hx := hout n hi (by simp) (by omega)
      have hcc := hc c (List.mem_cons_self ..)
      have hprod : (c * out[n]).natAbs ≤ 2 ^ 48 := by
        rw [Int.natAbs_mul]
        have h1 : c.natAbs ≤ 2 ^ 15 := by
          obtain ⟨a, b⟩ := hcc
          simp only [Nat.reducePow] at a b ⊢
          omega
        have h2 : (out[n]).natAbs ≤ 2 ^ 33 := by
          obtain ⟨a, b⟩ := hx
          simp only [Nat.reducePow] at a b ⊢
          omega
        calc c.natAbs * (out[n]).natAbs ≤ 2 ^ 15 * 2 ^ 33 := Nat.mul_le_mul h1 h2
          _ = 2 ^ 48 := by decide
      have := ih n (Nat.le_of_lt hi) (acc + c * out[n]) (fun d hd => hc d (List.mem_cons_of_mem _ hd))
        (fun j hj h1 h2 => hout j hj (by simp only [List.length_cons]; omega) (by omega))
      have hadd := Int.natAbs_add_le acc (c * out[n])
      simp only [List.length_cons]
      have : (cs.length + 1) * 2 ^ 48 = cs.length * 2 ^ 48 + 2 ^ 48 := by
        rw [Nat.succ_mul]
      omega

/-- `dot64_toInt` needing only the samples the walk reads. -/
theorem dot64_toInt_range (out : Array Int) :
    ∀ (cs : List Int) (n : Nat) (hn : n ≤ out.size) (acc : Int64),
      (∀ c ∈ cs, Bits.FitsSInt 16 c) →
      (∀ (j : Nat) (hj : j < out.size), n ≤ j + cs.length → j < n → Bits.FitsSInt 34 out[j]) →
      (dot64 out cs n hn acc).toInt = (acc.toInt + dotAGo out cs n hn 0).bmod (2 ^ 64) := by
  intro cs
  induction cs with
  | nil =>
    intro n hn acc _ _
    simp [dot64, dotAGo]
  | cons c cs ih =>
    intro n hn acc hc hout
    match n with
    | 0 => simp [dot64, dotAGo]
    | n + 1 =>
      simp only [dot64, dotAGo]
      have hi : n < out.size := Nat.lt_of_succ_le hn
      rw [ih n _ _ (fun d hd => hc d (List.mem_cons_of_mem _ hd))
          (fun j hj h1 h2 => hout j hj (by simp only [List.length_cons]; omega) (by omega)),
        dotAGo_acc out cs n _ (0 + c * out[n]),
        Int64.toInt_add, Int64.toInt_mul,
        Bits.toInt_toInt64_of_fits16 (hc c (List.mem_cons_self ..)),
        Bits.toInt_toInt64_of_fits34 (hout n hi (by simp) (by omega)),
        Int.add_bmod_bmod, Int.bmod_add_bmod, Int.zero_add, Int.add_assoc]

/-- The machine-word walk is the exact walk reduced mod `2^64`. -/
theorem dot64_toInt (out : Array Int) (hout : ∀ x ∈ out, Bits.FitsSInt 34 x) :
    ∀ (cs : List Int) (n : Nat) (hn : n ≤ out.size) (acc : Int64),
      (∀ c ∈ cs, Bits.FitsSInt 16 c) →
      (dot64 out cs n hn acc).toInt = (acc.toInt + dotAGo out cs n hn 0).bmod (2 ^ 64) := by
  intro cs
  induction cs with
  | nil =>
    intro n hn acc _
    simp [dot64, dotAGo]
  | cons c cs ih =>
    intro n hn acc hc
    match n with
    | 0 => simp [dot64, dotAGo]
    | n + 1 =>
      simp only [dot64, dotAGo]
      have hi : n < out.size := Nat.lt_of_succ_le hn
      rw [ih n _ _ (fun d hd => hc d (List.mem_cons_of_mem _ hd)),
        dotAGo_acc out cs n _ (0 + c * out[n]),
        Int64.toInt_add, Int64.toInt_mul,
        Bits.toInt_toInt64_of_fits16 (hc c (List.mem_cons_self ..)),
        Bits.toInt_toInt64_of_fits34 (hout out[n] (Array.getElem_mem hi)),
        Int.add_bmod_bmod, Int.bmod_add_bmod, Int.zero_add, Int.add_assoc]

/-- The generic step is the fold's step on the guarded domain. -/
theorem restoreStep_eq (b : Nat) (cs : List Int) (shift : Nat) (out : Array Int) (r : Int)
    (hb0 : 0 < b) (hb : b ≤ 33) (hsh : shift < 64) (hlen : cs.length ≤ 32)
    (hc : ∀ c ∈ cs, Bits.FitsSInt 16 c) (hout : ∀ x ∈ out, Bits.FitsSInt 34 x) :
    restoreStep b cs (Int64.ofNat shift) (-(Int64.ofNat (Bits.p2 (b - 1))))
        (Int64.ofNat (Bits.p2 (b - 1))) out r
      = Bits.wrapSInt b (r + predictA cs shift out) := by
  have hbound := dotAGo_bound out hout cs out.size (Nat.le_refl _) 0 hc
  have hlen' : cs.length * 2 ^ 48 ≤ 2 ^ 53 := by
    calc cs.length * 2 ^ 48 ≤ 32 * 2 ^ 48 := Nat.mul_le_mul_right _ hlen
      _ = 2 ^ 53 := by decide
  have hd : (dot64 out cs out.size (Nat.le_refl _) 0).toInt
      = dotAGo out cs out.size (Nat.le_refl _) 0 := by
    rw [dot64_toInt out hout cs out.size (Nat.le_refl _) 0 hc]
    simp only [Int64.toInt_zero, Int.zero_add]
    apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow] at hbound hlen' ⊢ <;> omega
  have hp : (dot64 out cs out.size (Nat.le_refl _) 0 >>> Int64.ofNat shift).toInt
      = Bits.sar (dotAGo out cs out.size (Nat.le_refl _) 0) shift := by
    rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hd, Bits.sar_eq_shiftRight]
  have hpow : Bits.p2 (b - 1) < 2 ^ 63 := by
    rw [Bits.p2_eq]
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (show b - 1 ≤ 32 by omega)) (by decide)
  have hPv : (Int64.ofNat (Bits.p2 (b - 1))).toInt = ((Bits.p2 (b - 1) : Nat) : Int) :=
    Int64.toInt_ofNat_of_lt hpow
  have hnegP : (-(Int64.ofNat (Bits.p2 (b - 1)))).toInt = -((Bits.p2 (b - 1) : Nat) : Int) :=
    Int64.toInt_neg_ofNat_of_le (Nat.le_of_lt hpow)
  have hsize : Int64.size = 2 ^ 64 := rfl
  have hx : (r.toInt64 + (dot64 out cs out.size (Nat.le_refl _) 0 >>> Int64.ofNat shift)).toInt
      = (r + Bits.sar (dotAGo out cs out.size (Nat.le_refl _) 0) shift).bmod (2 ^ 64) := by
    rw [Int64.toInt_add, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_add_bmod]
  unfold restoreStep predictA
  simp only []
  split
  · next hin =>
    obtain ⟨h1, h2⟩ := hin
    rw [Int64.le_iff_toInt_le, hnegP, hx] at h1
    rw [Int64.lt_iff_toInt_lt, hPv, hx] at h2
    rw [hx, Bits.wrapSInt_eq_bmod,
      ← Int.bmod_bmod_of_dvd (a := r + Bits.sar (dotAGo out cs out.size (Nat.le_refl _) 0) shift)
        (Nat.pow_dvd_pow 2 (show b ≤ 64 by omega))]
    symm
    have hb2 : (2 ^ b : Nat) = 2 * Bits.p2 (b - 1) := by
      rw [Bits.p2_eq, ← Nat.pow_succ']
      congr 1
      omega
    rw [hb2]
    generalize Bits.p2 (b - 1) = Q at h1 h2 ⊢
    apply Int.bmod_eq_of_le
    · have : ((2 * Q : Nat) : Int) / 2 = (Q : Int) := by omega
      omega
    · have : (((2 * Q : Nat) : Int) + 1) / 2 = (Q : Int) := by omega
      omega
  · rw [hp]

/-- Pointwise-equal step functions give equal push-folds, given a bound on
    the accumulator's size that the fold preserves. -/
private theorem foldl_push_congr (f g : Array Int → Int → Int) :
    ∀ (l : List Int) (init : Array Int) (bound : Nat), init.size + l.length ≤ bound →
      (∀ out r, out.size < bound → f out r = g out r) →
      l.foldl (fun out r => out.push (f out r)) init
        = l.foldl (fun out r => out.push (g out r)) init := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons r l ih =>
    intro init bound hsz hfg
    simp only [List.foldl_cons, List.length_cons] at hsz ⊢
    rw [hfg init r (by omega)]
    exact ih _ bound (by simp; omega) hfg

/-- The fold with the generic machine-word step is the boxed fold. -/
theorem foldl_restoreFast (b : Nat) (cs : List Int) (shift : Nat)
    (hb0 : 0 < b) (hb : b ≤ 33) (hsh : shift < 64) (hlen : cs.length ≤ 32)
    (hc : ∀ c ∈ cs, Bits.FitsSInt 16 c) :
    ∀ (l : List Int) (out : Array Int), (∀ x ∈ out, Bits.FitsSInt 34 x) →
      l.foldl (fun out r => out.push (restoreStep b cs (Int64.ofNat shift)
          (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))) out r)) out
        = l.foldl (fun out r => out.push (Bits.wrapSInt b (r + predictA cs shift out))) out := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons r l ih =>
    intro out hout
    rw [List.foldl_cons, List.foldl_cons, restoreStep_eq b cs shift out r hb0 hb hsh hlen hc hout]
    apply ih
    intro x hx
    rw [Array.mem_push] at hx
    rcases hx with hx | rfl
    · exact hout x hx
    · exact Bits.fitsSInt_mono (show b ≤ 34 by omega) (Bits.fitsSInt_wrapSInt b _)

/-- `USize` index arithmetic below `2^32` is exact on every platform. -/
theorem hist_index (n K j : Nat) (hK : K ≤ n) (hn : n < 4294967296) (hj : j < K) :
    (USize.ofNat n - USize.ofNat K + USize.ofNat j).toNat = n - K + j := by
  have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := by
    have := USize.le_size
    rwa [USize.size_eq_two_pow] at this
  have hK' : (USize.ofNat K).toNat = K := by
    rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hn' : (USize.ofNat n).toNat = n := by
    rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hj' : (USize.ofNat j).toNat = j := by
    rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hle : USize.ofNat K ≤ USize.ofNat n := USize.le_iff_toNat_le.2 (by omega)
  rw [USize.toNat_add, USize.toNat_sub_of_le _ _ hle, hn', hK', hj']
  exact Nat.mod_eq_of_lt (by omega)

theorem hist_index0 (n K : Nat) (hK : K ≤ n) (hn : n < 4294967296) :
    (USize.ofNat n - USize.ofNat K).toNat = n - K := by
  have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := by
    have := USize.le_size
    rwa [USize.size_eq_two_pow] at this
  have hK' : (USize.ofNat K).toNat = K := by
    rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hn' : (USize.ofNat n).toNat = n := by
    rw [USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hle : USize.ofNat K ≤ USize.ofNat n := USize.le_iff_toNat_le.2 (by omega)
  rw [USize.toNat_sub_of_le _ _ hle, hn', hK']

theorem histAt_eq (out : Array Int) (i : USize) (j : Nat) (hj : j < out.size)
    (hs : out.size < 4294967296) (hij : i.toNat = j) :
    histAt out i = (out[j]'hj).toInt64 := by
  have hs' : 4294967296 ≤ 2 ^ System.Platform.numBits := by
    have := USize.le_size
    rwa [USize.size_eq_two_pow] at this
  have hlt : i < out.usize := by
    rw [USize.lt_iff_toNat_lt, hij]
    simp only [Array.usize, Nat.toUSize_eq, USize.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hj
  unfold histAt
  rw [dif_pos hlt]
  subst hij
  rfl

theorem histAt_tap (out : Array Int) (n K j : Nat) (hK : K ≤ n) (hn : n ≤ out.size)
    (hs : out.size < 4294967296) (hj : j < K) :
    histAt out (n.toUSize - USize.ofNat K + USize.ofNat j)
      = (out[n - K + j]'(by omega)).toInt64 :=
  histAt_eq out _ _ _ hs (by
    simp only [Nat.toUSize_eq]
    exact hist_index n K j hK (by omega) hj)

theorem histAt_tap0 (out : Array Int) (n K : Nat) (hK : K ≤ n) (hn : n ≤ out.size)
    (hs : out.size < 4294967296) (hK0 : 0 < K) :
    histAt out (n.toUSize - USize.ofNat K) = (out[n - K]'(by omega)).toInt64 :=
  histAt_eq out _ _ _ hs (by
    simp only [Nat.toUSize_eq]
    exact hist_index0 n K hK (by omega))

theorem dot64_unfold1 (out : Array Int) (c0 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 1 ≤ n) (acc : Int64) :
    dot64 out [c0] n hn acc = acc + c0.toInt64 * (out[n - 1]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold2 (out : Array Int) (c0 c1 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 2 ≤ n) (acc : Int64) :
    dot64 out [c0, c1] n hn acc = acc + c0.toInt64 * (out[n - 2 + 1]'(by omega)).toInt64 + c1.toInt64 * (out[n - 2]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold3 (out : Array Int) (c0 c1 c2 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 3 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2] n hn acc = acc + c0.toInt64 * (out[n - 3 + 2]'(by omega)).toInt64 + c1.toInt64 * (out[n - 3 + 1]'(by omega)).toInt64 + c2.toInt64 * (out[n - 3]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold4 (out : Array Int) (c0 c1 c2 c3 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 4 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3] n hn acc = acc + c0.toInt64 * (out[n - 4 + 3]'(by omega)).toInt64 + c1.toInt64 * (out[n - 4 + 2]'(by omega)).toInt64 + c2.toInt64 * (out[n - 4 + 1]'(by omega)).toInt64 + c3.toInt64 * (out[n - 4]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold5 (out : Array Int) (c0 c1 c2 c3 c4 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 5 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4] n hn acc = acc + c0.toInt64 * (out[n - 5 + 4]'(by omega)).toInt64 + c1.toInt64 * (out[n - 5 + 3]'(by omega)).toInt64 + c2.toInt64 * (out[n - 5 + 2]'(by omega)).toInt64 + c3.toInt64 * (out[n - 5 + 1]'(by omega)).toInt64 + c4.toInt64 * (out[n - 5]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold6 (out : Array Int) (c0 c1 c2 c3 c4 c5 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 6 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5] n hn acc = acc + c0.toInt64 * (out[n - 6 + 5]'(by omega)).toInt64 + c1.toInt64 * (out[n - 6 + 4]'(by omega)).toInt64 + c2.toInt64 * (out[n - 6 + 3]'(by omega)).toInt64 + c3.toInt64 * (out[n - 6 + 2]'(by omega)).toInt64 + c4.toInt64 * (out[n - 6 + 1]'(by omega)).toInt64 + c5.toInt64 * (out[n - 6]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold7 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 7 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5, c6] n hn acc = acc + c0.toInt64 * (out[n - 7 + 6]'(by omega)).toInt64 + c1.toInt64 * (out[n - 7 + 5]'(by omega)).toInt64 + c2.toInt64 * (out[n - 7 + 4]'(by omega)).toInt64 + c3.toInt64 * (out[n - 7 + 3]'(by omega)).toInt64 + c4.toInt64 * (out[n - 7 + 2]'(by omega)).toInt64 + c5.toInt64 * (out[n - 7 + 1]'(by omega)).toInt64 + c6.toInt64 * (out[n - 7]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold8 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 8 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5, c6, c7] n hn acc = acc + c0.toInt64 * (out[n - 8 + 7]'(by omega)).toInt64 + c1.toInt64 * (out[n - 8 + 6]'(by omega)).toInt64 + c2.toInt64 * (out[n - 8 + 5]'(by omega)).toInt64 + c3.toInt64 * (out[n - 8 + 4]'(by omega)).toInt64 + c4.toInt64 * (out[n - 8 + 3]'(by omega)).toInt64 + c5.toInt64 * (out[n - 8 + 2]'(by omega)).toInt64 + c6.toInt64 * (out[n - 8 + 1]'(by omega)).toInt64 + c7.toInt64 * (out[n - 8]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold9 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 9 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5, c6, c7, c8] n hn acc = acc + c0.toInt64 * (out[n - 9 + 8]'(by omega)).toInt64 + c1.toInt64 * (out[n - 9 + 7]'(by omega)).toInt64 + c2.toInt64 * (out[n - 9 + 6]'(by omega)).toInt64 + c3.toInt64 * (out[n - 9 + 5]'(by omega)).toInt64 + c4.toInt64 * (out[n - 9 + 4]'(by omega)).toInt64 + c5.toInt64 * (out[n - 9 + 3]'(by omega)).toInt64 + c6.toInt64 * (out[n - 9 + 2]'(by omega)).toInt64 + c7.toInt64 * (out[n - 9 + 1]'(by omega)).toInt64 + c8.toInt64 * (out[n - 9]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold10 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 10 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] n hn acc = acc + c0.toInt64 * (out[n - 10 + 9]'(by omega)).toInt64 + c1.toInt64 * (out[n - 10 + 8]'(by omega)).toInt64 + c2.toInt64 * (out[n - 10 + 7]'(by omega)).toInt64 + c3.toInt64 * (out[n - 10 + 6]'(by omega)).toInt64 + c4.toInt64 * (out[n - 10 + 5]'(by omega)).toInt64 + c5.toInt64 * (out[n - 10 + 4]'(by omega)).toInt64 + c6.toInt64 * (out[n - 10 + 3]'(by omega)).toInt64 + c7.toInt64 * (out[n - 10 + 2]'(by omega)).toInt64 + c8.toInt64 * (out[n - 10 + 1]'(by omega)).toInt64 + c9.toInt64 * (out[n - 10]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold11 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 11 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] n hn acc = acc + c0.toInt64 * (out[n - 11 + 10]'(by omega)).toInt64 + c1.toInt64 * (out[n - 11 + 9]'(by omega)).toInt64 + c2.toInt64 * (out[n - 11 + 8]'(by omega)).toInt64 + c3.toInt64 * (out[n - 11 + 7]'(by omega)).toInt64 + c4.toInt64 * (out[n - 11 + 6]'(by omega)).toInt64 + c5.toInt64 * (out[n - 11 + 5]'(by omega)).toInt64 + c6.toInt64 * (out[n - 11 + 4]'(by omega)).toInt64 + c7.toInt64 * (out[n - 11 + 3]'(by omega)).toInt64 + c8.toInt64 * (out[n - 11 + 2]'(by omega)).toInt64 + c9.toInt64 * (out[n - 11 + 1]'(by omega)).toInt64 + c10.toInt64 * (out[n - 11]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

theorem dot64_unfold12 (out : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Int) (n : Nat)
    (hn : n ≤ out.size) (hK : 12 ≤ n) (acc : Int64) :
    dot64 out [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] n hn acc = acc + c0.toInt64 * (out[n - 12 + 11]'(by omega)).toInt64 + c1.toInt64 * (out[n - 12 + 10]'(by omega)).toInt64 + c2.toInt64 * (out[n - 12 + 9]'(by omega)).toInt64 + c3.toInt64 * (out[n - 12 + 8]'(by omega)).toInt64 + c4.toInt64 * (out[n - 12 + 7]'(by omega)).toInt64 + c5.toInt64 * (out[n - 12 + 6]'(by omega)).toInt64 + c6.toInt64 * (out[n - 12 + 5]'(by omega)).toInt64 + c7.toInt64 * (out[n - 12 + 4]'(by omega)).toInt64 + c8.toInt64 * (out[n - 12 + 3]'(by omega)).toInt64 + c9.toInt64 * (out[n - 12 + 2]'(by omega)).toInt64 + c10.toInt64 * (out[n - 12 + 1]'(by omega)).toInt64 + c11.toInt64 * (out[n - 12]'(by omega)).toInt64 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  simp only [dot64, Nat.add_sub_cancel, Nat.add_zero]

private theorem restoreStep1_eq (b : Nat) (c0 : Int)
    (hc : ∀ c ∈ [c0], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep1 b c0.toInt64 sh negP P out r
      = restoreStep b [c0] sh negP P out r := by
  unfold restoreStep1
  split
  · next hK =>
    dsimp only
    rw [histAt_tap0 out out.size 1 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold1 out c0 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp))]

private theorem restoreFold1_eq (b : Nat) (c0 : Int)
    (hc : ∀ c ∈ [c0], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold1 b c0.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0] sh negP P out r)) init := by
  unfold restoreFold1
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep1_eq b c0 hc sh negP P out hb r)

private theorem restoreStep2_eq (b : Nat) (c0 c1 : Int)
    (hc : ∀ c ∈ [c0, c1], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep2 b c0.toInt64 c1.toInt64 sh negP P out r
      = restoreStep b [c0, c1] sh negP P out r := by
  unfold restoreStep2
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 2 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 2 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold2 out c0 c1 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp))]

private theorem restoreFold2_eq (b : Nat) (c0 c1 : Int)
    (hc : ∀ c ∈ [c0, c1], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold2 b c0.toInt64 c1.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1] sh negP P out r)) init := by
  unfold restoreFold2
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep2_eq b c0 c1 hc sh negP P out hb r)

private theorem restoreStep3_eq (b : Nat) (c0 c1 c2 : Int)
    (hc : ∀ c ∈ [c0, c1, c2], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep3 b c0.toInt64 c1.toInt64 c2.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2] sh negP P out r := by
  unfold restoreStep3
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 3 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 3 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 3 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold3 out c0 c1 c2 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp))]

private theorem restoreFold3_eq (b : Nat) (c0 c1 c2 : Int)
    (hc : ∀ c ∈ [c0, c1, c2], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold3 b c0.toInt64 c1.toInt64 c2.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2] sh negP P out r)) init := by
  unfold restoreFold3
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep3_eq b c0 c1 c2 hc sh negP P out hb r)

private theorem restoreStep4_eq (b : Nat) (c0 c1 c2 c3 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep4 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3] sh negP P out r := by
  unfold restoreStep4
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 4 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 4 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 4 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 4 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold4 out c0 c1 c2 c3 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp))]

private theorem restoreFold4_eq (b : Nat) (c0 c1 c2 c3 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold4 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3] sh negP P out r)) init := by
  unfold restoreFold4
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep4_eq b c0 c1 c2 c3 hc sh negP P out hb r)

private theorem restoreStep5_eq (b : Nat) (c0 c1 c2 c3 c4 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep5 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4] sh negP P out r := by
  unfold restoreStep5
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 5 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 5 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 5 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 5 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 5 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold5 out c0 c1 c2 c3 c4 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp))]

private theorem restoreFold5_eq (b : Nat) (c0 c1 c2 c3 c4 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold5 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4] sh negP P out r)) init := by
  unfold restoreFold5
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep5_eq b c0 c1 c2 c3 c4 hc sh negP P out hb r)

private theorem restoreStep6_eq (b : Nat) (c0 c1 c2 c3 c4 c5 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep6 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5] sh negP P out r := by
  unfold restoreStep6
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 6 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 6 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 6 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 6 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 6 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 6 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold6 out c0 c1 c2 c3 c4 c5 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp))]

private theorem restoreFold6_eq (b : Nat) (c0 c1 c2 c3 c4 c5 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold6 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5] sh negP P out r)) init := by
  unfold restoreFold6
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep6_eq b c0 c1 c2 c3 c4 c5 hc sh negP P out hb r)

private theorem restoreStep7_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep7 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5, c6] sh negP P out r := by
  unfold restoreStep7
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 7 6 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 7 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 7 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 7 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 7 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 7 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 7 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold7 out c0 c1 c2 c3 c4 c5 c6 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c6 (by simp))]

private theorem restoreFold7_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold7 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5, c6] sh negP P out r)) init := by
  unfold restoreFold7
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep7_eq b c0 c1 c2 c3 c4 c5 c6 hc sh negP P out hb r)

private theorem restoreStep8_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep8 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7] sh negP P out r := by
  unfold restoreStep8
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 8 7 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 8 6 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 8 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 8 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 8 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 8 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 8 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 8 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold8 out c0 c1 c2 c3 c4 c5 c6 c7 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c6 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c7 (by simp))]

private theorem restoreFold8_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold8 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7] sh negP P out r)) init := by
  unfold restoreFold8
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep8_eq b c0 c1 c2 c3 c4 c5 c6 c7 hc sh negP P out hb r)

private theorem restoreStep9_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep9 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8] sh negP P out r := by
  unfold restoreStep9
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 9 8 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 7 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 6 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 9 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 9 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold9 out c0 c1 c2 c3 c4 c5 c6 c7 c8 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c6 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c7 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c8 (by simp))]

private theorem restoreFold9_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold9 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8] sh negP P out r)) init := by
  unfold restoreFold9
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep9_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 hc sh negP P out hb r)

private theorem restoreStep10_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep10 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] sh negP P out r := by
  unfold restoreStep10
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 10 9 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 8 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 7 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 6 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 10 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 10 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold10 out c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c6 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c7 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c8 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c9 (by simp))]

private theorem restoreFold10_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold10 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] sh negP P out r)) init := by
  unfold restoreFold10
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep10_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 hc sh negP P out hb r)

private theorem restoreStep11_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep11 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 c10.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] sh negP P out r := by
  unfold restoreStep11
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 11 10 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 9 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 8 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 7 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 6 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 11 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 11 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold11 out c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c6 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c7 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c8 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c9 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c10 (by simp))]

private theorem restoreFold11_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold11 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 c10.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10] sh negP P out r)) init := by
  unfold restoreFold11
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep11_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 hc sh negP P out hb r)

private theorem restoreStep12_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (out : Array Int) (hs : out.size < 4294967296) (r : Int) :
    restoreStep12 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 c10.toInt64 c11.toInt64 sh negP P out r
      = restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] sh negP P out r := by
  unfold restoreStep12
  split
  · next hK =>
    dsimp only
    rw [histAt_tap out out.size 12 11 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 10 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 9 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 8 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 7 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 6 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 5 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 4 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 3 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 2 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap out out.size 12 1 hK (Nat.le_refl _) hs (by omega)]
    rw [histAt_tap0 out out.size 12 hK (Nat.le_refl _) hs (by omega)]
    unfold restoreStep
    dsimp only
    rw [dot64_unfold12 out c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 out.size (Nat.le_refl _) hK 0, Int64.zero_add]
  · rw [Bits.toInt_toInt64_of_fits16 (hc c0 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c1 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c2 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c3 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c4 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c5 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c6 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c7 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c8 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c9 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c10 (by simp)), Bits.toInt_toInt64_of_fits16 (hc c11 (by simp))]

private theorem restoreFold12_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Int)
    (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11], Bits.FitsSInt 16 c) (sh negP P : Int64)
    (res init : Array Int) (hs : init.size + res.size < 4294967296) :
    restoreFold12 b c0.toInt64 c1.toInt64 c2.toInt64 c3.toInt64 c4.toInt64 c5.toInt64 c6.toInt64 c7.toInt64 c8.toInt64 c9.toInt64 c10.toInt64 c11.toInt64 sh negP P res init
      = res.foldl (fun out r => out.push (restoreStep b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] sh negP P out r)) init := by
  unfold restoreFold12
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_push_congr _ _ _ _ 4294967296 (by simp; omega)
    (fun out r hb => restoreStep12_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 hc sh negP P out hb r)

theorem getElem_eq_getD (out : Array Int) (i : Nat) (h : i < out.size) : out[i] = out.getD i 0 := by
  unfold Array.getD
  rw [dif_pos h]
  rfl

theorem getD_push_lt (out : Array Int) (v : Int) (i : Nat) (h : i < out.size) :
    (out.push v).getD i 0 = out.getD i 0 := by
  rw [← getElem_eq_getD _ _ (by simp; omega), ← getElem_eq_getD _ _ h, Array.getElem_push_lt]

theorem getD_push_eq (out : Array Int) (v : Int) : (out.push v).getD out.size 0 = v := by
  rw [← getElem_eq_getD _ _ (by simp), Array.getElem_push_eq]

private theorem restoreWin1_eq (b : Nat) (c0 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 : Int64) (out : Array Int), res.size - i = n →
      1 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 1) 0).toInt64 →
      restoreWin1 b c0 sh negP P res i h0 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep1 b c0 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 out hn hK hs hw0
    rw [restoreWin1, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 out hn hK hs hw0
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep1 b c0 sh negP P out res[i]
        = (let p := (c0 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep1
      rw [if_pos hK]
      dsimp only

      rw [histAt_tap0 out out.size 1 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      rfl
    rw [hstep]
    have heq : restoreWin1 b c0 sh negP P res i h0 out
        = restoreWin1 b c0 sh negP P res (i + 1) (let p := (c0 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin1, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, show out.size + 1 - 1 = out.size by omega, getD_push_eq])

private theorem restoreRoll1_eq_fold (b : Nat) (c0 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll1 b c0 sh negP P res init = restoreFold1 b c0 sh negP P res init := by
  unfold restoreRoll1
  split
  · next hK =>
    rw [restoreWin1_eq b c0 sh negP P res res.size 0 (init.getD (init.size - 1) 0).toInt64 init rfl hK (by omega)
      rfl]
    unfold restoreFold1
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin2_eq (b : Nat) (c0 c1 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 : Int64) (out : Array Int), res.size - i = n →
      2 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 2) 0).toInt64 →
      h1 = (out.getD (out.size - 2 + 1) 0).toInt64 →
      restoreWin2 b c0 c1 sh negP P res i h0 h1 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep2 b c0 c1 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 out hn hK hs hw0 hw1
    rw [restoreWin2, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 out hn hK hs hw0 hw1
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep2 b c0 c1 sh negP P out res[i]
        = (let p := (c0 * h1 + c1 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep2
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 2 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 2 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      rfl
    rw [hstep]
    have heq : restoreWin2 b c0 c1 sh negP P res i h0 h1 out
        = restoreWin2 b c0 c1 sh negP P res (i + 1) h1 (let p := (c0 * h1 + c1 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h1 + c1 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin2, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h1 + c1 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 2 = out.size - 2 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, show out.size + 1 - 2 + 1 = out.size by omega, getD_push_eq])

private theorem restoreRoll2_eq_fold (b : Nat) (c0 c1 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll2 b c0 c1 sh negP P res init = restoreFold2 b c0 c1 sh negP P res init := by
  unfold restoreRoll2
  split
  · next hK =>
    rw [restoreWin2_eq b c0 c1 sh negP P res res.size 0 (init.getD (init.size - 2) 0).toInt64 (init.getD (init.size - 2 + 1) 0).toInt64 init rfl hK (by omega)
      rfl rfl]
    unfold restoreFold2
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin3_eq (b : Nat) (c0 c1 c2 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 : Int64) (out : Array Int), res.size - i = n →
      3 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 3) 0).toInt64 →
      h1 = (out.getD (out.size - 3 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 3 + 2) 0).toInt64 →
      restoreWin3 b c0 c1 c2 sh negP P res i h0 h1 h2 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep3 b c0 c1 c2 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 out hn hK hs hw0 hw1 hw2
    rw [restoreWin3, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 out hn hK hs hw0 hw1 hw2
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep3 b c0 c1 c2 sh negP P out res[i]
        = (let p := (c0 * h2 + c1 * h1 + c2 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep3
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 3 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 3 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 3 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      rfl
    rw [hstep]
    have heq : restoreWin3 b c0 c1 c2 sh negP P res i h0 h1 h2 out
        = restoreWin3 b c0 c1 c2 sh negP P res (i + 1) h1 h2 (let p := (c0 * h2 + c1 * h1 + c2 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h2 + c1 * h1 + c2 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin3, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h2 + c1 * h1 + c2 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 3 = out.size - 3 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 3 + 1 = out.size - 3 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, show out.size + 1 - 3 + 2 = out.size by omega, getD_push_eq])

private theorem restoreRoll3_eq_fold (b : Nat) (c0 c1 c2 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll3 b c0 c1 c2 sh negP P res init = restoreFold3 b c0 c1 c2 sh negP P res init := by
  unfold restoreRoll3
  split
  · next hK =>
    rw [restoreWin3_eq b c0 c1 c2 sh negP P res res.size 0 (init.getD (init.size - 3) 0).toInt64 (init.getD (init.size - 3 + 1) 0).toInt64 (init.getD (init.size - 3 + 2) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl]
    unfold restoreFold3
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin4_eq (b : Nat) (c0 c1 c2 c3 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 : Int64) (out : Array Int), res.size - i = n →
      4 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 4) 0).toInt64 →
      h1 = (out.getD (out.size - 4 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 4 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 4 + 3) 0).toInt64 →
      restoreWin4 b c0 c1 c2 c3 sh negP P res i h0 h1 h2 h3 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep4 b c0 c1 c2 c3 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 out hn hK hs hw0 hw1 hw2 hw3
    rw [restoreWin4, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 out hn hK hs hw0 hw1 hw2 hw3
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep4 b c0 c1 c2 c3 sh negP P out res[i]
        = (let p := (c0 * h3 + c1 * h2 + c2 * h1 + c3 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep4
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 4 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 4 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 4 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 4 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      rfl
    rw [hstep]
    have heq : restoreWin4 b c0 c1 c2 c3 sh negP P res i h0 h1 h2 h3 out
        = restoreWin4 b c0 c1 c2 c3 sh negP P res (i + 1) h1 h2 h3 (let p := (c0 * h3 + c1 * h2 + c2 * h1 + c3 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h3 + c1 * h2 + c2 * h1 + c3 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin4, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h3 + c1 * h2 + c2 * h1 + c3 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 4 = out.size - 4 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 4 + 1 = out.size - 4 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 4 + 2 = out.size - 4 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, show out.size + 1 - 4 + 3 = out.size by omega, getD_push_eq])

private theorem restoreRoll4_eq_fold (b : Nat) (c0 c1 c2 c3 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll4 b c0 c1 c2 c3 sh negP P res init = restoreFold4 b c0 c1 c2 c3 sh negP P res init := by
  unfold restoreRoll4
  split
  · next hK =>
    rw [restoreWin4_eq b c0 c1 c2 c3 sh negP P res res.size 0 (init.getD (init.size - 4) 0).toInt64 (init.getD (init.size - 4 + 1) 0).toInt64 (init.getD (init.size - 4 + 2) 0).toInt64 (init.getD (init.size - 4 + 3) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl]
    unfold restoreFold4
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin5_eq (b : Nat) (c0 c1 c2 c3 c4 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 : Int64) (out : Array Int), res.size - i = n →
      5 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 5) 0).toInt64 →
      h1 = (out.getD (out.size - 5 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 5 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 5 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 5 + 4) 0).toInt64 →
      restoreWin5 b c0 c1 c2 c3 c4 sh negP P res i h0 h1 h2 h3 h4 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep5 b c0 c1 c2 c3 c4 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 out hn hK hs hw0 hw1 hw2 hw3 hw4
    rw [restoreWin5, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 out hn hK hs hw0 hw1 hw2 hw3 hw4
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep5 b c0 c1 c2 c3 c4 sh negP P out res[i]
        = (let p := (c0 * h4 + c1 * h3 + c2 * h2 + c3 * h1 + c4 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep5
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 5 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 5 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 5 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 5 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 5 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      rfl
    rw [hstep]
    have heq : restoreWin5 b c0 c1 c2 c3 c4 sh negP P res i h0 h1 h2 h3 h4 out
        = restoreWin5 b c0 c1 c2 c3 c4 sh negP P res (i + 1) h1 h2 h3 h4 (let p := (c0 * h4 + c1 * h3 + c2 * h2 + c3 * h1 + c4 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h4 + c1 * h3 + c2 * h2 + c3 * h1 + c4 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin5, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h4 + c1 * h3 + c2 * h2 + c3 * h1 + c4 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 5 = out.size - 5 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 5 + 1 = out.size - 5 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 5 + 2 = out.size - 5 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 5 + 3 = out.size - 5 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, show out.size + 1 - 5 + 4 = out.size by omega, getD_push_eq])

private theorem restoreRoll5_eq_fold (b : Nat) (c0 c1 c2 c3 c4 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll5 b c0 c1 c2 c3 c4 sh negP P res init = restoreFold5 b c0 c1 c2 c3 c4 sh negP P res init := by
  unfold restoreRoll5
  split
  · next hK =>
    rw [restoreWin5_eq b c0 c1 c2 c3 c4 sh negP P res res.size 0 (init.getD (init.size - 5) 0).toInt64 (init.getD (init.size - 5 + 1) 0).toInt64 (init.getD (init.size - 5 + 2) 0).toInt64 (init.getD (init.size - 5 + 3) 0).toInt64 (init.getD (init.size - 5 + 4) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl]
    unfold restoreFold5
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin6_eq (b : Nat) (c0 c1 c2 c3 c4 c5 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 : Int64) (out : Array Int), res.size - i = n →
      6 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 6) 0).toInt64 →
      h1 = (out.getD (out.size - 6 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 6 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 6 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 6 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 6 + 5) 0).toInt64 →
      restoreWin6 b c0 c1 c2 c3 c4 c5 sh negP P res i h0 h1 h2 h3 h4 h5 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep6 b c0 c1 c2 c3 c4 c5 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5
    rw [restoreWin6, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep6 b c0 c1 c2 c3 c4 c5 sh negP P out res[i]
        = (let p := (c0 * h5 + c1 * h4 + c2 * h3 + c3 * h2 + c4 * h1 + c5 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep6
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 6 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 6 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 6 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 6 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 6 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 6 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      rfl
    rw [hstep]
    have heq : restoreWin6 b c0 c1 c2 c3 c4 c5 sh negP P res i h0 h1 h2 h3 h4 h5 out
        = restoreWin6 b c0 c1 c2 c3 c4 c5 sh negP P res (i + 1) h1 h2 h3 h4 h5 (let p := (c0 * h5 + c1 * h4 + c2 * h3 + c3 * h2 + c4 * h1 + c5 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h5 + c1 * h4 + c2 * h3 + c3 * h2 + c4 * h1 + c5 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin6, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h5 + c1 * h4 + c2 * h3 + c3 * h2 + c4 * h1 + c5 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 6 = out.size - 6 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 6 + 1 = out.size - 6 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 6 + 2 = out.size - 6 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 6 + 3 = out.size - 6 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 6 + 4 = out.size - 6 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, show out.size + 1 - 6 + 5 = out.size by omega, getD_push_eq])

private theorem restoreRoll6_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll6 b c0 c1 c2 c3 c4 c5 sh negP P res init = restoreFold6 b c0 c1 c2 c3 c4 c5 sh negP P res init := by
  unfold restoreRoll6
  split
  · next hK =>
    rw [restoreWin6_eq b c0 c1 c2 c3 c4 c5 sh negP P res res.size 0 (init.getD (init.size - 6) 0).toInt64 (init.getD (init.size - 6 + 1) 0).toInt64 (init.getD (init.size - 6 + 2) 0).toInt64 (init.getD (init.size - 6 + 3) 0).toInt64 (init.getD (init.size - 6 + 4) 0).toInt64 (init.getD (init.size - 6 + 5) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl]
    unfold restoreFold6
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin7_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 h6 : Int64) (out : Array Int), res.size - i = n →
      7 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 7) 0).toInt64 →
      h1 = (out.getD (out.size - 7 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 7 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 7 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 7 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 7 + 5) 0).toInt64 →
      h6 = (out.getD (out.size - 7 + 6) 0).toInt64 →
      restoreWin7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res i h0 h1 h2 h3 h4 h5 h6 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep7 b c0 c1 c2 c3 c4 c5 c6 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 h6 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6
    rw [restoreWin7, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 h6 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep7 b c0 c1 c2 c3 c4 c5 c6 sh negP P out res[i]
        = (let p := (c0 * h6 + c1 * h5 + c2 * h4 + c3 * h3 + c4 * h2 + c5 * h1 + c6 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep7
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 7 6 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 7 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 7 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 7 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 7 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 7 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 7 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      rfl
    rw [hstep]
    have heq : restoreWin7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res i h0 h1 h2 h3 h4 h5 h6 out
        = restoreWin7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 (let p := (c0 * h6 + c1 * h5 + c2 * h4 + c3 * h3 + c4 * h2 + c5 * h1 + c6 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h6 + c1 * h5 + c2 * h4 + c3 * h3 + c4 * h2 + c5 * h1 + c6 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin7, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h6 + c1 * h5 + c2 * h4 + c3 * h3 + c4 * h2 + c5 * h1 + c6 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 h6 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 7 = out.size - 7 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 7 + 1 = out.size - 7 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 7 + 2 = out.size - 7 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 7 + 3 = out.size - 7 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 7 + 4 = out.size - 7 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 7 + 5 = out.size - 7 + 6 by omega]
        exact hw6)
      (by
        rw [Array.size_push, show out.size + 1 - 7 + 6 = out.size by omega, getD_push_eq])

private theorem restoreRoll7_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 c6 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res init = restoreFold7 b c0 c1 c2 c3 c4 c5 c6 sh negP P res init := by
  unfold restoreRoll7
  split
  · next hK =>
    rw [restoreWin7_eq b c0 c1 c2 c3 c4 c5 c6 sh negP P res res.size 0 (init.getD (init.size - 7) 0).toInt64 (init.getD (init.size - 7 + 1) 0).toInt64 (init.getD (init.size - 7 + 2) 0).toInt64 (init.getD (init.size - 7 + 3) 0).toInt64 (init.getD (init.size - 7 + 4) 0).toInt64 (init.getD (init.size - 7 + 5) 0).toInt64 (init.getD (init.size - 7 + 6) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl rfl]
    unfold restoreFold7
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin8_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 : Int64) (out : Array Int), res.size - i = n →
      8 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 8) 0).toInt64 →
      h1 = (out.getD (out.size - 8 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 8 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 8 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 8 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 8 + 5) 0).toInt64 →
      h6 = (out.getD (out.size - 8 + 6) 0).toInt64 →
      h7 = (out.getD (out.size - 8 + 7) 0).toInt64 →
      restoreWin8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7
    rw [restoreWin8, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P out res[i]
        = (let p := (c0 * h7 + c1 * h6 + c2 * h5 + c3 * h4 + c4 * h3 + c5 * h2 + c6 * h1 + c7 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep8
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 8 7 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 8 6 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 8 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 8 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 8 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 8 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 8 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 8 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      subst hw7
      rfl
    rw [hstep]
    have heq : restoreWin8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 out
        = restoreWin8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 (let p := (c0 * h7 + c1 * h6 + c2 * h5 + c3 * h4 + c4 * h3 + c5 * h2 + c6 * h1 + c7 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h7 + c1 * h6 + c2 * h5 + c3 * h4 + c4 * h3 + c5 * h2 + c6 * h1 + c7 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin8, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h7 + c1 * h6 + c2 * h5 + c3 * h4 + c4 * h3 + c5 * h2 + c6 * h1 + c7 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 h6 h7 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 = out.size - 8 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 + 1 = out.size - 8 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 + 2 = out.size - 8 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 + 3 = out.size - 8 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 + 4 = out.size - 8 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 + 5 = out.size - 8 + 6 by omega]
        exact hw6)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 8 + 6 = out.size - 8 + 7 by omega]
        exact hw7)
      (by
        rw [Array.size_push, show out.size + 1 - 8 + 7 = out.size by omega, getD_push_eq])

private theorem restoreRoll8_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res init = restoreFold8 b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res init := by
  unfold restoreRoll8
  split
  · next hK =>
    rw [restoreWin8_eq b c0 c1 c2 c3 c4 c5 c6 c7 sh negP P res res.size 0 (init.getD (init.size - 8) 0).toInt64 (init.getD (init.size - 8 + 1) 0).toInt64 (init.getD (init.size - 8 + 2) 0).toInt64 (init.getD (init.size - 8 + 3) 0).toInt64 (init.getD (init.size - 8 + 4) 0).toInt64 (init.getD (init.size - 8 + 5) 0).toInt64 (init.getD (init.size - 8 + 6) 0).toInt64 (init.getD (init.size - 8 + 7) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl rfl rfl]
    unfold restoreFold8
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin9_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 h8 : Int64) (out : Array Int), res.size - i = n →
      9 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 9) 0).toInt64 →
      h1 = (out.getD (out.size - 9 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 9 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 9 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 9 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 9 + 5) 0).toInt64 →
      h6 = (out.getD (out.size - 9 + 6) 0).toInt64 →
      h7 = (out.getD (out.size - 9 + 7) 0).toInt64 →
      h8 = (out.getD (out.size - 9 + 8) 0).toInt64 →
      restoreWin9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
    rw [restoreWin9, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P out res[i]
        = (let p := (c0 * h8 + c1 * h7 + c2 * h6 + c3 * h5 + c4 * h4 + c5 * h3 + c6 * h2 + c7 * h1 + c8 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep9
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 9 8 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 7 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 6 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 9 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 9 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      subst hw7
      subst hw8
      rfl
    rw [hstep]
    have heq : restoreWin9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 out
        = restoreWin9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 (let p := (c0 * h8 + c1 * h7 + c2 * h6 + c3 * h5 + c4 * h4 + c5 * h3 + c6 * h2 + c7 * h1 + c8 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h8 + c1 * h7 + c2 * h6 + c3 * h5 + c4 * h4 + c5 * h3 + c6 * h2 + c7 * h1 + c8 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin9, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h8 + c1 * h7 + c2 * h6 + c3 * h5 + c4 * h4 + c5 * h3 + c6 * h2 + c7 * h1 + c8 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 = out.size - 9 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 1 = out.size - 9 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 2 = out.size - 9 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 3 = out.size - 9 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 4 = out.size - 9 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 5 = out.size - 9 + 6 by omega]
        exact hw6)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 6 = out.size - 9 + 7 by omega]
        exact hw7)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 9 + 7 = out.size - 9 + 8 by omega]
        exact hw8)
      (by
        rw [Array.size_push, show out.size + 1 - 9 + 8 = out.size by omega, getD_push_eq])

private theorem restoreRoll9_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res init = restoreFold9 b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res init := by
  unfold restoreRoll9
  split
  · next hK =>
    rw [restoreWin9_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 sh negP P res res.size 0 (init.getD (init.size - 9) 0).toInt64 (init.getD (init.size - 9 + 1) 0).toInt64 (init.getD (init.size - 9 + 2) 0).toInt64 (init.getD (init.size - 9 + 3) 0).toInt64 (init.getD (init.size - 9 + 4) 0).toInt64 (init.getD (init.size - 9 + 5) 0).toInt64 (init.getD (init.size - 9 + 6) 0).toInt64 (init.getD (init.size - 9 + 7) 0).toInt64 (init.getD (init.size - 9 + 8) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    unfold restoreFold9
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin10_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Int64) (out : Array Int), res.size - i = n →
      10 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 10) 0).toInt64 →
      h1 = (out.getD (out.size - 10 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 10 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 10 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 10 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 10 + 5) 0).toInt64 →
      h6 = (out.getD (out.size - 10 + 6) 0).toInt64 →
      h7 = (out.getD (out.size - 10 + 7) 0).toInt64 →
      h8 = (out.getD (out.size - 10 + 8) 0).toInt64 →
      h9 = (out.getD (out.size - 10 + 9) 0).toInt64 →
      restoreWin10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9
    rw [restoreWin10, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P out res[i]
        = (let p := (c0 * h9 + c1 * h8 + c2 * h7 + c3 * h6 + c4 * h5 + c5 * h4 + c6 * h3 + c7 * h2 + c8 * h1 + c9 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep10
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 10 9 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 8 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 7 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 6 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 10 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 10 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      subst hw7
      subst hw8
      subst hw9
      rfl
    rw [hstep]
    have heq : restoreWin10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 out
        = restoreWin10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 (let p := (c0 * h9 + c1 * h8 + c2 * h7 + c3 * h6 + c4 * h5 + c5 * h4 + c6 * h3 + c7 * h2 + c8 * h1 + c9 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h9 + c1 * h8 + c2 * h7 + c3 * h6 + c4 * h5 + c5 * h4 + c6 * h3 + c7 * h2 + c8 * h1 + c9 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin10, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h9 + c1 * h8 + c2 * h7 + c3 * h6 + c4 * h5 + c5 * h4 + c6 * h3 + c7 * h2 + c8 * h1 + c9 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 = out.size - 10 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 1 = out.size - 10 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 2 = out.size - 10 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 3 = out.size - 10 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 4 = out.size - 10 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 5 = out.size - 10 + 6 by omega]
        exact hw6)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 6 = out.size - 10 + 7 by omega]
        exact hw7)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 7 = out.size - 10 + 8 by omega]
        exact hw8)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 10 + 8 = out.size - 10 + 9 by omega]
        exact hw9)
      (by
        rw [Array.size_push, show out.size + 1 - 10 + 9 = out.size by omega, getD_push_eq])

private theorem restoreRoll10_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res init = restoreFold10 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res init := by
  unfold restoreRoll10
  split
  · next hK =>
    rw [restoreWin10_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 sh negP P res res.size 0 (init.getD (init.size - 10) 0).toInt64 (init.getD (init.size - 10 + 1) 0).toInt64 (init.getD (init.size - 10 + 2) 0).toInt64 (init.getD (init.size - 10 + 3) 0).toInt64 (init.getD (init.size - 10 + 4) 0).toInt64 (init.getD (init.size - 10 + 5) 0).toInt64 (init.getD (init.size - 10 + 6) 0).toInt64 (init.getD (init.size - 10 + 7) 0).toInt64 (init.getD (init.size - 10 + 8) 0).toInt64 (init.getD (init.size - 10 + 9) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    unfold restoreFold10
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin11_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : Int64) (out : Array Int), res.size - i = n →
      11 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 11) 0).toInt64 →
      h1 = (out.getD (out.size - 11 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 11 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 11 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 11 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 11 + 5) 0).toInt64 →
      h6 = (out.getD (out.size - 11 + 6) 0).toInt64 →
      h7 = (out.getD (out.size - 11 + 7) 0).toInt64 →
      h8 = (out.getD (out.size - 11 + 8) 0).toInt64 →
      h9 = (out.getD (out.size - 11 + 9) 0).toInt64 →
      h10 = (out.getD (out.size - 11 + 10) 0).toInt64 →
      restoreWin11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10
    rw [restoreWin11, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P out res[i]
        = (let p := (c0 * h10 + c1 * h9 + c2 * h8 + c3 * h7 + c4 * h6 + c5 * h5 + c6 * h4 + c7 * h3 + c8 * h2 + c9 * h1 + c10 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep11
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 11 10 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 9 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 8 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 7 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 6 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 11 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 11 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      subst hw7
      subst hw8
      subst hw9
      subst hw10
      rfl
    rw [hstep]
    have heq : restoreWin11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 out
        = restoreWin11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (let p := (c0 * h10 + c1 * h9 + c2 * h8 + c3 * h7 + c4 * h6 + c5 * h5 + c6 * h4 + c7 * h3 + c8 * h2 + c9 * h1 + c10 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h10 + c1 * h9 + c2 * h8 + c3 * h7 + c4 * h6 + c5 * h5 + c6 * h4 + c7 * h3 + c8 * h2 + c9 * h1 + c10 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin11, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h10 + c1 * h9 + c2 * h8 + c3 * h7 + c4 * h6 + c5 * h5 + c6 * h4 + c7 * h3 + c8 * h2 + c9 * h1 + c10 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 = out.size - 11 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 1 = out.size - 11 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 2 = out.size - 11 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 3 = out.size - 11 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 4 = out.size - 11 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 5 = out.size - 11 + 6 by omega]
        exact hw6)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 6 = out.size - 11 + 7 by omega]
        exact hw7)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 7 = out.size - 11 + 8 by omega]
        exact hw8)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 8 = out.size - 11 + 9 by omega]
        exact hw9)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 11 + 9 = out.size - 11 + 10 by omega]
        exact hw10)
      (by
        rw [Array.size_push, show out.size + 1 - 11 + 10 = out.size by omega, getD_push_eq])

private theorem restoreRoll11_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res init = restoreFold11 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res init := by
  unfold restoreRoll11
  split
  · next hK =>
    rw [restoreWin11_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 sh negP P res res.size 0 (init.getD (init.size - 11) 0).toInt64 (init.getD (init.size - 11 + 1) 0).toInt64 (init.getD (init.size - 11 + 2) 0).toInt64 (init.getD (init.size - 11 + 3) 0).toInt64 (init.getD (init.size - 11 + 4) 0).toInt64 (init.getD (init.size - 11 + 5) 0).toInt64 (init.getD (init.size - 11 + 6) 0).toInt64 (init.getD (init.size - 11 + 7) 0).toInt64 (init.getD (init.size - 11 + 8) 0).toInt64 (init.getD (init.size - 11 + 9) 0).toInt64 (init.getD (init.size - 11 + 10) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    unfold restoreFold11
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
private theorem restoreWin12_eq (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 : Int64) (out : Array Int), res.size - i = n →
      12 ≤ out.size → out.size + (res.size - i) < 4294967296 →
      h0 = (out.getD (out.size - 12) 0).toInt64 →
      h1 = (out.getD (out.size - 12 + 1) 0).toInt64 →
      h2 = (out.getD (out.size - 12 + 2) 0).toInt64 →
      h3 = (out.getD (out.size - 12 + 3) 0).toInt64 →
      h4 = (out.getD (out.size - 12 + 4) 0).toInt64 →
      h5 = (out.getD (out.size - 12 + 5) 0).toInt64 →
      h6 = (out.getD (out.size - 12 + 6) 0).toInt64 →
      h7 = (out.getD (out.size - 12 + 7) 0).toInt64 →
      h8 = (out.getD (out.size - 12 + 8) 0).toInt64 →
      h9 = (out.getD (out.size - 12 + 9) 0).toInt64 →
      h10 = (out.getD (out.size - 12 + 10) 0).toInt64 →
      h11 = (out.getD (out.size - 12 + 11) 0).toInt64 →
      restoreWin12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
    rw [restoreWin12, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 out hn hK hs hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P out res[i]
        = (let p := (c0 * h11 + c1 * h10 + c2 * h9 + c3 * h8 + c4 * h7 + c5 * h6 + c6 * h5 + c7 * h4 + c8 * h3 + c9 * h2 + c10 * h1 + c11 * h0) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep12
      rw [if_pos hK]
      dsimp only
      rw [histAt_tap out out.size 12 11 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 10 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 9 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 8 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 7 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 6 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 5 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 4 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 3 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 2 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap out out.size 12 1 hK (Nat.le_refl _) (by omega) (by omega)]
      rw [histAt_tap0 out out.size 12 hK (Nat.le_refl _) (by omega) (by omega)]
      simp only [getElem_eq_getD]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      subst hw7
      subst hw8
      subst hw9
      subst hw10
      subst hw11
      rfl
    rw [hstep]
    have heq : restoreWin12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 out
        = restoreWin12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (let p := (c0 * h11 + c1 * h10 + c2 * h9 + c3 * h8 + c4 * h7 + c5 * h6 + c6 * h5 + c7 * h4 + c8 * h3 + c9 * h2 + c10 * h1 + c11 * h0) >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64
            (out.push (let p := (c0 * h11 + c1 * h10 + c2 * h9 + c3 * h8 + c4 * h7 + c5 * h6 + c6 * h5 + c7 * h4 + c8 * h3 + c9 * h2 + c10 * h1 + c11 * h0) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin12, dif_pos hi]
    rw [heq]
    generalize (let p := (c0 * h11 + c1 * h10 + c2 * h9 + c3 * h8 + c4 * h7 + c5 * h6 + c6 * h5 + c7 * h4 + c8 * h3 + c9 * h2 + c10 * h1 + c11 * h0) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 v.toInt64 (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 = out.size - 12 + 1 by omega]
        exact hw1)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 1 = out.size - 12 + 2 by omega]
        exact hw2)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 2 = out.size - 12 + 3 by omega]
        exact hw3)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 3 = out.size - 12 + 4 by omega]
        exact hw4)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 4 = out.size - 12 + 5 by omega]
        exact hw5)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 5 = out.size - 12 + 6 by omega]
        exact hw6)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 6 = out.size - 12 + 7 by omega]
        exact hw7)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 7 = out.size - 12 + 8 by omega]
        exact hw8)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 8 = out.size - 12 + 9 by omega]
        exact hw9)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 9 = out.size - 12 + 10 by omega]
        exact hw10)
      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show out.size + 1 - 12 + 10 = out.size - 12 + 11 by omega]
        exact hw11)
      (by
        rw [Array.size_push, show out.size + 1 - 12 + 11 = out.size by omega, getD_push_eq])

private theorem restoreRoll12_eq_fold (b : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res init = restoreFold12 b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res init := by
  unfold restoreRoll12
  split
  · next hK =>
    rw [restoreWin12_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 sh negP P res res.size 0 (init.getD (init.size - 12) 0).toInt64 (init.getD (init.size - 12 + 1) 0).toInt64 (init.getD (init.size - 12 + 2) 0).toInt64 (init.getD (init.size - 12 + 3) 0).toInt64 (init.getD (init.size - 12 + 4) 0).toInt64 (init.getD (init.size - 12 + 5) 0).toInt64 (init.getD (init.size - 12 + 6) 0).toInt64 (init.getD (init.size - 12 + 7) 0).toInt64 (init.getD (init.size - 12 + 8) 0).toInt64 (init.getD (init.size - 12 + 9) 0).toInt64 (init.getD (init.size - 12 + 10) 0).toInt64 (init.getD (init.size - 12 + 11) 0).toInt64 init rfl hK (by omega)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    unfold restoreFold12
    rw [List.drop_zero, Array.foldl_toList]
  · rfl

/-- **The kernel computes the fold.** Compiled code runs `restoreFast`
    wherever `restoreA` is called; every theorem keeps reading `restoreA`. -/
@[csimp] theorem restoreA_eq_restoreFast : @restoreA = @restoreFast := by
  funext b cs shift warmup res
  unfold restoreA restoreFast
  simp only []
  split
  · next hok =>
    obtain ⟨hb0, hb, hsh, hlen, hsz, hc, hw⟩ := hok
    rw [Bits.p2_eq] at hsz
    simp only [Nat.reducePow] at hsz
    have hinit : ∀ x ∈ (Array.emptyWithCapacity (warmup.length + res.size) ++ warmup.toArray
        : Array Int), Bits.FitsSInt 34 x := by
      intro x hx
      exact hw x (by simpa using hx)
    have hsz' : (Array.emptyWithCapacity (warmup.length + res.size) ++ warmup.toArray
        : Array Int).size + res.size < 4294967296 := by
      simp only [Array.size_append, Array.emptyWithCapacity_eq, Array.size_empty,
        List.size_toArray, List.length_nil]
      omega
    split
    · next _ c0 =>
      rw [restoreRoll1_eq_fold (res := res) (hs := hsz'), restoreFold1_eq b c0 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 =>
      rw [restoreRoll2_eq_fold (res := res) (hs := hsz'), restoreFold2_eq b c0 c1 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 =>
      rw [restoreRoll3_eq_fold (res := res) (hs := hsz'), restoreFold3_eq b c0 c1 c2 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 =>
      rw [restoreRoll4_eq_fold (res := res) (hs := hsz'), restoreFold4_eq b c0 c1 c2 c3 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 =>
      rw [restoreRoll5_eq_fold (res := res) (hs := hsz'), restoreFold5_eq b c0 c1 c2 c3 c4 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 =>
      rw [restoreRoll6_eq_fold (res := res) (hs := hsz'), restoreFold6_eq b c0 c1 c2 c3 c4 c5 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 c6 =>
      rw [restoreRoll7_eq_fold (res := res) (hs := hsz'), restoreFold7_eq b c0 c1 c2 c3 c4 c5 c6 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 c6 c7 =>
      rw [restoreRoll8_eq_fold (res := res) (hs := hsz'), restoreFold8_eq b c0 c1 c2 c3 c4 c5 c6 c7 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 c6 c7 c8 =>
      rw [restoreRoll9_eq_fold (res := res) (hs := hsz'), restoreFold9_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 =>
      rw [restoreRoll10_eq_fold (res := res) (hs := hsz'), restoreFold10_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 =>
      rw [restoreRoll11_eq_fold (res := res) (hs := hsz'), restoreFold11_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · next _ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 =>
      rw [restoreRoll12_eq_fold (res := res) (hs := hsz'), restoreFold12_eq b c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 hc _ _ _ res _ hsz', ← Array.foldl_toList,
        ← Array.foldl_toList]
      exact (foldl_restoreFast b _ shift hb0 hb hsh hlen hc res.toList _ hinit).symm
    · rw [← Array.foldl_toList, ← Array.foldl_toList]
      exact (foldl_restoreFast b cs shift hb0 hb hsh hlen hc res.toList _ hinit).symm
  · rfl

end Flac.Lpc
