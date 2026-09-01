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
    per sample (audit finding C04, the LPC residual analogue). -/
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

end Flac.Lpc
