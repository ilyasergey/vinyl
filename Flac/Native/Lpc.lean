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

/-- LPC residual: the first `cs.length` samples are warmup, the rest are
    prediction residuals. -/
def residual (cs : List Int) (shift : Nat) (xs : List Int) : List Int :=
  residualAux cs shift (xs.take cs.length).reverse (xs.drop cs.length)

def restoreAux (cs : List Int) (shift : Nat) (hist : List Int) :
    List Int → List Int
  | [] => []
  | r :: res =>
    let x := r + predict cs shift hist
    x :: restoreAux cs shift (x :: hist) res

/-- Restore samples from warmup and residual. -/
def restore (cs : List Int) (shift : Nat) (warmup res : List Int) : List Int :=
  warmup ++ restoreAux cs shift warmup.reverse res

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

/-- `predict` against the tail of the decoded prefix. -/
@[inline] def predictA (cs : List Int) (shift : Nat) (out : Array Int) : Int :=
  sar (dotAGo out cs out.size (Nat.le_refl _) 0) shift

/-- `restore` with the residual (and result) as arrays: the array is both
    the accumulating output and the prediction history. Callers guarantee
    `cs.length ≤ warmup.length` (the subframe grammar always does). -/
def restoreA (cs : List Int) (shift : Nat) (warmup : List Int) (res : Array Int) :
    Array Int :=
  res.foldl (fun out r => out.push (r + predictA cs shift out))
    ((Array.emptyWithCapacity (warmup.length + res.size)) ++ warmup.toArray)

end Flac.Lpc
