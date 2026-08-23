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
(Levinson–Durbin, windowing, quantization) never enters the kernel
(PLAN.md §4, L3 note).
-/

namespace Flac.Lpc

open Flac.Bits (sar)

/-- Dot product of coefficients with the reversed history (most recent
    sample first), then the quantization shift. -/
def predict (cs : List Int) (shift : Nat) (hist : List Int) : Int :=
  sar ((cs.zip hist).foldl (fun a p => a + p.1 * p.2) 0) shift

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

end Flac.Lpc
