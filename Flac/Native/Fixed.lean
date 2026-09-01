import Flac.Native.Bits

/-!
# Fixed predictors, orders 0–4 (RFC 9639 §9.2.4)

The order-`n` fixed-predictor residual (with the alternating-binomial
coefficients from the RFC) is exactly the `n`-th finite difference of the
sample sequence, so it is defined here by iterating first differences —
which is what makes the L3 restore proof (`Flac.Spec.Fixed`) a clean
induction. Orders above 4 never appear in streams (the subframe header
cannot express them), but the definitions and proofs are uniform in `ord`.
-/

namespace Flac.Fixed

/-- First differences: `diff1 [x₀, x₁, …] = [x₁ - x₀, x₂ - x₁, …]`. -/
def diff1 : List Int → List Int
  | x :: y :: t => (y - x) :: diff1 (y :: t)
  | _ => []

/-- `diff1` with the differences accumulated, so the recursive call is in tail
    position: the residual length is the block size, which the unchecked encoder
    lets grow without bound, so the cons-after-return form kept one native stack
    frame per sample (audit finding C04, the encode-side residual analogue of the
    per-frame `writeFrames`/`chunkChannels` swaps). -/
def diff1Acc (acc : List Int) : List Int → List Int
  | x :: y :: t => diff1Acc ((y - x) :: acc) (y :: t)
  | _ => acc.reverse

theorem diff1Acc_eq (acc : List Int) (xs : List Int) :
    diff1Acc acc xs = acc.reverse ++ diff1 xs := by
  induction xs using diff1.induct generalizing acc with
  | case1 x y t ih => rw [diff1Acc, diff1, ih ((y - x) :: acc)]; simp
  | case2 xs => cases xs <;> simp [diff1Acc, diff1]

def diff1TR (xs : List Int) : List Int := diff1Acc [] xs

/-- Swap the compiled `diff1` for the tail form; every theorem keeps the
    structural definition via the kernel. -/
@[csimp] theorem diff1_eq_diff1TR : @diff1 = @diff1TR := by
  funext xs
  unfold diff1TR
  rw [diff1Acc_eq]
  simp

/-- `n`-th differences. -/
def diffN : Nat → List Int → List Int
  | 0, xs => xs
  | n + 1, xs => diff1 (diffN n xs)

/-- Fixed-predictor residual of order `ord`. Length `xs.length - ord`;
    the first `ord` samples are transmitted verbatim as warmup. -/
def residual (ord : Nat) (xs : List Int) : List Int :=
  diffN ord xs

/-- Undo one differencing step, given the first sample of the target. -/
def undiff1 (x0 : Int) : List Int → List Int
  | [] => [x0]
  | d :: ds => x0 :: undiff1 (x0 + d) ds

/-- Restore samples from `ord` warmup samples and an order-`ord` residual,
    reduced to `b`-bit two's complement (RFC-conformant fixed-width wrap).

    The wrap is a single pointwise pass at the end: every step of the
    undifferencing chain is an addition, and addition commutes with taking
    residues mod `2^b`, so wrapping only the final values computes exactly
    what a register decoder wrapping at every step would. On any stream
    the encoder produced the samples fit `b` bits and the wrap is the
    identity (`Flac.Spec.Fixed.restore_residual` carries the hypothesis). -/
def restore (b : Nat) : (ord : Nat) → (warmup : List Int) → (res : List Int) → List Int
  | 0, _, res => res.map (Bits.wrapSInt b)
  | ord + 1, warmup, res =>
    restore b ord (warmup.take ord) (undiff1 ((diffN ord warmup).headD 0) res)

/-! ### Array forms (the production decoder's hot path)

Residuals arrive as an `Array Int`; the undifferencing passes run as array
folds and are proven equal to the list forms in `Flac.Spec.Fixed`
(`restoreA_toList`). The tiny warmup stays a list. -/

/-- `undiff1` over an array residual: running prefix sums pushed after
    `x0`. -/
def undiffA (x0 : Int) (ds : Array Int) : Array Int :=
  ds.foldl (fun out d => out.push (out.getD (out.size - 1) 0 + d))
    ((Array.emptyWithCapacity (ds.size + 1)).push x0)

/-- `restore` with the residual (and result) as arrays. The final wrap
    pass runs in place when the array is uniquely owned (it always is on
    the decode path). -/
def restoreA (b : Nat) : (ord : Nat) → (warmup : List Int) → (res : Array Int) → Array Int
  | 0, _, res => res.map (Bits.wrapSInt b)
  | ord + 1, warmup, res =>
    restoreA b ord (warmup.take ord) (undiffA ((diffN ord warmup).headD 0) res)

end Flac.Fixed
