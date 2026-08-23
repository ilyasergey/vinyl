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

/-- Restore samples from `ord` warmup samples and an order-`ord` residual. -/
def restore : (ord : Nat) → (warmup : List Int) → (res : List Int) → List Int
  | 0, _, res => res
  | ord + 1, warmup, res =>
    restore ord (warmup.take ord) (undiff1 ((diffN ord warmup).headD 0) res)

end Flac.Fixed
