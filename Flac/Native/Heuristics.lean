import Flac.Native.Subframe

/-!
# Heuristics — subframe/parameter search (UNVERIFIED BY DESIGN)

Everything here only decides *which* valid stream the encoder emits, never
whether the round-trip holds (PLAN.md §1). The single obligation carried is
`defaultChooser_valid` (in `Flac.Spec.Heuristics`): the returned
configuration satisfies `SubframeCfg.Valid`, so the keystone theorem
applies to it. Beyond that, this file is free optimization territory.

Current strategy (M3-initial): detect constant blocks; otherwise search
fixed orders 0–4 with a mean-based Rice parameter estimate, partition
order 0; fall back to VERBATIM when prediction does not pay.
-/

namespace Flac.Heuristics

open Flac Flac.Rice Flac.Subframe

/-- Mean-based Rice parameter estimate: smallest `k ≤ 14` with
    `Σ folded ≤ n · 2^k`. -/
def riceParam (sum n : Nat) : Nat :=
  go 14 0
where
  go : Nat → Nat → Nat
    | 0, k => k
    | fuel + 1, k => if sum ≤ n * 2 ^ k then k else go fuel (k + 1)

/-- Exact bit cost of Rice-coding folded residuals with parameter `k`
    (quotient unary + stop bit + `k` remainder bits each). -/
def riceCost (k : Nat) (us : List Nat) : Nat :=
  us.foldl (fun a u => a + u / 2 ^ k) 0 + us.length * (k + 1)

/-- Candidate: (order, rice parameter, bit cost). -/
private def pickMin (c : Nat × Nat × Nat) (cs : List (Nat × Nat × Nat)) :
    Nat × Nat × Nat :=
  cs.foldl (fun a c' => if c'.2.2 < a.2.2 then c' else a) c

/-- A FIXED configuration that is valid *by construction* for any nonempty
    block: order and Rice parameter are clamped into legal range here, so
    the validity proof never needs to reason about the search that chose
    them. -/
def fixedCfg (blk : List Int) (ord k : Nat) : SubframeCfg :=
  .fixed (min (min ord 4) (blk.length - 1))
    { method := .rice4, po := 0, choices := [.rice (min k 14)] }

/-- The default subframe chooser. Certified valid by
    `Flac.Spec.Heuristics.defaultChooser_valid`. -/
def defaultChooser (b : Nat) (blk : List Int) : SubframeCfg :=
  if blk.all (fun x => x == blk.headD 0) then .constant
  else
    match (List.range 5).filterMap (fun ord =>
      if ord + 1 ≤ blk.length then
        let us := (Fixed.residual ord blk).map Rice.zigzag
        let k := riceParam us.sum us.length
        some (ord, k, ord * b + riceCost k us)
      else none) with
    | [] => .verbatim
    | c :: cs =>
      if (pickMin c cs).2.2 < b * blk.length then
        fixedCfg blk (pickMin c cs).1 (pickMin c cs).2.1
      else .verbatim

end Flac.Heuristics
