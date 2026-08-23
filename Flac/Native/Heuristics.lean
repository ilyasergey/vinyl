import Flac.Native.Subframe
import Flac.Native.Lpc

/-!
# Heuristics — subframe/parameter search (UNVERIFIED BY DESIGN)

Everything here only decides *which* valid stream the encoder emits, never
whether the round-trip holds (PLAN.md §1). The single obligation carried is
`defaultChooser_valid` (in `Flac.Spec.Heuristics`): the returned
configuration satisfies `SubframeCfg.Valid`, so the keystone theorem
applies to it. Beyond that, this file is free optimization territory.

Current strategy (M3): detect constant blocks; search fixed orders 0–4 and
Welch-windowed Levinson–Durbin LPC (orders 1–8, 12-bit coefficients) by
exact Rice bit cost, partition order 0; fall back to VERBATIM when
prediction does not pay.
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

/-- Clamp into `p`-bit two's-complement range (explicit `if`s so the
    fits-proof is a pair of splits). -/
def clampSInt (p : Nat) (c : Int) : Int :=
  if c < -((2 ^ (p - 1) : Nat) : Int) then -((2 ^ (p - 1) : Nat) : Int)
  else if ((2 ^ (p - 1) : Nat) : Int) ≤ c then ((2 ^ (p - 1) : Nat) : Int) - 1
  else c

/-- An LPC configuration that is valid *by construction* (order,
    precision, shift, coefficients, and Rice parameter all clamped into
    legal range; degenerates to VERBATIM if no coefficients survive).
    Written without `let` so proofs can `split` on it directly. -/
def lpcCfg (blk : List Int) (cs : List Int) (shift prec k : Nat) : SubframeCfg :=
  if ((cs.map (clampSInt (min (max prec 1) 15))).take (min 32 (blk.length - 1))).isEmpty
  then .verbatim
  else
    .lpc ((cs.map (clampSInt (min (max prec 1) 15))).take (min 32 (blk.length - 1)))
      (min shift 15) (min (max prec 1) 15)
      { method := .rice4, po := 0, choices := [.rice (min k 14)] }

/-! ## Levinson–Durbin (Float, unverified — pure search) -/

/-- Welch window. -/
def welch (fl : Array Float) : Array Float :=
  let half := Float.ofNat (fl.size - 1) / 2
  fl.mapIdx fun i x =>
    let t := (Float.ofNat i - half) / half
    x * (1.0 - t * t)

def autocorr (w : Array Float) (maxLag : Nat) : Array Float := Id.run do
  let mut r := Array.replicate (maxLag + 1) 0.0
  for lag in [0:maxLag + 1] do
    let mut acc := 0.0
    for i in [lag:w.size] do
      acc := acc + w[i]! * w[i - lag]!
    r := r.set! lag acc
  return r

/-- Levinson–Durbin recursion: order-`ord` forward predictor coefficients
    (most recent sample first) from autocorrelation `r`. -/
def levinson (r : Array Float) (ord : Nat) : Array Float := Id.run do
  let mut lpc := Array.replicate ord 0.0
  let mut err := r[0]!
  for i in [0:ord] do
    if err ≤ 0.0 then
      return lpc
    let mut acc := r[i + 1]!
    for j in [0:i] do
      acc := acc - lpc[j]! * r[i - j]!
    let k := acc / err
    let old := lpc
    for j in [0:i] do
      lpc := lpc.set! j (old[j]! - k * old[i - 1 - j]!)
    lpc := lpc.set! i k
    err := err * (1.0 - k * k)
  return lpc

def floatToInt (f : Float) : Int :=
  if f ≥ 0 then Int.ofNat f.toUInt64.toNat
  else -(Int.ofNat (-f).toUInt64.toNat)

/-- Quantize Float coefficients to `prec`-bit integers with a shift
    (error-feedback rounding, libFLAC style). -/
def quantizeCoefs (cf : List Float) (prec : Nat) : List Int × Nat := Id.run do
  let cmax := cf.foldl (fun a c => max a c.abs) 0.0
  if cmax ≤ 0.0 then
    return (cf.map fun _ => 0, 0)
  let maxval := Float.ofNat (2 ^ (prec - 1) - 1)
  let s0 := Float.log2 (maxval / cmax)
  let shift := if s0 ≤ 0.0 then 0 else min 15 s0.floor.toUInt64.toNat
  let scale := Float.ofNat (2 ^ shift)
  let mut e := 0.0
  let mut out : List Int := []
  for c in cf do
    let v := c * scale + e
    let q := v.round
    e := v - q
    out := clampSInt prec (floatToInt q) :: out
  return (out.reverse, shift)

/-- LPC search: Welch window, autocorrelation, Levinson–Durbin at a few
    orders, quantize to 12 bits, exact Rice bit cost. Returns
    `(cs, shift, prec, k, cost)`. -/
def lpcSearch (b : Nat) (blk : List Int) : Option (List Int × Nat × Nat × Nat × Nat) := Id.run do
  if blk.length < 16 then
    return none
  let fl := (blk.map Float.ofInt).toArray
  let r := autocorr (welch fl) 8
  if !(r[0]! > 0.0) then
    return none
  let mut best : Option (List Int × Nat × Nat × Nat × Nat) := none
  for ord in [1, 2, 4, 6, 8] do
    if ord < blk.length then
      let (cs, shift) := quantizeCoefs (levinson r ord).toList 12
      let us := (Lpc.residual cs shift blk).map Rice.zigzag
      let k := riceParam us.sum us.length
      let cost := ord * b + 9 + ord * 12 + riceCost k us
      match best with
      | some (_, _, _, _, c) => if cost < c then best := some (cs, shift, 12, k, cost)
      | none => best := some (cs, shift, 12, k, cost)
  return best

/-- Search fixed orders 0–4, returning `(ord, k, cost)` of the best. -/
def fixedSearch (b : Nat) (blk : List Int) : Option (Nat × Nat × Nat) :=
  match (List.range 5).filterMap (fun ord =>
    if ord + 1 ≤ blk.length then
      let us := (Fixed.residual ord blk).map Rice.zigzag
      let k := riceParam us.sum us.length
      some (ord, k, ord * b + riceCost k us)
    else none) with
  | [] => none
  | c :: cs => some (pickMin c cs)

/-- The default subframe chooser. Certified valid by
    `Flac.Spec.Heuristics.defaultChooser_valid`. -/
def defaultChooser (b : Nat) (blk : List Int) : SubframeCfg :=
  if blk.all (fun x => x == blk.headD 0) then .constant
  else
    match fixedSearch b blk, lpcSearch b blk with
    | none, none => .verbatim
    | none, some (lcs, lsh, lp, lk, lcost) =>
      if lcost < b * blk.length then lpcCfg blk lcs lsh lp lk else .verbatim
    | some (ord, k, cost), none =>
      if cost < b * blk.length then fixedCfg blk ord k else .verbatim
    | some (ord, k, cost), some (lcs, lsh, lp, lk, lcost) =>
      if lcost ≤ cost then
        if lcost < b * blk.length then lpcCfg blk lcs lsh lp lk else .verbatim
      else
        if cost < b * blk.length then fixedCfg blk ord k else .verbatim

end Flac.Heuristics
