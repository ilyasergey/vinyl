import Flac.Native.Subframe
import Flac.Native.Lpc
import Flac.Native.Stereo
import Flac.Native.Frame

/-!
# Heuristics — subframe/parameter search (UNVERIFIED BY DESIGN)

Everything here only decides *which* valid stream the encoder emits, never
whether the round-trip holds. The single obligation carried is
`defaultChooser_valid` (in `Flac.Spec.Heuristics`): the returned
configuration satisfies `SubframeCfg.Valid`, so the keystone theorem
applies to it. Beyond that, this file is free optimization territory.

Current strategy: detect constant blocks; search fixed orders 0–4 and
Welch-windowed Levinson–Durbin LPC (orders 1–8, 12-bit coefficients) by
exact Rice bit cost, partition order 0; fall back to VERBATIM when
prediction does not pay.
-/

namespace Flac.Heuristics

open Flac Flac.Rice Flac.Subframe

/-- Mean-based Rice parameter estimate: smallest `k ≤ 14` with
    `Σ folded ≤ n · 2^k`.

    The bound is carried as `n · 2^k` and doubled per step, so a step is
    one add and one compare — no `p2` table lookup and no multiply. The
    partition cost search calls this once per partition per candidate
    partition order (127 times per candidate at `po ≤ 6`), which put the
    unoptimized loop at ~4% of encode. -/
def riceParam (sum n : Nat) : Nat :=
  go 14 0 n
where
  /-- `bound = n · 2^k`. -/
  go : Nat → Nat → Nat → Nat
    | 0, k, _ => k
    | fuel + 1, k, bound => if sum ≤ bound then k else go fuel (k + 1) (bound + bound)

/-- Estimated bit cost of Rice-coding a partition with parameter `k`,
    from its folded sum alone (the libFLAC-style estimate:
    `Σ (uᵢ >>> k) ≈ (Σ uᵢ) >>> k`, plus stop bit and remainder bits).
    O(1) per partition given the sum, which is what makes the partition
    search a prefix-sum walk instead of a per-element pass. -/
def riceCostEst (k sum n : Nat) : Nat :=
  (sum >>> k) + n * (k + 1)

/-- Best parameter and estimated cost for one partition, from its sum. -/
@[inline] def bestParamSum (sum n : Nat) : Nat × Nat :=
  let k := riceParam sum n
  (k, riceCostEst k sum n)

/-! ### The LPC candidate set

`lpcMaxOrder` is the highest order the recursion runs to, and so also the
autocorrelation lag count; `lpcCandidates` names the orders whose residual
and partitioning are then costed *exactly*. Both the verified chooser
(`lpcSearch`) and the fast encoder (`Flac.Encode.lpcChoiceF`) read them
from here, which is what keeps the two byte-identical.

libFLAC's `-8` costs exactly **one** order per apodization window — its
`do_exhaustive_model_search` is false at every level (`compression_levels_`
in `src/libFLAC/stream_encoder.c`), so `process_subframe_` evaluates only
`guess_lpc_order` — and buys its ratio with several windows instead. Vinyl
does the opposite: one Welch window, several orders. The candidate list is
therefore where Vinyl's compression-per-unit-work is decided. -/

/-- Highest LPC order considered (= autocorrelation lags). -/
def lpcMaxOrder : Nat := 8

/-- Orders costed exactly, beyond the Levinson estimate winner `est`.

    **Now just `est`** — libFLAC's own discipline: estimate the order from
    the Levinson prediction errors, then cost exactly one candidate. Every
    extra order means another full residual fold over the block, and the
    folds were the largest single cost in encode.

    The two corpora disagree sharply about what that costs, which is why the
    older table below (synthetic, 37 files of 1 MB) is kept:

    | base | synthetic ratio | real-audio ratio | encode |
    |---|---|---|---|
    | `[2,4,8]` (was chosen) | 39.634% | 38.757% | 1.00x |
    | **`[]`, estimate only** | **40.504%** | **38.795%** | **1.28x** |

    On synthetic signals the extra orders are worth 0.87 percentage points;
    on 32 MB of real music they are worth **0.038** — a tenth of a percent
    relative — for 28% of encode throughput. The synthetic corpus is tonal
    and degenerate material by construction, which is exactly where a second
    order pays; real audio is not. `flac -8` compresses better than either
    setting on both corpora (see `bench/README.md`), so the extra folds were
    not buying a margin, only narrowing a deficit.

    The estimate winner is listed first so it takes ties (candidates are
    compared with a strict `<`), which is why dropping orders costs so
    little: the estimator still reaches them.

    The full historical curve, measured on the synthetic corpus at a 32 MB
    probe, for anyone trading back the other way:

    | base | ratio | encode |
    |---|---|---|
    | `[1,2,4,6,8]` | 39.580% | 64.8 MB/s |
    | `[2,4,6,8]` | 39.580% | 67.7 MB/s |
    | `[1,2,4,8]` | 39.634% | 68.4 MB/s |
    | `[2,4,8]` | 39.634% | 71.2 MB/s |
    | `[2,8]` | 39.773% | 76.4 MB/s |
    | `[3,8]` | 39.912% | 76.7 MB/s |
    | `[8]` | 40.072% | — |
    | `[1,2,4,8,12]` at max order 12 | 39.450% | 0.94x of the top row |
 -/
def lpcCandidates (est : Nat) : List Nat :=
  [est]

/-- Search partition orders 0–6 over the folded residual: per-partition
    best parameters, estimated total bit cost from partition sums.
    Returns `(po, ks, cost)`. -/
def partitionSearch (bs ord : Nat) (us : List Nat) : Nat × List Nat × Nat := Id.run do
  let (k0, c0) := bestParamSum us.sum us.length
  let mut best : Nat × List Nat × Nat := (0, [k0], 6 + 4 + c0)
  for po in [1, 2, 3, 4, 5, 6] do
    if bs % Flac.Bits.p2 po = 0 ∧ ord < bs / Flac.Bits.p2 po then
      let c := bs / Flac.Bits.p2 po
      let sizes := (c - ord) :: List.replicate (Flac.Bits.p2 po - 1) c
      let parts := Rice.chunkBySizes sizes us
      let picks := parts.map fun p => bestParamSum p.sum p.length
      let cost := 6 + picks.foldl (fun a p => a + 4 + p.2) 0
      if cost < best.2.2 then
        best := (po, picks.map Prod.fst, cost)
  return best

/-- Pick the candidate with the least cost (cost is the second
    component). -/
private def pickMin {α : Type} (c : α × Nat) (cs : List (α × Nat)) : α × Nat :=
  cs.foldl (fun a c' => if c'.2 < a.2 then c' else a) c

/-- Per-partition Rice choices, padded/clamped so the list has exactly
    `2^po` entries with legal parameters — valid by construction. -/
def padChoices (po : Nat) (ks : List Nat) : List Rice.Partition :=
  (ks.map (fun k => Rice.Partition.rice (min k 14))).take (2 ^ po) ++
  List.replicate (2 ^ po - min ks.length (2 ^ po)) (.rice 10)

/-- A partitioned-Rice residual configuration that is valid by
    construction: the partition order is used only when the divisibility
    and first-partition conditions hold, else it degrades to a single
    partition. -/
def riceCfg (bs ord po : Nat) (ks : List Nat) : Rice.ResidualCfg :=
  if bs % 2 ^ po = 0 ∧ ord < bs / 2 ^ po ∧ po < 16 then
    { method := .rice4, po := po, choices := padChoices po ks }
  else
    { method := .rice4, po := 0, choices := [.rice (min (ks.headD 10) 14)] }

/-- A FIXED configuration that is valid *by construction* for any nonempty
    block: order and Rice parameters are clamped into legal range here, so
    the validity proof never needs to reason about the search that chose
    them. -/
def fixedCfg (blk : List Int) (ord po : Nat) (ks : List Nat) : SubframeCfg :=
  .fixed (min (min ord 4) (blk.length - 1))
    (riceCfg blk.length (min (min ord 4) (blk.length - 1)) po ks)

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
def lpcCfg (blk : List Int) (cs : List Int) (shift prec po : Nat)
    (ks : List Nat) : SubframeCfg :=
  if ((cs.map (clampSInt (min (max prec 1) 15))).take (min 32 (blk.length - 1))).isEmpty
  then .verbatim
  else
    .lpc ((cs.map (clampSInt (min (max prec 1) 15))).take (min 32 (blk.length - 1)))
      (min shift 15) (min (max prec 1) 15)
      (riceCfg blk.length
        ((cs.map (clampSInt (min (max prec 1) 15))).take (min 32 (blk.length - 1))).length
        po ks)

/-! ## Levinson–Durbin (Float, unverified — pure search) -/

/-- `0.0` by bit pattern: `Float` literals and `Float.ofNat`/`Float.ofInt`
    compile to `Float.ofScientific` calls that re-parse a big-integer
    constant per call — everything below sticks to the extern conversions
    (`UInt64.toFloat`, `Int64.toFloat`, `Float.ofBits`). -/
private def f0 : Float := Float.ofBits 0

/-- `1.0` by bit pattern. -/
private def f1 : Float := Float.ofBits 0x3FF0000000000000

/-- `2.0` by bit pattern. -/
private def f2 : Float := Float.ofBits 0x4000000000000000

/-- Extern-only `Nat → Float` (exact for `n < 2^53`, the only range the
    searches meet). -/
def floatOfNat (n : Nat) : Float := n.toUInt64.toFloat

/-- Extern-only `Int → Float` (exact for `|x| < 2^53`). -/
def floatOfInt (x : Int) : Float := x.toInt64.toFloat

/-! ### Windowing and autocorrelation

Block-sized float data is held in a `FloatArray`: a generic `Array Float`
boxes every element, which cost one heap allocation per sample per
subframe. The per-lag results stay boxed — there are only `maxLag + 1`
of them. -/

/-- Welch-windowed samples, unboxed. -/
def welchF (xs : Array Int) : FloatArray := Id.run do
  let n := xs.size
  let half := floatOfNat (n - 1) / f2
  let mut out := FloatArray.emptyWithCapacity n
  for i in [0 : n] do
    let t := (floatOfNat i - half) / half
    out := out.push (floatOfInt (xs.getD i 0) * (f1 - t * t))
  return out

/-- One autocorrelation lag, accumulator unboxed. -/
private def acorr1 (w : FloatArray) (lag : Nat) : (i : Nat) → Float → Float
  | i, acc =>
    if h : i < w.size then
      have h2 : i - lag < w.size := by omega
      acorr1 w lag (i + 1) (acc + w[i] * w[i - lag])
    else acc
  termination_by i => w.size - i

/-- Lags `lag`, `lag+1` and `lag+2` in **one** pass. At step `i` the pass
    reads `w[i]` and `w[i-lag]` and carries `w[i-lag-1]`/`w[i-lag-2]` in
    `p1`/`p2`, so a (lag, sample) pair costs two thirds of a load where
    three separate passes each re-read both operands. Every lag still
    accumulates ascending in `i` from `+0.0`, so the sums are bit-identical
    to the one-lag-at-a-time form. -/
private def acorr3 (w : FloatArray) (lag : Nat) :
    (i : Nat) → (a0 a1 a2 p1 p2 : Float) → Float × Float × Float
  | i, a0, a1, a2, p1, p2 =>
    if h : i < w.size then
      have h2 : i - lag < w.size := by omega
      let x := w[i]
      let y := w[i - lag]
      acorr3 w lag (i + 1) (a0 + x * y) (a1 + x * p1) (a2 + x * p2) y p1
    else (a0, a1, a2)
  termination_by i => w.size - i

/-- Autocorrelation lags `0 … maxLag` of the windowed samples, three lags
    per pass over the data (the remainder, and blocks too short for the
    fused pass to have a prologue, go through `acorr1`). -/
def autocorrF (w : FloatArray) (maxLag : Nat) : Array Float := Id.run do
  let mut r : Array Float := Array.emptyWithCapacity (maxLag + 1)
  let mut lag := 0
  for _ in [0 : maxLag + 1] do
    if maxLag < lag then
      break
    -- the fused pass needs `w[0]`, `w[1]`, `w[lag]` and `w[lag+1]`
    if h : lag + 2 ≤ maxLag ∧ lag + 1 < w.size ∧ 1 < w.size then
      have h0 : 0 < w.size := by omega
      have h1 : 1 < w.size := h.2.2
      have hl : lag < w.size := by omega
      have hl1 : lag + 1 < w.size := h.2.1
      let (a0, a1, a2) :=
        acorr3 w lag (lag + 2)
          (w[lag] * w[0] + w[lag + 1] * w[1]) (w[lag + 1] * w[0]) f0 w[1] w[0]
      r := ((r.push a0).push a1).push a2
      lag := lag + 3
    else
      r := r.push (acorr1 w lag lag f0)
      lag := lag + 1
  return r

/-- Levinson–Durbin recursion: order-`ord` forward predictor coefficients
    (most recent sample first) from autocorrelation `r`. -/
def levinson (r : Array Float) (ord : Nat) : Array Float := Id.run do
  let mut lpc := Array.replicate ord f0
  let mut err := r[0]!
  for i in [0:ord] do
    if err ≤ f0 then
      return lpc
    let mut acc := r[i + 1]!
    for j in [0:i] do
      acc := acc - lpc[j]! * r[i - j]!
    let k := acc / err
    let old := lpc
    for j in [0:i] do
      lpc := lpc.set! j (old[j]! - k * old[i - 1 - j]!)
    lpc := lpc.set! i k
    err := err * (f1 - k * k)
  return lpc

def floatToInt (f : Float) : Int :=
  if f ≥ f0 then Int.ofNat f.toUInt64.toNat
  else -(Int.ofNat (-f).toUInt64.toNat)

/-- Quantize Float coefficients to `prec`-bit integers with a shift
    (error-feedback rounding, libFLAC style). -/
def quantizeCoefs (cf : List Float) (prec : Nat) : List Int × Nat := Id.run do
  let cmax := cf.foldl (fun a c => max a c.abs) f0
  if cmax ≤ f0 then
    return (cf.map fun _ => 0, 0)
  let maxval := floatOfNat (2 ^ (prec - 1) - 1)
  let s0 := Float.log2 (maxval / cmax)
  let shift := if s0 ≤ f0 then 0 else min 15 s0.floor.toUInt64.toNat
  let scale := floatOfNat (2 ^ shift)
  let mut e := 0.0
  let mut out : List Int := []
  for c in cf do
    let v := c * scale + e
    let q := v.round
    e := v - q
    out := clampSInt prec (floatToInt q) :: out
  return (out.reverse, shift)

/-- The Levinson recursion's prediction error after each order `1..ord`
    (`errs[o-1]` is the error at order `o`; a non-positive error freezes
    the remaining entries, mirroring `levinson`'s early return). -/
def levinsonErrs (r : Array Float) (ord : Nat) : Array Float := Id.run do
  let mut lpc := Array.replicate ord f0
  let mut errs := Array.replicate ord f0
  let mut err := r[0]!
  let mut dead := false
  for i in [0:ord] do
    if dead ∨ err ≤ f0 then
      dead := true
      errs := errs.set! i err
    else
      let mut acc := r[i + 1]!
      for j in [0:i] do
        acc := acc - lpc[j]! * r[i - j]!
      let k := acc / err
      let old := lpc
      for j in [0:i] do
        lpc := lpc.set! j (old[j]! - k * old[i - 1 - j]!)
      lpc := lpc.set! i k
      err := err * (f1 - k * k)
      errs := errs.set! i err
  return errs

/-- libFLAC-style expected bits per residual sample from a Levinson
    prediction error over `n` (windowed) samples: `½·log₂(err/n)`,
    clamped at zero. -/
def expectedBits (err : Float) (n : Nat) : Float :=
  if err > f0 ∧ n ≠ 0 then
    let bits := Float.log2 (err / floatOfNat n) / f2
    if bits > f0 then bits else f0
  else f0

/-- Pick the LPC order among `1..errs.size` by estimated total bits
    (residual estimate + warmup/coefficient header); lowest order wins
    ties. -/
def pickLpcOrder (b n : Nat) (errs : Array Float) : Nat := Id.run do
  let mut best := 1
  let mut bestCost := f0
  for o in [1 : errs.size + 1] do
    let cost := floatOfNat (n - o) * (expectedBits (errs.getD (o - 1) f0) n + f1)
      + floatOfNat (o * (b + 12) + 9)
    if o = 1 ∨ cost < bestCost then
      best := o
      bestCost := cost
  return best

/-- LPC search, estimate-first (the libFLAC discipline): window +
    autocorrelation once, read the per-order prediction errors off the
    Levinson recursion, pick ONE order, and only then quantize, compute
    the residual, and search partitions. Returns `((cs, shift, po, ks),
    cost)`. -/
def lpcSearch (b : Nat) (blk : List Int) :
    Option ((List Int × Nat × Nat × List Nat) × Nat) := Id.run do
  if blk.length < 16 then
    return none
  let r := autocorrF (welchF blk.toArray) lpcMaxOrder
  if !(r[0]! > f0) then
    return none
  let ord := pickLpcOrder b blk.length (levinsonErrs r lpcMaxOrder)
  let mut best : Option ((List Int × Nat × Nat × List Nat) × Nat) := none
  for o in lpcCandidates ord do
    let (cs, shift) := quantizeCoefs (levinson r o).toList 12
    let us := (Lpc.residual cs shift blk).map Rice.zigzag
    let (po, ks, rcost) := partitionSearch blk.length o us
    let cost := o * b + 9 + o * 12 + rcost
    match best with
    | some (_, c) => if cost < c then best := some ((cs, shift, po, ks), cost)
    | none => best := some ((cs, shift, po, ks), cost)
  return best

/-- Fixed search: all orders 0–4 with exact (sum-estimated-partition)
    costs — the partition search is O(partitions) given the folded sums,
    so exhaustive evaluation is cheap. Lowest order wins ties. -/
def fixedSearch (b : Nat) (blk : List Int) :
    Option ((Nat × Nat × List Nat) × Nat) := Id.run do
  let mut best : Option ((Nat × Nat × List Nat) × Nat) := none
  let mut d := blk
  for ord in [0:5] do
    if ord + 1 ≤ blk.length then
      let us := d.map Rice.zigzag
      let (po, ks, rcost) := partitionSearch blk.length ord us
      let cost := ord * b + rcost
      match best with
      | some (_, c) => if cost < c then best := some ((ord, po, ks), cost)
      | none => best := some ((ord, po, ks), cost)
      d := Fixed.diff1 d
  return best

/-- The default subframe chooser. Certified valid by
    `Flac.Spec.Heuristics.defaultChooser_valid`. -/
def defaultChooser (b : Nat) (blk : List Int) : SubframeCfg :=
  if blk.all (fun x => x == blk.headD 0) then .constant
  else
    match fixedSearch b blk, lpcSearch b blk with
    | none, none => .verbatim
    | none, some ((lcs, lsh, lpo, lks), lcost) =>
      if lcost < b * blk.length then lpcCfg blk lcs lsh 12 lpo lks else .verbatim
    | some ((ord, po, ks), cost), none =>
      if cost < b * blk.length then fixedCfg blk ord po ks else .verbatim
    | some ((ord, po, ks), cost), some ((lcs, lsh, lpo, lks), lcost) =>
      if lcost ≤ cost then
        if lcost < b * blk.length then lpcCfg blk lcs lsh 12 lpo lks else .verbatim
      else
        if cost < b * blk.length then fixedCfg blk ord po ks else .verbatim

/-- Detect wasted bits: the largest `w < b` such that every sample is
    divisible by `2^w`. Sound by construction (`find?` returns only
    elements satisfying the predicate); 0 when nothing is found. -/
def wastedDetect (b : Nat) (xs : List Int) : Nat :=
  match (List.range b).reverse.find?
      (fun w => xs.all (fun x => x % ((2 ^ w : Nat) : Int) == 0)) with
  | some w => w
  | none => 0

/-- The full per-block chooser: detect wasted bits, then run the subframe
    search on the scaled-down samples at the reduced depth. -/
def defaultSubCfg (b : Nat) (blk : List Int) : Subframe.SubCfg :=
  ⟨wastedDetect b blk,
   defaultChooser (b - wastedDetect b blk)
     (blk.map (Flac.Bits.shiftDown (wastedDetect b blk)))⟩

/-! ## Stereo-mode decision -/

def sumAbs (xs : List Int) : Nat :=
  xs.foldl (fun a x => a + x.natAbs) 0

/-- Pick a stereo mode by the classic sum-of-magnitudes proxy:
    0 = independent, 1 = left/side, 2 = right/side, 3 = mid/side. -/
def stereoPick (l r : List Int) : Nat :=
  let al := sumAbs l
  let ar := sumAbs r
  let sa := sumAbs (Stereo.side l r)
  let am := sumAbs (Stereo.mid l r)
  if al + ar ≤ al + sa ∧ al + ar ≤ sa + ar ∧ al + ar ≤ am + sa then 0
  else if al + sa ≤ sa + ar ∧ al + sa ≤ am + sa then 1
  else if sa + ar ≤ am + sa then 2
  else 3

/-- The per-frame channel-assignment chooser: stereo-mode decision for two
    channels, independent coding otherwise; `defaultSubCfg` per subframe
    (at `b+1` bits for side channels). Certified valid by
    `Flac.Spec.Heuristics.defaultAsgChooser_valid`. -/
def defaultAsgChooser (b : Nat) (fr : List (List Int)) : Frame.ChannelAsg :=
  match fr with
  | [l, r] =>
    match stereoPick l r with
    | 1 => .leftSide (defaultSubCfg b l) (defaultSubCfg (b + 1) (Stereo.side l r))
    | 2 => .rightSide (defaultSubCfg (b + 1) (Stereo.side l r)) (defaultSubCfg b r)
    | 3 => .midSide (defaultSubCfg b (Stereo.mid l r))
        (defaultSubCfg (b + 1) (Stereo.side l r))
    | _ => .independent [defaultSubCfg b l, defaultSubCfg b r]
  | _ => .independent (fr.map (defaultSubCfg b))

end Flac.Heuristics
