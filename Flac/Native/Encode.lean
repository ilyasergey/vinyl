import Flac.Native.Heuristics
import Flac.Native.Md5
import Flac.Native.Crc

/-!
# The fast encoder (UNVERIFIED BY DESIGN — certified per call)

An `Array`/`ByteArray` reimplementation of exactly the stream the verified
encoder emits under the default heuristics: same subframe searches, same
Rice partitioning, same tie-breaking, byte-for-byte. Like
`Flac/Native/Heuristics.lean`, nothing here carries a proof obligation:
the shipping wrappers (`Flac.encodePcm16Fast` in `Flac.Native.Codec`)
*certify each call at runtime* by decoding the produced bytes with the
verified decoder and comparing against the input, falling back to the
verified encoder on any mismatch — so the byte-level round-trip theorem
(`Flac.decodePcm16_encodePcm16Fast`) holds with no hypotheses and no new
trusted code.

Everything hot avoids `Nat.pow`/`Nat.shiftLeft` (GMP-backed even for
word-sized values) in favour of the `p2` table and `>>>`/`&&&`/`*`.
-/

namespace Flac.Encode

open Flac.Bits (p2 sar)

/-! ## Bit writer -/

/-- MSB-first bit accumulator over a `ByteArray`. The low `n` bits of
    `acc` are pending; `n < 8` between pushes, and the bits above
    position `n` are stale (never read). `UInt64` throughout — its shifts
    and masks are unboxed intrinsics, unlike scalar `Nat` ops. -/
structure BitWriter where
  buf : ByteArray
  acc : UInt64
  n : Nat

namespace BitWriter

def empty (cap : Nat) : BitWriter := ⟨ByteArray.emptyWithCapacity cap, 0, 0⟩

/-- Emit the `n / 8` completed bytes out of the accumulator, most
    significant first.

    Returns only the buffer, deliberately. The tuple this used to return
    (`ByteArray × UInt64 × Nat`) cost three heap allocations per call —
    two `Prod` cells plus a boxed `UInt64`, since `Prod`'s fields are
    polymorphic and so always boxed — and `push` runs twice per residual
    sample, which made the bit writer the single largest allocator in the
    encoder. The two dropped components are recoverable without it: the
    new pending count is `n % 8`, and `acc` need not be masked at all
    because `toUInt8` truncates and no bit at or above position `n` is
    ever read back. -/
def flushBytes (buf : ByteArray) (acc : UInt64) (n : Nat) : ByteArray :=
  if h : n < 8 then buf
  else flushBytes (buf.push (acc >>> UInt64.ofNat (n - 8)).toUInt8) acc (n - 8)
termination_by n
decreasing_by omega

/-- Push the low `k` bits of `v`, MSB first. Requires `k ≤ 32` so the
    accumulator never overflows (`n + k ≤ 39`); use `pushBits` for wider
    fields. -/
def push (bw : BitWriter) (k : Nat) (v : Nat) : BitWriter :=
  let kk := UInt64.ofNat k
  let acc := (bw.acc <<< kk) ||| (UInt64.ofNat v &&& ((1 <<< kk) - 1))
  let n := bw.n + k
  ⟨flushBytes bw.buf acc n, acc, n % 8⟩

/-- Arbitrary-width big-endian push, chunked to keep the accumulator
    scalar. -/
def pushBits (bw : BitWriter) (k v : Nat) : BitWriter :=
  if h : k ≤ 32 then bw.push k v
  else (bw.pushBits (k - 32) (v >>> 32)).push 32 (v &&& 0xFFFFFFFF)
termination_by k
decreasing_by omega

/-- Unary code: `q` zero bits, then a one bit. -/
def pushUnary (bw : BitWriter) (q : Nat) : BitWriter :=
  if h : q < 32 then bw.push (q + 1) 1
  else pushUnary (bw.push 32 0) (q - 32)
termination_by q
decreasing_by omega

/-- `k`-bit two's complement (matches `Flac.Bits.writeSInt`). -/
def pushSInt (bw : BitWriter) (k : Nat) (x : Int) : BitWriter :=
  bw.pushBits k ((x + ((p2 k : Nat) : Int)).toNat &&& (p2 k - 1))

/-- Zero-pad to a byte boundary. -/
def align (bw : BitWriter) : BitWriter :=
  bw.push ((8 - bw.n % 8) % 8) 0

/-- Rice code with parameter `k` (zigzag + quotient unary + `k` bits). -/
def pushRice (bw : BitWriter) (k : Nat) (x : Int) : BitWriter :=
  let u := if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1
  (bw.pushUnary (u >>> k)).push k (u &&& (p2 k - 1))

/-- Coded number (mirrors `Flac.Utf8Num.write`). -/
def pushUtf8 (bw : BitWriter) (v : Nat) : BitWriter := Id.run do
  let conts (bw : BitWriter) (k : Nat) : BitWriter := Id.run do
    let mut w := bw
    for j in [0 : k] do
      w := w.push 8 (0x80 + (v >>> (6 * (k - 1 - j))) % 64)
    return w
  if v < p2 7 then return bw.push 8 v
  else if v < p2 11 then return conts ((bw.push 8 (0xC0 + (v >>> 6)))) 1
  else if v < p2 16 then return conts ((bw.push 8 (0xE0 + (v >>> 12)))) 2
  else if v < p2 21 then return conts ((bw.push 8 (0xF0 + (v >>> 18)))) 3
  else if v < p2 26 then return conts ((bw.push 8 (0xF8 + (v >>> 24)))) 4
  else if v < p2 31 then return conts ((bw.push 8 (0xFC + (v >>> 30)))) 5
  else return conts (bw.push 8 0xFE) 6

end BitWriter

/-! ## Residual searches (exact mirrors of `Flac.Heuristics`)

### Why the searches run on `Float`

A candidate search only *chooses* a subframe; the bytes are always emitted
from the exact `Int` path below. Every quantity a search computes is an
integer well inside `2^53`, and IEEE-754 doubles represent those exactly,
so running the searches over unboxed `FloatArray` picks the same subframe
*bit for bit* while replacing `lean_int_mul`/`lean_int_add` on boxed
`Array Int` with one hardware `fmul`/`fadd` per tap. For 16-bit input:
samples below `2^17` (side channels `< 2^18`), quantized coefficients
`< 2^11`, order at most 8, so a prediction sum is `< 2^32`, a residual
`< 2^19`, and a 4096-sample partition sum `< 2^32` — all exact, and exact
integer sums re-associate freely, so accumulation order is free too.

Measured on an order-8 4096-sample block: `2.5x` the Int form, with
identical partition sums. Two shapes matter for that number. Float-typed
`let mut` variables carried across a `for` loop get boxed once per
iteration, which costs more than the arithmetic saves — so every
accumulator here is a *tail-recursive parameter* instead (Lean keeps those
unboxed), and the `for` loops carry only heap objects (`Array`,
`FloatArray`) and `Nat` counters.
-/

/-- `0.0` by bit pattern (see `Heuristics.f0` on why not a literal). -/
private def ff0 : Float := Float.ofBits 0

/-- `1.0` by bit pattern. -/
private def ff1 : Float := Float.ofBits 0x3FF0000000000000

/-- `2.0` by bit pattern. -/
private def ff2 : Float := Float.ofBits 0x4000000000000000

/-- `2^-s` exactly, by exponent field (`s` at most 15 here: `quantizeCoefs`
    clamps the shift to 15). -/
@[inline] private def invPow2 (s : Nat) : Float :=
  Float.ofBits ((1023 - s).toUInt64 <<< 52)

/-- `Bits.sar` in exact float arithmetic: the dot product is an integer
    below `2^53` and `inv = 2^-shift` is exact, so the product is exact
    and `floor` is precisely the arithmetic shift. -/
@[inline] private def sarF (s inv : Float) : Float := Float.floor (s * inv)

/-- `foldResidual` in float arithmetic: `0 ≤ x ↦ 2x`, `x < 0 ↦ -2x - 1`. -/
@[inline] private def foldF (x : Float) : Float :=
  if x ≥ ff0 then x + x else -(x + x) - ff1

/-- A block of samples as exact floats. -/
def blockF (xs : Array Int) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity xs.size
  for x in xs do
    out := out.push (Heuristics.floatOfInt x)
  return out

/-- Welch window over an already-converted block — the same floats
    `Heuristics.welchF` produces, without reconverting the samples. -/
private def welchFf (xs : FloatArray) : FloatArray := Id.run do
  let n := xs.size
  let half := Heuristics.floatOfNat (n - 1) / ff2
  let mut out := FloatArray.emptyWithCapacity n
  for h : i in [0 : n] do
    have hi : i < xs.size := h.2.1
    let t := (Heuristics.floatOfNat i - half) / half
    out := out.push (xs[i] * (ff1 - t * t))
  return out

/-- One autocorrelation lag, accumulator unboxed. -/
private def acorrGo (w : FloatArray) (lag : Nat) : (i : Nat) → Float → Float
  | i, acc =>
    if h : i < w.size then
      have h2 : i - lag < w.size := by omega
      acorrGo w lag (i + 1) (acc + w[i] * w[i - lag])
    else acc
  termination_by i => w.size - i

/-- `Heuristics.autocorrF` with proof-carried indexing and an unboxed
    accumulator; same lags accumulated in the same order, so the same
    floats. -/
private def autocorrFf (w : FloatArray) (maxLag : Nat) : Array Float := Id.run do
  let mut r : Array Float := Array.emptyWithCapacity (maxLag + 1)
  for lag in [0 : maxLag + 1] do
    r := r.push (acorrGo w lag lag ff0)
  return r

/-- Largest legal partition order. Validity is downward-closed, so one
    pass characterises every order the cost search must consider. -/
private def partitionMaxF (bs ord : Nat) : Nat := Id.run do
  -- validity is downward-closed in po, so a single maximum characterises it
  let mut pomax := 0
  for po in [1, 2, 3, 4, 5, 6] do
    if bs % p2 po = 0 ∧ ord < bs / p2 po then
      pomax := po
  return pomax

/-- Cost all partition orders from the folded sums of the finest legal
    partitioning. Partition orders nest, so coarser sums are aggregates
    of consecutive entries. Lowest order wins ties. -/
private def partitionSearchSumsF (bs ord pomax : Nat) (sums : Array Nat) :
    Nat × Array Nat × Nat := Id.run do
  let mut best : Nat × Array Nat × Nat := (0, #[], 0)
  for po in [0 : pomax + 1] do
    let c := bs / p2 po
    let width := p2 (pomax - po)
    let mut ks : Array Nat := Array.emptyWithCapacity (p2 po)
    let mut cost := 6
    for j in [0 : p2 po] do
      let mut sum := 0
      for w in [j * width : (j + 1) * width] do
        sum := sum + sums.getD w 0
      let len := if j = 0 then c - ord else c
      let (k, ck) := Heuristics.bestParamSum sum len
      ks := ks.push k
      cost := cost + 4 + ck
    if po = 0 then
      best := (0, ks, cost)
    else if cost < best.2.2 then
      best := (po, ks, cost)
  return best

/-- Dot product of the coefficients (most recent tap first) with
    `xs[n-1], …`. Exact mirror of `lpcDotF`, in floats: the coefficients
    stay a (short) list, so walking them costs no bounds check per
    multiply, and `acc` is a parameter, so it stays unboxed. -/
private def lpcDotFf (xs : FloatArray) :
    (cs : List Float) → (n : Nat) → cs.length ≤ n → n ≤ xs.size → Float → Float
  | [], _, _, _, acc => acc
  | _ :: _, 0, hlen, _, _ => nomatch hlen
  | c :: cs, n + 1, hlen, hsize, acc =>
    have hi : n < xs.size := by omega
    have hlen' : cs.length ≤ n := by
      simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
    lpcDotFf xs cs n hlen' (Nat.le_of_lt hi) (acc + c * xs[n])

/-- Folded LPC residual magnitudes of the sample range `[i, stop)`,
    summed into an unboxed accumulator. -/
private def lpcFoldRange (xs : FloatArray) (cs : List Float) (inv : Float) :
    (i stop : Nat) → stop ≤ xs.size → cs.length ≤ i → Float → Float
  | i, stop, hstop, hlo, acc =>
    if h : i < stop then
      have hhi : i < xs.size := by omega
      lpcFoldRange xs cs inv (i + 1) stop hstop (by omega)
        (acc + foldF (xs[i] - sarF (lpcDotFf xs cs i hlo (Nat.le_of_lt hhi) ff0) inv))
    else acc
  termination_by i stop => stop - i

/-- Folded magnitudes of an already-computed residual range. -/
private def resFoldRange (res : FloatArray) :
    (i stop : Nat) → stop ≤ res.size → Float → Float
  | i, stop, hstop, acc =>
    if h : i < stop then
      have hhi : i < res.size := by omega
      resFoldRange res (i + 1) stop hstop (acc + foldF res[i])
    else acc
  termination_by i stop => stop - i

/-- Mirror of `Heuristics.partitionSearch`, fed by the residual directly:
    each finest partition is folded by one tail recursion, and each
    candidate order then costs O(partitions). -/
private def partitionSearchFf (bs ord : Nat) (res : FloatArray) :
    Nat × Array Nat × Nat := Id.run do
  let pomax := partitionMaxF bs ord
  let cF := bs / p2 pomax
  let np := p2 pomax
  let mut sums : Array Nat := Array.emptyWithCapacity np
  -- partition `j` covers residual indices `[j*cF - ord, (j+1)*cF - ord)`
  -- (`ord < cF`, so the first partition is the short one)
  for j in [0 : np] do
    let stop := (j + 1) * cF - ord
    let lo := if j = 0 then 0 else j * cF - ord
    if h : stop ≤ res.size then
      sums := sums.push (resFoldRange res lo stop h ff0).toUInt64.toNat
  return partitionSearchSumsF bs ord pomax sums

/-- Evaluate one LPC candidate directly into finest-partition sums. Same
    residual arithmetic and same visiting order as `lpcResidualArr`
    followed by `partitionSearchFf`, without allocating a block-sized
    residual for a candidate that may lose. -/
private def lpcPartitionSearchFf (cs : List Float) (shift : Nat) (xs : FloatArray) :
    Nat × Array Nat × Nat := Id.run do
  let ord := cs.length
  let bs := xs.size
  let pomax := partitionMaxF bs ord
  let cF := bs / p2 pomax
  let np := p2 pomax
  let inv := invPow2 shift
  let mut sums : Array Nat := Array.emptyWithCapacity np
  for j in [0 : np] do
    let stop := (j + 1) * cF
    let lo := if j = 0 then ord else j * cF
    if h : stop ≤ bs then
      if hlo : cs.length ≤ lo then
        sums := sums.push (lpcFoldRange xs cs inv lo stop h hlo ff0).toUInt64.toNat
  return partitionSearchSumsF bs ord pomax sums

/-- First differences over floats (exact: order-4 differences of 18-bit
    samples stay below `2^23`). -/
private def diffArrFf (xs : FloatArray) : FloatArray := Id.run do
  if xs.size = 0 then return FloatArray.empty
  let mut out := FloatArray.emptyWithCapacity (xs.size - 1)
  for h : i in [1 : xs.size] do
    have h1 : i < xs.size := h.2.1
    have h2 : i - 1 < xs.size := by omega
    out := out.push (xs[i] - xs[i - 1])
  return out

/-- First differences (`Fixed.diff1` over arrays) — the exact `Int` form,
    used when emitting the chosen FIXED subframe. -/
def diffArr (xs : Array Int) : Array Int := Id.run do
  if xs.size = 0 then return #[]
  let mut out := Array.emptyWithCapacity (xs.size - 1)
  for i in [1 : xs.size] do
    out := out.push (xs.getD i 0 - xs.getD (i - 1) 0)
  return out

/-- LPC residual (`Lpc.residual` over arrays): first `cs.length` samples
    are warmup, the rest are `x[n] - (Σ cs[i]·x[n-1-i]) >>ₐ shift`.
    The coefficients stay a (short) list — walking it costs no bounds
    check per multiply. -/
private def lpcDotF (xs : Array Int) :
    (cs : List Int) → (n : Nat) → cs.length ≤ n → n ≤ xs.size → Int → Int
  | [], _, _, _, acc => acc
  | _ :: _, 0, hlen, _, _ => nomatch hlen
  | c :: cs, n + 1, hlen, hsize, acc =>
    have hi : n < xs.size := by omega
    have hlen' : cs.length ≤ n := by
      simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
    lpcDotF xs cs n hlen' (Nat.le_of_lt hi) (acc + c * xs[n])

def lpcResidualArr (cs : List Int) (shift : Nat) (xs : Array Int) : Array Int := Id.run do
  let ord := cs.length
  if xs.size ≤ ord then return #[]
  let mut out := Array.emptyWithCapacity (xs.size - ord)
  for h : i in [ord : xs.size] do
    have hlo : cs.length ≤ i := by simpa only [ord] using h.1
    have hhi : i < xs.size := h.2.1
    let s := lpcDotF xs cs i hlo (Nat.le_of_lt hhi) 0
    out := out.push (xs[i] - sar s shift)
  return out

/-- Mirror of `Heuristics.fixedSearch`: all orders 0–4 with exact
    (sum-estimated-partition) costs off the difference cascade. -/
def fixedSearchF (b : Nat) (blkF : FloatArray) :
    Option ((Nat × Nat × Array Nat) × Nat) := Id.run do
  let mut best : Option ((Nat × Nat × Array Nat) × Nat) := none
  let mut d := blkF
  for ord in [0 : 5] do
    if ord + 1 ≤ blkF.size then
      let (po, ks, rcost) := partitionSearchFf blkF.size ord d
      let cost := ord * b + rcost
      match best with
      | some (_, c) => if cost < c then best := some ((ord, po, ks), cost)
      | none => best := some ((ord, po, ks), cost)
      d := diffArrFf d
  return best

private structure LpcChoice where
  cs : List Int
  shift : Nat
  po : Nat
  ks : Array Nat
  cost : Nat

/-- Internal LPC search result. Candidate residuals are folded directly
    into partition sums; the eventual winner's residual is materialized
    only if the subframe chooser actually selects LPC. -/
private def lpcChoiceF (b : Nat) (blkF : FloatArray) : Option LpcChoice := Id.run do
  if blkF.size < 16 then
    return none
  let r := autocorrFf (welchFf blkF) Heuristics.lpcMaxOrder
  if !(r.getD 0 ff0 > ff0) then
    return none
  let ord :=
    Heuristics.pickLpcOrder b blkF.size (Heuristics.levinsonErrs r Heuristics.lpcMaxOrder)
  let mut best : Option LpcChoice := none
  for o in Heuristics.lpcCandidates ord do
    let (cs, shift) := Heuristics.quantizeCoefs (Heuristics.levinson r o).toList 12
    let (po, ks, rcost) :=
      lpcPartitionSearchFf (cs.map Heuristics.floatOfInt) shift blkF
    let cost := o * b + 9 + o * 12 + rcost
    match best with
    | some old => if cost < old.cost then best := some ⟨cs, shift, po, ks, cost⟩
    | none => best := some ⟨cs, shift, po, ks, cost⟩
  return best

/-- Mirror of `Heuristics.lpcSearch`, estimate-first (the libFLAC
    discipline), preserving the existing result API and tie-breaking. -/
def lpcSearchF (b : Nat) (blk : Array Int) :
    Option ((List Int × Nat × Nat × Array Nat) × Nat) :=
  match lpcChoiceF b (blockF blk) with
  | none => none
  | some c => some ((c.cs, c.shift, c.po, c.ks), c.cost)

/-- Mirror of `Heuristics.wastedDetect`: the largest `w < b` such that
    `2^w` divides every sample (`b - 1` for the all-zero block). -/
def wastedDetectF (b : Nat) (blk : Array Int) : Nat := Id.run do
  if b = 0 then return 0
  let mut best := b - 1
  for x in blk do
    if best = 0 then return 0
    if x ≠ 0 then
      let mut tz := 0
      let mut w := x.natAbs
      for _ in [0 : b] do
        if w % 2 = 0 then
          tz := tz + 1
          w := w / 2
        else
          break
      best := min best tz
  return best

/-! ## Subframe plan (mirror of `Heuristics.defaultChooser`) -/

inductive SubPlan where
  | constant
  | verbatim
  | fixed (ord po : Nat) (ks : Array Nat)
  | lpc (cs : List Int) (shift po : Nat) (ks : Array Nat)

def SubPlan.typeCode : SubPlan → Nat
  | .constant => 0
  | .verbatim => 1
  | .fixed ord _ _ => 8 + ord
  | .lpc cs _ _ _ => 32 + (cs.length - 1)

/-- Attach the chosen LPC residual so emission can reuse it instead of
    running the winning predictor for a second time. -/
private def preparedLpc (blk : Array Int) (c : LpcChoice) :
    SubPlan × Option (Array Int) :=
  (.lpc c.cs c.shift c.po c.ks, some (lpcResidualArr c.cs c.shift blk))

/-- Internal chooser result with an emission-ready residual when LPC
    wins. The public `choosePlan` projection remains API-compatible. -/
private def choosePlanPrepared (b : Nat) (blk : Array Int) :
    SubPlan × Option (Array Int) :=
  if blk.all (fun x => x == blk.getD 0 0) then (.constant, none)
  else
    let blkF := blockF blk
    match fixedSearchF b blkF, lpcChoiceF b blkF with
    | none, none => (.verbatim, none)
    | none, some lc =>
      if lc.cost < b * blk.size then preparedLpc blk lc else (.verbatim, none)
    | some ((ord, po, ks), cost), none =>
      if cost < b * blk.size then (.fixed ord po ks, none) else (.verbatim, none)
    | some ((ord, po, ks), cost), some lc =>
      if lc.cost ≤ cost then
        if lc.cost < b * blk.size then preparedLpc blk lc else (.verbatim, none)
      else
        if cost < b * blk.size then (.fixed ord po ks, none) else (.verbatim, none)

/-- The default subframe chooser (constant detection, fixed vs LPC by
    exact cost, LPC preferred on ties, verbatim when prediction does not
    pay), exactly as `Heuristics.defaultChooser` decides it. -/
def choosePlan (b : Nat) (blk : Array Int) : SubPlan :=
  (choosePlanPrepared b blk).1

/-! ## Writers -/

/-- Rice-code `res[i] … res[stop-1]` with parameter `k`, carrying the
    writer state **unpacked**: `buf`/`acc`/`n` as three parameters rather
    than a `BitWriter`, so the per-sample path allocates nothing at all
    (a `UInt64` function parameter stays in a register, a `BitWriter`
    field does not). One `BitWriter` is built per partition, on exit.

    `mask = 2^k - 1` is hoisted by the caller. `q ≥ 32` (a residual more
    than 32·2^k from zero) is rare enough to hand back to `pushRice`. -/
def pushRiceRange (k mask : Nat) (res : Array Int) :
    (i stop : Nat) → (buf : ByteArray) → (acc : UInt64) → (n : Nat) → BitWriter
  | i, stop, buf, acc, n =>
    if h : i < stop then
      let x := res.getD i 0
      let u := if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1
      let q := u >>> k
      if q < 32 then
        -- unary quotient: `q` zero bits then a one bit — the low `q+1`
        -- bits of the value 1
        let acc1 := (acc <<< UInt64.ofNat (q + 1)) ||| 1
        let n1 := n + q + 1
        let buf1 := BitWriter.flushBytes buf acc1 n1
        -- then the `k` remainder bits
        let acc2 := (acc1 <<< UInt64.ofNat k) ||| UInt64.ofNat (u &&& mask)
        let n2 := n1 % 8 + k
        pushRiceRange k mask res (i + 1) stop (BitWriter.flushBytes buf1 acc2 n2) acc2 (n2 % 8)
      else
        let w := (BitWriter.mk buf acc n).pushRice k x
        pushRiceRange k mask res (i + 1) stop w.buf w.acc w.n
    else ⟨buf, acc, n⟩
  termination_by i stop => stop - i

/-- Partitioned coded residual (method RICE, the only one the default
    heuristics emit). -/
def pushResidual (bw : BitWriter) (bs ord po : Nat) (ks : Array Nat)
    (res : Array Int) : BitWriter := Id.run do
  let mut w := (bw.push 2 0).push 4 po
  let c := bs / p2 po
  let mut start := 0
  for j in [0 : p2 po] do
    let len := if j = 0 then c - ord else c
    let k := ks.getD j 10
    w := w.push 4 k
    w := pushRiceRange k (p2 k - 1) res start (start + len) w.buf w.acc w.n
    start := start + len
  return w

/-- One subframe at bit depth `b`: wasted-bit detection, subframe search
    on the scaled block, then the exact layout of `Subframe.write`. -/
def pushSubframe (bw : BitWriter) (b : Nat) (blk : Array Int) : BitWriter := Id.run do
  let wa := wastedDetectF b blk
  let scaled := if wa = 0 then blk else
    let m : Int := ((p2 wa : Nat) : Int)
    blk.map (· / m)
  let b' := b - wa
  let (plan, lpcRes) := choosePlanPrepared b' scaled
  let mut w := (bw.push 1 0).push 6 plan.typeCode
  w := if wa = 0 then w.push 1 0 else (w.push 1 1).pushUnary (wa - 1)
  match plan with
  | .constant => return w.pushSInt b' (scaled.getD 0 0)
  | .verbatim =>
    for x in scaled do
      w := w.pushSInt b' x
    return w
  | .fixed ord po ks =>
    let mut d := scaled
    for i in [0 : ord] do
      w := w.pushSInt b' (scaled.getD i 0)
      d := diffArr d
    return pushResidual w scaled.size ord po ks d
  | .lpc cs shift po ks =>
    let ord := cs.length
    for i in [0 : ord] do
      w := w.pushSInt b' (scaled.getD i 0)
    w := (w.push 4 (12 - 1)).pushSInt 5 (shift : Int)
    for cf in cs do
      w := w.pushSInt 12 cf
    let res := match lpcRes with
      | some cached => cached
      | none => lpcResidualArr cs shift scaled
    return pushResidual w scaled.size ord po ks res

def sumAbsArr (xs : Array Int) : Nat :=
  xs.foldl (fun a x => a + x.natAbs) 0

/-- One frame: stereo-mode decision (`Heuristics.stereoPick`), canonical
    header (blocksize code 7, sample rate from STREAMINFO), subframes,
    byte-alignment, CRCs over the emitted bytes. `bw` must be
    byte-aligned on entry (frames always are). -/
def pushFrame (bw : BitWriter) (b : Nat) (strat : Bool) (num : Nat)
    (chs : Array (Array Int)) : BitWriter := Id.run do
  let bs := (chs.getD 0 #[]).size
  -- (chCode, subframe plan as (depth, samples) pairs)
  let (chCode, plan) : Nat × Array (Nat × Array Int) :=
    if h : chs.size = 2 then
      let l := chs.getD 0 #[]
      let r := chs.getD 1 #[]
      let sd := l.zipWith (fun a b => a - b) r
      let md := l.zipWith (fun a b => sar (a + b) 1) r
      let al := sumAbsArr l
      let ar := sumAbsArr r
      let sa := sumAbsArr sd
      let am := sumAbsArr md
      if al + ar ≤ al + sa ∧ al + ar ≤ sa + ar ∧ al + ar ≤ am + sa then
        (1, #[(b, l), (b, r)])
      else if al + sa ≤ sa + ar ∧ al + sa ≤ am + sa then
        (8, #[(b, l), (b + 1, sd)])
      else if sa + ar ≤ am + sa then
        (9, #[(b + 1, sd), (b, r)])
      else
        (10, #[(b, md), (b + 1, sd)])
    else
      (chs.size - 1, chs.map ((b, ·)))
  let start := bw.buf.size
  let mut w := (((bw.push 14 0x3FFE).push 1 0).push 1 (if strat then 1 else 0)).push 4 7
  w := ((w.push 4 0).push 4 chCode).push 3 (Frame.bpsCode b)
  w := (w.push 1 0).pushUtf8 num
  w := w.push 16 (bs - 1)
  w := w.push 8 (Crc.crc8Range w.buf start w.buf.size).toNat
  for p in plan do
    w := pushSubframe w p.1 p.2
  w := w.align
  return w.push 16 (Crc.crc16Range w.buf start w.buf.size).toNat

/-! ## 16-bit PCM entry point -/

/-- One little-endian 16-bit sample at byte offset `j`. -/
@[inline] private def sampleAt (bytes : ByteArray) (j : Nat) : Int :=
  let lo := (if h : j < bytes.size then bytes[j] else 0).toNat
  let hi := (if h : j + 1 < bytes.size then bytes[j + 1] else 0).toNat
  let v := lo + 256 * hi
  if v < 32768 then (v : Int) else (v : Int) - 65536

/-- Channel arrays for the sample window `[lo, hi)`, read straight from
    the interleaved PCM bytes. -/
def frameChannels (bytes : ByteArray) (ch lo hi : Nat) : Array (Array Int) :=
  Id.run do
    let len := hi - lo
    if ch = 1 then
      let mut a : Array Int := Array.emptyWithCapacity len
      for i in [lo : hi] do
        a := a.push (sampleAt bytes (2 * i))
      return #[a]
    if ch = 2 then
      let mut a : Array Int := Array.emptyWithCapacity len
      let mut b : Array Int := Array.emptyWithCapacity len
      for i in [lo : hi] do
        a := a.push (sampleAt bytes (4 * i))
        b := b.push (sampleAt bytes (4 * i + 2))
      return #[a, b]
    let mut chans : Array (Array Int) := Array.emptyWithCapacity ch
    for c in [0 : ch] do
      let mut a : Array Int := Array.emptyWithCapacity len
      for i in [lo : hi] do
        a := a.push (sampleAt bytes (2 * (i * ch + c)))
      chans := chans.push a
    return chans

/-- One frame straight from the interleaved PCM bytes. -/
def frameBytesPcm (blockSize ch bps : Nat) (varBlk : Bool)
    (bytes : ByteArray) (n f : Nat) : ByteArray :=
  let lo := f * blockSize
  let hi := min (lo + blockSize) n
  (pushFrame (BitWriter.empty ((hi - lo) * ch * 2 + 64)) bps varBlk
    (if varBlk then f * blockSize else f) (frameChannels bytes ch lo hi)).buf

/-- Fast byte-level 16-bit encoder (the MD5 input of RFC 9639 §8.2 for
    16-bit interleaved LE PCM is the input byte string itself).

    Each frame worker deinterleaves its own window out of the shared PCM
    bytes. Deinterleaving the whole file up front was serial (17% of
    encode) and the per-frame `Array.extract` then copied every sample a
    second time; both are gone, and the workers read a shared immutable
    `ByteArray` instead. -/
def encodePcm16 (blockSize ch sr : Nat) (bytes : ByteArray) : ByteArray :=
  Id.run do
    if ch = 0 then return ByteArray.empty
    let n := bytes.size / (2 * ch)
    let md5 := Md5.md5 bytes
    let mut w := BitWriter.empty 64
    w := w.push 32 0x664C6143
    w := ((w.push 1 1).push 7 0).push 24 34
    w := (w.push 16 blockSize).push 16 blockSize
    w := (w.push 24 0).push 24 0
    w := ((w.push 20 sr).push 3 (ch - 1)).push 5 (16 - 1)
    w := w.pushBits 36 n
    for byte in md5.toList do
      w := w.push 8 byte.toNat
    if blockSize = 0 then return w.buf
    let tasks := (List.range ((n + blockSize - 1) / blockSize)).map fun f =>
      Task.spawn fun _ => frameBytesPcm blockSize ch 16 false bytes n f
    let mut out := w.buf
    for t in tasks do
      out := out ++ t.get
    return out

end Flac.Encode
