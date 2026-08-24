import Flac.Native.Heuristics
import Flac.Native.Md5
import Flac.Native.Crc
import Flac.Native.Emit

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

/-- Shift the low `k` bits of `v` into the accumulator, MSB first. The one
    accumulator step: `push` and the hot residual loop (`pushRiceRange`,
    which carries `buf`/`acc`/`n` unpacked) both go through it, so the
    latter is *definitionally* a `push` and needs no separate proof. -/
@[inline] def accPush (acc : UInt64) (k v : Nat) : UInt64 :=
  let kk := UInt64.ofNat k
  (acc <<< kk) ||| (UInt64.ofNat v &&& ((1 <<< kk) - 1))

/-- Push the low `k` bits of `v`, MSB first. Requires `k ≤ 32` so the
    accumulator never overflows (`n + k ≤ 39`); use `pushBits` for wider
    fields. -/
def push (bw : BitWriter) (k : Nat) (v : Nat) : BitWriter :=
  let acc := accPush bw.acc k v
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

/-- Rice code from an already-folded magnitude (the rare wide-quotient
    path of `pushRiceRange`). -/
def pushRiceFolded (bw : BitWriter) (k u : Nat) : BitWriter :=
  (bw.pushUnary (u >>> k)).push k (u &&& (p2 k - 1))

/-- Continuation bytes of a coded number (the shape of
    `Emit.W.pushConts`). -/
def pushConts (v : Nat) : (k : Nat) → BitWriter → BitWriter
  | 0, bw => bw
  | k + 1, bw => pushConts v k (bw.push 8 (0x80 + v / p2 (6 * k) % 64))

/-- Coded number (mirrors `Flac.Utf8Num.write`). -/
def pushUtf8 (bw : BitWriter) (v : Nat) : BitWriter :=
  if v < p2 7 then bw.push 8 v
  else if v < p2 11 then pushConts v 1 (bw.push 8 (0xC0 + v / p2 6))
  else if v < p2 16 then pushConts v 2 (bw.push 8 (0xE0 + v / p2 12))
  else if v < p2 21 then pushConts v 3 (bw.push 8 (0xF0 + v / p2 18))
  else if v < p2 26 then pushConts v 4 (bw.push 8 (0xF8 + v / p2 24))
  else if v < p2 31 then pushConts v 5 (bw.push 8 (0xFC + v / p2 30))
  else pushConts v 6 (bw.push 8 0xFE)

/-- Fixed-width run over `xs[start .. start+len)`, stopping at the array
    end (the shape of `Emit.W.pushSIntSeg`). -/
def pushSIntSeg (b : Nat) (xs : Array Int) :
    (start len : Nat) → BitWriter → BitWriter
  | _, 0, bw => bw
  | start, len + 1, bw =>
    if start < xs.size then
      pushSIntSeg b xs (start + 1) len (bw.pushSInt b (xs.getD start 0))
    else bw

/-- Fixed-width run over a (short) list — LPC coefficients (the shape of
    `Emit.W.pushSIntList`). -/
def pushSIntList (b : Nat) : List Int → BitWriter → BitWriter
  | [], bw => bw
  | x :: xs, bw => pushSIntList b xs (bw.pushSInt b x)

end BitWriter

/-! ## Residual searches (exact mirrors of `Flac.Heuristics`)

### Why the searches run on `Float`

A candidate search only *chooses* a subframe; every bit is emitted from
the exact `Int` residual (`Emit.fixedResA` / `Emit.lpcResA`, written by
`pushResidual`). That boundary is load-bearing, and it is what makes
emission provable: a `Float` in the emitted bytes could never be reasoned
about, since Lean's `Float` operations are compiler intrinsics with no
axiomatization — there are no equations to rewrite with. Costing
candidates in `Float` stays free, because a search that picks the wrong
candidate loses compression, never correctness.

Every quantity a search computes is an
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
    `xs[n-1], …`, in floats: the coefficients
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

/-! ### The fused fixed-order pass

The order-`ord` fixed residual is the `ord`-th finite difference, so one
traversal carrying the difference ladder yields all five residual streams
at once: one array read per sample instead of five, and no block-sized
difference array at any order. `FixedSums` is nine `Float`s — the previous
value of each difference order and the running folded sum of each — passed
as tail-recursion parameters so they stay unboxed.

The finest partitioning used is the one legal at order 0 (`partitionMaxF`
is antitone in `ord`); each order's own partitioning is a coarsening, and
partition sums nest, so `aggrSums` recovers it by adding consecutive
entries. Sample `i` belongs to order `ord`'s residual only for `i ≥ ord`,
which is what the guarded `fixedFoldHead` handles for the first four
samples. -/

/-- Difference-ladder state and per-order folded sums. -/
private structure FixedSums where
  /-- Previous value of the `k`-th difference, `k = 0 … 3`. -/
  l0 : Float
  l1 : Float
  l2 : Float
  l3 : Float
  /-- Running folded sum of the order-`k` residual, `k = 0 … 4`. -/
  a0 : Float
  a1 : Float
  a2 : Float
  a3 : Float
  a4 : Float

/-- Samples `[i, stop)` with `i < 4`: the ladder is warmed here, and order
    `ord` starts accumulating at sample `ord`. -/
private def fixedFoldHead (xs : FloatArray) :
    (i stop : Nat) → stop ≤ xs.size → FixedSums → FixedSums
  | i, stop, hs, s =>
    if h : i < stop then
      have hi : i < xs.size := by omega
      let e0 := xs[i]
      let e1 := e0 - s.l0
      let e2 := e1 - s.l1
      let e3 := e2 - s.l2
      let e4 := e3 - s.l3
      fixedFoldHead xs (i + 1) stop hs
        { l0 := e0, l1 := e1, l2 := e2, l3 := e3,
          a0 := s.a0 + foldF e0,
          a1 := if 1 ≤ i then s.a1 + foldF e1 else s.a1,
          a2 := if 2 ≤ i then s.a2 + foldF e2 else s.a2,
          a3 := if 3 ≤ i then s.a3 + foldF e3 else s.a3,
          a4 := if 4 ≤ i then s.a4 + foldF e4 else s.a4 }
    else s
  termination_by i stop => stop - i

/-- Samples `[i, stop)` with `4 ≤ i`: every order accumulates, so the loop
    carries no guards and no boxed state. -/
private def fixedFoldTail (xs : FloatArray) :
    (i stop : Nat) → stop ≤ xs.size →
    (l0 l1 l2 l3 a0 a1 a2 a3 a4 : Float) → FixedSums
  | i, stop, hs, l0, l1, l2, l3, a0, a1, a2, a3, a4 =>
    if h : i < stop then
      have hi : i < xs.size := by omega
      let e0 := xs[i]
      let e1 := e0 - l0
      let e2 := e1 - l1
      let e3 := e2 - l2
      let e4 := e3 - l3
      fixedFoldTail xs (i + 1) stop hs e0 e1 e2 e3
        (a0 + foldF e0) (a1 + foldF e1) (a2 + foldF e2) (a3 + foldF e3) (a4 + foldF e4)
    else ⟨l0, l1, l2, l3, a0, a1, a2, a3, a4⟩
  termination_by i stop => stop - i

/-- Finest-partition folded sums for fixed orders 0–4, one entry per
    order. -/
private def fixedPartitionSums (xs : FloatArray) : Array (Array Nat) := Id.run do
  let np := p2 (partitionMaxF xs.size 0)
  let cP := xs.size / np
  let mut s0 : Array Nat := Array.emptyWithCapacity np
  let mut s1 : Array Nat := Array.emptyWithCapacity np
  let mut s2 : Array Nat := Array.emptyWithCapacity np
  let mut s3 : Array Nat := Array.emptyWithCapacity np
  let mut s4 : Array Nat := Array.emptyWithCapacity np
  let mut st : FixedSums := ⟨ff0, ff0, ff0, ff0, ff0, ff0, ff0, ff0, ff0⟩
  for j in [0 : np] do
    let lo := j * cP
    let hi := (j + 1) * cP
    let split := max lo (min 4 hi)
    if hh : hi ≤ xs.size then
      let st1 := if hs : split ≤ xs.size then fixedFoldHead xs lo split hs st else st
      let st2 := fixedFoldTail xs split hi hh
        st1.l0 st1.l1 st1.l2 st1.l3 st1.a0 st1.a1 st1.a2 st1.a3 st1.a4
      s0 := s0.push st2.a0.toUInt64.toNat
      s1 := s1.push st2.a1.toUInt64.toNat
      s2 := s2.push st2.a2.toUInt64.toNat
      s3 := s3.push st2.a3.toUInt64.toNat
      s4 := s4.push st2.a4.toUInt64.toNat
      st := { st2 with a0 := ff0, a1 := ff0, a2 := ff0, a3 := ff0, a4 := ff0 }
  return #[s0, s1, s2, s3, s4]

/-- Coarsen finest-partition sums by adding groups of `group` consecutive
    entries (partition orders nest, so this is exact). -/
private def aggrSums (sums : Array Nat) (group : Nat) : Array Nat := Id.run do
  if group ≤ 1 then return sums
  let mut out : Array Nat := Array.emptyWithCapacity (sums.size / group + 1)
  for j in [0 : sums.size / group] do
    let mut acc := 0
    for w in [j * group : (j + 1) * group] do
      acc := acc + sums.getD w 0
    out := out.push acc
  return out

/-- Mirror of `Heuristics.fixedSearch`: all orders 0–4 with exact
    (sum-estimated-partition) costs, off one fused pass. -/
def fixedSearchF (b : Nat) (blkF : FloatArray) :
    Option ((Nat × Nat × Array Nat) × Nat) := Id.run do
  if blkF.size = 0 then return none
  let sums := fixedPartitionSums blkF
  let pfinest := partitionMaxF blkF.size 0
  let mut best : Option ((Nat × Nat × Array Nat) × Nat) := none
  for ord in [0 : 5] do
    if ord + 1 ≤ blkF.size then
      let pm := partitionMaxF blkF.size ord
      let (po, ks, rcost) := partitionSearchSumsF blkF.size ord pm
        (aggrSums (sums.getD ord #[]) (p2 (pfinest - pm)))
      let cost := ord * b + rcost
      match best with
      | some (_, c) => if cost < c then best := some ((ord, po, ks), cost)
      | none => best := some ((ord, po, ks), cost)
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
  let r := Heuristics.autocorrF (welchFf blkF) Heuristics.lpcMaxOrder
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

/-- The default subframe chooser (constant detection, fixed vs LPC by
    exact cost, LPC preferred on ties, verbatim when prediction does not
    pay), exactly as `Heuristics.defaultChooser` decides it. Takes the
    block's `Float` image, which the caller has already built. -/
def choosePlanF (b : Nat) (blk : Array Int) (blkF : FloatArray) : SubPlan :=
  if blk.all (fun x => x == blk.getD 0 0) then .constant
  else
    match fixedSearchF b blkF, lpcChoiceF b blkF with
    | none, none => .verbatim
    | none, some lc =>
      if lc.cost < b * blk.size then .lpc lc.cs lc.shift lc.po lc.ks else .verbatim
    | some ((ord, po, ks), cost), none =>
      if cost < b * blk.size then .fixed ord po ks else .verbatim
    | some ((ord, po, ks), cost), some lc =>
      if lc.cost ≤ cost then
        if lc.cost < b * blk.size then .lpc lc.cs lc.shift lc.po lc.ks else .verbatim
      else
        if cost < b * blk.size then .fixed ord po ks else .verbatim

@[inherit_doc choosePlanF]
def choosePlan (b : Nat) (blk : Array Int) : SubPlan :=
  choosePlanF b blk (blockF blk)

def sumAbsArr (xs : Array Int) : Nat :=
  xs.foldl (fun a x => a + x.natAbs) 0

/-! ## Search / emission split

`chooseSub`/`chooseFrame` make every heuristic decision a frame needs;
`pushSubframeOf`/`pushFrameOf` then only *emit*. The bytes are unchanged —
`pushFrame` is still emission after search — but each search is now a named
function of its inputs, which is what lets the emission side be proven
against `Flac.Emit` while the searches (`Float`, hence uncharacterizable)
are only ever *applied*, never reasoned about. -/

/-- One subframe's decision, plus the two arrays it was made from: the
    wasted-bit-scaled samples and their `Float` image (the search reads
    the latter; emission reads the former). `⟨depth, wasted, plan⟩` is the
    decision proper — the array mirror of `Subframe.SubCfg`. -/
structure SubPrep where
  depth : Nat
  wasted : Nat
  plan : SubPlan
  scaled : Array Int
  scaledF : FloatArray

/-- The search for one subframe at depth `b`: wasted-bit detection, then
    the plan search on the scaled block at the reduced depth. The array
    mirror of `Heuristics.defaultSubCfg`. -/
def chooseSub (b : Nat) (blk : Array Int) : SubPrep :=
  let wa := wastedDetectF b blk
  let scaled := if wa = 0 then blk else
    let m : Int := ((p2 wa : Nat) : Int)
    blk.map (· / m)
  let scaledF := blockF scaled
  ⟨b, wa, choosePlanF (b - wa) scaled scaledF, scaled, scaledF⟩

/-- One frame's decisions: the 4-bit channel code, the block size, and one
    `SubPrep` per subframe — the array mirror of `Frame.ChannelAsg` paired
    with the `(depth, samples)` list `Frame.subframePlan` derives from it. -/
structure FramePrep where
  chCode : Nat
  blockSize : Nat
  subs : List SubPrep

/-- The per-frame search: stereo-mode decision by the sum-of-magnitudes
    proxy (`Heuristics.stereoPick`) for two channels, independent coding
    otherwise, then `chooseSub` per subframe at the decorrelated depth.
    The array mirror of `Heuristics.defaultAsgChooser`. -/
def chooseFrame (b : Nat) (chs : Array (Array Int)) : FramePrep :=
  let bs := (chs.getD 0 #[]).size
  if chs.size = 2 then
    let l := chs.getD 0 #[]
    let r := chs.getD 1 #[]
    let sd := l.zipWith (fun a b => a - b) r
    let md := l.zipWith (fun a b => sar (a + b) 1) r
    let al := sumAbsArr l
    let ar := sumAbsArr r
    let sa := sumAbsArr sd
    let am := sumAbsArr md
    if al + ar ≤ al + sa ∧ al + ar ≤ sa + ar ∧ al + ar ≤ am + sa then
      ⟨1, bs, [chooseSub b l, chooseSub b r]⟩
    else if al + sa ≤ sa + ar ∧ al + sa ≤ am + sa then
      ⟨8, bs, [chooseSub b l, chooseSub (b + 1) sd]⟩
    else if sa + ar ≤ am + sa then
      ⟨9, bs, [chooseSub (b + 1) sd, chooseSub b r]⟩
    else
      ⟨10, bs, [chooseSub b md, chooseSub (b + 1) sd]⟩
  else
    ⟨chs.size - 1, bs, (chs.map (chooseSub b)).toList⟩

/-! ## Writers -/

/-- Rice-code `res[i] … res[stop-1]` with parameter `k`, carrying the
    writer state **unpacked**: `buf`/`acc`/`n` as three parameters rather
    than a `BitWriter`, so the per-sample path allocates nothing at all
    (a `UInt64` function parameter stays in a register, a `BitWriter`
    field does not). One `BitWriter` is built per partition, on exit.

    `mask = 2^k - 1` is hoisted by the caller. `q ≥ 32` (a residual more
    than 32·2^k from zero) is rare enough to hand back to `pushRice`.

    The residual is an exact `Array Int`: every bit a subframe emits comes
    from this path, never from the `Float` search arrays. -/
def pushRiceRange (k mask : Nat) (res : Array Int) :
    (i stop : Nat) → (buf : ByteArray) → (acc : UInt64) → (n : Nat) → BitWriter
  | i, stop, buf, acc, n =>
    if h : i < stop then
      let x := res.getD i 0
      let u := if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1
      let q := u >>> k
      if q < 32 then
        let acc1 := BitWriter.accPush acc (q + 1) 1
        let n1 := n + (q + 1)
        let buf1 := BitWriter.flushBytes buf acc1 n1
        let acc2 := BitWriter.accPush acc1 k u
        let n2 := n1 % 8 + k
        pushRiceRange k mask res (i + 1) stop
          (BitWriter.flushBytes buf1 acc2 n2) acc2 (n2 % 8)
      else
        let w := (BitWriter.mk buf acc n).pushRiceFolded k u
        pushRiceRange k mask res (i + 1) stop w.buf w.acc w.n
    else ⟨buf, acc, n⟩
  termination_by i stop => stop - i

/-- The per-partition Rice parameters as the reference's choice list. The
    fast plan carries `ks : Array Nat`; `Rice.Partition` is what
    `Emit.W.pushParts` consumes. -/
def riceChoices (po : Nat) (ks : Array Nat) : List Rice.Partition :=
  (List.range (p2 po)).map fun j => .rice (ks.getD j 10)

/-- The partitions of a coded residual, one `(choice, size)` pair at a time
    — the shape of `Emit.W.pushParts`. -/
def pushPartsR (m : Rice.Method) (res : Array Int) :
    (choices : List Rice.Partition) → (sizes : List Nat) → (start : Nat) →
      BitWriter → BitWriter
  | [], _, _, bw => bw
  | _ :: _, [], _, bw => bw
  | ch :: choices, sz :: sizes, start, bw =>
    let bw' := match ch with
      | .rice k =>
        let w := bw.push m.paramBits k
        pushRiceRange k (p2 k - 1) res start (start + sz) w.buf w.acc w.n
      | .escape bits =>
        BitWriter.pushSIntSeg bits res start sz
          ((bw.push m.paramBits m.escapeCode).push 5 bits)
    pushPartsR m res choices sizes (start + sz) bw'

/-- The reference residual configuration a fast plan's `(po, ks)` denotes —
    the residual half of the plan correspondence. -/
def riceCfgOf (po : Nat) (ks : Array Nat) : Rice.ResidualCfg :=
  ⟨.rice4, po, riceChoices po ks⟩

/-- The reference subframe configuration a fast plan denotes — the plan
    correspondence at the subframe level. `SubPlan.typeCode` and
    `Subframe.SubframeCfg.typeCode` agree by construction. -/
def subCfgOf : SubPlan → Subframe.SubframeCfg
  | .constant => .constant
  | .verbatim => .verbatim
  | .fixed ord po ks => .fixed ord (riceCfgOf po ks)
  | .lpc cs shift po ks => .lpc cs shift 12 (riceCfgOf po ks)

/-- A `SubPrep`'s cached block is the wasted-bit-scaled image of the block
    it was chosen from. The chooser establishes this; emission consumes
    it. -/
def SubPrep.Denotes (p : SubPrep) (xs : Array Int) : Prop :=
  p.scaled = (if p.wasted = 0 then xs else xs.map (Flac.Bits.shiftDown p.wasted))

/-- The reference subframe plan a list of decisions denotes, paired with the
    unscaled blocks they were chosen from (mirrors `Emit.planA`'s output). -/
def planOf : List (SubPrep × Array Int) →
    List ((Nat × Subframe.SubCfg) × Array Int)
  | [] => []
  | (p, xs) :: rest => ((p.depth, ⟨p.wasted, subCfgOf p.plan⟩), xs) :: planOf rest

/-- What *emission* needs of a plan, over and above the round-trip
    certificate `Subframe.SubCfg.Valid`: Rice parameters that fit the
    writer's field, and partitions that cover no more than the residual
    they code. Decidable, so the encoder can check it per call. -/
def SubPlan.EmitOk (p : SubPlan) (xs : Array Int) : Prop :=
  match p with
  | .constant => True
  | .verbatim => True
  | .fixed ord po ks =>
    (∀ j, ks.getD j 10 ≤ 32) ∧
      (Rice.partSizes xs.size po ord).sum ≤ (Emit.fixedResA ord xs).size
  | .lpc cs shift po ks =>
    (∀ j, ks.getD j 10 ≤ 32) ∧
      (Rice.partSizes xs.size po cs.length).sum ≤ (Emit.lpcResA cs shift xs).size

/-- Partitioned coded residual (method RICE, the only one the default
    heuristics emit). -/
def pushResidual (bw : BitWriter) (bs ord po : Nat) (ks : Array Nat)
    (res : Array Int) : BitWriter :=
  pushPartsR .rice4 res (riceChoices po ks) (Rice.partSizes bs po ord) 0
    ((bw.push 2 0).push 4 po)

/-- Subframe content (the shape of `Emit.W.pushContent`). -/
def pushContentOf (bw : BitWriter) (b : Nat) (pl : SubPlan) (xs : Array Int) :
    BitWriter :=
  match pl with
  | .constant => bw.pushSInt b (xs.getD 0 0)
  | .verbatim => BitWriter.pushSIntSeg b xs 0 xs.size bw
  | .fixed ord po ks =>
    pushResidual (BitWriter.pushSIntSeg b xs 0 ord bw) xs.size ord po ks
      (Emit.fixedResA ord xs)
  | .lpc cs shift po ks =>
    pushResidual
      (BitWriter.pushSIntList 12 cs
        (((BitWriter.pushSIntSeg b xs 0 cs.length bw).push 4 (12 - 1)).pushSInt 5
          (shift : Int)))
      xs.size cs.length po ks (Emit.lpcResA cs shift xs)

/-- One subframe, from its decision: the exact layout of `Subframe.write`,
    in the shape of `Emit.W.pushSubframe`. Emission only — `p` already holds
    the search result, `p.scaled` the wasted-bit-scaled block. -/
def pushSubframeOf (bw : BitWriter) (p : SubPrep) : BitWriter :=
  pushContentOf
    (if p.wasted = 0 then ((bw.push 1 0).push 6 p.plan.typeCode).push 1 0
     else (((bw.push 1 0).push 6 p.plan.typeCode).push 1 1).pushUnary
       (p.wasted - 1))
    (p.depth - p.wasted) p.plan p.scaled

/-- The subframes of a frame, one at a time (the shape of
    `Emit.W.pushPlan`). -/
def pushPlanOf : List SubPrep → BitWriter → BitWriter
  | [], bw => bw
  | p :: ps, bw => pushPlanOf ps (pushSubframeOf bw p)

/-- One frame, from its decisions: canonical header (blocksize code 7,
    sample rate from STREAMINFO), subframes, byte-alignment, CRCs over the
    emitted bytes — the shape of `Emit.W.pushFrame`. Emission only. `bw`
    must be byte-aligned on entry (frames always are). -/
def pushFrameOf (bw : BitWriter) (b : Nat) (strat : Bool) (num : Nat)
    (fp : FramePrep) : BitWriter :=
  let start := bw.buf.size
  let w1 := (((((((((bw.push 14 0x3FFE).push 1 0).push 1
    (if strat then 1 else 0)).push 4 7).push 4 0).push 4 fp.chCode).push 3
    (Frame.bpsCode b)).push 1 0).pushUtf8 num).push 16 (fp.blockSize - 1)
  let w2 := w1.push 8 (Crc.crc8Range w1.buf start w1.buf.size).toNat
  let w3 := pushPlanOf fp.subs w2
  let w4 := w3.align
  w4.push 16 (Crc.crc16Range w4.buf start w4.buf.size).toNat

/-- One frame: the search (`chooseFrame`), then emission (`pushFrameOf`). -/
def pushFrame (bw : BitWriter) (b : Nat) (strat : Bool) (num : Nat)
    (chs : Array (Array Int)) : BitWriter :=
  pushFrameOf bw b strat num (chooseFrame b chs)

/-! ## 16-bit PCM entry point -/

/-- One little-endian 16-bit sample at byte offset `j`. -/
@[inline] def sampleAt (bytes : ByteArray) (j : Nat) : Int :=
  let lo := (if h : j < bytes.size then bytes[j] else 0).toNat
  let hi := (if h : j + 1 < bytes.size then bytes[j + 1] else 0).toNat
  let v := lo + 256 * hi
  if v < 32768 then (v : Int) else (v : Int) - 65536

/-- One channel's samples for the window `[i, i+rem)`, read straight from
    the interleaved PCM bytes. Structural, so it can be related to
    `List.take`/`List.drop` of the reference's deinterleaved channel. -/
def channelSeg (bytes : ByteArray) (ch c : Nat) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    channelSeg bytes ch c (i + 1) rem
      (out.push (sampleAt bytes (2 * (i * ch + c))))

/-- Channels `[c, c+rem)` of the window `[lo, lo+len)`. -/
def frameChannelsGo (bytes : ByteArray) (ch lo len : Nat) :
    (c rem : Nat) → Array (Array Int) → Array (Array Int)
  | _, 0, out => out
  | c, rem + 1, out =>
    frameChannelsGo bytes ch lo len (c + 1) rem
      (out.push (channelSeg bytes ch c lo len (Array.emptyWithCapacity len)))

/-- Channel arrays for the sample window `[lo, hi)`, read straight from
    the interleaved PCM bytes. -/
def frameChannels (bytes : ByteArray) (ch lo hi : Nat) : Array (Array Int) :=
  frameChannelsGo bytes ch lo (hi - lo) 0 ch (Array.emptyWithCapacity ch)

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
    -- MD5 is chained, so it cannot be split across workers — but it does
    -- not have to sit on the critical path either. Spawned here and
    -- collected below, it overlaps the frame workers instead: it was
    -- 62 ms of a 550 ms 32 MB encode, all of it serial, because the
    -- STREAMINFO digest was computed before the first frame task started.
    let md5Task := Task.spawn fun _ => Md5.md5 bytes
    let frameTasks := if blockSize = 0 then [] else
      (List.range ((n + blockSize - 1) / blockSize)).map fun f =>
        Task.spawn fun _ => frameBytesPcm blockSize ch 16 false bytes n f
    let md5 := md5Task.get
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
    let mut out := w.buf
    for t in frameTasks do
      out := out ++ t.get
    return out

end Flac.Encode
