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
    `acc` are pending; `n < 8` between pushes. `UInt64` throughout — its
    shifts and masks are unboxed intrinsics, unlike scalar `Nat` ops. -/
structure BitWriter where
  buf : ByteArray
  acc : UInt64
  n : Nat

namespace BitWriter

def empty (cap : Nat) : BitWriter := ⟨ByteArray.emptyWithCapacity cap, 0, 0⟩

/-- Emit completed bytes out of the accumulator. -/
def flushGo (buf : ByteArray) (acc : UInt64) (n : Nat) : ByteArray × UInt64 × Nat :=
  if h : n < 8 then (buf, acc, n)
  else
    let hi := n - 8
    flushGo (buf.push (acc >>> UInt64.ofNat hi).toUInt8)
      (acc &&& ((1 <<< UInt64.ofNat hi) - 1)) hi
termination_by n
decreasing_by omega

/-- Push the low `k` bits of `v`, MSB first. Requires `k ≤ 32` so the
    accumulator never overflows (`n + k ≤ 39`); use `pushBits` for wider
    fields. -/
def push (bw : BitWriter) (k : Nat) (v : Nat) : BitWriter :=
  let kk := UInt64.ofNat k
  let (buf, acc, n) := flushGo bw.buf
    ((bw.acc <<< kk) ||| (UInt64.ofNat v &&& ((1 <<< kk) - 1))) (bw.n + k)
  ⟨buf, acc, n⟩

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

/-! ## Residual searches (exact mirrors of `Flac.Heuristics`) -/

@[inline] private def foldResidual (x : Int) : Nat :=
  if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1

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

/-- Mirror of `Heuristics.partitionSearch`, fed by the residual directly:
    one pass folds each residual (zigzag) into its finest-partition sum;
    each candidate order then costs O(partitions). -/
def partitionSearchF (bs ord : Nat) (res : Array Int) : Nat × Array Nat × Nat := Id.run do
  let pomax := partitionMaxF bs ord
  let cF := bs / p2 pomax
  let mut sums : Array Nat := Array.emptyWithCapacity (p2 pomax)
  let mut acc := 0
  let mut left := cF - ord
  for i in [0 : res.size] do
    let x := res.getD i 0
    acc := acc + foldResidual x
    left := left - 1
    if left = 0 then
      sums := sums.push acc
      acc := 0
      left := cF
  return partitionSearchSumsF bs ord pomax sums

/-- First differences (`Fixed.diff1` over arrays). -/
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

/-- Evaluate one LPC candidate directly into finest-partition sums. This
    performs the same residual arithmetic and visits values in the same
    order as `lpcResidualArr` followed by `partitionSearchF`, but does not
    allocate a block-sized residual for a candidate that may lose. -/
private def lpcPartitionSearchF (cs : List Int) (shift : Nat) (xs : Array Int) :
    Nat × Array Nat × Nat := Id.run do
  let ord := cs.length
  let pomax := partitionMaxF xs.size ord
  let cF := xs.size / p2 pomax
  let mut sums : Array Nat := Array.emptyWithCapacity (p2 pomax)
  let mut acc := 0
  let mut left := cF - ord
  for h : i in [ord : xs.size] do
    have hlo : cs.length ≤ i := by simpa only [ord] using h.1
    have hhi : i < xs.size := h.2.1
    let s := lpcDotF xs cs i hlo (Nat.le_of_lt hhi) 0
    let x := xs[i] - sar s shift
    acc := acc + foldResidual x
    left := left - 1
    if left = 0 then
      sums := sums.push acc
      acc := 0
      left := cF
  return partitionSearchSumsF xs.size ord pomax sums

/-- Mirror of `Heuristics.fixedSearch`: all orders 0–4 with exact
    (sum-estimated-partition) costs off the difference cascade. -/
def fixedSearchF (b : Nat) (blk : Array Int) :
    Option ((Nat × Nat × Array Nat) × Nat) := Id.run do
  let mut best : Option ((Nat × Nat × Array Nat) × Nat) := none
  let mut d := blk
  for ord in [0 : 5] do
    if ord + 1 ≤ blk.size then
      let (po, ks, rcost) := partitionSearchF blk.size ord d
      let cost := ord * b + rcost
      match best with
      | some (_, c) => if cost < c then best := some ((ord, po, ks), cost)
      | none => best := some ((ord, po, ks), cost)
      d := diffArr d
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
private def lpcChoiceF (b : Nat) (blk : Array Int) : Option LpcChoice := Id.run do
  if blk.size < 16 then
    return none
  let r := Heuristics.autocorrF (Heuristics.welchF blk) 8
  if !(r.getD 0 (Float.ofBits 0) > Float.ofBits 0) then
    return none
  let ord := Heuristics.pickLpcOrder b blk.size (Heuristics.levinsonErrs r 8)
  let mut best : Option LpcChoice := none
  for o in (if ord = 1 ∨ ord = 2 ∨ ord = 4 ∨ ord = 6 ∨ ord = 8 then [1, 2, 4, 6, 8] else [ord, 1, 2, 4, 6, 8]) do
    let (cs, shift) := Heuristics.quantizeCoefs (Heuristics.levinson r o).toList 12
    let (po, ks, rcost) := lpcPartitionSearchF cs shift blk
    let cost := o * b + 9 + o * 12 + rcost
    match best with
    | some old => if cost < old.cost then best := some ⟨cs, shift, po, ks, cost⟩
    | none => best := some ⟨cs, shift, po, ks, cost⟩
  return best

/-- Mirror of `Heuristics.lpcSearch`, estimate-first (the libFLAC
    discipline), preserving the existing result API and tie-breaking. -/
def lpcSearchF (b : Nat) (blk : Array Int) :
    Option ((List Int × Nat × Nat × Array Nat) × Nat) :=
  match lpcChoiceF b blk with
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
    match fixedSearchF b blk, lpcChoiceF b blk with
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
    for i in [start : start + len] do
      w := w.pushRice k (res.getD i 0)
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

/-- One frame into its own buffer (frames are byte-aligned and
    self-contained, so they can be encoded independently). -/
def frameBytes (blockSize : Nat) (bps : Nat) (varBlk : Bool)
    (chs : Array (Array Int)) (n f : Nat) : ByteArray :=
  let lo := f * blockSize
  let hi := min (lo + blockSize) n
  (pushFrame (BitWriter.empty ((hi - lo) * chs.size * 2 + 64)) bps varBlk
    (if varBlk then f * blockSize else f) (chs.map (·.extract lo hi))).buf

/-- The full stream: `fLaC` marker, STREAMINFO, frames — the exact
    layout of `Stream.writeStream` under the default heuristics. Frames
    are encoded in parallel (`Task` per frame) and concatenated in order,
    so the output is byte-for-byte what the serial encoder writes. -/
def encodeArrays (blockSize : Nat) (varBlk : Bool) (chs : Array (Array Int))
    (bps sr : Nat) (md5 : ByteArray) : ByteArray := Id.run do
  let n := (chs.getD 0 #[]).size
  let mut w := BitWriter.empty 64
  w := w.push 32 0x664C6143
  w := ((w.push 1 1).push 7 0).push 24 34
  w := (w.push 16 blockSize).push 16 blockSize
  w := (w.push 24 0).push 24 0
  w := ((w.push 20 sr).push 3 (chs.size - 1)).push 5 (bps - 1)
  w := w.pushBits 36 n
  for byte in md5.toList do
    w := w.push 8 byte.toNat
  if blockSize = 0 then return w.buf
  let tasks := (List.range ((n + blockSize - 1) / blockSize)).map fun f =>
    Task.spawn fun _ => frameBytes blockSize bps varBlk chs n f
  let mut out := w.buf
  for t in tasks do
    out := out ++ t.get
  return out

/-! ## 16-bit PCM entry point -/

/-- One little-endian 16-bit sample at byte offset `j`. -/
@[inline] private def sampleAt (bytes : ByteArray) (j : Nat) : Int :=
  let lo := (if h : j < bytes.size then bytes[j] else 0).toNat
  let hi := (if h : j + 1 < bytes.size then bytes[j + 1] else 0).toNat
  let v := lo + 256 * hi
  if v < 32768 then (v : Int) else (v : Int) - 65536

/-- Deinterleave signed 16-bit little-endian PCM into channel arrays.
    Channel-major: each channel array is filled by its own loop, so a
    sample costs one `Array.push`. The sample-major version updated the
    outer array of channels once per sample (`Array.modify`), which made
    deinterleaving 17% of encode time and all of it serial. -/
def pcm16Channels (ch : Nat) (bytes : ByteArray) : Array (Array Int) := Id.run do
  if ch = 0 then return #[]
  let n := bytes.size / (2 * ch)
  if ch = 1 then
    let mut a : Array Int := Array.emptyWithCapacity n
    for i in [0 : n] do
      a := a.push (sampleAt bytes (2 * i))
    return #[a]
  if ch = 2 then
    let mut a : Array Int := Array.emptyWithCapacity n
    let mut b : Array Int := Array.emptyWithCapacity n
    for i in [0 : n] do
      a := a.push (sampleAt bytes (4 * i))
      b := b.push (sampleAt bytes (4 * i + 2))
    return #[a, b]
  let mut chans : Array (Array Int) := Array.emptyWithCapacity ch
  for c in [0 : ch] do
    let mut a : Array Int := Array.emptyWithCapacity n
    for i in [0 : n] do
      a := a.push (sampleAt bytes (2 * (i * ch + c)))
    chans := chans.push a
  return chans

/-- Fast byte-level 16-bit encoder (the MD5 input of RFC 9639 §8.2 for
    16-bit interleaved LE PCM is the input byte string itself). -/
def encodePcm16 (blockSize ch sr : Nat) (bytes : ByteArray) : ByteArray :=
  encodeArrays blockSize false (pcm16Channels ch bytes) 16 sr (Md5.md5 bytes)

end Flac.Encode
