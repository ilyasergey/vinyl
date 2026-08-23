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
    `acc` are pending; `n < 8` between pushes, so `acc` stays a scalar. -/
structure BitWriter where
  buf : ByteArray
  acc : Nat
  n : Nat

namespace BitWriter

def empty (cap : Nat) : BitWriter := ⟨ByteArray.emptyWithCapacity cap, 0, 0⟩

/-- Emit completed bytes out of the accumulator. -/
def flushGo (buf : ByteArray) (acc n : Nat) : ByteArray × Nat × Nat :=
  if h : n < 8 then (buf, acc, n)
  else
    let hi := n - 8
    flushGo (buf.push (UInt8.ofNat (acc >>> hi))) (acc &&& (p2 hi - 1)) hi
termination_by n
decreasing_by omega

/-- Push the low `k` bits of `v`, MSB first. Requires `k ≤ 55` so the
    accumulator stays scalar; use `pushBits` for wider fields. -/
def push (bw : BitWriter) (k v : Nat) : BitWriter :=
  let (buf, acc, n) := flushGo bw.buf (bw.acc * p2 k + (v &&& (p2 k - 1))) (bw.n + k)
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

/-- Mirror of `Heuristics.partitionSearch`, fed by the residual directly:
    one pass folds each residual (zigzag) into its finest-partition sum
    (partition orders nest, so every coarser level's sums are pairwise
    aggregates); each candidate order then costs O(partitions). Lowest
    order wins ties, exactly like the list version. -/
def partitionSearchF (bs ord : Nat) (res : Array Int) : Nat × Array Nat × Nat := Id.run do
  -- validity is downward-closed in po, so a single maximum characterises it
  let mut pomax := 0
  for po in [1, 2, 3, 4, 5, 6] do
    if bs % p2 po = 0 ∧ ord < bs / p2 po then
      pomax := po
  let cF := bs / p2 pomax
  let mut sums : Array Nat := Array.replicate (p2 pomax) 0
  for i in [0 : res.size] do
    let x := res.getD i 0
    let u := if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1
    sums := sums.modify ((i + ord) / cF) (· + u)
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

/-- First differences (`Fixed.diff1` over arrays). -/
def diffArr (xs : Array Int) : Array Int := Id.run do
  if xs.size = 0 then return #[]
  let mut out := Array.emptyWithCapacity (xs.size - 1)
  for i in [1 : xs.size] do
    out := out.push (xs.getD i 0 - xs.getD (i - 1) 0)
  return out

/-- LPC residual (`Lpc.residual` over arrays): first `cs.size` samples
    are warmup, the rest are `x[n] - (Σ cs[i]·x[n-1-i]) >>ₐ shift`. -/
def lpcResidualArr (cs : Array Int) (shift : Nat) (xs : Array Int) : Array Int := Id.run do
  let ord := cs.size
  if xs.size ≤ ord then return #[]
  let mut out := Array.emptyWithCapacity (xs.size - ord)
  for i in [ord : xs.size] do
    let mut s : Int := 0
    for j in [0 : ord] do
      s := s + cs.getD j 0 * xs.getD (i - 1 - j) 0
    out := out.push (xs.getD i 0 - sar s shift)
  return out

/-- Mirror of `Heuristics.fixedSearch`: orders 0–4 by exact cost,
    lowest order wins ties. -/
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

/-- Mirror of `Heuristics.lpcSearch`: Welch window, autocorrelation,
    Levinson–Durbin at orders 1,2,4,6,8, 12-bit quantization, adaptive
    partitions, exact cost. -/
def lpcSearchF (b : Nat) (blk : Array Int) :
    Option ((List Int × Nat × Nat × Array Nat) × Nat) := Id.run do
  if blk.size < 16 then
    return none
  let r := Heuristics.autocorr (Heuristics.welch (blk.map Heuristics.floatOfInt)) 8
  if !(r.getD 0 (Float.ofBits 0) > Float.ofBits 0) then
    return none
  let mut best : Option ((List Int × Nat × Nat × Array Nat) × Nat) := none
  for ord in [1, 2, 4, 6, 8] do
    if ord < blk.size then
      let (cs, shift) := Heuristics.quantizeCoefs (Heuristics.levinson r ord).toList 12
      let (po, ks, rcost) := partitionSearchF blk.size ord (lpcResidualArr cs.toArray shift blk)
      let cost := ord * b + 9 + ord * 12 + rcost
      match best with
      | some (_, c) => if cost < c then best := some ((cs, shift, po, ks), cost)
      | none => best := some ((cs, shift, po, ks), cost)
  return best

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
    pay), exactly as `Heuristics.defaultChooser` decides it. -/
def choosePlan (b : Nat) (blk : Array Int) : SubPlan :=
  if blk.all (fun x => x == blk.getD 0 0) then .constant
  else
    match fixedSearchF b blk, lpcSearchF b blk with
    | none, none => .verbatim
    | none, some ((lcs, lsh, lpo, lks), lcost) =>
      if lcost < b * blk.size then .lpc lcs lsh lpo lks else .verbatim
    | some ((ord, po, ks), cost), none =>
      if cost < b * blk.size then .fixed ord po ks else .verbatim
    | some ((ord, po, ks), cost), some ((lcs, lsh, lpo, lks), lcost) =>
      if lcost ≤ cost then
        if lcost < b * blk.size then .lpc lcs lsh lpo lks else .verbatim
      else
        if cost < b * blk.size then .fixed ord po ks else .verbatim

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
  let plan := choosePlan b' scaled
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
    return pushResidual w scaled.size ord po ks (lpcResidualArr cs.toArray shift scaled)

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
  w := w.push 8 (Crc.crc8 (w.buf.extract start w.buf.size)).toNat
  for p in plan do
    w := pushSubframe w p.1 p.2
  w := w.align
  return w.push 16 (Crc.crc16 (w.buf.extract start w.buf.size)).toNat

/-- The full stream: `fLaC` marker, STREAMINFO, frames — the exact
    layout of `Stream.writeStream` under the default heuristics. -/
def encodeArrays (blockSize : Nat) (varBlk : Bool) (chs : Array (Array Int))
    (bps sr : Nat) (md5 : ByteArray) : ByteArray := Id.run do
  let n := (chs.getD 0 #[]).size
  let mut w := BitWriter.empty (n * chs.size + 1024)
  w := w.push 32 0x664C6143
  w := ((w.push 1 1).push 7 0).push 24 34
  w := (w.push 16 blockSize).push 16 blockSize
  w := (w.push 24 0).push 24 0
  w := ((w.push 20 sr).push 3 (chs.size - 1)).push 5 (bps - 1)
  w := w.pushBits 36 n
  for byte in md5.toList do
    w := w.push 8 byte.toNat
  if blockSize = 0 then return w.buf
  for f in [0 : (n + blockSize - 1) / blockSize] do
    let lo := f * blockSize
    let hi := min (lo + blockSize) n
    w := pushFrame w bps varBlk (if varBlk then f * blockSize else f)
      (chs.map (·.extract lo hi))
  return w.buf

/-! ## 16-bit PCM entry point -/

/-- Deinterleave signed 16-bit little-endian PCM into channel arrays. -/
def pcm16Channels (ch : Nat) (bytes : ByteArray) : Array (Array Int) := Id.run do
  let n := bytes.size / (2 * ch)
  let mut chans : Array (Array Int) :=
    (Array.range ch).map fun _ => Array.emptyWithCapacity n
  let mut i := 0
  for _ in [0 : n] do
    for c in [0 : ch] do
      let lo := (if h : i < bytes.size then bytes[i] else 0).toNat
      let hi := (if h : i + 1 < bytes.size then bytes[i + 1] else 0).toNat
      let v := lo + 256 * hi
      let x : Int := if v < 32768 then (v : Int) else (v : Int) - 65536
      chans := chans.modify c (·.push x)
      i := i + 2
  return chans

/-- Fast byte-level 16-bit encoder (the MD5 input of RFC 9639 §8.2 for
    16-bit interleaved LE PCM is the input byte string itself). -/
def encodePcm16 (blockSize ch sr : Nat) (bytes : ByteArray) : ByteArray :=
  encodeArrays blockSize false (pcm16Channels ch bytes) 16 sr (Md5.md5 bytes)

end Flac.Encode
