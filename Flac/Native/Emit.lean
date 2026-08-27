import Flac.Native.Bits
import Flac.Native.Rice
import Flac.Native.Subframe
import Flac.Native.Lpc
import Flac.Native.Frame
import Flac.Native.Crc
import Flac.Native.Utf8Num
import Flac.Native.Stream

/-!
# The verified fast emitter — bit writer layer

`W` is a byte buffer plus a small bit accumulator (the low `n` bits of
`acc`, `n < 8` between pushes, MSB-first). Every primitive is proven in
`Flac.Spec.Emit` to *emit* exactly what the corresponding `List Bool`
model writer produces: `(f w).bits = w.bits ++ modelBits`. That is the
writer-side mirror of the reader simulation (`Flac.Spec.Reader`), and it
is what lets `Flac.Stream.Unchecked.encode` run on arrays and a `ByteArray` without
touching any theorem statement.

The accumulator is a `Nat` (scalar for our sizes): `acc < 2^n` is an
invariant, pushes are chunked to ≤ 32 bits, and all arithmetic uses the
GMP-free `p2` table and `>>>`/`&&&`.
-/

namespace Flac.Emit

open Flac.Bits (p2)

/-- The bit writer: completed bytes in `buf`, pending bits in the low
    `n` bits of `acc` (`n < 8`, `acc < 2^n` — `Flac.Spec.Emit.Inv`). -/
structure W where
  buf : ByteArray
  acc : Nat
  n : Nat

namespace W

def empty (cap : Nat) : W := ⟨ByteArray.emptyWithCapacity cap, 0, 0⟩

/-- Emit completed bytes out of the accumulator. -/
def flushGo (buf : ByteArray) (acc n : Nat) : ByteArray × Nat × Nat :=
  if _h : n < 8 then (buf, acc, n)
  else
    let hi := n - 8
    flushGo (buf.push (UInt8.ofNat (acc >>> hi))) (acc &&& (p2 hi - 1)) hi
termination_by n
decreasing_by omega

/-- Push the low `k` bits of `v`, MSB first (callers keep `k ≤ 32`;
    `v` is masked). -/
def push (w : W) (k v : Nat) : W :=
  let (buf, acc, n) := flushGo w.buf (w.acc * p2 k + (v &&& (p2 k - 1))) (w.n + k)
  ⟨buf, acc, n⟩

/-- Arbitrary-width big-endian push, chunked to keep the accumulator
    scalar. -/
def pushBits (w : W) (k v : Nat) : W :=
  if _h : k ≤ 32 then w.push k v
  else (w.pushBits (k - 32) (v >>> 32)).push 32 (v &&& 0xFFFFFFFF)
termination_by k
decreasing_by omega

/-- Unary code: `q` zero bits, then a one bit. -/
def pushUnary (w : W) (q : Nat) : W :=
  if _h : q < 32 then w.push (q + 1) 1
  else pushUnary (w.push 32 0) (q - 32)
termination_by q
decreasing_by omega

/-- `k`-bit two's complement (computes `Flac.Bits.writeSInt`). -/
def pushSInt (w : W) (k : Nat) (x : Int) : W :=
  w.pushBits k ((x + ((p2 k : Nat) : Int)).toNat &&& (p2 k - 1))

/-- Rice code with parameter `k` (computes `Flac.Rice.writeRice`). -/
def pushRice (w : W) (k : Nat) (x : Int) : W :=
  let u := Rice.zigzag x
  (w.pushUnary (u >>> k)).push k (u &&& (p2 k - 1))

/-! ## Sequences, partitions, residuals (mirroring the model writers) -/

/-- Fixed-width run over the segment `xs[start .. start+len)` (stopping
    at the array end, exactly like the model's `take`). -/
def pushSIntSeg (b : Nat) (xs : Array Int) : (start len : Nat) → W → W
  | _, 0, w => w
  | start, len + 1, w =>
    if start < xs.size then
      pushSIntSeg b xs (start + 1) len (w.pushSInt b (xs.getD start 0))
    else w

/-- Rice run over the segment `xs[start .. start+len)` (stopping at the
    array end). -/
def pushRiceSeg (k : Nat) (xs : Array Int) : (start len : Nat) → W → W
  | _, 0, w => w
  | start, len + 1, w =>
    if start < xs.size then
      pushRiceSeg k xs (start + 1) len (w.pushRice k (xs.getD start 0))
    else w

/-- Fixed-width run over a (short) list — LPC coefficients. -/
def pushSIntList (b : Nat) : List Int → W → W
  | [], w => w
  | x :: xs, w => pushSIntList b xs (w.pushSInt b x)

/-- The partitions of a coded residual, one `(choice, size)` pair at a
    time, walking `res` by index (computes
    `writeParts ∘ zip choices ∘ chunkBySizes`). -/
def pushParts (m : Rice.Method) (res : Array Int) :
    (choices : List Rice.Partition) → (sizes : List Nat) → (start : Nat) → W → W
  | [], _, _, w => w
  | _ :: _, [], _, w => w
  | ch :: choices, sz :: sizes, start, w =>
    let w' := match ch with
      | .rice k => pushRiceSeg k res start sz (w.push m.paramBits k)
      | .escape bits =>
        pushSIntSeg bits res start sz
          ((w.push m.paramBits m.escapeCode).push 5 bits)
    pushParts m res choices sizes (start + sz) w'

/-- A coded residual (computes `Rice.writeResidual`). -/
def pushResidual (bs ord : Nat) (cfg : Rice.ResidualCfg) (res : Array Int)
    (w : W) : W :=
  pushParts cfg.method res cfg.choices (Rice.partSizes bs cfg.po ord) 0
    ((w.push 2 cfg.method.code).push 4 cfg.po)

end W

/-! ## Predictor residuals over arrays (structural, for the proofs) -/

/-- First differences: `rem` of them starting at index `i`. -/
def diffGo (xs : Array Int) : (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    diffGo xs (i + 1) rem (out.push (xs.getD (i + 1) 0 - xs.getD i 0))

/-- `Fixed.diff1` over arrays. -/
def diffA (xs : Array Int) : Array Int :=
  diffGo xs 0 (xs.size - 1) (Array.emptyWithCapacity (xs.size - 1))

/-- `Fixed.residual` (the `ord`-th difference) over arrays. -/
def fixedResA : (ord : Nat) → Array Int → Array Int
  | 0, xs => xs
  | ord + 1, xs => diffA (fixedResA ord xs)

/-- LPC residuals: `rem` of them starting at index `i`, predicting from
    the array prefix (`Lpc.dotA` walks it most-recent-first). -/
def lpcResGo (cs : List Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo cs shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dotA cs xs (i - 1)) shift))

/-! ### Tap-specialised residual loops

One loop per coefficient count, so the specialisation is chosen **once per
subframe** by `lpcResA` and the taps are loop-invariant parameters that stay in
registers for the whole block. `Flac.Spec.Emit.lpcResGo{k}_eq` proves each is
`lpcResGo` at a fixed coefficient list. -/

def lpcResGo1 (c0 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo1 c0 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot1At xs c0 i) shift))

def lpcResGo2 (c0 c1 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo2 c0 c1 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot2At xs c0 c1 i) shift))

def lpcResGo3 (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo3 c0 c1 c2 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot3At xs c0 c1 c2 i) shift))

def lpcResGo4 (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo4 c0 c1 c2 c3 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot4At xs c0 c1 c2 c3 i) shift))

def lpcResGo5 (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo5 c0 c1 c2 c3 c4 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot5At xs c0 c1 c2 c3 c4 i) shift))

def lpcResGo6 (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot6At xs c0 c1 c2 c3 c4 c5 i) shift))

def lpcResGo7 (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot7At xs c0 c1 c2 c3 c4 c5 c6 i) shift))

def lpcResGo8 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot8At xs c0 c1 c2 c3 c4 c5 c6 c7 i) shift))

/-- `Lpc.residual` over arrays, dispatching the tap walk once per subframe. -/
def lpcResA (cs : List Int) (shift : Nat) (xs : Array Int) : Array Int :=
  let i := cs.length
  let rem := xs.size - cs.length
  let out := Array.emptyWithCapacity rem
  match cs with
  | [c0] => lpcResGo1 c0 shift xs i rem out
  | [c0, c1] => lpcResGo2 c0 c1 shift xs i rem out
  | [c0, c1, c2] => lpcResGo3 c0 c1 c2 shift xs i rem out
  | [c0, c1, c2, c3] => lpcResGo4 c0 c1 c2 c3 shift xs i rem out
  | [c0, c1, c2, c3, c4] => lpcResGo5 c0 c1 c2 c3 c4 shift xs i rem out
  | [c0, c1, c2, c3, c4, c5] => lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs i rem out
  | [c0, c1, c2, c3, c4, c5, c6] =>
    lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs i rem out
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
    lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out
  | cs' => lpcResGo cs' shift xs i rem out

namespace W

/-! ## Subframes -/

/-- Subframe content (computes `Subframe.writeContent`). -/
def pushContent (b : Nat) (cfg : Subframe.SubframeCfg) (xs : Array Int)
    (w : W) : W :=
  match cfg with
  | .constant => w.pushSInt b (xs.getD 0 0)
  | .verbatim => pushSIntSeg b xs 0 xs.size w
  | .fixed ord rcfg =>
    pushResidual xs.size ord rcfg (fixedResA ord xs)
      (pushSIntSeg b xs 0 ord w)
  | .lpc cs shift prec rcfg =>
    pushResidual xs.size cs.length rcfg (lpcResA cs shift xs)
      (pushSIntList prec cs
        (((pushSIntSeg b xs 0 cs.length w).push 4 (prec - 1)).pushSInt 5
          (shift : Int)))

/-- One subframe (computes `Subframe.write`). -/
def pushSubframe (b : Nat) (sc : Subframe.SubCfg) (xs : Array Int) (w : W) : W :=
  let scaled := if sc.wasted = 0 then xs
    else xs.map (Flac.Bits.shiftDown sc.wasted)
  pushContent (b - sc.wasted) sc.inner scaled
    (if sc.wasted = 0 then ((w.push 1 0).push 6 sc.inner.typeCode).push 1 0
     else (((w.push 1 0).push 6 sc.inner.typeCode).push 1 1).pushUnary
       (sc.wasted - 1))

/-- Continuation bytes of a coded number (computes
    `Utf8Num.writeConts`). -/
def pushConts (v : Nat) : (k : Nat) → W → W
  | 0, w => w
  | k + 1, w => pushConts v k (w.push 8 (0x80 + v / p2 (6 * k) % 64))

/-- Coded number (computes `Utf8Num.write`). -/
def pushUtf8 (v : Nat) (w : W) : W :=
  if v < p2 7 then w.push 8 v
  else if v < p2 11 then pushConts v 1 (w.push 8 (0xC0 + v / p2 6))
  else if v < p2 16 then pushConts v 2 (w.push 8 (0xE0 + v / p2 12))
  else if v < p2 21 then pushConts v 3 (w.push 8 (0xF0 + v / p2 18))
  else if v < p2 26 then pushConts v 4 (w.push 8 (0xF8 + v / p2 24))
  else if v < p2 31 then pushConts v 5 (w.push 8 (0xFC + v / p2 30))
  else pushConts v 6 (w.push 8 0xFE)

/-- Frame-header fields up to the CRC-8 (computes `Frame.headerCore`). -/
def pushHeaderCore (b : Nat) (strat : Bool) (num bs chCode : Nat) (w : W) : W :=
  (pushUtf8 num ((((((((w.push 14 0x3FFE).push 1 0).push 1
    (if strat then 1 else 0)).push 4 7).push 4 0).push 4 chCode).push 3
    (Frame.bpsCode b)).push 1 0)).push 16 (bs - 1)

/-- The subframe plan over arrays (mirrors `Frame.subframePlan`). -/
def planA (b : Nat) (asg : Frame.ChannelAsg) (chs : List (Array Int)) :
    List ((Nat × Subframe.SubCfg) × Array Int) :=
  match asg, chs with
  | .independent cfgs, chs => (cfgs.map ((b, ·))).zip chs
  | .leftSide c0 c1, [l, r] =>
    [((b, c0), l), ((b + 1, c1), Stereo.sideA l r)]
  | .rightSide c0 c1, [l, r] =>
    [((b + 1, c0), Stereo.sideA l r), ((b, c1), r)]
  | .midSide c0 c1, [l, r] =>
    [((b, c0), Stereo.midA l r), ((b + 1, c1), Stereo.sideA l r)]
  | _, _ => []

def pushPlan : List ((Nat × Subframe.SubCfg) × Array Int) → W → W
  | [], w => w
  | p :: ps, w => pushPlan ps (pushSubframe p.1.1 p.1.2 p.2 w)

/-- One frame: header, CRC-8, subframes, alignment, CRC-16, all CRCs
    computed over the emitter's own bytes (computes `Frame.write`;
    requires a byte-aligned writer, which frames always have). -/
def pushFrame (b : Nat) (strat : Bool) (num : Nat) (asg : Frame.ChannelAsg)
    (chs : List (Array Int)) (w : W) : W :=
  let start := w.buf.size
  let w1 := pushHeaderCore b strat num (chs.headD #[]).size
    (asg.code chs.length) w
  let w2 := w1.push 8 (Crc.crc8Range w1.buf start w1.buf.size).toNat
  let w3 := pushPlan (planA b asg chs) w2
  let w4 := w3.push ((8 - w3.n % 8) % 8) 0
  w4.push 16 (Crc.crc16Range w4.buf start w4.buf.size).toNat

/-! ## Streams -/

/-- The fixed-size STREAMINFO payload (computes `Stream.writeStreamInfo`). -/
def pushStreamInfo (bs sr ch b total md5 : Nat) (w : W) : W :=
  ((((((((w.push 16 bs).push 16 bs).push 24 0).push 24 0).push 20 sr).push 3
    (ch - 1)).push 5 (b - 1)).pushBits 36 total).pushBits 128 md5

/-- A sequence of already chunked frames. The model chooser stays on
    lists; only the samples handed to the emitter are materialized as
    arrays. -/
def pushFrames (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    Nat → List (List (List Int)) → W → W
  | _, [], w => w
  | i, fr :: frs, w =>
    pushFrames b varBlk blockSize chooser (i + 1) frs
      (pushFrame b varBlk (if varBlk then i * blockSize else i)
        (chooser fr) (fr.map List.toArray) w)

/-- The byte-aligned marker + STREAMINFO prefix. -/
def pushStreamPrefix (cfg : Stream.EncoderCfg) (a : Stream.Audio) (w : W) : W :=
  let md5 := Stream.md5Nat (Md5.md5 (Stream.pcmBytes a.bps a.channels))
  let w1 := (((w.push 32 0x664C6143).push 1 1).push 7 0).push 24 34
  pushStreamInfo cfg.blockSize a.sampleRate a.channels.length a.bps
    a.numSamples md5 w1

/-- Marker, STREAMINFO, and all frames (computes `Stream.writeStream`). -/
def pushStream (cfg : Stream.EncoderCfg) (a : Stream.Audio) (w : W) : W :=
  pushFrames a.bps cfg.variableBlocking cfg.blockSize (cfg.safeChooser a.bps) 0
    (Stream.chunkChannels cfg.blockSize a.channels) (pushStreamPrefix cfg a w)

/-- Byte output of the verified emitter. -/
def encode (cfg : Stream.EncoderCfg) (a : Stream.Audio) : ByteArray :=
  (pushStream cfg a
    (empty (64 + 2 * a.channels.length * a.numSamples))).buf

end W

/-- Statically verified stream-emitter entry point. Its equality to the
    reference encoder is `Flac.Emit.emitFast_eq_encode`. -/
def emitFast (cfg : Stream.EncoderCfg) (a : Stream.Audio) : ByteArray :=
  W.encode cfg a

end Flac.Emit
