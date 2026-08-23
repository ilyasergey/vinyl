import Flac.Native.Bits
import Flac.Native.Rice
import Flac.Native.Subframe
import Flac.Native.Lpc

/-!
# The verified fast emitter — bit writer layer

`W` is a byte buffer plus a small bit accumulator (the low `n` bits of
`acc`, `n < 8` between pushes, MSB-first). Every primitive is proven in
`Flac.Spec.Emit` to *emit* exactly what the corresponding `List Bool`
model writer produces: `(f w).bits = w.bits ++ modelBits`. That is the
writer-side mirror of the reader simulation (`Flac.Spec.Reader`), and it
is what lets `Flac.Stream.encode` run on arrays and a `ByteArray` without
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

/-- `Lpc.residual` over arrays. -/
def lpcResA (cs : List Int) (shift : Nat) (xs : Array Int) : Array Int :=
  lpcResGo cs shift xs cs.length (xs.size - cs.length)
    (Array.emptyWithCapacity (xs.size - cs.length))

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
  pushContent (b - sc.wasted) sc.inner (xs.map (Flac.Bits.shiftDown sc.wasted))
    (if sc.wasted = 0 then ((w.push 1 0).push 6 sc.inner.typeCode).push 1 0
     else (((w.push 1 0).push 6 sc.inner.typeCode).push 1 1).pushUnary
       (sc.wasted - 1))

end W
end Flac.Emit
