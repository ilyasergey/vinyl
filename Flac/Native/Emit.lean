import Flac.Native.Bits
import Flac.Native.Rice
import Flac.Native.Subframe

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

end W
end Flac.Emit
