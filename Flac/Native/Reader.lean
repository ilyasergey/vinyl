import Flac.Native.Bits

/-!
# Buffered bit reader — the production decoder's input layer

`BitReader` reads MSB-first bits directly from a `ByteArray` at a bit
position, with no intermediate `List Bool`. Every primitive is proven to
simulate the model reader in `Flac.Spec.Reader`: for a reader `br`,
`toStream br = (bytesToBits br.data).drop br.pos`, and each production
read returns exactly what the model read returns on `toStream br`.

Bit extraction is deliberately bit-at-a-time and structured like the
model's `readBits`, keeping the simulation proofs one-induction affairs;
word-at-a-time fast paths can replace it later under the same theorems.
-/

namespace Flac.Bits

/-- A byte buffer with a bit cursor. -/
structure BitReader where
  data : ByteArray
  pos : Nat

namespace BitReader

/-- The `i`-th bit of the buffer, MSB-first within each byte.
    (Indexes the `ByteArray` directly — `.data` would copy.) -/
def bit (d : ByteArray) (i : Nat) : Bool :=
  decide ((if h : i / 8 < d.size then d[i / 8] else 0).toNat
    / 2 ^ (7 - i % 8) % 2 = 1)

/-- Read `n` bits starting at `pos` (callers check bounds). -/
def extractBits (d : ByteArray) (pos : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if bit d pos then 2 ^ n else 0) + extractBits d (pos + 1) n

/-- Total bit count of the buffer. -/
def size (br : BitReader) : Nat := 8 * br.data.size

/-- Bits left to read. -/
def remaining (br : BitReader) : Nat := br.size - br.pos

def readBits (n : Nat) (br : BitReader) : Option (Nat × BitReader) :=
  if n = 0 then some (0, br)
  else if br.pos + n ≤ br.size then
    some (extractBits br.data br.pos n, ⟨br.data, br.pos + n⟩)
  else none

/-- Unary code: count zero bits up to the terminating one bit. -/
def readUnaryGo (d : ByteArray) (q : Nat) (pos : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    if bit d pos then some (q, pos + 1)
    else readUnaryGo d (q + 1) (pos + 1) fuel

def readUnary (br : BitReader) : Option (Nat × BitReader) :=
  match readUnaryGo br.data 0 br.pos br.remaining with
  | none => none
  | some (q, pos') => some (q, ⟨br.data, pos'⟩)

def readSInt (n : Nat) (br : BitReader) : Option (Int × BitReader) :=
  match readBits n br with
  | none => none
  | some (v, br') =>
    some (if 2 * v < 2 ^ n then (v : Int) else (v : Int) - ((2 ^ n : Nat) : Int), br')

/-- Skip `n` bits. -/
def skip (n : Nat) (br : BitReader) : Option BitReader :=
  if n = 0 then some br
  else if br.pos + n ≤ br.size then some ⟨br.data, br.pos + n⟩ else none

end BitReader
end Flac.Bits
