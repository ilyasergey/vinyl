/-!
# L0 — Bit-level model (MSB-first)

FLAC is big-endian / MSB-first throughout (RFC 9639 §1.1). The bitstream
model is `List Bool` (`true` = 1 bit). Writers are pure functions returning
bit lists; readers are structural-recursive consumers returning
`Option (α × List Bool)` (no `partial`, no panicking access — decoder
totality by construction, PLAN.md §5.7).

This representation is the *proof* backbone; production (buffered) bit I/O
arrives with M5 and is transferred against this model. Round-trip theorems
live in `Flac.Spec.Bits`.
-/

namespace Flac

/-- MSB-first bitstream: `true` is a 1 bit. -/
abbrev BitStream := List Bool

namespace Bits

/-- Write the low `n` bits of `v`, most significant bit first. -/
def writeBits : (n : Nat) → (v : Nat) → BitStream
  | 0, _ => []
  | n+1, v => (decide (v / 2 ^ n % 2 = 1)) :: writeBits n v

/-- Read `n` bits MSB-first into a `Nat`. -/
def readBits : (n : Nat) → BitStream → Option (Nat × BitStream)
  | 0, s => some (0, s)
  | _+1, [] => none
  | n+1, b :: s =>
    match readBits n s with
    | none => none
    | some (v, s') => some ((if b then 2 ^ n else 0) + v, s')

/-- FLAC unary code: `q` zero bits followed by a single one bit
    (RFC 9639 §9.2.7). -/
def writeUnary (q : Nat) : BitStream :=
  List.replicate q false ++ [true]

def readUnary : BitStream → Option (Nat × BitStream)
  | [] => none
  | true :: s => some (0, s)
  | false :: s =>
    match readUnary s with
    | none => none
    | some (q, s') => some (q + 1, s')

/-- Zero-bits needed to pad `len` bits to a byte boundary. -/
def padLen (len : Nat) : Nat := (8 - len % 8) % 8

/-- Pad a bitstream to byte alignment with zero bits (frame footers are
    byte-aligned before the CRC-16, RFC 9639 §9.3). -/
def alignToByte (s : BitStream) : BitStream :=
  s ++ List.replicate (padLen s.length) false

/-! ## Bytes ↔ bits -/

/-- One byte as 8 bits, MSB first. -/
def byteToBits (b : UInt8) : BitStream := writeBits 8 b.toNat

/-- Assemble one byte from 8 bits, MSB first. -/
def bitsToByte (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : UInt8 :=
  UInt8.ofNat (128 * b0.toNat + 64 * b1.toNat + 32 * b2.toNat + 16 * b3.toNat
    + 8 * b4.toNat + 4 * b5.toNat + 2 * b6.toNat + b7.toNat)

def byteListToBits (bs : List UInt8) : BitStream :=
  bs.flatMap byteToBits

/-- Pack bits into bytes, 8 at a time, MSB first. Callers guarantee
    `8 ∣ length`; a trailing partial byte is dropped. -/
def bitsToByteList : BitStream → List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    bitsToByte b0 b1 b2 b3 b4 b5 b6 b7 :: bitsToByteList rest
  | _ => []

def bytesToBits (bs : ByteArray) : BitStream :=
  byteListToBits bs.data.toList

def bitsToBytes (s : BitStream) : ByteArray :=
  (bitsToByteList s).toByteArray

end Bits
end Flac
