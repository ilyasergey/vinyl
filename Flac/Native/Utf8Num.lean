import Flac.Native.Bits

/-!
# Coded numbers (extended UTF-8)

Frame/sample numbers are stored in a UTF-8-like variable-length code
extended to 36 bits / 7 bytes (RFC 9639 §9.1.5, Table 18). Defined over the
bit model; round-trip proof in `Flac.Spec.Utf8Num`.
-/

namespace Flac.Utf8Num

open Flac.Bits

/-- One continuation byte `10xxxxxx` carrying the low 6 bits of `x`. -/
def writeContByte (x : Nat) : BitStream :=
  writeBits 8 (0x80 + x % 64)

/-- `k` continuation bytes carrying the low `6*k` bits of `n`,
    most significant group first. -/
def writeConts : (k : Nat) → (n : Nat) → BitStream
  | 0, _ => []
  | k+1, n => writeContByte (n / 64 ^ k) ++ writeConts k n

/-- Encode a coded number. Callers guarantee `n < 2^36` (36-bit sample
    numbers; frame numbers are further restricted to 31 bits). -/
def write (n : Nat) : BitStream :=
  if n < 2 ^ 7 then writeBits 8 n
  else if n < 2 ^ 11 then writeBits 8 (0xC0 + n / 2 ^ 6) ++ writeConts 1 n
  else if n < 2 ^ 16 then writeBits 8 (0xE0 + n / 2 ^ 12) ++ writeConts 2 n
  else if n < 2 ^ 21 then writeBits 8 (0xF0 + n / 2 ^ 18) ++ writeConts 3 n
  else if n < 2 ^ 26 then writeBits 8 (0xF8 + n / 2 ^ 24) ++ writeConts 4 n
  else if n < 2 ^ 31 then writeBits 8 (0xFC + n / 2 ^ 30) ++ writeConts 5 n
  else writeBits 8 0xFE ++ writeConts 6 n

/-- Read `k` continuation bytes, accumulating 6 bits each onto `acc`. -/
def readConts : (k : Nat) → (acc : Nat) → BitStream → Option (Nat × BitStream)
  | 0, acc, s => some (acc, s)
  | k+1, acc, s =>
    match readBits 8 s with
    | none => none
    | some (c, s') =>
      if 0x80 ≤ c ∧ c < 0xC0 then readConts k (acc * 64 + (c - 0x80)) s'
      else none

/-- Decode a coded number. Overlong (non-minimal) encodings are accepted;
    only the byte-level grammar is enforced. -/
def read (s : BitStream) : Option (Nat × BitStream) :=
  match readBits 8 s with
  | none => none
  | some (b, s') =>
    if b < 0x80 then some (b, s')
    else if b < 0xC0 then none          -- bare continuation byte
    else if b < 0xE0 then readConts 1 (b - 0xC0) s'
    else if b < 0xF0 then readConts 2 (b - 0xE0) s'
    else if b < 0xF8 then readConts 3 (b - 0xF0) s'
    else if b < 0xFC then readConts 4 (b - 0xF8) s'
    else if b < 0xFE then readConts 5 (b - 0xFC) s'
    else if b = 0xFE then readConts 6 0 s'
    else none                           -- 0xFF is invalid

end Flac.Utf8Num
