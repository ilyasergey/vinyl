import Flac.Native.Frame
import Flac.Spec.Bits
import Flac.Spec.Utf8Num
import Flac.Spec.Subframe

/-!
# L5 (part 2) — frame round-trip

`frameDecode_frameEncode` of PLAN.md §4, restricted to the M2 profile
(mono, fixed-blocksize numbering). The CRC checks are discharged
definitionally: the decoder recomputes the same CRC function over the same
consumed bits (`withConsumed_spec`) that the encoder wrote by construction.
-/

namespace Flac.Frame

open Flac.Bits

theorem bpsCode_lt (b : Nat) : bpsCode b < 2 ^ 3 := by
  unfold bpsCode; split <;> omega

theorem bpsOfCode_bpsCode (b : Nat) : bpsOfCode (bpsCode b) b = some b := by
  unfold bpsCode; split <;> rfl

theorem resolveBlockSize_seven (bs : Nat) (h1 : 1 ≤ bs) (h2 : bs ≤ 65536)
    (tail : BitStream) :
    resolveBlockSize 7 (writeBits 16 (bs - 1) ++ tail) = some (bs, tail) := by
  unfold resolveBlockSize
  rw [if_neg (by omega), if_neg (by omega : ¬(2 ≤ 7 ∧ 7 ≤ 5)), if_neg (by omega),
    if_pos (by trivial)]
  simp only [readBits_writeBits _ _ _ (by omega : bs - 1 < 2 ^ 16),
    Option.some.injEq, Prod.mk.injEq]
  exact ⟨by omega, trivial⟩

theorem skipSampleRate_zero (s : BitStream) : skipSampleRate 0 s = some s := by
  unfold skipSampleRate
  rw [if_neg (by omega), if_neg (by omega : ¬((0 : Nat) = 13 ∨ (0 : Nat) = 14)),
    if_neg (by omega)]

/-- Parsing the canonical header core recovers the fields. `b0` is the
    STREAMINFO bit depth; the encoder's 3-bit code round-trips through it. -/
theorem readFields_headerCore (b0 b idx bs : Nat) (tail : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b)
    (hidx : idx < 2 ^ 36) (hbs1 : 1 ≤ bs) (hbs2 : bs ≤ 65536) :
    readFields b0 (headerCore b idx bs ++ tail) = some (⟨bs, b, idx⟩, tail) := by
  simp only [headerCore, readFields, List.append_assoc,
    readBits_writeBits _ _ _ (by omega : 0x3FFE < 2 ^ 14),
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
    readBits_writeBits _ _ _ (by omega : 7 < 2 ^ 4),
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 4),
    readBits_writeBits _ _ _ (bpsCode_lt b),
    hb, Utf8Num.read_write idx hidx,
    resolveBlockSize_seven bs hbs1 hbs2, skipSampleRate_zero]
  rw [if_pos (by trivial), if_pos (by trivial), if_pos (by trivial), if_pos (by trivial),
    if_pos (by trivial)]

/-- Header round-trip, CRC-8 verified. -/
theorem readHeader_writeHeader (b0 b idx bs : Nat) (tail : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b)
    (hidx : idx < 2 ^ 36) (hbs1 : 1 ≤ bs) (hbs2 : bs ≤ 65536) :
    readHeader b0 (writeHeader b idx bs ++ tail) = some (⟨bs, b, idx⟩, tail) := by
  unfold writeHeader readHeader
  rw [List.append_assoc]
  simp only [withConsumed_spec (readFields b0) (headerCore b idx bs) _ _
      (readFields_headerCore b0 b idx bs _ hb hidx hbs1 hbs2),
    readBits_writeBits _ _ _
      (show (Crc.crc8 (bitsToBytes (headerCore b idx bs))).toNat < 2 ^ 8 from
        UInt8.toNat_lt_size _)]
  rw [if_pos (by trivial)]

/-- Header + subframe. -/
theorem readHeaderSub_spec (b0 b idx : Nat) (cfg : Subframe.SubCfg)
    (xs : List Int) (tail : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b) (hidx : idx < 2 ^ 36)
    (h1 : 1 ≤ xs.length) (h2 : xs.length ≤ 65536)
    (hv : cfg.Valid b xs) :
    readHeaderSub b0 ((writeHeader b idx xs.length ++ Subframe.write b cfg xs) ++ tail)
      = some (xs, tail) := by
  unfold readHeaderSub
  rw [List.append_assoc]
  simp only [readHeader_writeHeader b0 b idx xs.length _ hb hidx h1 h2]
  exact Subframe.read_write b cfg xs hv tail

/-- Header + subframe + alignment padding. -/
theorem readBody_spec (b0 b idx : Nat) (cfg : Subframe.SubCfg)
    (xs : List Int) (tail : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b) (hidx : idx < 2 ^ 36)
    (h1 : 1 ≤ xs.length) (h2 : xs.length ≤ 65536)
    (hv : cfg.Valid b xs) :
    readBody b0 (body b idx cfg xs ++ tail) = some (xs, tail) := by
  unfold readBody body alignToByte
  rw [List.append_assoc]
  simp only [withConsumed_spec (readHeaderSub b0)
      (writeHeader b idx xs.length ++ Subframe.write b cfg xs) _ _
      (readHeaderSub_spec b0 b idx cfg xs _ hb hidx h1 h2 hv),
    readBits_replicate_false]
  rw [if_pos (by trivial)]

/-- **Frame round-trip** (M2 profile: mono, fixed-blocksize numbering). -/
theorem read_write (b0 b idx : Nat) (cfg : Subframe.SubCfg)
    (xs : List Int) (rest : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b) (hidx : idx < 2 ^ 36)
    (h1 : 1 ≤ xs.length) (h2 : xs.length ≤ 65536)
    (hv : cfg.Valid b xs) :
    read b0 (write b idx cfg xs ++ rest) = some (xs, rest) := by
  unfold write read
  rw [List.append_assoc]
  simp only [withConsumed_spec (readBody b0) (body b idx cfg xs) _ _
      (readBody_spec b0 b idx cfg xs _ hb hidx h1 h2 hv),
    readBits_writeBits _ _ _
      (show (Crc.crc16 (bitsToBytes (body b idx cfg xs))).toNat < 2 ^ 16 from
        UInt16.toNat_lt_size _)]
  rw [if_pos (by trivial)]

end Flac.Frame
