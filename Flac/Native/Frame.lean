import Flac.Native.Bits
import Flac.Native.Crc
import Flac.Native.Utf8Num
import Flac.Native.Subframe

/-!
# Frames (RFC 9639 §9.1, §9.3)

M2 scope: mono frames, fixed-blocksize numbering, explicit (code 7)
blocksize field, sample rate from STREAMINFO (code 0), CRC-8-verified
header, CRC-16-verified frame. Multichannel/stereo modes arrive at M4.

Both CRCs are recomputed by the decoder over the exact bits it consumed,
via `Flac.Bits.withConsumed`. The encoder emits a canonical header (this is
a *choice*, not a restriction — any valid stream decodes; the encoder just
never emits, e.g., table-coded block sizes).
-/

namespace Flac.Frame

open Flac.Bits

/-- 3-bit bit-depth code for the frame header (RFC 9639 Table 15);
    0 means "get from STREAMINFO", used for depths without a code. -/
def bpsCode : Nat → Nat
  | 8 => 1
  | 12 => 2
  | 16 => 4
  | 20 => 5
  | 24 => 6
  | 32 => 7
  | _ => 0

/-- Decode a 3-bit bit-depth code, with STREAMINFO fallback `b0`. -/
def bpsOfCode : Nat → Nat → Option Nat
  | 0, b0 => some b0
  | 1, _ => some 8
  | 2, _ => some 12
  | 4, _ => some 16
  | 5, _ => some 20
  | 6, _ => some 24
  | 7, _ => some 32
  | _, _ => none          -- 3 is reserved

/-- Frame-header fields the (mono) decoder needs downstream. -/
structure Fields where
  blockSize : Nat
  bps : Nat
  idx : Nat
deriving Repr, DecidableEq

/-- The frame header up to (not including) its CRC-8. Canonical choices:
    blocksize code 7 (explicit 16-bit), sample rate code 0 (STREAMINFO). -/
def headerCore (b idx bs : Nat) : BitStream :=
  writeBits 14 0x3FFE ++ writeBits 1 0 ++ writeBits 1 0 ++
  writeBits 4 7 ++ writeBits 4 0 ++ writeBits 4 0 ++
  writeBits 3 (bpsCode b) ++ writeBits 1 0 ++
  Utf8Num.write idx ++ writeBits 16 (bs - 1)

def writeHeader (b idx bs : Nat) : BitStream :=
  headerCore b idx bs ++
    writeBits 8 (Crc.crc8 (bitsToBytes (headerCore b idx bs))).toNat

/-- Header + subframe, padded to byte alignment: everything the CRC-16
    covers. -/
def body (b idx : Nat) (cfg : Subframe.SubCfg) (xs : List Int) : BitStream :=
  alignToByte (writeHeader b idx xs.length ++ Subframe.write b cfg xs)

def write (b idx : Nat) (cfg : Subframe.SubCfg) (xs : List Int) : BitStream :=
  body b idx cfg xs ++
    writeBits 16 (Crc.crc16 (bitsToBytes (body b idx cfg xs))).toNat

/-! ## Decoding -/

/-- Resolve the 4-bit blocksize code (RFC 9639 Table 14), reading the
    explicit 8/16-bit value for codes 6/7. -/
def resolveBlockSize (code : Nat) (s : BitStream) : Option (Nat × BitStream) :=
  if code = 1 then some (192, s)
  else if 2 ≤ code ∧ code ≤ 5 then some (576 * 2 ^ (code - 2), s)
  else if code = 6 then
    match readBits 8 s with
    | none => none
    | some (v, s) => some (v + 1, s)
  else if code = 7 then
    match readBits 16 s with
    | none => none
    | some (v, s) => some (v + 1, s)
  else if 8 ≤ code ∧ code ≤ 15 then some (256 * 2 ^ (code - 8), s)
  else none                -- 0 is reserved

/-- Skip the explicit sample-rate field for codes 12–14 (the sample rate
    itself does not affect sample reconstruction). -/
def skipSampleRate (code : Nat) (s : BitStream) : Option BitStream :=
  if code = 12 then
    match readBits 8 s with
    | none => none
    | some (_, s) => some s
  else if code = 13 ∨ code = 14 then
    match readBits 16 s with
    | none => none
    | some (_, s) => some s
  else if code = 15 then none
  else some s

/-- Parse all frame-header fields (everything the CRC-8 covers).
    `b0` is the STREAMINFO bit depth. Mono only until M4. -/
def readFields (b0 : Nat) (s : BitStream) : Option (Fields × BitStream) :=
  match readBits 14 s with
  | none => none
  | some (sync, s) =>
    if sync = 0x3FFE then
      match readBits 1 s with
      | none => none
      | some (r0, s) =>
        if r0 = 0 then
          match readBits 1 s with
          | none => none
          | some (strat, s) =>
            if strat = 0 then       -- fixed blocksize streams only until M4
              match readBits 4 s with
              | none => none
              | some (bsCode, s) =>
                match readBits 4 s with
                | none => none
                | some (srCode, s) =>
                  match readBits 4 s with
                  | none => none
                  | some (chCode, s) =>
                    if chCode = 0 then     -- mono until M4
                      match readBits 3 s with
                      | none => none
                      | some (bpsC, s) =>
                        match bpsOfCode bpsC b0 with
                        | none => none
                        | some b =>
                          match readBits 1 s with
                          | none => none
                          | some (r1, s) =>
                            if r1 = 0 then
                              match Utf8Num.read s with
                              | none => none
                              | some (idx, s) =>
                                match resolveBlockSize bsCode s with
                                | none => none
                                | some (bs, s) =>
                                  match skipSampleRate srCode s with
                                  | none => none
                                  | some s =>
                                    some (⟨bs, b, idx⟩, s)
                            else none
                    else none
            else none
        else none
    else none

/-- Parse the header and verify its CRC-8 over the consumed bits. -/
def readHeader (b0 : Nat) (s : BitStream) : Option (Fields × BitStream) :=
  match withConsumed (readFields b0) s with
  | none => none
  | some (f, consumed, s1) =>
    match readBits 8 s1 with
    | none => none
    | some (c8, s2) =>
      if c8 = (Crc.crc8 (bitsToBytes consumed)).toNat then some (f, s2)
      else none

def readHeaderSub (b0 : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  match readHeader b0 s with
  | none => none
  | some (f, s1) => Subframe.read f.blockSize f.bps s1

/-- Header, subframe, and zero padding to byte alignment. -/
def readBody (b0 : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  match withConsumed (readHeaderSub b0) s with
  | none => none
  | some (xs, consumed, s1) =>
    match readBits (padLen consumed.length) s1 with
    | none => none
    | some (z, s2) => if z = 0 then some (xs, s2) else none

/-- Read one complete frame, verifying its CRC-16. -/
def read (b0 : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  match withConsumed (readBody b0) s with
  | none => none
  | some (xs, consumed, s1) =>
    match readBits 16 s1 with
    | none => none
    | some (c16, s2) =>
      if c16 = (Crc.crc16 (bitsToBytes consumed)).toNat then some (xs, s2)
      else none

end Flac.Frame
