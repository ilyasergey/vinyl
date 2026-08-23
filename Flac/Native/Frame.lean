import Flac.Native.Bits
import Flac.Native.Crc
import Flac.Native.Utf8Num
import Flac.Native.Subframe
import Flac.Native.Stereo

/-!
# Frames (RFC 9639 §9.1, §9.3) — multichannel

1–8 independent channels, or stereo with left/side, right/side, or
mid/side decorrelation (side channel at `b+1` bits — the L5 width
bookkeeping). Fixed- and variable-blocksize numbering strategies. The
encoder emits a canonical header (blocksize code 7, sample rate from
STREAMINFO); the decoder accepts the general grammar.

Both CRCs are recomputed by the decoder over the exact bits it consumed,
via `Flac.Bits.withConsumed`.
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

/-- Per-frame channel assignment (the stereo-mode decision is a heuristic
    input). -/
inductive ChannelAsg where
  | independent (cfgs : List Subframe.SubCfg)
  | leftSide (c0 c1 : Subframe.SubCfg)
  | rightSide (c0 c1 : Subframe.SubCfg)
  | midSide (c0 c1 : Subframe.SubCfg)

/-- 4-bit channel code (RFC 9639 Table 13). -/
def ChannelAsg.code (nch : Nat) : ChannelAsg → Nat
  | .independent _ => nch - 1
  | .leftSide .. => 8
  | .rightSide .. => 9
  | .midSide .. => 10

/-- The subframes a frame writes: `((bit depth, config), samples)` per
    channel, after decorrelation. -/
def subframePlan (b : Nat) (asg : ChannelAsg) (chs : List (List Int)) :
    List ((Nat × Subframe.SubCfg) × List Int) :=
  match asg, chs with
  | .independent cfgs, chs => (cfgs.map ((b, ·))).zip chs
  | .leftSide c0 c1, [l, r] =>
      [((b, c0), l), ((b + 1, c1), Stereo.side l r)]
  | .rightSide c0 c1, [l, r] =>
      [((b + 1, c0), Stereo.side l r), ((b, c1), r)]
  | .midSide c0 c1, [l, r] =>
      [((b, c0), Stereo.mid l r), ((b + 1, c1), Stereo.side l r)]
  | _, _ => []

def writeSubframes (plan : List ((Nat × Subframe.SubCfg) × List Int)) : BitStream :=
  plan.flatMap fun p => Subframe.write p.1.1 p.1.2 p.2

/-- Validity of a channel assignment for concrete channels of length `bs`:
    the shape matches, and every subframe configuration is valid at its
    (possibly `b+1`) bit depth. -/
def ChannelAsg.Valid (asg : ChannelAsg) (b bs : Nat)
    (chs : List (List Int)) : Prop :=
  (∀ c ∈ chs, c.length = bs) ∧
  match asg, chs with
  | .independent cfgs, chs =>
      1 ≤ chs.length ∧ chs.length ≤ 8 ∧ cfgs.length = chs.length ∧
      ∀ p ∈ cfgs.zip chs, p.1.Valid b p.2
  | .leftSide c0 c1, [l, r] =>
      c0.Valid b l ∧ c1.Valid (b + 1) (Stereo.side l r)
  | .rightSide c0 c1, [l, r] =>
      c0.Valid (b + 1) (Stereo.side l r) ∧ c1.Valid b r
  | .midSide c0 c1, [l, r] =>
      c0.Valid b (Stereo.mid l r) ∧ c1.Valid (b + 1) (Stereo.side l r)
  | _, _ => False

/-- Frame-header fields the decoder needs downstream. -/
structure Fields where
  blockSize : Nat
  bps : Nat
  chCode : Nat
  num : Nat
deriving Repr, DecidableEq

/-- The frame header up to (not including) its CRC-8. Canonical choices:
    blocksize code 7 (explicit 16-bit), sample rate code 0 (STREAMINFO). -/
def headerCore (b : Nat) (strat : Bool) (num bs chCode : Nat) : BitStream :=
  writeBits 14 0x3FFE ++ writeBits 1 0 ++
  writeBits 1 (if strat then 1 else 0) ++
  writeBits 4 7 ++ writeBits 4 0 ++ writeBits 4 chCode ++
  writeBits 3 (bpsCode b) ++ writeBits 1 0 ++
  Utf8Num.write num ++ writeBits 16 (bs - 1)

def writeHeader (b : Nat) (strat : Bool) (num bs chCode : Nat) : BitStream :=
  headerCore b strat num bs chCode ++
    writeBits 8 (Crc.crc8 (bitsToBytes (headerCore b strat num bs chCode))).toNat

/-- Header + subframes, padded to byte alignment: everything the CRC-16
    covers. -/
def body (b : Nat) (strat : Bool) (num : Nat) (asg : ChannelAsg)
    (chs : List (List Int)) : BitStream :=
  alignToByte (writeHeader b strat num (chs.headD []).length (asg.code chs.length)
    ++ writeSubframes (subframePlan b asg chs))

def write (b : Nat) (strat : Bool) (num : Nat) (asg : ChannelAsg)
    (chs : List (List Int)) : BitStream :=
  body b strat num asg chs ++
    writeBits 16 (Crc.crc16 (bitsToBytes (body b strat num asg chs))).toNat

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
    `b0` is the STREAMINFO bit depth. Both numbering strategies accepted;
    the coded number is parsed and carried, not enforced. -/
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
          | some (_strat, s) =>
            match readBits 4 s with
            | none => none
            | some (bsCode, s) =>
              match readBits 4 s with
              | none => none
              | some (srCode, s) =>
                match readBits 4 s with
                | none => none
                | some (chCode, s) =>
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
                          | some (num, s) =>
                            match resolveBlockSize bsCode s with
                            | none => none
                            | some (bs, s) =>
                              match skipSampleRate srCode s with
                              | none => none
                              | some s =>
                                some (⟨bs, b, chCode, num⟩, s)
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

/-- Read `n` independent subframes at bit depth `b`. -/
def readSubframes (bs b : Nat) : Nat → BitStream → Option (List (List Int) × BitStream)
  | 0, s => some ([], s)
  | n + 1, s =>
    match Subframe.read bs b s with
    | none => none
    | some (c, s) =>
      match readSubframes bs b n s with
      | none => none
      | some (cs, s) => some (c :: cs, s)

/-- Read the frame's channels according to the channel code, undoing
    stereo decorrelation (side channels at `b+1` bits). -/
def readChannels (bs b chCode : Nat) (s : BitStream) :
    Option (List (List Int) × BitStream) :=
  if chCode ≤ 7 then
    readSubframes bs b (chCode + 1) s
  else if chCode = 8 then
    match Subframe.read bs b s with
    | none => none
    | some (l, s) =>
      match Subframe.read bs (b + 1) s with
      | none => none
      | some (sd, s) => some ([l, Stereo.decodeLS l sd], s)
  else if chCode = 9 then
    match Subframe.read bs (b + 1) s with
    | none => none
    | some (sd, s) =>
      match Subframe.read bs b s with
      | none => none
      | some (r, s) => some ([Stereo.decodeRS sd r, r], s)
  else if chCode = 10 then
    match Subframe.read bs b s with
    | none => none
    | some (m, s) =>
      match Subframe.read bs (b + 1) s with
      | none => none
      | some (sd, s) => some ([Stereo.decodeMSL m sd, Stereo.decodeMSR m sd], s)
  else none                -- 11–15 reserved

def readHeaderChannels (b0 : Nat) (s : BitStream) :
    Option (List (List Int) × BitStream) :=
  match readHeader b0 s with
  | none => none
  | some (f, s1) => readChannels f.blockSize f.bps f.chCode s1

/-- Header, subframes, and zero padding to byte alignment. -/
def readBody (b0 : Nat) (s : BitStream) : Option (List (List Int) × BitStream) :=
  match withConsumed (readHeaderChannels b0) s with
  | none => none
  | some (chs, consumed, s1) =>
    match readBits (padLen consumed.length) s1 with
    | none => none
    | some (z, s2) => if z = 0 then some (chs, s2) else none

/-- Read one complete frame, verifying its CRC-16. -/
def read (b0 : Nat) (s : BitStream) : Option (List (List Int) × BitStream) :=
  match withConsumed (readBody b0) s with
  | none => none
  | some (chs, consumed, s1) =>
    match readBits 16 s1 with
    | none => none
    | some (c16, s2) =>
      if c16 = (Crc.crc16 (bitsToBytes consumed)).toNat then some (chs, s2)
      else none

end Flac.Frame
