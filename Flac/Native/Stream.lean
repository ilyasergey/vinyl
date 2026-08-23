import Flac.Native.Frame
import Flac.Native.Md5

/-!
# Stream layer (RFC 9639 §8) — multichannel

`fLaC` marker, STREAMINFO, frames. The encoder emits marker + a single
STREAMINFO metadata block + frames (fixed- or variable-blocksize
numbering); the reference decoder additionally skips unknown metadata
blocks by length, so foreign files with VORBIS_COMMENT etc. still decode.

`decodeReference` is the verified reference decoder: total by
construction (fuel-bounded loops, no `partial`, no `!`).
-/

namespace Flac.Stream

open Flac.Bits

def takeAll (n : Nat) (chs : List (List Int)) : List (List Int) :=
  chs.map (·.take n)

def dropAll (n : Nat) (chs : List (List Int)) : List (List Int) :=
  chs.map (·.drop n)

def tailAll (chs : List (List Int)) : List (List Int) :=
  chs.map (·.tail)

/-- Split all channels into consecutive frames of `n` samples; the last
    frame may be shorter. Channels are assumed equally long. -/
def chunkChannels (n : Nat) (chs : List (List Int)) : List (List (List Int)) :=
  if _h : (chs.headD []).length = 0 ∨ n = 0 then []
  else takeAll n chs :: chunkChannels n (dropAll n chs)
termination_by (chs.headD []).length
decreasing_by
  rcases chs with _ | ⟨c, t⟩
  · simp at _h
  · simp only [dropAll, List.map_cons, List.headD_cons, List.length_drop]
    simp only [List.headD_cons] at _h
    rw [not_or] at _h
    omega

/-- Reassemble channels from per-frame channel blocks (`ch` = channel
    count, used when there are zero frames). -/
def recombine (ch : Nat) : List (List (List Int)) → List (List Int)
  | [] => List.replicate ch []
  | fr :: frs => List.zipWith (· ++ ·) fr (recombine ch frs)

/-- Interleave channels sample-by-sample (the MD5 input order,
    RFC 9639 §8.2). -/
def interleave (chs : List (List Int)) : List Int :=
  if _h : (chs.headD []).isEmpty then []
  else chs.map (·.headD 0) ++ interleave (tailAll chs)
termination_by (chs.headD []).length
decreasing_by
  rcases chs with _ | ⟨c, t⟩
  · simp at _h
  · simp only [tailAll, List.map_cons, List.headD_cons, List.length_tail]
    simp only [List.headD_cons, List.isEmpty_iff] at _h
    have : 0 < c.length := List.length_pos_iff.mpr _h
    omega

/-- Interleaved PCM as little-endian two's-complement bytes, `⌈b/8⌉` bytes
    per sample (the MD5 input format of RFC 9639 §8.2). Unverified — MD5
    is a conformance checksum, not part of the losslessness claim. -/
def pcmBytes (b : Nat) (chs : List (List Int)) : ByteArray :=
  let w := (b + 7) / 8
  ⟨((interleave chs).flatMap fun x =>
      let u := ((x + ((2 ^ (8 * w) : Nat) : Int)).toNat) % 2 ^ (8 * w)
      (List.range w).map fun i => UInt8.ofNat (u / 2 ^ (8 * i) % 256)).toArray⟩

/-- A digest as a big-endian natural, for `writeBits 128`. -/
def md5Nat (d : ByteArray) : Nat :=
  d.foldl (fun a c => a * 256 + c.toNat) 0

/-- STREAMINFO for a fixed-blocksize stream: min = max block size,
    unknown (0) frame sizes. -/
def writeStreamInfo (bs sr ch b total md5 : Nat) : BitStream :=
  writeBits 16 bs ++ writeBits 16 bs ++
  writeBits 24 0 ++ writeBits 24 0 ++
  writeBits 20 sr ++ writeBits 3 (ch - 1) ++ writeBits 5 (b - 1) ++
  writeBits 36 total ++ writeBits 128 md5

/-- Parsed STREAMINFO fields the decoder consumes downstream. -/
structure Info where
  minBlock : Nat
  maxBlock : Nat
  sampleRate : Nat
  channels : Nat
  bps : Nat
  totalSamples : Nat
deriving Repr, DecidableEq

def readStreamInfo (s : BitStream) : Option (Info × BitStream) :=
  match readBits 16 s with
  | none => none
  | some (minB, s) =>
    match readBits 16 s with
    | none => none
    | some (maxB, s) =>
      match readBits 24 s with
      | none => none
      | some (_, s) =>
        match readBits 24 s with
        | none => none
        | some (_, s) =>
          match readBits 20 s with
          | none => none
          | some (sr, s) =>
            match readBits 3 s with
            | none => none
            | some (ch, s) =>
              match readBits 5 s with
              | none => none
              | some (bm1, s) =>
                match readBits 36 s with
                | none => none
                | some (total, s) =>
                  match readBits 128 s with
                  | none => none
                  | some (_, s) =>
                    some (⟨minB, maxB, sr, ch + 1, bm1 + 1, total⟩, s)

/-- Drop `n` bits (skipping metadata content by declared length). -/
def skipBits (n : Nat) (s : BitStream) : Option BitStream :=
  if n ≤ s.length then some (s.drop n) else none

/-- Skip metadata blocks until one is flagged last. -/
def skipBlocks : Nat → BitStream → Option BitStream
  | 0, _ => none
  | fuel + 1, s =>
    match readBits 1 s with
    | none => none
    | some (last, s) =>
      match readBits 7 s with
      | none => none
      | some (_, s) =>
        match readBits 24 s with
        | none => none
        | some (len, s) =>
          match skipBits (8 * len) s with
          | none => none
          | some s => if last = 1 then some s else skipBlocks fuel s

/-- Read the metadata section: a STREAMINFO block first (mandatory,
    RFC 9639 §8.1), then any other blocks skipped by length. -/
def readMeta (fuel : Nat) (s : BitStream) : Option (Info × BitStream) :=
  match readBits 1 s with
  | none => none
  | some (last, s) =>
    match readBits 7 s with
    | none => none
    | some (ty, s) =>
      match readBits 24 s with
      | none => none
      | some (len, s) =>
        if ty = 0 then
          if len = 34 then
            match readStreamInfo s with
            | none => none
            | some (si, s) =>
              if last = 1 then some (si, s)
              else
                match skipBlocks fuel s with
                | none => none
                | some s => some (si, s)
          else none
        else none

/-! ## Frame sequences -/

def writeFrames (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    Nat → List (List (List Int)) → BitStream
  | _, [] => []
  | i, fr :: frs =>
    Frame.write b varBlk (if varBlk then i * blockSize else i)
      (chooser fr) fr ++
    writeFrames b varBlk blockSize chooser (i + 1) frs

/-- Decode frames until the stream is exhausted. Fuel bounds the loop
    (each frame consumes at least one bit, so `s.length + 1` suffices). -/
def readFrames (b0 : Nat) : Nat → BitStream → Option (List (List (List Int)))
  | 0, s => if s = [] then some [] else none
  | fuel + 1, s =>
    if s = [] then some []
    else
      match Frame.read b0 s with
      | none => none
      | some (chs, s') =>
        match readFrames b0 fuel s' with
        | none => none
        | some rest => some (chs :: rest)

/-! ## Top level -/

/-- Interleaved multichannel PCM. -/
structure Audio where
  channels : List (List Int)
  bps : Nat
  sampleRate : Nat

def Audio.numSamples (a : Audio) : Nat := (a.channels.headD []).length

/-- Well-formedness: 1–8 equal-length channels, samples in
    range for the bit depth. -/
def Audio.WellFormed (a : Audio) : Prop :=
  1 ≤ a.channels.length ∧ a.channels.length ≤ 8 ∧
  1 ≤ a.bps ∧ a.bps ≤ 32 ∧
  (∀ c ∈ a.channels, c.length = a.numSamples) ∧
  (∀ c ∈ a.channels, ∀ x ∈ c, FitsSInt a.bps x)

/-- Encoder options: block size, numbering
    strategy, and the per-frame channel-assignment/subframe heuristic —
    every knob the capstone quantifies over. -/
structure EncoderCfg where
  blockSize : Nat
  variableBlocking : Bool
  chooser : List (List Int) → Frame.ChannelAsg

def writeStream (cfg : EncoderCfg) (a : Audio) : BitStream :=
  writeBits 32 0x664C6143 ++
  writeBits 1 1 ++ writeBits 7 0 ++ writeBits 24 34 ++
  writeStreamInfo cfg.blockSize a.sampleRate a.channels.length a.bps
    a.numSamples (md5Nat (Md5.md5 (pcmBytes a.bps a.channels))) ++
  writeFrames a.bps cfg.variableBlocking cfg.blockSize cfg.chooser 0
    (chunkChannels cfg.blockSize a.channels)

/-- **The encoder.** -/
def encode (cfg : EncoderCfg) (a : Audio) : ByteArray :=
  bitsToBytes (writeStream cfg a)

/-- **The verified reference decoder**: returns the decoded channels. -/
def decodeReference (bytes : ByteArray) : Option (List (List Int)) :=
  let s := bytesToBits bytes
  match readBits 32 s with
  | none => none
  | some (marker, s) =>
    if marker = 0x664C6143 then
      match readMeta s.length s with
      | none => none
      | some (si, s) =>
        match readFrames si.bps (s.length + 1) s with
        | none => none
        | some frames => some (recombine si.channels frames)
    else none

/-! ## Default heuristics -/

/-- The safe fallback: independent channels, VERBATIM, no wasted bits. -/
def verbatimChooser : List (List Int) → Frame.ChannelAsg :=
  fun fr => .independent (fr.map fun _ => ⟨0, .verbatim⟩)

end Flac.Stream
