import Flac.Native.Frame
import Flac.Native.Md5

/-!
# Stream layer (RFC 9639 §8): `fLaC` marker, STREAMINFO, frames

M2 scope: mono streams at any bit depth 1–32, fixed-blocksize numbering.
The encoder emits marker + a single STREAMINFO metadata block + frames;
the reference decoder additionally skips unknown metadata blocks by length
(so foreign files with VORBIS_COMMENT etc. still decode).

`decodeReference` is the verified reference decoder of PLAN.md: total by
construction (fuel-bounded loops, no `partial`, no `!`).
-/

namespace Flac.Stream

open Flac.Bits

/-- Split into consecutive blocks of `n` samples; the last block may be
    shorter. `n = 0` yields no blocks. -/
def chunkFixed (n : Nat) (xs : List Int) : List (List Int) :=
  if _h : xs = [] ∨ n = 0 then []
  else xs.take n :: chunkFixed n (xs.drop n)
termination_by xs.length
decreasing_by
  simp only [List.length_drop]
  have hx : xs ≠ [] := fun hc => _h (Or.inl hc)
  have hn : n ≠ 0 := fun hc => _h (Or.inr hc)
  have : 0 < xs.length := List.length_pos_iff.mpr hx
  omega

/-- PCM as little-endian two's-complement bytes, `⌈b/8⌉` bytes per sample
    (the MD5 input format of RFC 9639 §8.2). Unverified — MD5 is a
    conformance checksum, not part of the losslessness claim. -/
def pcmBytes (b : Nat) (pcm : List Int) : ByteArray :=
  let w := (b + 7) / 8
  ⟨(pcm.flatMap fun x =>
      let u := ((x + ((2 ^ (8 * w) : Nat) : Int)).toNat) % 2 ^ (8 * w)
      (List.range w).map fun i => UInt8.ofNat (u / 2 ^ (8 * i) % 256)).toArray⟩

/-- A digest as a big-endian natural, for `writeBits 128`. -/
def md5Nat (d : ByteArray) : Nat :=
  d.foldl (fun a c => a * 256 + c.toNat) 0

/-- STREAMINFO for a fixed-blocksize mono stream: min = max block size,
    unknown (0) frame sizes. -/
def writeStreamInfo (bs sr b total md5 : Nat) : BitStream :=
  writeBits 16 bs ++ writeBits 16 bs ++
  writeBits 24 0 ++ writeBits 24 0 ++
  writeBits 20 sr ++ writeBits 3 0 ++ writeBits 5 (b - 1) ++
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

def writeFrames (b : Nat) (chooser : List Int → Subframe.SubCfg) :
    Nat → List (List Int) → BitStream
  | _, [] => []
  | idx, blk :: blks =>
    Frame.write b idx (chooser blk) blk ++ writeFrames b chooser (idx + 1) blks

/-- Decode frames until the stream is exhausted. Fuel bounds the loop
    (each frame consumes at least one bit, so `s.length + 1` suffices). -/
def readFrames (b0 : Nat) : Nat → BitStream → Option (List Int)
  | 0, s => if s = [] then some [] else none
  | fuel + 1, s =>
    if s = [] then some []
    else
      match Frame.read b0 s with
      | none => none
      | some (xs, s') =>
        match readFrames b0 fuel s' with
        | none => none
        | some rest => some (xs ++ rest)

/-! ## Top level -/

/-- Encoder options for the M2 profile (mono). The `chooser` is the
    heuristic layer: any choice satisfying `SubframeCfg.Valid` yields a
    valid stream (the round-trip theorem quantifies over it). -/
structure EncoderCfg where
  blockSize : Nat
  sampleRate : Nat
  bps : Nat
  chooser : List Int → Subframe.SubCfg

def writeStream (cfg : EncoderCfg) (pcm : List Int) : BitStream :=
  writeBits 32 0x664C6143 ++
  writeBits 1 1 ++ writeBits 7 0 ++ writeBits 24 34 ++
  writeStreamInfo cfg.blockSize cfg.sampleRate cfg.bps pcm.length
    (md5Nat (Md5.md5 (pcmBytes cfg.bps pcm))) ++
  writeFrames cfg.bps cfg.chooser 0 (chunkFixed cfg.blockSize pcm)

/-- **The encoder** (M2 profile: mono, fixed block size). -/
def encode (cfg : EncoderCfg) (pcm : List Int) : ByteArray :=
  bitsToBytes (writeStream cfg pcm)

/-- **The verified reference decoder** (M2 profile: mono streams). -/
def decodeReference (bytes : ByteArray) : Option (List Int) :=
  let s := bytesToBits bytes
  match readBits 32 s with
  | none => none
  | some (marker, s) =>
    if marker = 0x664C6143 then
      match readMeta s.length s with
      | none => none
      | some (si, s) => readFrames si.bps (s.length + 1) s
    else none

/-! ## Default heuristic -/

/-- The safe fallback chooser: VERBATIM everything, no wasted bits.
    Valid whenever the samples fit the bit depth. -/
def verbatimChooser : List Int → Subframe.SubCfg := fun _ => ⟨0, .verbatim⟩

end Flac.Stream
