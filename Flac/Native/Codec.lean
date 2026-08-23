import Flac.Native.Decode
import Flac.Native.Heuristics
import Flac.Native.Stream
import Flac.Native.Encode

/-!
# The shipped encoder entry points

`Flac.encode` pairs with `Flac.decode` (in `Flac.Native.Decode`); the
checked variants test the (decidable) precondition at runtime, so a `some`
result carries the round-trip theorem with no hypotheses.
-/

namespace Flac

/-- **The encoder**: default heuristics (wasted-bit detection,
    fixed/LPC order search, Rice parameter search, stereo-mode decision),
    4096-sample blocks. -/
def encode (a : Flac.Stream.Audio) : ByteArray :=
  Flac.Stream.encode ⟨4096, false, Heuristics.defaultAsgChooser a.bps⟩ a

/-- The encoder with its precondition checked at runtime: a `some` result
    carries the round-trip guarantee with **no hypotheses at all**
    (`Flac.decode_encodeChecked`). -/
def encodeChecked (a : Flac.Stream.Audio) : Option ByteArray :=
  if a.WellFormed then some (encode a) else none

/-- Checked encode under an arbitrary configuration (block size and
    heuristic supplied by the caller). -/
def encodeCheckedCfg (cfg : Flac.Stream.EncoderCfg) (a : Flac.Stream.Audio) :
    Option ByteArray :=
  if a.WellFormed ∧ 16 ≤ cfg.blockSize ∧ cfg.blockSize ≤ 65535 then
    some (Flac.Stream.encode cfg a)
  else none

/-! ## Byte-level 16-bit PCM pipeline

Interleaved signed 16-bit little-endian PCM bytes in, FLAC bytes out,
original bytes back — with the round-trip guarantee carried by
`Flac.decodePcm16_encodePcm16` under no hypotheses beyond `encodePcm16`
having returned bytes at all. -/

/-- Signed 16-bit little-endian sample from two bytes. -/
def sInt16 (lo hi : UInt8) : Int :=
  let v := lo.toNat + 256 * hi.toNat
  if v < 32768 then (v : Int) else (v : Int) - 65536

/-- Parse little-endian 16-bit samples (any trailing odd byte is ignored;
    `encodePcm16` rejects such input up front). -/
def pcm16OfByteList : List UInt8 → List Int
  | lo :: hi :: rest => sInt16 lo hi :: pcm16OfByteList rest
  | _ => []

/-- Serialize samples as little-endian 16-bit (two's complement). -/
def byteListOfPcm16 : List Int → List UInt8
  | [] => []
  | x :: rest =>
    UInt8.ofNat ((x % 65536).toNat % 256) ::
    UInt8.ofNat ((x % 65536).toNat / 256) :: byteListOfPcm16 rest

/-- Split interleaved samples into `ch` channels of `n` samples each. -/
def deinterleaveN (ch : Nat) : Nat → List Int → List (List Int)
  | 0, _ => List.replicate ch []
  | n + 1, l =>
    List.zipWith (· :: ·) (l.take ch) (deinterleaveN ch n (l.drop ch))

/-- Interleave equal-length channels of `n` samples each. -/
def interleaveN : Nat → List (List Int) → List Int
  | 0, _ => []
  | n + 1, chs => chs.map (·.headD 0) ++ interleaveN n (chs.map (·.tail))

def deinterleave (ch : Nat) (l : List Int) : List (List Int) :=
  deinterleaveN ch (l.length / ch) l

def interleave (chs : List (List Int)) : List Int :=
  interleaveN (chs.headD []).length chs

/-- Byte-level encoder, arbitrary configuration: interleaved signed 16-bit
    little-endian PCM with `ch` channels. Checks its whole precondition at
    runtime (byte-count shape plus audio well-formedness). -/
def encodePcm16Cfg (cfg : Flac.Stream.EncoderCfg) (ch sampleRate : Nat)
    (bytes : ByteArray) : Option ByteArray :=
  if 0 < ch ∧ bytes.size % (2 * ch) = 0 then
    encodeCheckedCfg cfg
      ⟨deinterleave ch (pcm16OfByteList bytes.data.toList), 16, sampleRate⟩
  else none

/-- **Byte-level encoder**, default configuration (44.1 kHz label). -/
def encodePcm16 (ch : Nat) (bytes : ByteArray) : Option ByteArray :=
  encodePcm16Cfg ⟨4096, false, Heuristics.defaultAsgChooser 16⟩ ch 44100 bytes

/-- **Byte-level decoder**: back to interleaved signed 16-bit
    little-endian PCM. -/
def decodePcm16 (flac : ByteArray) : Except String ByteArray :=
  match decode flac with
  | .error e => .error e
  | .ok a =>
    if a.bps = 16 then .ok (byteListOfPcm16 (interleave a.channels)).toByteArray
    else .error "not 16-bit audio"

/-! ## The certified fast encoder

`Flac.Encode` is unverified by design (like the heuristics), so every call
is certified at runtime instead: decode the produced bytes with the
*verified* decoder and compare with the input; on any mismatch fall back
to the verified encoder. `Flac.decodePcm16_encodePcm16Fast` is therefore
hypothesis-free — no unverified code is trusted. -/

/-- The runtime certificate: do the produced bytes decode (under the
    *verified* decoder) to exactly the input PCM? -/
def pcm16Certified (bytes out : ByteArray) : Bool :=
  match decodePcm16 out with
  | .ok back => decide (back = bytes)
  | .error _ => false

/-- Keep the fast output only with a valid certificate; otherwise encode
    with the verified encoder. -/
def encodePcm16FastGo (blockSize ch sampleRate : Nat) (bytes out : ByteArray) :
    Option ByteArray :=
  if pcm16Certified bytes out then some out
  else encodePcm16Cfg ⟨blockSize, false, Heuristics.defaultAsgChooser 16⟩
    ch sampleRate bytes

/-- **The fast byte-level encoder**, certified per call. `some` results
    carry the round-trip guarantee (`Flac.decodePcm16_encodePcm16Fast`). -/
def encodePcm16Fast (blockSize ch sampleRate : Nat) (bytes : ByteArray) :
    Option ByteArray :=
  if 0 < ch ∧ bytes.size % (2 * ch) = 0 then
    encodePcm16FastGo blockSize ch sampleRate bytes
      (Encode.encodePcm16 blockSize ch sampleRate bytes)
  else none

end Flac
