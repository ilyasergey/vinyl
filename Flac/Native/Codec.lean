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

/-- One interleaved row of 16-bit LE samples at index `i`. -/
def pcm16Row (arrs : List (Array Int)) (i : Nat) (out : ByteArray) : ByteArray :=
  match arrs with
  | [] => out
  | a :: rest =>
    let u := (a.getD i 0 % 65536).toNat
    pcm16Row rest i ((out.push (UInt8.ofNat (u % 256))).push (UInt8.ofNat (u / 256)))

def pcm16Go (arrs : List (Array Int)) : (n i : Nat) → ByteArray → ByteArray
  | 0, _, out => out
  | n + 1, i, out => pcm16Go arrs n (i + 1) (pcm16Row arrs i out)

/-- Interleave + serialize in one indexed pass, straight off the decoder's
    arrays (`Flac.pcm16FastA_eq` relates it to the list form). -/
def pcm16FastA (arrs : List (Array Int)) : ByteArray :=
  pcm16Go arrs (arrs.headD #[]).size 0
    (ByteArray.emptyWithCapacity (2 * arrs.length * (arrs.headD #[]).size))

/-! ### Serializing in parallel windows

The interleaved layout is sample-major, so a window of samples serializes
independently and the windows concatenate. Each worker returns a
`PcmChunk` carrying the equation for the window it actually serialized,
and the consumer uses a chunk only when its recorded window matches the
one it wants, serializing that window itself otherwise — the same
self-certifying arrangement the parallel frame decoder uses. So
`pcm16FastPar_eq` needs no lemma about how the window list was produced,
and none about `Task`. -/

/-- The serialization of the sample window `[lo, lo + len)`. -/
def pcm16Window (arrs : List (Array Int)) (lo len : Nat) : ByteArray :=
  pcm16Go arrs len lo (ByteArray.emptyWithCapacity (2 * arrs.length * len))

/-- A serialized window together with the equation for it. -/
structure PcmChunk (arrs : List (Array Int)) where
  lo : Nat
  len : Nat
  bytes : ByteArray
  ok : bytes = pcm16Window arrs lo len

def pcm16ChunkAt (arrs : List (Array Int)) (lo len : Nat) : PcmChunk arrs :=
  ⟨lo, len, pcm16Window arrs lo len, rfl⟩

/-- Concatenate precomputed windows, checking each against the window it
    is supposed to cover. Proven equal to `pcm16Go` by
    `Flac.pcm16Chunks_eq`. -/
def pcm16Chunks (arrs : List (Array Int)) (win : Nat) :
    List (PcmChunk arrs) → (n lo : Nat) → ByteArray → ByteArray
  | [], n, lo, out => pcm16Go arrs n lo out
  | c :: cs', n, lo, out =>
    match n with
    | 0 => out
    | rem + 1 =>
      if _h : c.lo = lo ∧ c.len = max 1 (min (rem + 1) win) then
        pcm16Chunks arrs win cs' (rem + 1 - max 1 (min (rem + 1) win))
          (lo + max 1 (min (rem + 1) win)) (out ++ c.bytes)
      else pcm16Go arrs (rem + 1) lo out

/-- One worker per window. Every task is spawned before any is collected —
    that ordering is what makes the windows run concurrently. -/
def pcm16Tasks (arrs : List (Array Int)) (ws : List (Nat × Nat)) :
    List (PcmChunk arrs) :=
  (ws.map fun w => Task.spawn fun _ => pcm16ChunkAt arrs w.1 w.2).map Task.get

/-- `pcm16FastA` with the windows computed in parallel (equal to it by
    `Flac.pcm16FastPar_eq`). This is the encoder's runtime certificate
    doing its own serialization, which was 10% of encode and serial. -/
def pcm16FastPar (arrs : List (Array Int)) : ByteArray :=
  if (arrs.headD #[]).size ≤ Flac.Stream.pcmWindow then pcm16FastA arrs
  else
    pcm16Chunks arrs Flac.Stream.pcmWindow
      (pcm16Tasks arrs (Flac.Stream.pcmWindows (arrs.headD #[]).size))
      (arrs.headD #[]).size 0
      (ByteArray.emptyWithCapacity (2 * arrs.length * (arrs.headD #[]).size))

/-- Interleave + serialize in one indexed pass — proven equal to the
    compositional `byteListOfPcm16 ∘ interleave` by `Flac.pcm16Fast_eq`. -/
def pcm16Fast (chs : List (List Int)) : ByteArray :=
  pcm16Go (chs.map List.toArray) (chs.headD []).length 0
    (ByteArray.emptyWithCapacity (2 * chs.length * (chs.headD []).length))

/-- **Byte-level decoder**: back to interleaved signed 16-bit
    little-endian PCM. -/
def decodePcm16 (flac : ByteArray) : Except String ByteArray :=
  match decode flac with
  | .error e => .error e
  | .ok a =>
    if a.bps = 16 then .ok (pcm16Fast a.channels)
    else .error "not 16-bit audio"

/-- `decodePcm16` without the decoder's list conversion: it serializes the
    decoded arrays directly. Proven equal to `decodePcm16` by
    `Flac.decodePcm16A_eq`, which is what lets the runtime certificate and
    the CLI run it in place of the list path. -/
def decodePcm16A (flac : ByteArray) : Except String ByteArray :=
  match Decode.decodeArrays flac with
  | none => .error "not a decodable FLAC stream (within the v1 feature set)"
  | some (chs, bps, _) =>
    if bps = 16 then .ok (pcm16FastPar chs)
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
  match decodePcm16A out with
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
