import Flac

/-!
# Capstone pins — the theorem↔executable linkage, machine-checked

`scripts/check.sh` greps for capstone *names*, which cannot notice a
theorem that keeps its name while its statement drifts. Every `example`
below restates a capstone in full and discharges it with the real
theorem, so `lake build` fails if any of them is weakened, re-stated
about a different function, or renamed.

Each pin names the function the `vinyl` CLI actually calls, so together
they answer "is the thing I ran the thing that was proved?":

| CLI mode | function it calls | pinned by |
|---|---|---|
| `--encode` | `Flac.encodePcm16Fast` | `pin_encode_fast` |
| `--encode-slow` | `Flac.encodePcm16Cfg` | `pin_encode_cfg` |
| `--decode-pcm16` | `Flac.decodePcm16A` | `pin_decodePcm16A` |
| `--decode-fast` | `Flac.Decode.decodeBytes` | `pin_decodeBytes` |
| `--decode-fast` (fallback) | `Flac.Decode.decodeArrays` | `pin_decodeArrays` |
| `--decode` | `Stream.decodeReference` | `pin_reference` |

The CLI *call sites* are pinned separately, by grep, in
`scripts/check.sh` — which function a `do` block invokes is not something
a type can express.

`--decode-fast` used to serialize with `Stream.pcmBytesA`, whose window
concatenation carried no theorem — it could not, since it reasons through
`Task`. It now runs `Flac.Decode.decodeBytes`, whose result is *proved*
to be `Stream.pcmBytesRange` of the samples `decodeArrays` returns
(`pin_decodeBytes`), because every frame's step carries its own equation.
`--decode` still serializes with `Stream.pcmBytesA`; the theorem-backed
byte-level decode of the reference pipeline is `--decode-pcm16`. See
`ARCHITECTURE.md`.
-/

namespace FlacTest.Capstones

open Flac Flac.Stream

/-- **The capstone**: the shipped pair round-trips every well-formed audio. -/
theorem pin_decode_encode :
    ∀ (a : Audio), a.WellFormed → Flac.decode (Flac.encode a) = .ok a :=
  @Flac.decode_encode

/-- The runtime-checked encoder needs no hypothesis. -/
theorem pin_encodeChecked :
    ∀ {a : Audio} {bytes : ByteArray},
      Flac.encodeChecked a = some bytes → Flac.decode bytes = .ok a :=
  @Flac.decode_encodeChecked

/-- Arbitrary encoder configuration, including the heuristic. -/
theorem pin_encode_cfg :
    ∀ {cfg : EncoderCfg} {ch sr : Nat} {bytes flac : ByteArray},
      Flac.encodePcm16Cfg cfg ch sr bytes = some flac →
        Flac.decodePcm16 flac = .ok bytes :=
  @Flac.decodePcm16_encodePcm16Cfg

/-- The byte-level guarantee for the default encoder. -/
theorem pin_encodePcm16 :
    ∀ {ch : Nat} {bytes flac : ByteArray},
      Flac.encodePcm16 ch bytes = some flac → Flac.decodePcm16 flac = .ok bytes :=
  @Flac.decodePcm16_encodePcm16

/-- **What `vinyl --encode` runs**: the fast (unverified) encoder, certified
    per call, with no hypothesis and no trust in `Flac.Encode`. -/
theorem pin_encode_fast :
    ∀ {blockSize ch sr : Nat} {bytes flac : ByteArray},
      Flac.encodePcm16Fast blockSize ch sr bytes = some flac →
        Flac.decodePcm16 flac = .ok bytes :=
  @Flac.decodePcm16_encodePcm16Fast

/-- The shipped decoder computes the verified reference decoder. -/
theorem pin_reference :
    ∀ (bytes : ByteArray),
      Flac.Decode.decodeOption bytes = Stream.decodeReference bytes :=
  @Flac.Decode.decodeOption_eq_reference

/-- **What `vinyl --decode-fast` runs**: `decodeArrays` is `decodeOption`
    without the per-sample `Array → List` conversion, so pinning the
    conversion pins the array core the CLI consumes. -/
theorem pin_decodeArrays :
    ∀ (bytes : ByteArray),
      Flac.Decode.decodeOption bytes
        = (Flac.Decode.decodeArrays bytes).map
            (fun p => ⟨p.1.map (·.toList), p.2.1, p.2.2⟩) :=
  fun _ => rfl

/-- **What `vinyl --decode-pcm16` runs**: equal to the `decodePcm16` named
    in the byte-level capstone. -/
theorem pin_decodePcm16A :
    ∀ (flac : ByteArray), Flac.decodePcm16A flac = Flac.decodePcm16 flac :=
  @Flac.decodePcm16A_eq

/-- Frame-parallel decoding is the serial loop. -/
theorem pin_parallel_decode :
    ∀ (b0 : Nat) (d : ByteArray) (fuel pos : Nat), pos ≤ 8 * d.size →
      Flac.Decode.readFramesFast b0 d fuel pos
        = Flac.Decode.readFrames b0 fuel ⟨d, pos⟩ :=
  @Flac.Decode.readFramesFast_eq

/-- Parallel PCM serialization is the serial serializer. -/
theorem pin_parallel_serialize :
    ∀ (arrs : List (Array Int)), Flac.pcm16FastPar arrs = Flac.pcm16FastA arrs :=
  @Flac.pcm16FastPar_eq

/-- **What `vinyl --decode-fast` runs**: whenever the frame-parallel byte
    decoder returns bytes, they are exactly the interleaved PCM
    serialization of the samples `decodeArrays` returns. -/
theorem pin_decodeBytes :
    ∀ (bytes out : ByteArray), Flac.Decode.decodeBytes bytes = some out →
      ∃ chs bps sr, Flac.Decode.decodeArrays bytes = some (chs, bps, sr)
        ∧ out = Flac.Stream.pcmBytesRange bps chs 0 (chs.headD #[]).size :=
  @Flac.Stream.decodeBytes_spec

end FlacTest.Capstones
