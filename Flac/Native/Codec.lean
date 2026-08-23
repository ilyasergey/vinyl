import Flac.Native.Stream
import Flac.Native.Heuristics

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

end Flac
