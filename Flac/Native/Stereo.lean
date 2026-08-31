import Flac.Native.Bits

/-!
# Stereo decorrelation (RFC 9639 §4.2, §9.1.3)

Left/side, right/side, and mid/side transforms. The side channel is
`L - R` (needs one extra bit of depth — the `b+1` bookkeeping at L5);
mid is `(L + R) >>ₐ 1`, recoverable exactly because `L+R` and `L-R`
share parity.

Decoding follows libFLAC's formulation: reconstruct `2·mid + parity(side)`
= `L + R`, then halve `(L+R) ± (L-R)` with an arithmetic shift.
-/

namespace Flac.Stereo

open Flac.Bits (sar)

/-- Side channel: `L - R`. -/
def side (l r : List Int) : List Int :=
  List.zipWith (fun a b => a - b) l r

/-- Mid channel: `(L + R) >>ₐ 1`. -/
def mid (l r : List Int) : List Int :=
  List.zipWith (fun a b => sar (a + b) 1) l r

/-- Left/side decode: `R = L - S`. -/
def decodeLS (b : Nat) (l s : List Int) : List Int :=
  List.zipWith (fun a v => Bits.wrapSInt b (a - v)) l s

/-- Right/side decode: `L = R + S`. -/
def decodeRS (b : Nat) (s r : List Int) : List Int :=
  List.zipWith (fun v rr => Bits.wrapSInt b (rr + v)) s r

/-- Mid/side decode, left: `L = (2·M + parity(S) + S) >>ₐ 1`. -/
def decodeMSL (b : Nat) (m s : List Int) : List Int :=
  List.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)) m s

/-- Mid/side decode, right: `R = (2·M + parity(S) - S) >>ₐ 1`. -/
def decodeMSR (b : Nat) (m s : List Int) : List Int :=
  List.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)) m s

/-! ### Array forms (the production codec's hot paths; proven equal to
the list forms in `Flac.Spec.Stereo`) -/

/-- Side channel over arrays: `L - R`. -/
def sideA (l r : Array Int) : Array Int :=
  Array.zipWith (fun a b => a - b) l r

/-- Mid channel over arrays: `(L + R) >>ₐ 1`. -/
def midA (l r : Array Int) : Array Int :=
  Array.zipWith (fun a b => sar (a + b) 1) l r

def decodeLSA (b : Nat) (l s : Array Int) : Array Int :=
  Array.zipWith (fun a v => Bits.wrapSInt b (a - v)) l s

def decodeRSA (b : Nat) (s r : Array Int) : Array Int :=
  Array.zipWith (fun v rr => Bits.wrapSInt b (rr + v)) s r

def decodeMSLA (b : Nat) (m s : Array Int) : Array Int :=
  Array.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)) m s

def decodeMSRA (b : Nat) (m s : Array Int) : Array Int :=
  Array.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)) m s

end Flac.Stereo
