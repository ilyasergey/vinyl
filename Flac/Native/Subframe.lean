import Flac.Native.Bits
import Flac.Native.Rice
import Flac.Native.Fixed

/-!
# Subframes (RFC 9639 §9.2): CONSTANT, VERBATIM, FIXED

M2 scope: the three non-LPC subframe types, no wasted bits (the encoder
never emits the flag yet; the decoder rejects it until M4). LPC arrives
with M3, wasted bits and the side-channel bit-depth bookkeeping with M4.

The per-block choice of subframe type (and residual configuration) is a
heuristic *input* (`SubframeCfg`), carrying a validity certificate
(`SubframeCfg.Valid`); the round-trip in `Flac.Spec.Subframe` holds for
every valid choice.
-/

namespace Flac.Subframe

open Flac.Bits Flac.Rice

/-- Encoder-side subframe choice (produced by the heuristics layer). -/
inductive SubframeCfg where
  /-- All samples in the block are equal. -/
  | constant
  /-- Store samples unencoded. Always valid; the fallback. -/
  | verbatim
  /-- Fixed predictor of order `ord ≤ 4` with the given residual coding. -/
  | fixed (ord : Nat) (rcfg : Rice.ResidualCfg)

/-- Subframe type code for the 6-bit header field (RFC 9639 Table 9). -/
def SubframeCfg.typeCode : SubframeCfg → Nat
  | .constant => 0
  | .verbatim => 1
  | .fixed ord _ => 8 + ord

/-- Validity certificate for a subframe choice on a concrete block `xs`
    at bit depth `b` (block size is `xs.length`, enforced upstream). -/
def SubframeCfg.Valid (cfg : SubframeCfg) (b : Nat) (xs : List Int) : Prop :=
  match cfg with
  | .constant => (∀ x ∈ xs, x = xs.headD 0) ∧ FitsSInt b (xs.headD 0)
  | .verbatim => ∀ x ∈ xs, FitsSInt b x
  | .fixed ord rcfg =>
      ord ≤ 4 ∧ (∀ x ∈ xs.take ord, FitsSInt b x) ∧
      rcfg.Valid xs.length ord (Fixed.residual ord xs)

def write (b : Nat) (cfg : SubframeCfg) (xs : List Int) : BitStream :=
  writeBits 1 0 ++ writeBits 6 cfg.typeCode ++ writeBits 1 0 ++
  match cfg with
  | .constant => writeSInt b (xs.headD 0)
  | .verbatim => writeSIntSeq b xs
  | .fixed ord rcfg =>
      writeSIntSeq b (xs.take ord) ++
      Rice.writeResidual xs.length ord rcfg (Fixed.residual ord xs)

/-- Read one subframe of `bs` samples at bit depth `b`. -/
def read (bs b : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  match readBits 1 s with
  | none => none
  | some (r, s) =>
    if r = 0 then
      match readBits 6 s with
      | none => none
      | some (ty, s) =>
        match readBits 1 s with
        | none => none
        | some (w, s) =>
          if w = 0 then
            if ty = 0 then
              match readSInt b s with
              | none => none
              | some (v, s) => some (List.replicate bs v, s)
            else if ty = 1 then
              readSIntSeq b bs s
            else if 8 ≤ ty ∧ ty ≤ 12 then
              match readSIntSeq b (ty - 8) s with
              | none => none
              | some (warmup, s) =>
                match Rice.readResidual bs (ty - 8) s with
                | none => none
                | some (res, s) => some (Fixed.restore (ty - 8) warmup res, s)
            else none                    -- reserved / LPC (M3) / invalid
          else none                      -- wasted bits: M4
    else none                            -- reserved bit must be 0

end Flac.Subframe
