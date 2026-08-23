import Flac.Native.Bits
import Flac.Native.Rice
import Flac.Native.Fixed
import Flac.Native.Lpc

/-!
# Subframes (RFC 9639 §9.2): CONSTANT, VERBATIM, FIXED

All four subframe types, with wasted-bits support (RFC 9639 §9.2.2): a
subframe whose samples all share `w` low zero bits stores them scaled down
at bit depth `b - w`, with `w` coded in the header (flag + unary `w-1`).

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
  /-- Linear predictor: coefficients (most recent sample first, order
      `cs.length ∈ 1..32`), coefficient precision `prec ∈ 1..15` bits,
      non-negative quantization shift `≤ 15`. -/
  | lpc (cs : List Int) (shift prec : Nat) (rcfg : Rice.ResidualCfg)

/-- Subframe type code for the 6-bit header field (RFC 9639 Table 9). -/
def SubframeCfg.typeCode : SubframeCfg → Nat
  | .constant => 0
  | .verbatim => 1
  | .fixed ord _ => 8 + ord
  | .lpc cs _ _ _ => 32 + (cs.length - 1)

/-- Validity certificate for a subframe choice on a concrete block `xs`
    at bit depth `b` (block size is `xs.length`, enforced upstream). -/
def SubframeCfg.Valid (cfg : SubframeCfg) (b : Nat) (xs : List Int) : Prop :=
  match cfg with
  | .constant => (∀ x ∈ xs, x = xs.headD 0) ∧ FitsSInt b (xs.headD 0)
  | .verbatim => ∀ x ∈ xs, FitsSInt b x
  | .fixed ord rcfg =>
      ord ≤ 4 ∧ (∀ x ∈ xs.take ord, FitsSInt b x) ∧
      rcfg.Valid xs.length ord (Fixed.residual ord xs)
  | .lpc cs shift prec rcfg =>
      1 ≤ cs.length ∧ cs.length ≤ 32 ∧
      (∀ x ∈ xs.take cs.length, FitsSInt b x) ∧
      1 ≤ prec ∧ prec ≤ 15 ∧ (∀ c ∈ cs, FitsSInt prec c) ∧
      shift ≤ 15 ∧
      rcfg.Valid xs.length cs.length (Lpc.residual cs shift xs)

/-- A subframe configuration: wasted-bits count plus the inner choice.
    The inner configuration describes the *scaled-down* samples. -/
structure SubCfg where
  wasted : Nat
  inner : SubframeCfg

/-- Validity: `w` in range, all samples divisible by `2^w`, and the inner
    configuration valid for the scaled samples at the reduced depth —
    the width bookkeeping of PLAN.md §5.6. -/
def SubCfg.Valid (sc : SubCfg) (b : Nat) (xs : List Int) : Prop :=
  sc.wasted < b ∧
  (∀ x ∈ xs, ((2 ^ sc.wasted : Nat) : Int) ∣ x) ∧
  sc.inner.Valid (b - sc.wasted) (xs.map (shiftDown sc.wasted))

def writeContent (b : Nat) (cfg : SubframeCfg) (xs : List Int) : BitStream :=
  match cfg with
  | .constant => writeSInt b (xs.headD 0)
  | .verbatim => writeSIntSeq b xs
  | .fixed ord rcfg =>
      writeSIntSeq b (xs.take ord) ++
      Rice.writeResidual xs.length ord rcfg (Fixed.residual ord xs)
  | .lpc cs shift prec rcfg =>
      writeSIntSeq b (xs.take cs.length) ++
      writeBits 4 (prec - 1) ++ writeSInt 5 (shift : Int) ++
      writeSIntSeq prec cs ++
      Rice.writeResidual xs.length cs.length rcfg (Lpc.residual cs shift xs)

def write (b : Nat) (sc : SubCfg) (xs : List Int) : BitStream :=
  writeBits 1 0 ++ writeBits 6 sc.inner.typeCode ++
  (if sc.wasted = 0 then writeBits 1 0
   else writeBits 1 1 ++ writeUnary (sc.wasted - 1)) ++
  writeContent (b - sc.wasted) sc.inner (xs.map (shiftDown sc.wasted))

/-- Read the content of a subframe of type `ty`: `bs` samples at
    (wasted-reduced) bit depth `b`. -/
def readContent (bs b ty : Nat) (s : BitStream) : Option (List Int × BitStream) :=
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
  else if 32 ≤ ty then                   -- ty ≤ 63 always (6-bit field)
    match readSIntSeq b (ty - 31) s with
    | none => none
    | some (warmup, s) =>
      match readBits 4 s with
      | none => none
      | some (pm1, s) =>
        if pm1 = 15 then none            -- forbidden precision code
        else
          match readSInt 5 s with
          | none => none
          | some (sh, s) =>
            if 0 ≤ sh then               -- negative shift is forbidden
              match readSIntSeq (pm1 + 1) (ty - 31) s with
              | none => none
              | some (cs, s) =>
                match Rice.readResidual bs (ty - 31) s with
                | none => none
                | some (res, s) =>
                  some (Lpc.restore cs sh.toNat warmup res, s)
            else none
  else none                              -- reserved / invalid

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
        | some (wf, s) =>
          if wf = 0 then
            readContent bs b ty s
          else
            match readUnary s with
            | none => none
            | some (k, s) =>
              match readContent bs (b - (k + 1)) ty s with
              | none => none
              | some (ys, s) => some (ys.map (shiftUp (k + 1)), s)
    else none                            -- reserved bit must be 0

end Flac.Subframe
