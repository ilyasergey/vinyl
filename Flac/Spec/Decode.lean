import Flac.Native.Codec
import Flac.Native.Decode
import Flac.Spec.Crc
import Flac.Spec.Reader
import Flac.Spec.Heuristics

/-!
# Production↔reference decoder equivalence

Layer-by-layer simulation: each production reader returns exactly what its
reference counterpart returns on the denoted bitstream, culminating in
`decodeOption_eq_reference` and the accept-set transfer.
-/

namespace Flac.Decode

open Flac Flac.Bits Flac.Bits.BitReader

/-- The uniform simulation statement. -/
def Sim {α : Type} (R : BitStream → Option (α × BitStream))
    (P : BitReader → Option (α × BitReader)) : Prop :=
  ∀ br : BitReader, R (toStream br) = (P br).map (fun p => (p.1, toStream p.2))

/-! ## Coded numbers -/

theorem readConts_sim (k : Nat) :
    ∀ (acc : Nat) (br : BitReader),
      Utf8Num.readConts k acc (toStream br)
        = (readConts k acc br).map (fun p => (p.1, toStream p.2)) := by
  induction k with
  | zero => intro acc br; rfl
  | succ k ih =>
    intro acc br
    show Utf8Num.readConts (k + 1) acc (toStream br) = _
    unfold Utf8Num.readConts readConts
    rw [readBits_sim 8 br]
    cases hp : br.readBits 8 with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      by_cases hc : 0x80 ≤ p.1 ∧ p.1 < 0xC0
      · rw [if_pos hc, if_pos hc, ih]
      · rw [if_neg hc, if_neg hc]
        rfl

theorem readUtf8_sim (br : BitReader) :
    Utf8Num.read (toStream br)
      = (readUtf8 br).map (fun p => (p.1, toStream p.2)) := by
  unfold Utf8Num.read readUtf8
  rw [readBits_sim 8 br]
  cases hp : br.readBits 8 with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    by_cases h1 : p.1 < 0x80
    · rw [if_pos h1, if_pos h1]; rfl
    rw [if_neg h1, if_neg h1]
    by_cases h2 : p.1 < 0xC0
    · rw [if_pos h2, if_pos h2]; rfl
    rw [if_neg h2, if_neg h2]
    by_cases h3 : p.1 < 0xE0
    · rw [if_pos h3, if_pos h3]; exact readConts_sim 1 _ _
    rw [if_neg h3, if_neg h3]
    by_cases h4 : p.1 < 0xF0
    · rw [if_pos h4, if_pos h4]; exact readConts_sim 2 _ _
    rw [if_neg h4, if_neg h4]
    by_cases h5 : p.1 < 0xF8
    · rw [if_pos h5, if_pos h5]; exact readConts_sim 3 _ _
    rw [if_neg h5, if_neg h5]
    by_cases h6 : p.1 < 0xFC
    · rw [if_pos h6, if_pos h6]; exact readConts_sim 4 _ _
    rw [if_neg h6, if_neg h6]
    by_cases h7 : p.1 < 0xFE
    · rw [if_pos h7, if_pos h7]; exact readConts_sim 5 _ _
    rw [if_neg h7, if_neg h7]
    by_cases h8 : p.1 = 0xFE
    · rw [if_pos h8, if_pos h8]; exact readConts_sim 6 _ _
    · rw [if_neg h8, if_neg h8]; rfl

/-! ## Rice codes -/

theorem readRiceNat_sim (k : Nat) (br : BitReader) :
    Rice.readRiceNat k (toStream br)
      = (readRiceNat k br).map (fun p => (p.1, toStream p.2)) := by
  unfold Rice.readRiceNat readRiceNat
  rw [readUnary_sim br]
  cases br.readUnary with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    rw [readBits_sim k p.2]
    cases p.2.readBits k with
    | none => rfl
    | some q => simp only [p2_eq]; rfl

theorem readRice_sim (k : Nat) (br : BitReader) :
    Rice.readRice k (toStream br)
      = (readRice k br).map (fun p => (p.1, toStream p.2)) := by
  unfold Rice.readRice readRice
  rw [readRiceNat_sim k br]
  cases readRiceNat k br with
  | none => rfl
  | some p => rfl

/-! ### The fused sequence readers compute the reader-chain forms -/

/-- `readRice` unrolled to raw bit positions. -/
private theorem readRice_pos (k : Nat) (d : ByteArray) (pos : Nat) :
    readRice k ⟨d, pos⟩
      = match readUnaryGo d 0 pos (8 * d.size - pos) with
        | none => none
        | some (q, pos1) =>
          if k = 0 then some (Rice.unzigzag q, (⟨d, pos1⟩ : BitReader))
          else if pos1 + k ≤ 8 * d.size then
            some (Rice.unzigzag (q * p2 k + extractBitsFast d pos1 k),
              (⟨d, pos1 + k⟩ : BitReader))
          else none := by
  unfold readRice readRiceNat BitReader.readUnary
  dsimp only [BitReader.remaining, BitReader.size]
  cases readUnaryGo d 0 pos (8 * d.size - pos) with
  | none => rfl
  | some p =>
    dsimp only
    unfold BitReader.readBits
    dsimp only [BitReader.size]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk, hk]
      dsimp only
      rw [show p.1 * p2 0 + 0 = p.1 from by simp]
    · rw [if_neg hk, if_neg hk]
      by_cases hb : p.2 + k ≤ 8 * d.size
      · simp only [hb, if_true]
      · simp only [hb, if_false]

/-- `readSInt` unrolled to raw bit positions. -/
private theorem readSInt_pos (bits : Nat) (d : ByteArray) (pos : Nat) :
    BitReader.readSInt bits ⟨d, pos⟩
      = (if bits = 0 then some ((0 : Int), (⟨d, pos⟩ : BitReader))
         else if pos + bits ≤ 8 * d.size then
           some ((if 2 * extractBitsFast d pos bits < p2 bits then
               ((extractBitsFast d pos bits : Nat) : Int)
             else ((extractBitsFast d pos bits : Nat) : Int)
               - ((p2 bits : Nat) : Int)), ⟨d, pos + bits⟩)
         else none) := by
  unfold BitReader.readSInt BitReader.readBits
  dsimp only [BitReader.size]
  by_cases hz : bits = 0
  · rw [if_pos hz, if_pos hz, hz]
    dsimp only
    rw [if_pos (by simp)]
    rfl
  · rw [if_neg hz, if_neg hz]
    by_cases hb : pos + bits ≤ 8 * d.size
    · simp only [hb, if_true]
    · simp only [hb, if_false]

/-- The allocation-free Rice state machine computes the original fused
    position reader.  This is the only bridge needed by callers: the existing
    sequence simulation and every decoder capstone keep their statements. -/
theorem readRiceSeqScan_eq (d : ByteArray) (k : Nat) :
    ∀ (count pos : Nat) (acc : Array Int),
      readRiceSeqScan d k (p2 k) (8 * d.size) count pos acc =
        readRiceSeqGo d k count pos acc := by
  intro count
  induction count with
  | zero => intro pos acc; rfl
  | succ count ih =>
    intro pos acc
    unfold readRiceSeqScan readRiceSeqGo
    by_cases hp : pos < 8 * d.size
    · rw [if_pos hp]
      have hs := scanOne_spec d (8 * d.size - pos) pos 0
      rw [show pos + (8 * d.size - pos) = 8 * d.size from by omega] at hs
      rw [hs]
      have hfuel : 8 * d.size - pos = (8 * d.size - (pos + 1)) + 1 := by omega
      have hscan : scanOne d pos (8 * d.size - pos) =
          (if bitFast d pos then pos
           else scanOne d (pos + 1) (8 * d.size - (pos + 1))) := by
        rw [hfuel]
        rfl
      rw [hscan]
      by_cases hb : bitFast d pos
      · simp only [hb, if_true, hp]
        by_cases hk : k = 0
        · simp only [hk, if_true, Rice.unzigzag]
          simpa [hk] using ih (pos + 1) (acc.push 0)
        · simp only [hk, if_false]
          by_cases hr : pos + 1 + k ≤ 8 * d.size
          · simp only [hr, if_true, Nat.zero_add]
            simpa [hk] using ih (pos + 1 + k)
              (acc.push (Rice.unzigzag (extractBitsFast d (pos + 1) k)))
          · simp only [hr, if_false]
      · simp only [hb, Bool.false_eq_true, if_false]
        by_cases ho : scanOne d (pos + 1) (8 * d.size - (pos + 1)) < 8 * d.size
        · simp only [ho, if_true, Nat.zero_add]
          by_cases hk : k = 0
          · simp only [hk, if_true]
            simpa [hk] using ih
              (scanOne d (pos + 1) (8 * d.size - (pos + 1)) + 1)
              (acc.push (Rice.unzigzag
                (scanOne d (pos + 1) (8 * d.size - (pos + 1)) - pos)))
          · simp only [hk, if_false]
            by_cases hr : scanOne d (pos + 1) (8 * d.size - (pos + 1)) + 1 + k ≤
                8 * d.size
            · simp only [hr, if_true]
              simpa [hk] using ih
                (scanOne d (pos + 1) (8 * d.size - (pos + 1)) + 1 + k)
                (acc.push (Rice.unzigzag
                  ((scanOne d (pos + 1) (8 * d.size - (pos + 1)) - pos) * p2 k +
                    extractBitsFast d
                      (scanOne d (pos + 1) (8 * d.size - (pos + 1)) + 1) k)))
            · simp only [hr, if_false]
        · simp only [ho, if_false]
    · rw [if_neg hp]
      have hz : 8 * d.size - pos = 0 := by omega
      rw [hz]
      rfl

theorem readRiceSeqFast_eq (k : Nat) :
    ∀ (count : Nat) (br : BitReader) (acc : Array Int),
      readRiceSeqFast k count br acc = readRiceSeqA k count br acc := by
  intro count
  induction count with
  | zero => intro br acc; rfl
  | succ count ih =>
    intro br acc
    obtain ⟨d, pos⟩ := br
    unfold readRiceSeqFast
    rw [readRiceSeqScan_eq]
    unfold readRiceSeqGo readRiceSeqA
    dsimp only
    rw [readRice_pos]
    cases readUnaryGo d 0 pos (8 * d.size - pos) with
    | none => rfl
    | some p =>
      dsimp only
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk]
        have h := ih ⟨d, p.2⟩ (acc.push (Rice.unzigzag p.1))
        unfold readRiceSeqFast at h
        rw [readRiceSeqScan_eq] at h
        exact h
      · rw [if_neg hk, if_neg hk]
        by_cases hb : p.2 + k ≤ 8 * d.size
        · simp only [hb, if_true]
          have h := ih ⟨d, p.2 + k⟩
            (acc.push (Rice.unzigzag (p.1 * p2 k + extractBitsFast d p.2 k)))
          unfold readRiceSeqFast at h
          rw [readRiceSeqScan_eq] at h
          exact h
        · simp only [hb, if_false]

theorem readSIntSeqFast_eq (bits : Nat) :
    ∀ (count : Nat) (br : BitReader) (acc : Array Int),
      readSIntSeqFast bits count br acc = readSIntSeqA bits count br acc := by
  intro count
  induction count with
  | zero => intro br acc; rfl
  | succ count ih =>
    intro br acc
    obtain ⟨d, pos⟩ := br
    unfold readSIntSeqFast readSIntSeqGo readSIntSeqA
    dsimp only
    rw [readSInt_pos]
    by_cases hz : bits = 0
    · rw [if_pos hz, if_pos hz]
      have h := ih ⟨d, pos⟩ (acc.push 0)
      unfold readSIntSeqFast at h
      exact h
    · rw [if_neg hz, if_neg hz]
      by_cases hb : pos + bits ≤ 8 * d.size
      · simp only [hb, if_true]
        have h := ih ⟨d, pos + bits⟩
          (acc.push (if 2 * extractBitsFast d pos bits < p2 bits then
              ((extractBitsFast d pos bits : Nat) : Int)
            else ((extractBitsFast d pos bits : Nat) : Int)
              - ((p2 bits : Nat) : Int)))
        unfold readSIntSeqFast at h
        exact h
      · simp only [hb, if_false]

/-- Accumulator normalization: reading into `acc` is reading into `#[]`
    prepended with `acc`. -/
theorem readRiceSeqA_acc (k : Nat) :
    ∀ (count : Nat) (br : BitReader) (acc : Array Int),
      readRiceSeqA k count br acc
        = (readRiceSeqA k count br #[]).map (fun p => (acc ++ p.1, p.2)) := by
  intro count
  induction count with
  | zero => intro br acc; simp [readRiceSeqA]
  | succ count ih =>
    intro br acc
    unfold readRiceSeqA
    cases readRice k br with
    | none => rfl
    | some p =>
      dsimp only
      rw [ih p.2 (acc.push p.1), ih p.2 (#[].push p.1)]
      cases readRiceSeqA k count p.2 #[] with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        refine ⟨Array.toList_inj.mp ?_, trivial⟩
        simp

theorem readSIntSeqA_acc (bits : Nat) :
    ∀ (count : Nat) (br : BitReader) (acc : Array Int),
      readSIntSeqA bits count br acc
        = (readSIntSeqA bits count br #[]).map (fun p => (acc ++ p.1, p.2)) := by
  intro count
  induction count with
  | zero => intro br acc; simp [readSIntSeqA]
  | succ count ih =>
    intro br acc
    unfold readSIntSeqA
    cases br.readSInt bits with
    | none => rfl
    | some p =>
      dsimp only
      rw [ih p.2 (acc.push p.1), ih p.2 (#[].push p.1)]
      cases readSIntSeqA bits count p.2 #[] with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        refine ⟨Array.toList_inj.mp ?_, trivial⟩
        simp

theorem readRiceSeqA_sim (k : Nat) :
    ∀ (count : Nat) (br : BitReader),
      Rice.readRiceSeq k count (toStream br)
        = (readRiceSeqA k count br #[]).map (fun p => (p.1.toList, toStream p.2)) := by
  intro count
  induction count with
  | zero => intro br; rfl
  | succ count ih =>
    intro br
    unfold Rice.readRiceSeq readRiceSeqA
    rw [readRice_sim k br]
    cases readRice k br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2, readRiceSeqA_acc k count p.2 (#[].push p.1)]
      cases readRiceSeqA k count p.2 #[] with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨by simp, trivial⟩

theorem readSIntSeqA_sim (bits : Nat) :
    ∀ (count : Nat) (br : BitReader),
      Rice.readSIntSeq bits count (toStream br)
        = (readSIntSeqA bits count br #[]).map (fun p => (p.1.toList, toStream p.2)) := by
  intro count
  induction count with
  | zero => intro br; rfl
  | succ count ih =>
    intro br
    unfold Rice.readSIntSeq readSIntSeqA
    rw [readSInt_sim bits br]
    cases br.readSInt bits with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2, readSIntSeqA_acc bits count p.2 (#[].push p.1)]
      cases readSIntSeqA bits count p.2 #[] with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨by simp, trivial⟩

/-- The list-level wrapper computes the model reader (the statement every
    caller above the residual layer keeps using). -/
theorem readSIntSeq_sim (bits : Nat) (count : Nat) (br : BitReader) :
    Rice.readSIntSeq bits count (toStream br)
      = (readSIntSeq bits count br).map (fun p => (p.1, toStream p.2)) := by
  unfold readSIntSeq
  simp only [readSIntSeqFast_eq]
  rw [readSIntSeqA_sim bits count br]
  cases readSIntSeqA bits count br #[] with
  | none => rfl
  | some p => rfl

/-! ## Partitions -/

theorem readPartA_acc (m : Rice.Method) (count : Nat) (br : BitReader)
    (acc : Array Int) :
    readPartA m count br acc
      = (readPartA m count br #[]).map (fun p => (acc ++ p.1, p.2)) := by
  unfold readPartA
  simp only [readRiceSeqFast_eq, readSIntSeqFast_eq]
  cases br.readBits m.paramBits with
  | none => rfl
  | some p =>
    dsimp only
    by_cases hk : p.1 = m.escapeCode
    · rw [if_pos hk, if_pos hk]
      cases p.2.readBits 5 with
      | none => rfl
      | some q => exact readSIntSeqA_acc q.1 count q.2 acc
    · rw [if_neg hk, if_neg hk]
      exact readRiceSeqA_acc p.1 count p.2 acc

theorem readPartA_sim (m : Rice.Method) (count : Nat) (br : BitReader) :
    Rice.readPart m count (toStream br)
      = (readPartA m count br #[]).map (fun p => (p.1.toList, toStream p.2)) := by
  unfold Rice.readPart readPartA
  simp only [readRiceSeqFast_eq, readSIntSeqFast_eq]
  rw [readBits_sim m.paramBits br]
  cases br.readBits m.paramBits with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    by_cases hk : p.1 = m.escapeCode
    · rw [if_pos hk, if_pos hk, readBits_sim 5 p.2]
      cases p.2.readBits 5 with
      | none => rfl
      | some q => exact readSIntSeqA_sim q.1 count q.2
    · rw [if_neg hk, if_neg hk]
      exact readRiceSeqA_sim p.1 count p.2

theorem readPartsA_acc (m : Rice.Method) :
    ∀ (sizes : List Nat) (br : BitReader) (acc : Array Int),
      readPartsA m sizes br acc
        = (readPartsA m sizes br #[]).map (fun p => (acc ++ p.1, p.2)) := by
  intro sizes
  induction sizes with
  | nil => intro br acc; simp [readPartsA]
  | cons sz sizes ih =>
    intro br acc
    unfold readPartsA
    rw [readPartA_acc m sz br acc]
    cases readPartA m sz br #[] with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2 (acc ++ p.1), ih p.2 p.1]
      cases readPartsA m sizes p.2 #[] with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        refine ⟨Array.toList_inj.mp ?_, trivial⟩
        simp

theorem readPartsA_sim (m : Rice.Method) :
    ∀ (sizes : List Nat) (br : BitReader),
      Rice.readParts m sizes (toStream br)
        = (readPartsA m sizes br #[]).map (fun p => (p.1.toList, toStream p.2)) := by
  intro sizes
  induction sizes with
  | nil => intro br; rfl
  | cons sz sizes ih =>
    intro br
    unfold Rice.readParts readPartsA
    rw [readPartA_sim m sz br]
    cases readPartA m sz br #[] with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2, readPartsA_acc m sizes p.2 p.1]
      cases readPartsA m sizes p.2 #[] with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨by simp, trivial⟩

theorem readResidualA_sim (bs ord : Nat) (br : BitReader) :
    Rice.readResidual bs ord (toStream br)
      = (readResidualA bs ord br).map (fun p => (p.1.toList, toStream p.2)) := by
  unfold Rice.readResidual readResidualA
  rw [readBits_sim 2 br]
  cases br.readBits 2 with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    cases Rice.Method.ofCode p.1 with
    | none => rfl
    | some m =>
      rw [readBits_sim 4 p.2]
      cases p.2.readBits 4 with
      | none => rfl
      | some q =>
        simp only [Option.map_some]
        by_cases hc : bs % 2 ^ q.1 = 0 ∧ ord < bs / 2 ^ q.1
        · rw [if_pos hc, if_pos hc, Array.emptyWithCapacity_eq]
          exact readPartsA_sim m _ q.2
        · rw [if_neg hc, if_neg hc]
          rfl

theorem readContent_sim (bs b ty : Nat) (br : BitReader) :
    Subframe.readContent bs b ty (toStream br)
      = (readContent bs b ty br).map (fun p => (p.1.toList, toStream p.2)) := by
  unfold Subframe.readContent readContent
  by_cases h0 : ty = 0
  · rw [if_pos h0, if_pos h0, readSInt_sim b br]
    cases br.readSInt b with
    | none => rfl
    | some p => simp only [Option.map_some, Array.toList_replicate]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : ty = 1
  · rw [if_pos h1, if_pos h1, readSIntSeqFast_eq]
    exact readSIntSeqA_sim b bs br
  rw [if_neg h1, if_neg h1]
  by_cases h2 : 8 ≤ ty ∧ ty ≤ 12
  · rw [if_pos h2, if_pos h2, readSIntSeq_sim b (ty - 8) br]
    cases readSIntSeq b (ty - 8) br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [readResidualA_sim bs (ty - 8) p.2]
      cases readResidualA bs (ty - 8) p.2 with
      | none => rfl
      | some q => simp only [Option.map_some, Fixed.restoreA_toList]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : 32 ≤ ty
  · rw [if_pos h3, if_pos h3, readSIntSeq_sim b (ty - 31) br]
    cases readSIntSeq b (ty - 31) br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [readBits_sim 4 p.2]
      cases p.2.readBits 4 with
      | none => rfl
      | some q =>
        simp only [Option.map_some]
        by_cases h4 : q.1 = 15
        · rw [if_pos h4, if_pos h4]
          rfl
        · rw [if_neg h4, if_neg h4, readSInt_sim 5 q.2]
          cases q.2.readSInt 5 with
          | none => rfl
          | some r =>
            simp only [Option.map_some]
            by_cases h5 : (0 : Int) ≤ r.1
            · rw [if_pos h5, if_pos h5, readSIntSeq_sim (q.1 + 1) (ty - 31) r.2]
              cases readSIntSeq (q.1 + 1) (ty - 31) r.2 with
              | none => rfl
              | some u =>
                simp only [Option.map_some]
                rw [readResidualA_sim bs (ty - 31) u.2]
                cases readResidualA bs (ty - 31) u.2 with
                | none => rfl
                | some w => simp only [Option.map_some, Lpc.restoreA_toList]
            · rw [if_neg h5, if_neg h5]
              rfl
  · rw [if_neg h3, if_neg h3]
    rfl

theorem readSubframe_sim (bs b : Nat) (br : BitReader) :
    Subframe.read bs b (toStream br)
      = (readSubframe bs b br).map (fun p => (p.1.toList, toStream p.2)) := by
  unfold Subframe.read readSubframe
  rw [readBits_sim 1 br]
  cases br.readBits 1 with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    by_cases h0 : p.1 = 0
    · rw [if_pos h0, if_pos h0, readBits_sim 6 p.2]
      cases p.2.readBits 6 with
      | none => rfl
      | some q =>
        simp only [Option.map_some]
        rw [readBits_sim 1 q.2]
        cases q.2.readBits 1 with
        | none => rfl
        | some w =>
          simp only [Option.map_some]
          by_cases h1 : w.1 = 0
          · rw [if_pos h1, if_pos h1]
            exact readContent_sim bs b q.1 w.2
          · rw [if_neg h1, if_neg h1, readUnary_sim w.2]
            cases w.2.readUnary with
            | none => rfl
            | some k =>
              simp only [Option.map_some]
              rw [readContent_sim bs (b - (k.1 + 1)) q.1 k.2]
              cases readContent bs (b - (k.1 + 1)) q.1 k.2 with
              | none => rfl
              | some u => simp only [Option.map_some, Array.toList_map]
    · rw [if_neg h0, if_neg h0]
      rfl

/-! ## Position monotonicity (bounds for the CRC slices and padding) -/

/-- The uniform position fact: data preserved, cursor monotone and
    in-bounds (given it started in-bounds). -/
def PosOK {α : Type} (P : BitReader → Option (α × BitReader)) : Prop :=
  ∀ br a br', br.pos ≤ br.size → P br = some (a, br') →
    br'.data = br.data ∧ br.pos ≤ br'.pos ∧ br'.pos ≤ br.size

theorem posOK_readBits (n : Nat) : PosOK (BitReader.readBits n) := by
  intro br a br' hwf h
  obtain ⟨hd, hp, hb⟩ := readBits_spec h
  exact ⟨hd, by omega, hb hwf⟩

theorem posOK_readUnary : PosOK BitReader.readUnary := by
  intro br a br' hwf h
  obtain ⟨hd, hp, hb⟩ := readUnary_spec h
  exact ⟨hd, by omega, hb⟩

theorem posOK_readSInt (n : Nat) : PosOK (BitReader.readSInt n) := by
  intro br a br' hwf h
  obtain ⟨hd, hp, hb⟩ := readSInt_spec h
  exact ⟨hd, by omega, hb hwf⟩

private theorem size_congr {br br' : BitReader} (hd : br'.data = br.data) :
    br'.size = br.size := by
  unfold BitReader.size
  rw [hd]

theorem posOK_readRiceNat (k : Nat) : PosOK (readRiceNat k) := by
  intro br a br' hwf h
  unfold readRiceNat at h
  match h1 : br.readUnary with
  | none => rw [h1] at h; simp at h
  | some (q, br1) =>
    simp only [h1] at h
    match h2 : br1.readBits k with
    | none => rw [h2] at h; simp at h
    | some (r, br2) =>
      simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbr⟩ := h
      subst hbr
      obtain ⟨d1, p1, b1⟩ := posOK_readUnary br q br1 hwf h1
      obtain ⟨d2, p2, b2⟩ := posOK_readBits k br1 r _ (by rw [size_congr d1]; omega) h2
      rw [size_congr d1] at b2
      exact ⟨by rw [d2, d1], by omega, b2⟩

theorem posOK_readRice (k : Nat) : PosOK (readRice k) := by
  intro br a br' hwf h
  unfold readRice at h
  match h1 : readRiceNat k br with
  | none => rw [h1] at h; simp at h
  | some (u, br1) =>
    simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact posOK_readRiceNat k br u _ hwf h1

/-- Sequencing step for `PosOK` proofs: chain two position facts. -/
theorem posOK_step {br br1 br' : BitReader}
    (h1 : br1.data = br.data ∧ br.pos ≤ br1.pos ∧ br1.pos ≤ br.size)
    (h2 : br'.data = br1.data ∧ br1.pos ≤ br'.pos ∧ br'.pos ≤ br1.size) :
    br'.data = br.data ∧ br.pos ≤ br'.pos ∧ br'.pos ≤ br.size := by
  obtain ⟨d1, p1, b1⟩ := h1
  obtain ⟨d2, p2, b2⟩ := h2
  rw [size_congr d1] at b2
  exact ⟨by rw [d2, d1], by omega, b2⟩

theorem posOK_readRiceSeqA (k : Nat) :
    ∀ (count : Nat) (acc : Array Int),
      PosOK (fun br => readRiceSeqA k count br acc) := by
  intro count
  induction count with
  | zero =>
    intro acc br a br' hwf h
    simp only [readRiceSeqA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | succ count ih =>
    intro acc br a br' hwf h
    simp only [readRiceSeqA] at h
    match h1 : readRice k br with
    | none => rw [h1] at h; simp at h
    | some (x, br1) =>
      simp only [h1] at h
      have s1 := posOK_readRice k br x br1 hwf h1
      exact posOK_step s1
        (ih (acc.push x) br1 a br' (by rw [size_congr s1.1]; omega) h)

theorem posOK_readSIntSeqA (bits : Nat) :
    ∀ (count : Nat) (acc : Array Int),
      PosOK (fun br => readSIntSeqA bits count br acc) := by
  intro count
  induction count with
  | zero =>
    intro acc br a br' hwf h
    simp only [readSIntSeqA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | succ count ih =>
    intro acc br a br' hwf h
    simp only [readSIntSeqA] at h
    match h1 : br.readSInt bits with
    | none => rw [h1] at h; simp at h
    | some (x, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSInt bits br x br1 hwf h1
      exact posOK_step s1
        (ih (acc.push x) br1 a br' (by rw [size_congr s1.1]; omega) h)

theorem posOK_readSIntSeq (bits : Nat) : ∀ (count : Nat), PosOK (readSIntSeq bits count) := by
  intro count br a br' hwf h
  unfold readSIntSeq at h
  simp only [readSIntSeqFast_eq] at h
  match h1 : readSIntSeqA bits count br #[] with
  | none => rw [h1] at h; simp at h
  | some (xs, br1) =>
    rw [h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact posOK_readSIntSeqA bits count #[] br xs _ hwf h1

theorem posOK_readPartA (m : Rice.Method) (count : Nat) (acc : Array Int) :
    PosOK (fun br => readPartA m count br acc) := by
  intro br a br' hwf h
  simp only [readPartA, readRiceSeqFast_eq, readSIntSeqFast_eq] at h
  match h1 : br.readBits m.paramBits with
  | none => rw [h1] at h; simp at h
  | some (k, br1) =>
    simp only [h1] at h
    have s1 := posOK_readBits m.paramBits br k br1 hwf h1
    split at h
    · match h2 : br1.readBits 5 with
      | none => rw [h2] at h; simp at h
      | some (bits, br2) =>
        simp only [h2] at h
        have s2 := posOK_readBits 5 br1 bits br2 (by rw [size_congr s1.1]; omega) h2
        have s3 := posOK_readSIntSeqA bits count acc br2 a br'
          (by rw [size_congr s2.1, size_congr s1.1]
              rw [size_congr s1.1] at s2
              omega) h
        exact posOK_step s1 (posOK_step s2 s3)
    · exact posOK_step s1 (posOK_readRiceSeqA k count acc br1 a br'
        (by rw [size_congr s1.1]; omega) h)

theorem posOK_readPartsA (m : Rice.Method) :
    ∀ sizes (acc : Array Int), PosOK (fun br => readPartsA m sizes br acc) := by
  intro sizes
  induction sizes with
  | nil =>
    intro acc br a br' hwf h
    simp only [readPartsA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | cons sz sizes ih =>
    intro acc br a br' hwf h
    simp only [readPartsA] at h
    match h1 : readPartA m sz br acc with
    | none => rw [h1] at h; simp at h
    | some (acc1, br1) =>
      simp only [h1] at h
      have s1 := posOK_readPartA m sz acc br acc1 br1 hwf h1
      exact posOK_step s1 (ih acc1 br1 a br' (by rw [size_congr s1.1]; omega) h)

theorem posOK_readResidualA (bs ord : Nat) : PosOK (readResidualA bs ord) := by
  intro br a br' hwf h
  unfold readResidualA at h
  match h1 : br.readBits 2 with
  | none => rw [h1] at h; simp at h
  | some (mc, br1) =>
    simp only [h1] at h
    have s1 := posOK_readBits 2 br mc br1 hwf h1
    match hm : Rice.Method.ofCode mc with
    | none => rw [hm] at h; simp at h
    | some m =>
      simp only [hm] at h
      match h2 : br1.readBits 4 with
      | none => rw [h2] at h; simp at h
      | some (po, br2) =>
        simp only [h2] at h
        have s2 := posOK_readBits 4 br1 po br2 (by rw [size_congr s1.1]; omega) h2
        split at h
        · refine posOK_step s1 (posOK_step s2 (posOK_readPartsA m _ _ br2 a br' ?_ h))
          rw [size_congr s2.1, size_congr s1.1]
          rw [size_congr s1.1] at s2
          omega
        · simp at h

theorem posOK_readContent (bs b ty : Nat) : PosOK (readContent bs b ty) := by
  intro br a br' hwf h
  unfold readContent at h
  split at h
  · match h1 : br.readSInt b with
    | none => rw [h1] at h; simp at h
    | some (v, br1) =>
      simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbr⟩ := h
      subst hbr
      exact posOK_readSInt b br v _ hwf h1
  split at h
  · rw [readSIntSeqFast_eq] at h
    exact posOK_readSIntSeqA b bs #[] br a br' hwf h
  split at h
  · match h1 : readSIntSeq b (ty - 8) br with
    | none => rw [h1] at h; simp at h
    | some (warm, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSIntSeq b (ty - 8) br warm br1 hwf h1
      match h2 : readResidualA bs (ty - 8) br1 with
      | none => rw [h2] at h; simp at h
      | some (res, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (posOK_readResidualA bs (ty - 8) br1 res _
          (by rw [size_congr s1.1]; omega) h2)
  split at h
  · match h1 : readSIntSeq b (ty - 31) br with
    | none => rw [h1] at h; simp at h
    | some (warm, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSIntSeq b (ty - 31) br warm br1 hwf h1
      match h2 : br1.readBits 4 with
      | none => rw [h2] at h; simp at h
      | some (pm1, br2) =>
        simp only [h2] at h
        have s2 := posOK_readBits 4 br1 pm1 br2 (by rw [size_congr s1.1]; omega) h2
        have hw2 : br2.pos ≤ br2.size := by
          rw [size_congr s2.1, size_congr s1.1]
          rw [size_congr s1.1] at s2
          omega
        split at h
        · simp at h
        · match h3 : br2.readSInt 5 with
          | none => rw [h3] at h; simp at h
          | some (sh, br3) =>
            simp only [h3] at h
            have s3 := posOK_readSInt 5 br2 sh br3 hw2 h3
            have hw3 : br3.pos ≤ br3.size := by
              rw [size_congr s3.1]
              exact s3.2.2
            split at h
            · match h4 : readSIntSeq (pm1 + 1) (ty - 31) br3 with
              | none => rw [h4] at h; simp at h
              | some (cs, br4) =>
                simp only [h4] at h
                have s4 := posOK_readSIntSeq (pm1 + 1) (ty - 31) br3 cs br4 hw3 h4
                match h5 : readResidualA bs (ty - 31) br4 with
                | none => rw [h5] at h; simp at h
                | some (res, br5) =>
                  simp only [h5, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, hbr⟩ := h
                  subst hbr
                  have s5 := posOK_readResidualA bs (ty - 31) br4 res _
                    (by rw [size_congr s4.1]; omega) h5
                  exact posOK_step s1 (posOK_step s2 (posOK_step s3 (posOK_step s4 s5)))
            · simp at h
  · simp at h

theorem posOK_readSubframe (bs b : Nat) : PosOK (readSubframe bs b) := by
  intro br a br' hwf h
  unfold readSubframe at h
  match h1 : br.readBits 1 with
  | none => rw [h1] at h; simp at h
  | some (r, br1) =>
    simp only [h1] at h
    have s1 := posOK_readBits 1 br r br1 hwf h1
    split at h
    · match h2 : br1.readBits 6 with
      | none => rw [h2] at h; simp at h
      | some (ty, br2) =>
        simp only [h2] at h
        have s2 := posOK_readBits 6 br1 ty br2 (by rw [size_congr s1.1]; omega) h2
        have hw2 : br2.pos ≤ br2.size := by
          rw [size_congr s2.1, size_congr s1.1]
          rw [size_congr s1.1] at s2
          omega
        match h3 : br2.readBits 1 with
        | none => rw [h3] at h; simp at h
        | some (wf, br3) =>
          simp only [h3] at h
          have s3 := posOK_readBits 1 br2 wf br3 hw2 h3
          have hw3 : br3.pos ≤ br3.size := by
            rw [size_congr s3.1]
            exact s3.2.2
          split at h
          · exact posOK_step s1 (posOK_step s2 (posOK_step s3
              (posOK_readContent bs b ty br3 a br' hw3 h)))
          · match h4 : br3.readUnary with
            | none => rw [h4] at h; simp at h
            | some (k, br4) =>
              simp only [h4] at h
              have s4' := readUnary_spec h4
              have s4 : br4.data = br3.data ∧ br3.pos ≤ br4.pos ∧ br4.pos ≤ br3.size :=
                ⟨s4'.1, by omega, s4'.2.2⟩
              match h5 : readContent bs (b - (k + 1)) ty br4 with
              | none => rw [h5] at h; simp at h
              | some (ys, br5) =>
                simp only [h5, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, hbr⟩ := h
                subst hbr
                have s5 := posOK_readContent bs (b - (k + 1)) ty br4 ys _
                  (by rw [size_congr s4.1]; omega) h5
                exact posOK_step s1 (posOK_step s2 (posOK_step s3 (posOK_step s4 s5)))
    · simp at h

theorem posOK_readSubframes (bs b : Nat) : ∀ n, PosOK (readSubframes bs b n) := by
  intro n
  induction n with
  | zero =>
    intro br a br' hwf h
    simp only [readSubframes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | succ n ih =>
    intro br a br' hwf h
    unfold readSubframes at h
    match h1 : readSubframe bs b br with
    | none => rw [h1] at h; simp at h
    | some (c, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSubframe bs b br c br1 hwf h1
      match h2 : readSubframes bs b n br1 with
      | none => rw [h2] at h; simp at h
      | some (cs, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (ih br1 cs _ (by rw [size_congr s1.1]; omega) h2)

theorem posOK_readChannels (bs b chCode : Nat) : PosOK (readChannels bs b chCode) := by
  intro br a br' hwf h
  unfold readChannels at h
  split at h
  · exact posOK_readSubframes bs b (chCode + 1) br a br' hwf h
  split at h
  · match h1 : readSubframe bs b br with
    | none => rw [h1] at h; simp at h
    | some (l, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSubframe bs b br l br1 hwf h1
      match h2 : readSubframe bs (b + 1) br1 with
      | none => rw [h2] at h; simp at h
      | some (sd, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (posOK_readSubframe bs (b + 1) br1 sd _
          (by rw [size_congr s1.1]; omega) h2)
  split at h
  · match h1 : readSubframe bs (b + 1) br with
    | none => rw [h1] at h; simp at h
    | some (sd, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSubframe bs (b + 1) br sd br1 hwf h1
      match h2 : readSubframe bs b br1 with
      | none => rw [h2] at h; simp at h
      | some (r, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (posOK_readSubframe bs b br1 r _
          (by rw [size_congr s1.1]; omega) h2)
  split at h
  · match h1 : readSubframe bs b br with
    | none => rw [h1] at h; simp at h
    | some (m, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSubframe bs b br m br1 hwf h1
      match h2 : readSubframe bs (b + 1) br1 with
      | none => rw [h2] at h; simp at h
      | some (sd, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (posOK_readSubframe bs (b + 1) br1 sd _
          (by rw [size_congr s1.1]; omega) h2)
  · simp at h

/-! ## Byte-aligned consumption (for the CRC slices) -/

theorem readConts_pos8 (k : Nat) :
    ∀ (acc : Nat) {br br' : BitReader} {n : Nat},
      readConts k acc br = some (n, br') →
      br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
        ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  induction k with
  | zero =>
    intro acc br br' n h
    simp only [readConts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, ⟨0, by omega⟩, fun hw => hw⟩
  | succ k ih =>
    intro acc br br' n h
    unfold readConts at h
    match h1 : br.readBits 8 with
    | none => rw [h1] at h; simp at h
    | some (c, br1) =>
      simp only [h1] at h
      split at h
      · obtain ⟨d1, p1, b1⟩ := readBits_spec h1
        obtain ⟨d2, ⟨j, p2⟩, b2⟩ := ih _ h
        rw [size_congr d1] at b2
        exact ⟨by rw [d2, d1], ⟨j + 1, by omega⟩,
          fun hw => b2 (by have := b1 hw; omega)⟩
      · simp at h

theorem readUtf8_pos8 {br br' : BitReader} {n : Nat}
    (h : readUtf8 br = some (n, br')) :
    br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold readUtf8 at h
  match h1 : br.readBits 8 with
  | none => rw [h1] at h; simp at h
  | some (c, br1) =>
    simp only [h1] at h
    obtain ⟨d1, p1, b1⟩ := readBits_spec h1
    have step : ∀ {k acc}, readConts k acc br1 = some (n, br') →
        br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
          ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
      intro k acc hc
      obtain ⟨d2, ⟨j, p2⟩, b2⟩ := readConts_pos8 k acc hc
      rw [size_congr d1] at b2
      exact ⟨by rw [d2, d1], ⟨j + 1, by omega⟩,
        fun hw => b2 (by have := b1 hw; omega)⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbr⟩ := h
      subst hbr
      exact ⟨d1, ⟨1, by omega⟩, b1⟩
    split at h
    · simp at h
    split at h
    · exact step h
    split at h
    · exact step h
    split at h
    · exact step h
    split at h
    · exact step h
    split at h
    · exact step h
    split at h
    · exact step h
    · simp at h

theorem resolveBlockSize_pos {code : Nat} {br br' : BitReader} {bs : Nat}
    (h : resolveBlockSize code br = some (bs, br')) :
    br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold resolveBlockSize at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h; subst hbr
    exact ⟨rfl, ⟨0, by omega⟩, fun hw => hw⟩
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h; subst hbr
    exact ⟨rfl, ⟨0, by omega⟩, fun hw => hw⟩
  split at h
  · match h1 : br.readBits 8 with
    | none => rw [h1] at h; simp at h
    | some (v, br1) =>
      simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbr⟩ := h; subst hbr
      obtain ⟨d1, p1, b1⟩ := readBits_spec h1
      exact ⟨d1, ⟨1, by omega⟩, b1⟩
  split at h
  · match h1 : br.readBits 16 with
    | none => rw [h1] at h; simp at h
    | some (v, br1) =>
      simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbr⟩ := h; subst hbr
      obtain ⟨d1, p1, b1⟩ := readBits_spec h1
      exact ⟨d1, ⟨2, by omega⟩, b1⟩
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h; subst hbr
    exact ⟨rfl, ⟨0, by omega⟩, fun hw => hw⟩
  · simp at h

theorem skipSampleRate_pos {code : Nat} {br br' : BitReader}
    (h : skipSampleRate code br = some br') :
    br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold skipSampleRate at h
  split at h
  · match h1 : br.readBits 8 with
    | none => rw [h1] at h; simp at h
    | some (v, br1) =>
      simp only [h1, Option.some.injEq] at h
      subst h
      obtain ⟨d1, p1, b1⟩ := readBits_spec h1
      exact ⟨d1, ⟨1, by omega⟩, b1⟩
  split at h
  · match h1 : br.readBits 16 with
    | none => rw [h1] at h; simp at h
    | some (v, br1) =>
      simp only [h1, Option.some.injEq] at h
      subst h
      obtain ⟨d1, p1, b1⟩ := readBits_spec h1
      exact ⟨d1, ⟨2, by omega⟩, b1⟩
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, ⟨0, by omega⟩, fun hw => hw⟩

theorem readFields_pos8 {b0 : Nat} {br br' : BitReader} {f : Frame.Fields}
    (h : readFields b0 br = some (f, br')) :
    br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold readFields at h
  match h1 : br.readBits 14 with
  | none => rw [h1] at h; simp at h
  | some (sync, br1) =>
    simp only [h1] at h
    obtain ⟨d1, p1, b1⟩ := readBits_spec h1
    split at h
    case isFalse => simp at h
    match h2 : br1.readBits 1 with
    | none => rw [h2] at h; simp at h
    | some (r0, br2) =>
      simp only [h2] at h
      obtain ⟨d2, p2, b2⟩ := readBits_spec h2
      split at h
      case isFalse => simp at h
      match h3 : br2.readBits 1 with
      | none => rw [h3] at h; simp at h
      | some (strat, br3) =>
        simp only [h3] at h
        obtain ⟨d3, p3, b3⟩ := readBits_spec h3
        match h4 : br3.readBits 4 with
        | none => rw [h4] at h; simp at h
        | some (bsC, br4) =>
          simp only [h4] at h
          obtain ⟨d4, p4, b4⟩ := readBits_spec h4
          match h5 : br4.readBits 4 with
          | none => rw [h5] at h; simp at h
          | some (srC, br5) =>
            simp only [h5] at h
            obtain ⟨d5, p5, b5⟩ := readBits_spec h5
            match h6 : br5.readBits 4 with
            | none => rw [h6] at h; simp at h
            | some (chC, br6) =>
              simp only [h6] at h
              obtain ⟨d6, p6, b6⟩ := readBits_spec h6
              match h7 : br6.readBits 3 with
              | none => rw [h7] at h; simp at h
              | some (bpsC, br7) =>
                simp only [h7] at h
                obtain ⟨d7, p7, b7⟩ := readBits_spec h7
                match hb : Frame.bpsOfCode bpsC b0 with
                | none => rw [hb] at h; simp at h
                | some b =>
                  simp only [hb] at h
                  match h8 : br7.readBits 1 with
                  | none => rw [h8] at h; simp at h
                  | some (r1, br8) =>
                    simp only [h8] at h
                    obtain ⟨d8, p8, b8⟩ := readBits_spec h8
                    split at h
                    case isFalse => simp at h
                    match h9 : readUtf8 br8 with
                    | none => rw [h9] at h; simp at h
                    | some (num, br9) =>
                      simp only [h9] at h
                      obtain ⟨d9, ⟨j9, p9⟩, b9⟩ := readUtf8_pos8 h9
                      match h10 : resolveBlockSize bsC br9 with
                      | none => rw [h10] at h; simp at h
                      | some (bs, br10) =>
                        simp only [h10] at h
                        obtain ⟨d10, ⟨j10, p10⟩, b10⟩ := resolveBlockSize_pos h10
                        match h11 : skipSampleRate srC br10 with
                        | none => rw [h11] at h; simp at h
                        | some br11 =>
                          simp only [h11, Option.some.injEq, Prod.mk.injEq] at h
                          obtain ⟨-, hbr⟩ := h
                          subst hbr
                          obtain ⟨d11, ⟨j11, p11⟩, b11⟩ := skipSampleRate_pos h11
                          have e1 : br1.size = br.size := size_congr d1
                          have e2 : br2.size = br.size := by
                            rw [size_congr d2, e1]
                          have e3 : br3.size = br.size := by
                            rw [size_congr d3, e2]
                          have e4 : br4.size = br.size := by
                            rw [size_congr d4, e3]
                          have e5 : br5.size = br.size := by
                            rw [size_congr d5, e4]
                          have e6 : br6.size = br.size := by
                            rw [size_congr d6, e5]
                          have e7 : br7.size = br.size := by
                            rw [size_congr d7, e6]
                          have e8 : br8.size = br.size := by
                            rw [size_congr d8, e7]
                          have e9 : br9.size = br.size := by
                            rw [size_congr d9, e8]
                          have e10 : br10.size = br.size := by
                            rw [size_congr d10, e9]
                          rw [e1] at b2
                          rw [e2] at b3
                          rw [e3] at b4
                          rw [e4] at b5
                          rw [e5] at b6
                          rw [e6] at b7
                          rw [e7] at b8
                          rw [e8] at b9
                          rw [e9] at b10
                          rw [e10] at b11
                          refine ⟨by rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1],
                            ⟨4 + j9 + j10 + j11, by omega⟩, fun hw =>
                            b11 (b10 (b9 (b8 (b7 (b6 (b5 (b4 (b3 (b2 (b1 hw))))))))))⟩

/-! ## Frame-header simulations -/

theorem resolveBlockSize_sim (code : Nat) (br : BitReader) :
    Frame.resolveBlockSize code (toStream br)
      = (resolveBlockSize code br).map (fun p => (p.1, toStream p.2)) := by
  unfold Frame.resolveBlockSize resolveBlockSize
  by_cases h1 : code = 1
  · rw [if_pos h1, if_pos h1]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : 2 ≤ code ∧ code ≤ 5
  · rw [if_pos h2, if_pos h2]; rfl
  rw [if_neg h2, if_neg h2]
  by_cases h3 : code = 6
  · rw [if_pos h3, if_pos h3, readBits_sim 8 br]
    cases br.readBits 8 with
    | none => rfl
    | some p => rfl
  rw [if_neg h3, if_neg h3]
  by_cases h4 : code = 7
  · rw [if_pos h4, if_pos h4, readBits_sim 16 br]
    cases br.readBits 16 with
    | none => rfl
    | some p => rfl
  rw [if_neg h4, if_neg h4]
  by_cases h5 : 8 ≤ code ∧ code ≤ 15
  · rw [if_pos h5, if_pos h5]; rfl
  · rw [if_neg h5, if_neg h5]; rfl

theorem skipSampleRate_sim (code : Nat) (br : BitReader) :
    Frame.skipSampleRate code (toStream br)
      = (skipSampleRate code br).map toStream := by
  unfold Frame.skipSampleRate skipSampleRate
  by_cases h1 : code = 12
  · rw [if_pos h1, if_pos h1, readBits_sim 8 br]
    cases br.readBits 8 with
    | none => rfl
    | some p => rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : code = 13 ∨ code = 14
  · rw [if_pos h2, if_pos h2, readBits_sim 16 br]
    cases br.readBits 16 with
    | none => rfl
    | some p => rfl
  rw [if_neg h2, if_neg h2]
  by_cases h3 : code = 15
  · rw [if_pos h3, if_pos h3]; rfl
  · rw [if_neg h3, if_neg h3]; rfl

theorem readFields_sim (b0 : Nat) (br : BitReader) :
    Frame.readFields b0 (toStream br)
      = (readFields b0 br).map (fun p => (p.1, toStream p.2)) := by
  unfold Frame.readFields readFields
  rw [readBits_sim 14 br]
  cases br.readBits 14 with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    by_cases hs : p.1 = 0x3FFE
    case neg => rw [if_neg hs, if_neg hs]; rfl
    rw [if_pos hs, if_pos hs, readBits_sim 1 p.2]
    cases p.2.readBits 1 with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      by_cases hr : q.1 = 0
      case neg => rw [if_neg hr, if_neg hr]; rfl
      rw [if_pos hr, if_pos hr, readBits_sim 1 q.2]
      cases q.2.readBits 1 with
      | none => rfl
      | some w =>
        simp only [Option.map_some]
        rw [readBits_sim 4 w.2]
        cases w.2.readBits 4 with
        | none => rfl
        | some x =>
          simp only [Option.map_some]
          rw [readBits_sim 4 x.2]
          cases x.2.readBits 4 with
          | none => rfl
          | some y =>
            simp only [Option.map_some]
            rw [readBits_sim 4 y.2]
            cases y.2.readBits 4 with
            | none => rfl
            | some z =>
              simp only [Option.map_some]
              rw [readBits_sim 3 z.2]
              cases z.2.readBits 3 with
              | none => rfl
              | some u =>
                simp only [Option.map_some]
                cases Frame.bpsOfCode u.1 b0 with
                | none => rfl
                | some b =>
                  rw [readBits_sim 1 u.2]
                  cases u.2.readBits 1 with
                  | none => rfl
                  | some v =>
                    simp only [Option.map_some]
                    by_cases hv : v.1 = 0
                    case neg => rw [if_neg hv, if_neg hv]; rfl
                    rw [if_pos hv, if_pos hv, readUtf8_sim v.2]
                    cases readUtf8 v.2 with
                    | none => rfl
                    | some n =>
                      simp only [Option.map_some]
                      rw [resolveBlockSize_sim x.1 n.2]
                      cases resolveBlockSize x.1 n.2 with
                      | none => rfl
                      | some bs =>
                        simp only [Option.map_some]
                        rw [skipSampleRate_sim y.1 bs.2]
                        cases skipSampleRate y.1 bs.2 with
                        | none => rfl
                        | some fin => rfl

/-! ## The CRC byte-slice equality -/

theorem padLen_add (n : Nat) : (n + padLen n) % 8 = 0 := by
  unfold padLen
  omega

/-- The allocation-free CRC-8 over a cursor slice equals CRC-8 of the
    extracted slice. -/
theorem crc8Slice_eq (br0 br1 : BitReader) :
    crc8Slice br0 br1 = Crc.crc8 (sliceBytes br0 br1) := by
  rw [crc8Slice, sliceBytes]
  exact Crc.crc8Range_eq_extract _ _ _

/-- The allocation-free CRC-16 over a cursor slice equals CRC-16 of the
    extracted slice. -/
theorem crc16Slice_eq (br0 br1 : BitReader) :
    crc16Slice br0 br1 = Crc.crc16 (sliceBytes br0 br1) := by
  rw [crc16Slice, sliceBytes]
  exact Crc.crc16Range_eq_extract _ _ _

/-- At byte-aligned cursor positions, the production byte slice equals the
    packed model take. -/
theorem sliceBytes_eq (br0 br1 : BitReader) (_hd : br1.data = br0.data)
    (hle : br0.pos ≤ br1.pos) (h0 : br0.pos % 8 = 0)
    (hdiff : (br1.pos - br0.pos) % 8 = 0) :
    bitsToBytes ((toStream br0).take (br1.pos - br0.pos)) = sliceBytes br0 br1 := by
  obtain ⟨a, ha⟩ : ∃ a, br0.pos = 8 * a := ⟨br0.pos / 8, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, br1.pos - br0.pos = 8 * m := ⟨(br1.pos - br0.pos) / 8, by omega⟩
  have hbits : (toStream br0).take (br1.pos - br0.pos)
      = byteListToBits ((br0.data.data.toList.drop a).take m) := by
    show ((byteListToBits br0.data.data.toList).drop br0.pos).take _ = _
    rw [ha] at hm
    rw [ha, hm, drop_byteListToBits, take_byteListToBits]
  rw [hbits]
  unfold bitsToBytes sliceBytes
  rw [bitsToByteList_byteListToBits]
  have hpos1 : br1.pos / 8 = a + m := by omega
  rw [ha, hpos1, show (8 * a) / 8 = a from by omega]
  apply ByteArray.ext
  show ((br0.data.data.toList.drop a).take m).toByteArray.data
    = (br0.data.extract a (a + m)).data
  rw [ByteArray.data_extract]
  have h1 : ((br0.data.data.toList.drop a).take m).toByteArray.data.toList
      = (br0.data.data.extract a (a + m)).toList := by
    rw [List.toList_data_toByteArray, Array.toList_extract,
      List.extract_eq_take_drop]
    congr 1
    omega
  exact Array.toList_inj.mp h1

/-! ## Frame simulations (byte-aligned readers) -/

theorem length_sub_toStream {br br' : BitReader} (hd : br'.data = br.data)
    (hle : br.pos ≤ br'.pos) (hb : br'.pos ≤ br.size) :
    (toStream br).length - (toStream br').length = br'.pos - br.pos := by
  simp only [length_toStream, size_congr hd]
  omega

theorem readHeader_sim (b0 : Nat) (br : BitReader)
    (h8 : br.pos % 8 = 0) (hwf : br.pos ≤ br.size) :
    Frame.readHeader b0 (toStream br)
      = (readHeader b0 br).map (fun p => (p.1, toStream p.2)) := by
  unfold Frame.readHeader readHeader Flac.Bits.withConsumed
  rw [readFields_sim b0 br]
  cases hf : readFields b0 br with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    obtain ⟨d1, ⟨j, hj⟩, b1⟩ := readFields_pos8 hf
    have hlen : (toStream br).length - (toStream p.2).length = p.2.pos - br.pos :=
      length_sub_toStream d1 (by omega) (b1 hwf)
    rw [hlen, sliceBytes_eq br p.2 d1 (by omega) h8 (by omega),
      readBits_sim 8 p.2, crc8Slice_eq]
    cases p.2.readBits 8 with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      by_cases hc : q.1 = (Crc.crc8 (sliceBytes br p.2)).toNat
      · rw [if_pos hc, if_pos hc]
        rfl
      · rw [if_neg hc, if_neg hc]
        rfl

theorem readHeader_pos8 {b0 : Nat} {br br' : BitReader} {f : Frame.Fields}
    (h : readHeader b0 br = some (f, br')) :
    br'.data = br.data ∧ (∃ k, br'.pos = br.pos + 8 * k)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold readHeader at h
  match h1 : readFields b0 br with
  | none => rw [h1] at h; simp at h
  | some (fl, br1) =>
    simp only [h1] at h
    obtain ⟨d1, ⟨j, hj⟩, b1⟩ := readFields_pos8 h1
    match h2 : br1.readBits 8 with
    | none => rw [h2] at h; simp at h
    | some (c8, br2) =>
      simp only [h2] at h
      obtain ⟨d2, p2, b2⟩ := readBits_spec h2
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        rw [size_congr d1] at b2
        exact ⟨by rw [d2, d1], ⟨j + 1, by omega⟩,
          fun hw => b2 (b1 hw)⟩
      · simp at h

theorem readSubframes_sim (bs b : Nat) :
    ∀ (n : Nat) (br : BitReader),
      Frame.readSubframes bs b n (toStream br)
        = (readSubframes bs b n br).map
            (fun p => (p.1.map (·.toList), toStream p.2)) := by
  intro n
  induction n with
  | zero => intro br; rfl
  | succ n ih =>
    intro br
    unfold Frame.readSubframes readSubframes
    rw [readSubframe_sim bs b br]
    cases readSubframe bs b br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2]
      cases readSubframes bs b n p.2 with
      | none => rfl
      | some q => rfl

theorem readChannels_sim (bs b chCode : Nat) (br : BitReader) :
    Frame.readChannels bs b chCode (toStream br)
      = (readChannels bs b chCode br).map
          (fun p => (p.1.map (·.toList), toStream p.2)) := by
  unfold Frame.readChannels readChannels
  by_cases h1 : chCode ≤ 7
  · rw [if_pos h1, if_pos h1]
    exact readSubframes_sim bs b (chCode + 1) br
  rw [if_neg h1, if_neg h1]
  by_cases h2 : chCode = 8
  · rw [if_pos h2, if_pos h2, readSubframe_sim bs b br]
    cases readSubframe bs b br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [readSubframe_sim bs (b + 1) p.2]
      cases readSubframe bs (b + 1) p.2 with
      | none => rfl
      | some q => simp [Stereo.decodeLSA_toList]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : chCode = 9
  · rw [if_pos h3, if_pos h3, readSubframe_sim bs (b + 1) br]
    cases readSubframe bs (b + 1) br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [readSubframe_sim bs b p.2]
      cases readSubframe bs b p.2 with
      | none => rfl
      | some q => simp [Stereo.decodeRSA_toList]
  rw [if_neg h3, if_neg h3]
  by_cases h4 : chCode = 10
  · rw [if_pos h4, if_pos h4, readSubframe_sim bs b br]
    cases readSubframe bs b br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [readSubframe_sim bs (b + 1) p.2]
      cases readSubframe bs (b + 1) p.2 with
      | none => rfl
      | some q => simp [Stereo.decodeMSLA_toList, Stereo.decodeMSRA_toList]
  · rw [if_neg h4, if_neg h4]
    rfl

theorem readHeaderChannels_sim (b0 : Nat) (br : BitReader)
    (h8 : br.pos % 8 = 0) (hwf : br.pos ≤ br.size) :
    Frame.readHeaderChannels b0 (toStream br)
      = (readHeaderChannels b0 br).map
          (fun p => (p.1.map (·.toList), toStream p.2)) := by
  unfold Frame.readHeaderChannels readHeaderChannels
  rw [readHeader_sim b0 br h8 hwf]
  cases readHeader b0 br with
  | none => rfl
  | some p => exact readChannels_sim p.1.blockSize p.1.bps p.1.chCode p.2

theorem posOK_readHeaderChannels (b0 : Nat) : PosOK (readHeaderChannels b0) := by
  intro br a br' hwf h
  unfold readHeaderChannels at h
  match h1 : readHeader b0 br with
  | none => rw [h1] at h; simp at h
  | some (f, br1) =>
    simp only [h1] at h
    obtain ⟨d1, ⟨j, hj⟩, b1⟩ := readHeader_pos8 h1
    exact posOK_step ⟨d1, by omega, b1 hwf⟩
      (posOK_readChannels f.blockSize f.bps f.chCode br1 a br'
        (by rw [size_congr d1]; exact b1 hwf) h)

theorem readBody_sim (b0 : Nat) (br : BitReader)
    (h8 : br.pos % 8 = 0) (hwf : br.pos ≤ br.size) :
    Frame.readBody b0 (toStream br)
      = (readBody b0 br).map (fun p => (p.1.map (·.toList), toStream p.2)) := by
  unfold Frame.readBody readBody Flac.Bits.withConsumed
  rw [readHeaderChannels_sim b0 br h8 hwf]
  cases hc : readHeaderChannels b0 br with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    obtain ⟨d1, p1, b1⟩ := posOK_readHeaderChannels b0 br p.1 p.2 hwf hc
    rw [List.length_take, length_sub_toStream d1 p1 b1]
    rw [show min (p.2.pos - br.pos) (toStream br).length = p.2.pos - br.pos from by
      simp only [length_toStream]
      omega]
    rw [readBits_sim (padLen (p.2.pos - br.pos)) p.2]
    cases p.2.readBits (padLen (p.2.pos - br.pos)) with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      by_cases hz : q.1 = 0
      · rw [if_pos hz, if_pos hz]
        rfl
      · rw [if_neg hz, if_neg hz]
        rfl

theorem readBody_pos8 {b0 : Nat} {br br' : BitReader} {chs : List (Array Int)}
    (hwf : br.pos ≤ br.size) (h : readBody b0 br = some (chs, br')) :
    br'.data = br.data ∧ (∃ k, br'.pos = br.pos + 8 * k)
      ∧ br'.pos ≤ br.size := by
  unfold readBody at h
  match h1 : readHeaderChannels b0 br with
  | none => rw [h1] at h; simp at h
  | some (cs, br1) =>
    simp only [h1] at h
    obtain ⟨d1, p1, b1⟩ := posOK_readHeaderChannels b0 br cs br1 hwf h1
    match h2 : br1.readBits (padLen (br1.pos - br.pos)) with
    | none => rw [h2] at h; simp at h
    | some (z, br2) =>
      simp only [h2] at h
      obtain ⟨d2, p2, b2⟩ := readBits_spec h2
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        have hpad := padLen_add (br1.pos - br.pos)
        rw [size_congr d1] at b2
        refine ⟨by rw [d2, d1], ⟨(br1.pos + padLen (br1.pos - br.pos) - br.pos) / 8, by omega⟩,
          b2 b1⟩
      · simp at h

theorem readFrame_sim (b0 : Nat) (br : BitReader)
    (h8 : br.pos % 8 = 0) (hwf : br.pos ≤ br.size) :
    Frame.read b0 (toStream br)
      = (readFrame b0 br).map (fun p => (p.1.map (·.toList), toStream p.2)) := by
  unfold Frame.read readFrame Flac.Bits.withConsumed
  rw [readBody_sim b0 br h8 hwf]
  cases hb : readBody b0 br with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    obtain ⟨d1, ⟨k, hk⟩, b1⟩ := readBody_pos8 hwf hb
    have hlen : (toStream br).length - (toStream p.2).length = p.2.pos - br.pos :=
      length_sub_toStream d1 (by omega) b1
    rw [hlen, sliceBytes_eq br p.2 d1 (by omega) h8 (by omega),
      readBits_sim 16 p.2, crc16Slice_eq]
    cases p.2.readBits 16 with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      by_cases hc : q.1 = (Crc.crc16 (sliceBytes br p.2)).toNat
      · rw [if_pos hc, if_pos hc]
        rfl
      · rw [if_neg hc, if_neg hc]
        rfl

theorem readFrame_pos8 {b0 : Nat} {br br' : BitReader} {chs : List (Array Int)}
    (hwf : br.pos ≤ br.size) (h : readFrame b0 br = some (chs, br')) :
    br'.data = br.data ∧ (∃ k, br'.pos = br.pos + 8 * k)
      ∧ br'.pos ≤ br.size ∧ br.pos < br'.pos := by
  unfold readFrame at h
  match h1 : readBody b0 br with
  | none => rw [h1] at h; simp at h
  | some (cs, br1) =>
    simp only [h1] at h
    obtain ⟨d1, ⟨k, hk⟩, b1⟩ := readBody_pos8 hwf h1
    match h2 : br1.readBits 16 with
    | none => rw [h2] at h; simp at h
    | some (c16, br2) =>
      simp only [h2] at h
      obtain ⟨d2, p2, b2⟩ := readBits_spec h2
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        rw [size_congr d1] at b2
        exact ⟨by rw [d2, d1], ⟨k + 2, by omega⟩, b2 b1, by omega⟩
      · simp at h

/-! ## Stream simulations -/

theorem readStreamInfo_sim (br : BitReader) :
    Stream.readStreamInfo (toStream br)
      = (readStreamInfo br).map (fun p => (p.1, toStream p.2)) := by
  unfold Stream.readStreamInfo readStreamInfo
  rw [readBits_sim 16 br]
  cases br.readBits 16 with
  | none => rfl
  | some p1 =>
    simp only [Option.map_some]
    rw [readBits_sim 16 p1.2]
    cases p1.2.readBits 16 with
    | none => rfl
    | some p2 =>
      simp only [Option.map_some]
      rw [readBits_sim 24 p2.2]
      cases p2.2.readBits 24 with
      | none => rfl
      | some p3 =>
        simp only [Option.map_some]
        rw [readBits_sim 24 p3.2]
        cases p3.2.readBits 24 with
        | none => rfl
        | some p4 =>
          simp only [Option.map_some]
          rw [readBits_sim 20 p4.2]
          cases p4.2.readBits 20 with
          | none => rfl
          | some p5 =>
            simp only [Option.map_some]
            rw [readBits_sim 3 p5.2]
            cases p5.2.readBits 3 with
            | none => rfl
            | some p6 =>
              simp only [Option.map_some]
              rw [readBits_sim 5 p6.2]
              cases p6.2.readBits 5 with
              | none => rfl
              | some p7 =>
                simp only [Option.map_some]
                rw [readBits_sim 36 p7.2]
                cases p7.2.readBits 36 with
                | none => rfl
                | some p8 =>
                  simp only [Option.map_some]
                  rw [readBits_sim 128 p8.2]
                  cases p8.2.readBits 128 with
                  | none => rfl
                  | some p9 => rfl

theorem skip_sim (n : Nat) (br : BitReader) :
    Stream.skipBits n (toStream br) = (br.skip n).map toStream := by
  unfold Stream.skipBits BitReader.skip
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl, if_pos (by simp)]
    simp [toStream]
  rw [if_neg h0]
  by_cases hb : br.pos + n ≤ br.size
  · rw [if_pos hb, if_pos (by simp only [length_toStream]; omega)]
    show some (((bytesToBits br.data).drop br.pos).drop n) = _
    rw [List.drop_drop]
    rfl
  · rw [if_neg hb, if_neg (by
      simp only [length_toStream]
      simp only [size] at hb ⊢
      omega)]
    rfl

theorem skipBlocks_sim :
    ∀ (fuel : Nat) (br : BitReader),
      Stream.skipBlocks fuel (toStream br)
        = (skipBlocks fuel br).map toStream := by
  intro fuel
  induction fuel with
  | zero => intro br; rfl
  | succ fuel ih =>
    intro br
    unfold Stream.skipBlocks skipBlocks
    rw [readBits_sim 1 br]
    cases br.readBits 1 with
    | none => rfl
    | some p1 =>
      simp only [Option.map_some]
      rw [readBits_sim 7 p1.2]
      cases p1.2.readBits 7 with
      | none => rfl
      | some p2 =>
        simp only [Option.map_some]
        rw [readBits_sim 24 p2.2]
        cases p2.2.readBits 24 with
        | none => rfl
        | some p3 =>
          simp only [Option.map_some]
          rw [skip_sim (8 * p3.1) p3.2]
          cases p3.2.skip (8 * p3.1) with
          | none => rfl
          | some br4 =>
            simp only [Option.map_some]
            by_cases hl : p1.1 = 1
            · rw [if_pos hl, if_pos hl]
              rfl
            · rw [if_neg hl, if_neg hl]
              exact ih br4

theorem readMeta_sim (fuel : Nat) (br : BitReader) :
    Stream.readMeta fuel (toStream br)
      = (readMeta fuel br).map (fun p => (p.1, toStream p.2)) := by
  unfold Stream.readMeta readMeta
  rw [readBits_sim 1 br]
  cases br.readBits 1 with
  | none => rfl
  | some p1 =>
    simp only [Option.map_some]
    rw [readBits_sim 7 p1.2]
    cases p1.2.readBits 7 with
    | none => rfl
    | some p2 =>
      simp only [Option.map_some]
      rw [readBits_sim 24 p2.2]
      cases p2.2.readBits 24 with
      | none => rfl
      | some p3 =>
        simp only [Option.map_some]
        by_cases ht : p2.1 = 0
        case neg => rw [if_neg ht, if_neg ht]; rfl
        rw [if_pos ht, if_pos ht]
        by_cases hl : p3.1 = 34
        case neg => rw [if_neg hl, if_neg hl]; rfl
        rw [if_pos hl, if_pos hl, readStreamInfo_sim p3.2]
        cases readStreamInfo p3.2 with
        | none => rfl
        | some p4 =>
          simp only [Option.map_some]
          by_cases hlast : p1.1 = 1
          · rw [if_pos hlast, if_pos hlast]
            rfl
          · rw [if_neg hlast, if_neg hlast, skipBlocks_sim fuel p4.2]
            cases skipBlocks fuel p4.2 with
            | none => rfl
            | some br5 => rfl

/-! ## Byte-aligned consumption for metadata -/

theorem skip_pos8 {n : Nat} {br br' : BitReader} (h : br.skip (8 * n) = some br') :
    br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  obtain ⟨hd, hp, hb⟩ := skip_spec h
  exact ⟨hd, ⟨n, hp⟩, hb⟩

theorem skipBlocks_pos8 :
    ∀ {fuel : Nat} {br br' : BitReader}, skipBlocks fuel br = some br' →
      br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
        ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  intro fuel
  induction fuel with
  | zero => intro br br' h; simp [skipBlocks] at h
  | succ fuel ih =>
    intro br br' h
    unfold skipBlocks at h
    match h1 : br.readBits 1 with
    | none => rw [h1] at h; simp at h
    | some (last, br1) =>
      simp only [h1] at h
      obtain ⟨d1, p1, b1⟩ := readBits_spec h1
      match h2 : br1.readBits 7 with
      | none => rw [h2] at h; simp at h
      | some (ty, br2) =>
        simp only [h2] at h
        obtain ⟨d2, p2, b2⟩ := readBits_spec h2
        match h3 : br2.readBits 24 with
        | none => rw [h3] at h; simp at h
        | some (len, br3) =>
          simp only [h3] at h
          obtain ⟨d3, p3, b3⟩ := readBits_spec h3
          match h4 : br3.skip (8 * len) with
          | none => rw [h4] at h; simp at h
          | some br4 =>
            simp only [h4] at h
            obtain ⟨d4, ⟨j4, p4⟩, b4⟩ := skip_pos8 h4
            have e1 : br1.size = br.size := size_congr d1
            have e2 : br2.size = br.size := by rw [size_congr d2, e1]
            have e3 : br3.size = br.size := by rw [size_congr d3, e2]
            rw [e1] at b2
            rw [e2] at b3
            rw [e3] at b4
            split at h
            · simp only [Option.some.injEq] at h
              subst h
              exact ⟨by rw [d4, d3, d2, d1], ⟨4 + j4, by omega⟩,
                fun hw => b4 (b3 (b2 (b1 hw)))⟩
            · obtain ⟨d5, ⟨j5, p5⟩, b5⟩ := ih h
              rw [size_congr d4, e3] at b5
              exact ⟨by rw [d5, d4, d3, d2, d1], ⟨4 + j4 + j5, by omega⟩,
                fun hw => b5 (b4 (b3 (b2 (b1 hw))))⟩

theorem readMeta_pos8 {fuel : Nat} {br br' : BitReader} {si : Stream.Info}
    (h : readMeta fuel br = some (si, br')) :
    br'.data = br.data ∧ (∃ j, br'.pos = br.pos + 8 * j)
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold readMeta at h
  match h1 : br.readBits 1 with
  | none => rw [h1] at h; simp at h
  | some (last, br1) =>
    simp only [h1] at h
    obtain ⟨d1, p1, b1⟩ := readBits_spec h1
    match h2 : br1.readBits 7 with
    | none => rw [h2] at h; simp at h
    | some (ty, br2) =>
      simp only [h2] at h
      obtain ⟨d2, p2, b2⟩ := readBits_spec h2
      match h3 : br2.readBits 24 with
      | none => rw [h3] at h; simp at h
      | some (len, br3) =>
        simp only [h3] at h
        obtain ⟨d3, p3, b3⟩ := readBits_spec h3
        split at h
        case isFalse => simp at h
        split at h
        case isFalse => simp at h
        match h4 : readStreamInfo br3 with
        | none => rw [h4] at h; simp at h
        | some (si0, br4) =>
          simp only [h4] at h
          -- STREAMINFO is 272 bits: chase the nine readBits
          have hsi : br4.data = br3.data ∧ br4.pos = br3.pos + 272
              ∧ (br3.pos ≤ br3.size → br4.pos ≤ br3.size) := by
            unfold readStreamInfo at h4
            match g1 : br3.readBits 16 with
            | none => rw [g1] at h4; simp at h4
            | some (v1, c1) =>
              simp only [g1] at h4
              obtain ⟨e1, q1, a1⟩ := readBits_spec g1
              match g2 : c1.readBits 16 with
              | none => rw [g2] at h4; simp at h4
              | some (v2, c2) =>
                simp only [g2] at h4
                obtain ⟨e2, q2, a2⟩ := readBits_spec g2
                match g3 : c2.readBits 24 with
                | none => rw [g3] at h4; simp at h4
                | some (v3, c3) =>
                  simp only [g3] at h4
                  obtain ⟨e3, q3, a3⟩ := readBits_spec g3
                  match g4 : c3.readBits 24 with
                  | none => rw [g4] at h4; simp at h4
                  | some (v4, c4) =>
                    simp only [g4] at h4
                    obtain ⟨e4, q4, a4⟩ := readBits_spec g4
                    match g5 : c4.readBits 20 with
                    | none => rw [g5] at h4; simp at h4
                    | some (v5, c5) =>
                      simp only [g5] at h4
                      obtain ⟨e5, q5, a5⟩ := readBits_spec g5
                      match g6 : c5.readBits 3 with
                      | none => rw [g6] at h4; simp at h4
                      | some (v6, c6) =>
                        simp only [g6] at h4
                        obtain ⟨e6, q6, a6⟩ := readBits_spec g6
                        match g7 : c6.readBits 5 with
                        | none => rw [g7] at h4; simp at h4
                        | some (v7, c7) =>
                          simp only [g7] at h4
                          obtain ⟨e7, q7, a7⟩ := readBits_spec g7
                          match g8 : c7.readBits 36 with
                          | none => rw [g8] at h4; simp at h4
                          | some (v8, c8) =>
                            simp only [g8] at h4
                            obtain ⟨e8, q8, a8⟩ := readBits_spec g8
                            match g9 : c8.readBits 128 with
                            | none => rw [g9] at h4; simp at h4
                            | some (v9, c9) =>
                              simp only [g9, Option.some.injEq,
                                Prod.mk.injEq] at h4
                              obtain ⟨-, hbr⟩ := h4
                              subst hbr
                              obtain ⟨e9, q9, a9⟩ := readBits_spec g9
                              have f1 : c1.size = br3.size := size_congr e1
                              have f2 : c2.size = br3.size := by
                                rw [size_congr e2, f1]
                              have f3 : c3.size = br3.size := by
                                rw [size_congr e3, f2]
                              have f4 : c4.size = br3.size := by
                                rw [size_congr e4, f3]
                              have f5 : c5.size = br3.size := by
                                rw [size_congr e5, f4]
                              have f6 : c6.size = br3.size := by
                                rw [size_congr e6, f5]
                              have f7 : c7.size = br3.size := by
                                rw [size_congr e7, f6]
                              have f8 : c8.size = br3.size := by
                                rw [size_congr e8, f7]
                              rw [f1] at a2
                              rw [f2] at a3
                              rw [f3] at a4
                              rw [f4] at a5
                              rw [f5] at a6
                              rw [f6] at a7
                              rw [f7] at a8
                              rw [f8] at a9
                              exact ⟨by rw [e9, e8, e7, e6, e5, e4, e3, e2, e1],
                                by omega,
                                fun hw => a9 (a8 (a7 (a6 (a5 (a4 (a3 (a2 (a1 hw))))))))⟩
          have e1 : br1.size = br.size := size_congr d1
          have e2 : br2.size = br.size := by rw [size_congr d2, e1]
          have e3 : br3.size = br.size := by rw [size_congr d3, e2]
          rw [e1] at b2
          rw [e2] at b3
          obtain ⟨d4, p4, b4⟩ := hsi
          rw [e3] at b4
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hbr⟩ := h
            subst hbr
            exact ⟨by rw [d4, d3, d2, d1], ⟨38, by omega⟩,
              fun hw => b4 (b3 (b2 (b1 hw)))⟩
          · match h5 : skipBlocks fuel br4 with
            | none => rw [h5] at h; simp at h
            | some br5 =>
              simp only [h5, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, hbr⟩ := h
              subst hbr
              obtain ⟨d5, ⟨j5, p5⟩, b5⟩ := skipBlocks_pos8 h5
              rw [size_congr d4, e3] at b5
              exact ⟨by rw [d5, d4, d3, d2, d1], ⟨38 + j5, by omega⟩,
                fun hw => b5 (b4 (b3 (b2 (b1 hw))))⟩

/-! ## Frame sequence and top level -/

theorem readFrames_sim (b0 : Nat) :
    ∀ (fuel : Nat) (br : BitReader), br.pos % 8 = 0 → br.pos ≤ br.size →
      Stream.readFrames b0 fuel (toStream br)
        = (readFrames b0 fuel br).map (·.map (·.map (·.toList))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro br _ _
    unfold Stream.readFrames readFrames
    by_cases hrem : br.remaining = 0
    · have hnil : toStream br = [] :=
        List.eq_nil_of_length_eq_zero (by rw [length_toStream]; exact hrem)
      rw [if_pos hnil, if_pos hrem]
      rfl
    · have hnil : ¬ toStream br = [] := by
        intro h
        apply hrem
        have := congrArg List.length h
        rw [length_toStream] at this
        exact this
      rw [if_neg hnil, if_neg hrem]
      rfl
  | succ fuel ih =>
    intro br h8 hwf
    unfold Stream.readFrames readFrames
    by_cases hrem : br.remaining = 0
    · have hnil : toStream br = [] :=
        List.eq_nil_of_length_eq_zero (by rw [length_toStream]; exact hrem)
      rw [if_pos hnil, if_pos hrem]
      rfl
    · have hnil : ¬ toStream br = [] := by
        intro h
        apply hrem
        have := congrArg List.length h
        rw [length_toStream] at this
        exact this
      rw [if_neg hnil, if_neg hrem, readFrame_sim b0 br h8 hwf]
      match hf : readFrame b0 br with
      | none => rfl
      | some (chs, br') =>
        simp only [Option.map_some]
        obtain ⟨d1, ⟨k, hk⟩, hb, _⟩ := readFrame_pos8 hwf hf
        have hsz : br'.size = br.size := size_congr d1
        rw [ih br' (by omega) (by omega)]
        cases readFrames b0 fuel br' with
        | none => rfl
        | some rest => rfl

/-! ### Channel reassembly: the left-fold array form computes `recombine` -/

private theorem zipApp_toList (a : List (Array Int)) :
    ∀ b : List (Array Int),
      (List.zipWith (· ++ ·) a b).map (·.toList)
        = List.zipWith (· ++ ·) (a.map (·.toList)) (b.map (·.toList)) := by
  induction a with
  | nil => intro b; rfl
  | cons x t ih =>
    intro b
    cases b with
    | nil => rfl
    | cons y u => simp [ih]

private theorem zipApp_assoc (a : List (List Int)) :
    ∀ (b c : List (List Int)),
      List.zipWith (· ++ ·) (List.zipWith (· ++ ·) a b) c
        = List.zipWith (· ++ ·) a (List.zipWith (· ++ ·) b c) := by
  induction a with
  | nil => intro b c; rfl
  | cons x t ih =>
    intro b c
    cases b with
    | nil => rfl
    | cons y u =>
      cases c with
      | nil => rfl
      | cons z v => simp [ih, List.append_assoc]

private theorem recombineGo_eq (ch : Nat) :
    ∀ (frs : List (List (Array Int))) (acc : List (Array Int)),
      (recombineGo ch acc frs).map (·.toList)
        = List.zipWith (· ++ ·) (acc.map (·.toList))
            (Stream.recombine ch (frs.map (·.map (·.toList)))) := by
  intro frs
  induction frs with
  | nil =>
    intro acc
    show (List.zipWith (· ++ ·) acc (List.replicate ch #[])).map (·.toList) = _
    rw [zipApp_toList]
    show _ = List.zipWith (· ++ ·) (acc.map (·.toList)) (List.replicate ch [])
    simp
  | cons fr frs ih =>
    intro acc
    show (recombineGo ch (List.zipWith (· ++ ·) acc fr) frs).map (·.toList) = _
    rw [ih, zipApp_toList]
    show _ = List.zipWith (· ++ ·) (acc.map (·.toList))
      (List.zipWith (· ++ ·) (fr.map (·.toList))
        (Stream.recombine ch (frs.map (·.map (·.toList)))))
    rw [zipApp_assoc]

private theorem recombineA_toList (ch : Nat) (frames : List (List (Array Int))) :
    (recombineA ch frames).map (·.toList)
      = Stream.recombine ch (frames.map (·.map (·.toList))) := by
  match frames with
  | [] => simp [recombineA, Stream.recombine]
  | fr :: frs =>
    show (recombineGo ch fr frs).map (·.toList) = _
    rw [recombineGo_eq]
    rfl

/-- **Decoder equivalence**: the buffered production decoder computes
    exactly the reference decoder's result on every input. -/
theorem decodeOption_eq_reference (bytes : ByteArray) :
    decodeOption bytes = Stream.decodeReference bytes := by
  have h0 : bytesToBits bytes = toStream (⟨bytes, 0⟩ : BitReader) := by
    simp [toStream]
  simp only [decodeOption, Stream.decodeReference, h0]
  rw [readBits_sim 32 ⟨bytes, 0⟩]
  match h1 : BitReader.readBits 32 ⟨bytes, 0⟩ with
  | none => rfl
  | some (marker, br1) =>
    simp only [Option.map_some]
    by_cases hm : marker = 0x664C6143
    case neg => rw [if_neg hm, if_neg hm]
    rw [if_pos hm, if_pos hm]
    have hf1 : (toStream br1).length = br1.remaining := by
      rw [length_toStream]; rfl
    rw [hf1, readMeta_sim br1.remaining br1]
    match h2 : readMeta br1.remaining br1 with
    | none => rfl
    | some (si, br2) =>
      simp only [Option.map_some]
      have hf2 : (toStream br2).length = br2.remaining := by
        rw [length_toStream]; rfl
      obtain ⟨d1, p1, b1⟩ := readBits_spec h1
      have p1' : br1.pos = 32 := p1
      obtain ⟨d2, ⟨j, p2⟩, b2⟩ := readMeta_pos8 h2
      have e1 : br1.size = BitReader.size ⟨bytes, 0⟩ := size_congr d1
      have e2 : br2.size = BitReader.size ⟨bytes, 0⟩ := by
        rw [size_congr d2, e1]
      have hwf0 : (⟨bytes, 0⟩ : BitReader).pos ≤ BitReader.size ⟨bytes, 0⟩ := by
        show 0 ≤ _; omega
      rw [e1] at b2
      rw [hf2, readFrames_sim si.bps (br2.remaining + 1) br2
        (by omega) (by have := b2 (b1 hwf0); omega)]
      match readFrames si.bps (br2.remaining + 1) br2 with
      | none => rfl
      | some frames => simp only [Option.map_some, recombineA_toList]

end Flac.Decode

namespace Flac

/-- **Accept-set transfer**: the shipped decoder succeeds with a given
    result exactly when the verified reference decoder does. -/
theorem decode_ok_iff_reference (bytes : ByteArray) (a : Stream.Audio) :
    decode bytes = .ok a ↔ Stream.decodeReference bytes = some a := by
  unfold decode
  rw [Decode.decodeOption_eq_reference]
  match Stream.decodeReference bytes with
  | none => simp
  | some a' => simp

/-- General form of the capstone: any encoder configuration — block size,
    numbering strategy, and *arbitrary* channel-assignment heuristic. -/
theorem decode_encode_cfg (cfg : Stream.EncoderCfg) (a : Stream.Audio)
    (hwf : a.WellFormed)
    (hbs1 : 16 ≤ cfg.blockSize) (hbs2 : cfg.blockSize ≤ 65535) :
    decode (Stream.encode cfg a) = .ok a :=
  (decode_ok_iff_reference _ _).mpr
    (Stream.decodeReference_encode cfg a hwf hbs1 hbs2)

/-- **The capstone**: decoding an encoded stream recovers the samples,
    for every well-formed audio. `Flac.encode` and `Flac.decode` are the
    shipped production entry points; `Audio.WellFormed` says exactly
    "representable as FLAC" (1–8 equal-length channels, bit depth 1–32,
    samples in range, STREAMINFO field bounds) and is decidable. -/
theorem decode_encode (a : Stream.Audio) (h : a.WellFormed) :
    decode (encode a) = .ok a :=
  decode_encode_cfg _ a h (by show 16 ≤ 4096; omega) (by show 4096 ≤ 65535; omega)

/-- Hypothesis-free capstone for the runtime-checked encoder: whenever
    `encodeChecked` returns bytes at all, decoding them recovers the
    samples. The runner's test *is* the theorem's precondition. -/
theorem decode_encodeChecked {a : Stream.Audio} {bytes : ByteArray}
    (h : encodeChecked a = some bytes) : decode bytes = .ok a := by
  unfold encodeChecked at h
  split at h
  · cases h
    exact decode_encode a ‹_›
  · cases h

/-- Hypothesis-free capstone, arbitrary configuration. -/
theorem decode_encodeCheckedCfg {cfg : Stream.EncoderCfg}
    {a : Stream.Audio} {bytes : ByteArray}
    (h : encodeCheckedCfg cfg a = some bytes) :
    decode bytes = .ok a := by
  unfold encodeCheckedCfg at h
  split at h
  case isTrue hc =>
    cases h
    exact decode_encode_cfg cfg a hc.1 hc.2.1 hc.2.2
  case isFalse => cases h


/-! ## Byte-level PCM round-trip -/

private theorem byteListOfPcm16_pcm16OfByteList :
    ∀ l : List UInt8, l.length % 2 = 0 →
      byteListOfPcm16 (pcm16OfByteList l) = l
  | [], _ => rfl
  | [_], h => by simp at h
  | lo :: hi :: rest, h => by
    have hrest := byteListOfPcm16_pcm16OfByteList rest
      (by simp only [List.length_cons] at h; omega)
    have hlo : lo.toNat < 256 := UInt8.toNat_lt lo
    have hhi : hi.toNat < 256 := UInt8.toNat_lt hi
    have hval : (sInt16 lo hi % 65536).toNat = lo.toNat + 256 * hi.toNat := by
      simp only [sInt16]
      split <;> omega
    simp only [pcm16OfByteList, byteListOfPcm16, hval, hrest]
    rw [show (lo.toNat + 256 * hi.toNat) % 256 = lo.toNat from by omega,
      show (lo.toNat + 256 * hi.toNat) / 256 = hi.toNat from by omega,
      UInt8.ofNat_toNat, UInt8.ofNat_toNat]

private theorem length_pcm16OfByteList :
    ∀ l : List UInt8, (pcm16OfByteList l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [pcm16OfByteList]
  | lo :: hi :: rest => by
    simp only [pcm16OfByteList, List.length_cons,
      length_pcm16OfByteList rest]
    omega

private theorem map_headD_zipWith_cons :
    ∀ (xs : List Int) (chs : List (List Int)), xs.length = chs.length →
      (List.zipWith (· :: ·) xs chs).map (fun c => c.headD 0) = xs := by
  intro xs
  induction xs with
  | nil => intro chs _; rfl
  | cons x xs ih =>
    intro chs hl
    match chs with
    | c :: chs =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.headD_cons]
      rw [ih chs (by simpa using hl)]

private theorem map_tail_zipWith_cons :
    ∀ (xs : List Int) (chs : List (List Int)), xs.length = chs.length →
      (List.zipWith (· :: ·) xs chs).map (·.tail) = chs := by
  intro xs
  induction xs with
  | nil =>
    intro chs hl
    match chs with
    | [] => rfl
  | cons x xs ih =>
    intro chs hl
    match chs with
    | c :: chs =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.tail_cons]
      rw [ih chs (by simpa using hl)]

private theorem length_deinterleaveN (ch : Nat) :
    ∀ (n : Nat) (l : List Int), n * ch ≤ l.length →
      (deinterleaveN ch n l).length = ch := by
  intro n
  induction n with
  | zero => intro l _; simp [deinterleaveN]
  | succ n ih =>
    intro l hl
    have hstep : (n + 1) * ch = n * ch + ch := Nat.succ_mul ..
    have := ih (l.drop ch) (by simp only [List.length_drop]; omega)
    simp only [deinterleaveN, List.length_zipWith, List.length_take, this]
    omega

private theorem interleaveN_deinterleaveN (ch : Nat) :
    ∀ (n : Nat) (l : List Int), l.length = n * ch →
      interleaveN n (deinterleaveN ch n l) = l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro l hl
    have hstep : (n + 1) * ch = n * ch + ch := Nat.succ_mul ..
    have htk : (l.take ch).length = ch := by
      simp only [List.length_take]
      omega
    have hdl : (deinterleaveN ch n (l.drop ch)).length = ch :=
      length_deinterleaveN ch n _ (by simp only [List.length_drop]; omega)
    simp only [deinterleaveN, interleaveN]
    rw [map_headD_zipWith_cons _ _ (by omega),
      map_tail_zipWith_cons _ _ (by omega),
      ih (l.drop ch) (by simp only [List.length_drop]; omega),
      List.take_append_drop]

private theorem headD_deinterleaveN {ch : Nat} (hch : 0 < ch) :
    ∀ (n : Nat) (l : List Int), l.length = n * ch →
      ((deinterleaveN ch n l).headD []).length = n := by
  obtain ⟨k, rfl⟩ : ∃ k, ch = k + 1 := ⟨ch - 1, by omega⟩
  intro n
  induction n with
  | zero =>
    intro l _
    simp [deinterleaveN, List.replicate_succ]
  | succ n ih =>
    intro l hl
    have hstep : (n + 1) * (k + 1) = n * (k + 1) + (k + 1) := Nat.succ_mul ..
    match l, hl with
    | [], hl => simp only [List.length_nil] at hl; omega
    | x :: l', hl =>
      have hdl : (deinterleaveN (k + 1) n ((x :: l').drop (k + 1))).length
          = k + 1 :=
        length_deinterleaveN (k + 1) n _
          (by simp only [List.length_drop]; omega)
      have hih := ih ((x :: l').drop (k + 1))
        (by simp only [List.length_drop]; omega)
      match hd : deinterleaveN (k + 1) n ((x :: l').drop (k + 1)) with
      | [] => rw [hd] at hdl; simp only [List.length_nil] at hdl; omega
      | c :: cs =>
        rw [hd] at hih
        simp only [List.headD_cons] at hih
        show ((List.zipWith (· :: ·) ((x :: l').take (k + 1))
          (deinterleaveN (k + 1) n ((x :: l').drop (k + 1)))).headD
            []).length = n + 1
        rw [hd]
        simp only [List.take_succ_cons, List.zipWith_cons_cons,
          List.headD_cons, List.length_cons]
        omega

private theorem toByteArray_toList_data (b : ByteArray) :
    b.data.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]

/-! ### The fused PCM16 serializer computes `byteListOfPcm16 ∘ interleave` -/

private theorem data_toList_push (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b
  simp [ByteArray.push]

private theorem byteListOfPcm16_append (l₁ l₂ : List Int) :
    byteListOfPcm16 (l₁ ++ l₂) = byteListOfPcm16 l₁ ++ byteListOfPcm16 l₂ := by
  induction l₁ with
  | nil => rfl
  | cons x t ih =>
    show UInt8.ofNat ((x % 65536).toNat % 256) :: UInt8.ofNat ((x % 65536).toNat / 256)
        :: byteListOfPcm16 (t ++ l₂) = _
    rw [ih]
    rfl

private theorem headD_drop (l : List Int) : ∀ i, (l.drop i).headD 0 = l.getD i 0 := by
  induction l with
  | nil => intro i; cases i <;> rfl
  | cons x t ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem getD_toArray (l : List Int) (i : Nat) :
    l.toArray.getD i 0 = l.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

private theorem pcm16Row_eq (i : Nat) :
    ∀ (chs : List (List Int)) (out : ByteArray),
      pcm16Row (chs.map List.toArray) i out
        = out ++ (byteListOfPcm16 (chs.map (fun l => l.getD i 0))).toByteArray := by
  intro chs
  induction chs with
  | nil =>
    intro out
    show out = out ++ ([] : List UInt8).toByteArray
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_append]
    simp [List.toList_data_toByteArray]
  | cons c t ih =>
    intro out
    show pcm16Row (t.map List.toArray) i
        ((out.push (UInt8.ofNat ((c.toArray.getD i 0 % 65536).toNat % 256))).push
          (UInt8.ofNat ((c.toArray.getD i 0 % 65536).toNat / 256))) = _
    rw [ih, getD_toArray]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_append, ByteArray.data_append, Array.toList_append,
      Array.toList_append, data_toList_push, data_toList_push,
      List.toList_data_toByteArray, List.toList_data_toByteArray]
    simp [byteListOfPcm16]

private theorem map_headD_drop (chs : List (List Int)) (i : Nat) :
    (chs.map (·.drop i)).map (·.headD 0) = chs.map (fun l => l.getD i 0) := by
  induction chs with
  | nil => rfl
  | cons c t ih => simp only [List.map_cons, ih, headD_drop]

private theorem map_tail_drop (chs : List (List Int)) (i : Nat) :
    (chs.map (·.drop i)).map (·.tail) = chs.map (·.drop (i + 1)) := by
  induction chs with
  | nil => rfl
  | cons c t ih => simp only [List.map_cons, ih, List.tail_drop]

private theorem toByteArray_append (a b : List UInt8) :
    (a ++ b).toByteArray = a.toByteArray ++ b.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_append]
  simp [List.toList_data_toByteArray]

private theorem pcm16Go_eq (chs : List (List Int)) :
    ∀ (n i : Nat) (out : ByteArray),
      pcm16Go (chs.map List.toArray) n i out
        = out ++ (byteListOfPcm16 (interleaveN n (chs.map (·.drop i)))).toByteArray := by
  intro n
  induction n with
  | zero =>
    intro i out
    show out = out ++ ([] : List UInt8).toByteArray
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_append]
    simp [List.toList_data_toByteArray]
  | succ n ih =>
    intro i out
    show pcm16Go (chs.map List.toArray) n (i + 1) (pcm16Row (chs.map List.toArray) i out) = _
    rw [ih (i + 1), pcm16Row_eq,
      show interleaveN (n + 1) (chs.map (·.drop i))
          = (chs.map (·.drop i)).map (·.headD 0)
            ++ interleaveN n ((chs.map (·.drop i)).map (·.tail)) from rfl,
      map_headD_drop, map_tail_drop, byteListOfPcm16_append, toByteArray_append,
      ByteArray.append_assoc]

private theorem emptyWithCapacity_eq_empty' (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := by
  apply ByteArray.ext
  rfl

/-- The fused serializer computes the compositional byte-level output. -/
theorem pcm16Fast_eq (chs : List (List Int)) :
    pcm16Fast chs = (byteListOfPcm16 (interleave chs)).toByteArray := by
  unfold pcm16Fast interleave
  rw [pcm16Go_eq chs (chs.headD []).length 0, emptyWithCapacity_eq_empty',
    ByteArray.empty_append,
    show chs.map (·.drop 0) = chs from by simp]

/-- **The byte-level guarantee**: whenever `encodePcm16Cfg` produces a
    FLAC file at all, decoding that file returns exactly the input PCM
    bytes — no hypotheses. -/
theorem decodePcm16_encodePcm16Cfg {cfg : Stream.EncoderCfg}
    {ch sr : Nat} {bytes flac : ByteArray}
    (h : encodePcm16Cfg cfg ch sr bytes = some flac) :
    decodePcm16 flac = .ok bytes := by
  unfold encodePcm16Cfg at h
  split at h
  case isFalse => cases h
  case isTrue hc =>
    obtain ⟨hch, hsz⟩ := hc
    have hdec := decode_encodeCheckedCfg h
    unfold decodePcm16
    simp only [hdec]
    rw [if_pos (by trivial), pcm16Fast_eq]
    have hlist : bytes.data.toList.length = bytes.size := Array.length_toList
    obtain ⟨m, hm⟩ : ∃ m, bytes.size = m * (2 * ch) :=
      ⟨bytes.size / (2 * ch),
        (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hsz)).symm⟩
    have hplen : (pcm16OfByteList bytes.data.toList).length = ch * m := by
      rw [length_pcm16OfByteList, hlist, hm, Nat.mul_left_comm,
        Nat.mul_comm ch m]
      omega
    have hn : (pcm16OfByteList bytes.data.toList).length / ch = m := by
      rw [hplen]
      exact Nat.mul_div_cancel_left m hch
    show Except.ok (byteListOfPcm16 (interleave (deinterleave ch
      (pcm16OfByteList bytes.data.toList)))).toByteArray = Except.ok bytes
    unfold deinterleave interleave
    rw [hn,
      headD_deinterleaveN hch m _ (by rw [hplen, Nat.mul_comm]),
      interleaveN_deinterleaveN ch m _ (by rw [hplen, Nat.mul_comm]),
      byteListOfPcm16_pcm16OfByteList _
        (by rw [hlist, hm, Nat.mul_left_comm]; omega),
      toByteArray_toList_data]

/-- Byte-level guarantee for the default-configuration encoder. -/
theorem decodePcm16_encodePcm16 {ch : Nat} {bytes flac : ByteArray}
    (h : encodePcm16 ch bytes = some flac) :
    decodePcm16 flac = .ok bytes :=
  decodePcm16_encodePcm16Cfg h

/-- **Byte-level guarantee for the fast encoder** — no hypotheses, and no
    trust in `Flac.Encode`: the wrapper certifies each call by running the
    verified decoder on the produced bytes (falling back to the verified
    encoder), so a `some` result is correct by construction whichever path
    produced it. -/
theorem pcm16Certified_ok {bytes out : ByteArray}
    (h : pcm16Certified bytes out = true) :
    decodePcm16 out = .ok bytes := by
  unfold pcm16Certified at h
  split at h
  case h_1 back hdec => rw [hdec, of_decide_eq_true h]
  case h_2 => cases h

theorem decodePcm16_encodePcm16Fast {blockSize ch sr : Nat}
    {bytes flac : ByteArray}
    (h : encodePcm16Fast blockSize ch sr bytes = some flac) :
    decodePcm16 flac = .ok bytes := by
  unfold encodePcm16Fast encodePcm16FastGo at h
  split at h
  case isFalse => cases h
  case isTrue =>
    split at h
    case isTrue hc =>
      cases h
      exact pcm16Certified_ok hc
    case isFalse => exact decodePcm16_encodePcm16Cfg h

end Flac
