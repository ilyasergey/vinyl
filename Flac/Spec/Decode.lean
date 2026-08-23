import Flac.Native.Decode
import Flac.Spec.Reader

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
    | some q => rfl

theorem readRice_sim (k : Nat) (br : BitReader) :
    Rice.readRice k (toStream br)
      = (readRice k br).map (fun p => (p.1, toStream p.2)) := by
  unfold Rice.readRice readRice
  rw [readRiceNat_sim k br]
  cases readRiceNat k br with
  | none => rfl
  | some p => rfl

theorem readRiceSeq_sim (k : Nat) :
    ∀ (count : Nat) (br : BitReader),
      Rice.readRiceSeq k count (toStream br)
        = (readRiceSeq k count br).map (fun p => (p.1, toStream p.2)) := by
  intro count
  induction count with
  | zero => intro br; rfl
  | succ count ih =>
    intro br
    unfold Rice.readRiceSeq readRiceSeq
    rw [readRice_sim k br]
    cases readRice k br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2]
      cases readRiceSeq k count p.2 with
      | none => rfl
      | some q => rfl

theorem readSIntSeq_sim (bits : Nat) :
    ∀ (count : Nat) (br : BitReader),
      Rice.readSIntSeq bits count (toStream br)
        = (readSIntSeq bits count br).map (fun p => (p.1, toStream p.2)) := by
  intro count
  induction count with
  | zero => intro br; rfl
  | succ count ih =>
    intro br
    unfold Rice.readSIntSeq readSIntSeq
    rw [readSInt_sim bits br]
    cases br.readSInt bits with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2]
      cases readSIntSeq bits count p.2 with
      | none => rfl
      | some q => rfl

/-! ## Partitions -/

theorem readPart_sim (m : Rice.Method) (count : Nat) (br : BitReader) :
    Rice.readPart m count (toStream br)
      = (readPart m count br).map (fun p => (p.1, toStream p.2)) := by
  unfold Rice.readPart readPart
  rw [readBits_sim m.paramBits br]
  cases br.readBits m.paramBits with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    by_cases hk : p.1 = m.escapeCode
    · rw [if_pos hk, if_pos hk, readBits_sim 5 p.2]
      cases p.2.readBits 5 with
      | none => rfl
      | some q => exact readSIntSeq_sim q.1 count q.2
    · rw [if_neg hk, if_neg hk]
      exact readRiceSeq_sim p.1 count p.2

theorem readParts_sim (m : Rice.Method) :
    ∀ (sizes : List Nat) (br : BitReader),
      Rice.readParts m sizes (toStream br)
        = (readParts m sizes br).map (fun p => (p.1, toStream p.2)) := by
  intro sizes
  induction sizes with
  | nil => intro br; rfl
  | cons sz sizes ih =>
    intro br
    unfold Rice.readParts readParts
    rw [readPart_sim m sz br]
    cases readPart m sz br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [ih p.2]
      cases readParts m sizes p.2 with
      | none => rfl
      | some q => rfl

theorem readResidual_sim (bs ord : Nat) (br : BitReader) :
    Rice.readResidual bs ord (toStream br)
      = (readResidual bs ord br).map (fun p => (p.1, toStream p.2)) := by
  unfold Rice.readResidual readResidual
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
        · rw [if_pos hc, if_pos hc]
          exact readParts_sim m _ q.2
        · rw [if_neg hc, if_neg hc]
          rfl

theorem readContent_sim (bs b ty : Nat) (br : BitReader) :
    Subframe.readContent bs b ty (toStream br)
      = (readContent bs b ty br).map (fun p => (p.1, toStream p.2)) := by
  unfold Subframe.readContent readContent
  by_cases h0 : ty = 0
  · rw [if_pos h0, if_pos h0, readSInt_sim b br]
    cases br.readSInt b with
    | none => rfl
    | some p => rfl
  rw [if_neg h0, if_neg h0]
  by_cases h1 : ty = 1
  · rw [if_pos h1, if_pos h1]
    exact readSIntSeq_sim b bs br
  rw [if_neg h1, if_neg h1]
  by_cases h2 : 8 ≤ ty ∧ ty ≤ 12
  · rw [if_pos h2, if_pos h2, readSIntSeq_sim b (ty - 8) br]
    cases readSIntSeq b (ty - 8) br with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [readResidual_sim bs (ty - 8) p.2]
      cases readResidual bs (ty - 8) p.2 with
      | none => rfl
      | some q => rfl
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
                rw [readResidual_sim bs (ty - 31) u.2]
                cases readResidual bs (ty - 31) u.2 with
                | none => rfl
                | some w => rfl
            · rw [if_neg h5, if_neg h5]
              rfl
  · rw [if_neg h3, if_neg h3]
    rfl

theorem readSubframe_sim (bs b : Nat) (br : BitReader) :
    Subframe.read bs b (toStream br)
      = (readSubframe bs b br).map (fun p => (p.1, toStream p.2)) := by
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
              | some u => rfl
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

theorem posOK_readRiceSeq (k : Nat) : ∀ (count : Nat), PosOK (readRiceSeq k count) := by
  intro count
  induction count with
  | zero =>
    intro br a br' hwf h
    simp only [readRiceSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | succ count ih =>
    intro br a br' hwf h
    unfold readRiceSeq at h
    match h1 : readRice k br with
    | none => rw [h1] at h; simp at h
    | some (x, br1) =>
      simp only [h1] at h
      match h2 : readRiceSeq k count br1 with
      | none => rw [h2] at h; simp at h
      | some (xs, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        obtain ⟨d1, p1, b1⟩ := posOK_readRice k br x br1 hwf h1
        obtain ⟨d2, p2, b2⟩ := ih br1 xs _ (by rw [size_congr d1]; omega) h2
        rw [size_congr d1] at b2
        exact ⟨by rw [d2, d1], by omega, b2⟩

theorem posOK_readSIntSeq (bits : Nat) : ∀ (count : Nat), PosOK (readSIntSeq bits count) := by
  intro count
  induction count with
  | zero =>
    intro br a br' hwf h
    simp only [readSIntSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | succ count ih =>
    intro br a br' hwf h
    unfold readSIntSeq at h
    match h1 : br.readSInt bits with
    | none => rw [h1] at h; simp at h
    | some (x, br1) =>
      simp only [h1] at h
      match h2 : readSIntSeq bits count br1 with
      | none => rw [h2] at h; simp at h
      | some (xs, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        obtain ⟨d1, p1, b1⟩ := posOK_readSInt bits br x br1 hwf h1
        obtain ⟨d2, p2, b2⟩ := ih br1 xs _ (by rw [size_congr d1]; omega) h2
        rw [size_congr d1] at b2
        exact ⟨by rw [d2, d1], by omega, b2⟩

/-- Sequencing step for `PosOK` proofs: chain two position facts. -/
theorem posOK_step {br br1 br' : BitReader}
    (h1 : br1.data = br.data ∧ br.pos ≤ br1.pos ∧ br1.pos ≤ br.size)
    (h2 : br'.data = br1.data ∧ br1.pos ≤ br'.pos ∧ br'.pos ≤ br1.size) :
    br'.data = br.data ∧ br.pos ≤ br'.pos ∧ br'.pos ≤ br.size := by
  obtain ⟨d1, p1, b1⟩ := h1
  obtain ⟨d2, p2, b2⟩ := h2
  rw [size_congr d1] at b2
  exact ⟨by rw [d2, d1], by omega, b2⟩

theorem posOK_readPart (m : Rice.Method) (count : Nat) : PosOK (readPart m count) := by
  intro br a br' hwf h
  unfold readPart at h
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
        have s3 := posOK_readSIntSeq bits count br2 a br'
          (by rw [size_congr s2.1, size_congr s1.1]
              rw [size_congr s1.1] at s2
              omega) h
        exact posOK_step s1 (posOK_step s2 s3)
    · exact posOK_step s1 (posOK_readRiceSeq k count br1 a br'
        (by rw [size_congr s1.1]; omega) h)

theorem posOK_readParts (m : Rice.Method) :
    ∀ sizes, PosOK (readParts m sizes) := by
  intro sizes
  induction sizes with
  | nil =>
    intro br a br' hwf h
    simp only [readParts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact ⟨rfl, by omega, hwf⟩
  | cons sz sizes ih =>
    intro br a br' hwf h
    unfold readParts at h
    match h1 : readPart m sz br with
    | none => rw [h1] at h; simp at h
    | some (pp, br1) =>
      simp only [h1] at h
      have s1 := posOK_readPart m sz br pp br1 hwf h1
      match h2 : readParts m sizes br1 with
      | none => rw [h2] at h; simp at h
      | some (ps, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (ih br1 ps _ (by rw [size_congr s1.1]; omega) h2)

theorem posOK_readResidual (bs ord : Nat) : PosOK (readResidual bs ord) := by
  intro br a br' hwf h
  unfold readResidual at h
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
        · refine posOK_step s1 (posOK_step s2 (posOK_readParts m _ br2 a br' ?_ h))
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
  · exact posOK_readSIntSeq b bs br a br' hwf h
  split at h
  · match h1 : readSIntSeq b (ty - 8) br with
    | none => rw [h1] at h; simp at h
    | some (warm, br1) =>
      simp only [h1] at h
      have s1 := posOK_readSIntSeq b (ty - 8) br warm br1 hwf h1
      match h2 : readResidual bs (ty - 8) br1 with
      | none => rw [h2] at h; simp at h
      | some (res, br2) =>
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hbr⟩ := h
        subst hbr
        exact posOK_step s1 (posOK_readResidual bs (ty - 8) br1 res _
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
                match h5 : readResidual bs (ty - 31) br4 with
                | none => rw [h5] at h; simp at h
                | some (res, br5) =>
                  simp only [h5, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, hbr⟩ := h
                  subst hbr
                  have s5 := posOK_readResidual bs (ty - 31) br4 res _
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
