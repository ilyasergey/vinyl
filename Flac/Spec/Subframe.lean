import Flac.Native.Subframe
import Flac.Spec.Bits
import Flac.Spec.Rice
import Flac.Spec.Fixed
import Flac.Spec.Lpc

/-!
# L5 (part 1) — subframe round-trip

`readSubframe ∘ writeSubframe = id` for every valid subframe configuration,
including wasted bits: the content round-trips at the reduced bit depth
`b - w` (the width bookkeeping of), and the scale-down /
scale-up pair cancels by `Flac.Bits.map_shiftUp_shiftDown`.
-/

namespace Flac.Subframe

open Flac.Bits Flac.Rice

private theorem eq_replicate_of_forall_eq (xs : List Int) (v : Int)
    (h : ∀ x ∈ xs, x = v) : xs = List.replicate xs.length v := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
    simp only [List.length_cons, List.replicate_succ]
    rw [h x (List.mem_cons_self ..), ← ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem typeCode_lt {cfg : SubframeCfg} {b : Nat} {xs : List Int}
    (hv : cfg.Valid b xs) : cfg.typeCode < 2 ^ 6 := by
  match cfg with
  | .constant => decide
  | .verbatim => decide
  | .fixed ord rcfg =>
    obtain ⟨h, _⟩ := hv
    simp only [SubframeCfg.typeCode]
    omega
  | .lpc cs _ _ _ =>
    obtain ⟨_, h, _⟩ := hv
    simp only [SubframeCfg.typeCode]
    omega

/-- Content round-trip at a fixed (already wasted-reduced) bit depth. -/
theorem readContent_writeContent (b : Nat) (cfg : SubframeCfg) (xs : List Int)
    (hv : cfg.Valid b xs) (rest : BitStream) :
    readContent xs.length b cfg.typeCode (writeContent b cfg xs ++ rest)
      = some (xs, rest) := by
  match cfg with
  | .constant =>
    obtain ⟨hconst, hfit⟩ := hv
    simp only [writeContent, SubframeCfg.typeCode, readContent,
      readSInt_writeSInt b _ hfit]
    rw [if_pos (by trivial), ← eq_replicate_of_forall_eq xs _ hconst]
  | .verbatim =>
    simp only [writeContent, SubframeCfg.typeCode, readContent]
    rw [if_neg (by omega : ¬(1 : Nat) = 0), if_pos (by trivial)]
    exact readSIntSeq_writeSIntSeq b xs rest hv
  | .fixed ord rcfg =>
    obtain ⟨hord, hwarm, hrv⟩ := hv
    have hordlen : ord < xs.length := by
      have h1 := hrv.ord_lt
      have h2 : xs.length / 2 ^ rcfg.po ≤ xs.length := Nat.div_le_self _ _
      omega
    have hseq := readSIntSeq_writeSIntSeq b (xs.take ord)
      (Rice.writeResidual xs.length ord rcfg (Fixed.residual ord xs) ++ rest) hwarm
    rw [show (xs.take ord).length = ord by simp only [List.length_take]; omega] at hseq
    simp only [writeContent, SubframeCfg.typeCode, readContent, List.append_assoc]
    rw [if_neg (by omega), if_neg (by omega),
      if_pos (by omega : 8 ≤ 8 + ord ∧ 8 + ord ≤ 12)]
    simp only [show 8 + ord - 8 = ord from by omega, hseq,
      readResidual_writeResidual xs.length ord rcfg (Fixed.residual ord xs) hrv,
      Fixed.restore_residual ord xs (by omega)]
  | .lpc cs shift prec rcfg =>
    obtain ⟨ho1, ho2, hwarm, hp1, hp2, hcs, hsh, hrv⟩ := hv
    have hordlen : cs.length < xs.length := by
      have h1 := hrv.ord_lt
      have h2 : xs.length / 2 ^ rcfg.po ≤ xs.length := Nat.div_le_self _ _
      omega
    have hshfit : FitsSInt 5 (shift : Int) := by unfold FitsSInt; omega
    have hseq : ∀ t, readSIntSeq b cs.length (writeSIntSeq b (xs.take cs.length) ++ t)
        = some (xs.take cs.length, t) := by
      intro t
      have h := readSIntSeq_writeSIntSeq b (xs.take cs.length) t hwarm
      rwa [show (xs.take cs.length).length = cs.length by
        simp only [List.length_take]; omega] at h
    have hcseq : ∀ t, readSIntSeq prec cs.length (writeSIntSeq prec cs ++ t)
        = some (cs, t) := fun t => readSIntSeq_writeSIntSeq prec cs t hcs
    simp only [writeContent, SubframeCfg.typeCode, readContent, List.append_assoc]
    rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega : ¬(8 ≤ 32 + (cs.length - 1) ∧ 32 + (cs.length - 1) ≤ 12)),
      if_pos (by omega : 32 ≤ 32 + (cs.length - 1))]
    simp only [show 32 + (cs.length - 1) - 31 = cs.length from by omega, hseq,
      readBits_writeBits _ _ _ (by omega : prec - 1 < 2 ^ 4),
      readSInt_writeSInt 5 (shift : Int) hshfit]
    rw [if_neg (by omega : ¬(prec - 1 = 15)), if_pos (by omega : (0 : Int) ≤ (shift : Int))]
    simp only [show prec - 1 + 1 = prec from by omega,
      show ((shift : Int)).toNat = shift from by omega, hcseq,
      readResidual_writeResidual xs.length cs.length rcfg (Lpc.residual cs shift xs) hrv,
      Lpc.restore_residual cs shift xs]

/-- **Subframe round-trip** (wasted bits included): reading back a written
    subframe recovers the block, for every valid configuration. -/
theorem read_write (b : Nat) (sc : SubCfg) (xs : List Int)
    (hv : sc.Valid b xs) (rest : BitStream) :
    read xs.length b (write b sc xs ++ rest) = some (xs, rest) := by
  obtain ⟨hwlt, hdvd, hinner⟩ := hv
  have hcontent : ∀ t, readContent xs.length (b - sc.wasted) sc.inner.typeCode
      (writeContent (b - sc.wasted) sc.inner (xs.map (shiftDown sc.wasted)) ++ t)
      = some (xs.map (shiftDown sc.wasted), t) := by
    intro t
    have h := readContent_writeContent (b - sc.wasted) sc.inner
      (xs.map (shiftDown sc.wasted)) hinner t
    rwa [List.length_map] at h
  have htc : sc.inner.typeCode < 2 ^ 6 := typeCode_lt hinner
  by_cases hw : sc.wasted = 0
  · simp only [write, read, if_pos hw, List.append_assoc,
      readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
      readBits_writeBits _ _ _ htc]
    rw [if_pos (by trivial), if_pos (by trivial)]
    have h := hcontent rest
    rw [hw] at h ⊢
    simpa [map_shiftDown_zero] using h
  · simp only [write, read, if_neg hw, List.append_assoc,
      readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
      readBits_writeBits _ _ _ (by omega : 1 < 2 ^ 1),
      readBits_writeBits _ _ _ htc, readUnary_writeUnary]
    rw [if_pos (by trivial), if_neg (by simp),
      show sc.wasted - 1 + 1 = sc.wasted from by omega]
    simp only [hcontent, map_shiftUp_shiftDown sc.wasted xs hdvd]

end Flac.Subframe
