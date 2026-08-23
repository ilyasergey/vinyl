import Flac.Native.Subframe
import Flac.Spec.Bits
import Flac.Spec.Rice
import Flac.Spec.Fixed

/-!
# L5 (part 1) — subframe round-trip

`readSubframe ∘ writeSubframe = id` for every valid subframe configuration:
the first composition-layer theorem. Width bookkeeping is trivial here
(mono, no wasted bits); it grows teeth at M4.
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

/-- **Subframe round-trip**: reading back a written subframe recovers the
    block, for every valid configuration. -/
theorem read_write (b : Nat) (cfg : SubframeCfg) (xs : List Int)
    (hv : cfg.Valid b xs) (rest : BitStream) :
    read xs.length b (write b cfg xs ++ rest) = some (xs, rest) := by
  match cfg with
  | .constant =>
    obtain ⟨hconst, hfit⟩ := hv
    simp only [write, SubframeCfg.typeCode, read, List.append_assoc,
      readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
      readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 6),
      readSInt_writeSInt b _ hfit]
    rw [if_pos trivial, if_pos trivial, if_pos trivial,
      ← eq_replicate_of_forall_eq xs _ hconst]
  | .verbatim =>
    simp only [write, SubframeCfg.typeCode, read, List.append_assoc,
      readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
      readBits_writeBits _ _ _ (by omega : 1 < 2 ^ 6)]
    rw [if_pos trivial, if_pos trivial, if_neg (by omega : ¬(1 : Nat) = 0),
      if_pos trivial]
    exact readSIntSeq_writeSIntSeq b xs rest hv
  | .fixed ord rcfg =>
    obtain ⟨hord, hwarm, hrv⟩ := hv
    have hordlen : ord < xs.length := by
      have h1 := hrv.ord_lt
      have h2 : xs.length / 2 ^ rcfg.po ≤ xs.length := Nat.div_le_self _ _
      omega
    have hwlen : (xs.take ord).length = ord := by
      simp only [List.length_take]; omega
    have hseq := readSIntSeq_writeSIntSeq b (xs.take ord)
      (Rice.writeResidual xs.length ord rcfg (Fixed.residual ord xs) ++ rest) hwarm
    rw [hwlen] at hseq
    simp only [write, SubframeCfg.typeCode, read, List.append_assoc,
      readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
      readBits_writeBits _ _ _ (by omega : 8 + ord < 2 ^ 6)]
    rw [if_pos trivial, if_pos trivial, if_neg (by omega), if_neg (by omega),
      if_pos (by omega : 8 ≤ 8 + ord ∧ 8 + ord ≤ 12)]
    simp only [show 8 + ord - 8 = ord from by omega, hseq,
      readResidual_writeResidual xs.length ord rcfg (Fixed.residual ord xs) hrv,
      Fixed.restore_residual ord xs (by omega)]

end Flac.Subframe
