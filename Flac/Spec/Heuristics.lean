import Flac.Native.Heuristics
import Flac.Native.Stream
import Flac.Spec.Stream

/-!
# The heuristics' single proof obligation

`defaultChooser` always returns a valid subframe configuration — the only
fact the kernel ever needs about the heuristic layer (PLAN.md §4 L3 note).
With it, the M2 keystone specializes to the hypothesis-light corollary
`decodeReference_encode_default`.
-/

namespace Flac.Heuristics

open Flac Flac.Bits Flac.Rice Flac.Subframe

private theorem mem_zip_singleton {α β : Type} (a : α) (l : List β)
    (p : α × β) (h : p ∈ [a].zip l) : p.1 = a := by
  match l with
  | [] => simp at h
  | b :: l =>
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at h
    simp [h]

/-- `fixedCfg` is valid for every nonempty block whose samples fit. -/
theorem fixedCfg_valid (b : Nat) (blk : List Int) (ord k : Nat)
    (hne : 1 ≤ blk.length) (hfit : ∀ x ∈ blk, FitsSInt b x) :
    (fixedCfg blk ord k).Valid b blk := by
  unfold fixedCfg
  refine ⟨by omega, fun x hx => hfit x (List.mem_of_mem_take hx), ?_⟩
  refine ⟨by simp, ?_, ?_, ?_, by simp, ?_⟩
  · simp
  · simp only [Nat.pow_zero, Nat.div_one]
    omega
  · show (Fixed.diffN _ blk).length = _
    simp only [Fixed.length_diffN]
  · intro p hp
    have h1 := mem_zip_singleton _ _ p hp
    rw [h1]
    show min k 14 < 15
    omega

/-- The chooser's certificate: its output is always valid. -/
theorem defaultChooser_valid (b : Nat) (blk : List Int)
    (hne : 1 ≤ blk.length) (hfit : ∀ x ∈ blk, FitsSInt b x) :
    (defaultChooser b blk).Valid b blk := by
  unfold defaultChooser
  by_cases hc : blk.all (fun x => x == blk.headD 0)
  · rw [if_pos hc]
    have hall : ∀ x ∈ blk, x = blk.headD 0 := fun x hx =>
      beq_iff_eq.mp (List.all_eq_true.mp hc x hx)
    have hhead : blk.headD 0 ∈ blk := by
      match blk, hne with
      | y :: t, _ => simp
    exact ⟨hall, hfit _ hhead⟩
  · rw [if_neg hc]
    split
    · exact fun x hx => hfit x hx
    · split
      · exact fixedCfg_valid b blk _ _ hne hfit
      · exact fun x hx => hfit x hx

/-- **Keystone corollary with the default heuristic**: no chooser
    hypothesis left — encode with `defaultChooser`, decode, get the input
    back, kernel-checked. -/
theorem _root_.Flac.Stream.decodeReference_encode_default
    (blockSize sampleRate b : Nat) (pcm : List Int)
    (hbs1 : 16 ≤ blockSize) (hbs2 : blockSize ≤ 65535)
    (hsr : sampleRate < 2 ^ 20) (hb1 : 1 ≤ b) (hb2 : b ≤ 32)
    (htot : pcm.length < 2 ^ 36)
    (hfit : ∀ x ∈ pcm, FitsSInt b x) :
    Stream.decodeReference (Stream.encode
      ⟨blockSize, sampleRate, b, defaultChooser b⟩ pcm) = some pcm :=
  Stream.decodeReference_encode _ pcm hbs1 hbs2 hsr hb1 hb2 htot
    (fun ys h1 _ hmem => defaultChooser_valid b ys h1
      (fun x hx => hfit x (hmem x hx)))

end Flac.Heuristics
