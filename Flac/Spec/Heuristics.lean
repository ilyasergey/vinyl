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

/-- `clampSInt` really clamps: the result fits `p` bits. -/
theorem fitsSInt_clampSInt (p : Nat) (hp : 1 ≤ p) (c : Int) :
    FitsSInt p (clampSInt p c) := by
  unfold FitsSInt clampSInt
  have h2p : (2 ^ p : Nat) = 2 ^ (p - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hBpos : 0 < (2 ^ (p - 1) : Nat) := Nat.two_pow_pos (p - 1)
  split
  · omega
  · split <;> omega

/-- `lpcCfg` is valid for every nonempty block whose samples fit. -/
theorem lpcCfg_valid (b : Nat) (blk : List Int) (cs : List Int)
    (shift prec k : Nat) (hne : 1 ≤ blk.length)
    (hfit : ∀ x ∈ blk, FitsSInt b x) :
    (lpcCfg blk cs shift prec k).Valid b blk := by
  unfold lpcCfg
  split
  · exact fun x hx => hfit x hx
  · rename_i hemp
    have hlen : ((cs.map (clampSInt (min (max prec 1) 15))).take
        (min 32 (blk.length - 1))).length ≠ 0 := by
      intro h0
      exact hemp (List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero h0))
    have hlen2 : ((cs.map (clampSInt (min (max prec 1) 15))).take
        (min 32 (blk.length - 1))).length ≤ min 32 (blk.length - 1) := by
      simp only [List.length_take]
      omega
    refine ⟨by omega, by omega,
      fun x hx => hfit x (List.mem_of_mem_take hx), by omega, by omega,
      ?_, by omega, ?_⟩
    · intro c hc
      obtain ⟨orig, _, horig⟩ := List.mem_map.mp (List.mem_of_mem_take hc)
      rw [← horig]
      exact fitsSInt_clampSInt _ (by omega) orig
    · refine ⟨by simp, by simp, ?_, ?_, by simp, ?_⟩
      · simp only [Nat.pow_zero, Nat.div_one]
        omega
      · show (Lpc.residualAux _ _ _ _).length = _
        rw [Lpc.length_residualAux]
        simp only [List.length_drop]
      · intro p hp
        rw [mem_zip_singleton _ _ p hp]
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
    have hverb : SubframeCfg.Valid .verbatim b blk := fun x hx => hfit x hx
    split
    · exact hverb
    · split
      · exact lpcCfg_valid b blk _ _ _ _ hne hfit
      · exact hverb
    · split
      · exact fixedCfg_valid b blk _ _ hne hfit
      · exact hverb
    · split
      · split
        · exact lpcCfg_valid b blk _ _ _ _ hne hfit
        · exact hverb
      · split
        · exact fixedCfg_valid b blk _ _ hne hfit
        · exact hverb

/-! ## Wasted-bits detection -/

/-- Scaling down an exactly-divisible sample keeps it in the reduced
    width: the pointwise width bookkeeping of PLAN.md §5.6. -/
theorem fitsSInt_shiftDown (b w : Nat) (hw : w < b) (x : Int)
    (hfit : FitsSInt b x) (hdvd : ((2 ^ w : Nat) : Int) ∣ x) :
    FitsSInt (b - w) (shiftDown w x) := by
  obtain ⟨q, hq⟩ := hdvd
  have hP : (0 : Int) < ((2 ^ w : Nat) : Int) := by
    have := Nat.two_pow_pos w
    omega
  have hqx : shiftDown w x = q := by
    rw [shiftDown, hq, Int.mul_ediv_cancel_left _ (by omega)]
  rw [hqx]
  obtain ⟨h1, h2⟩ := hfit
  have hsplit : (2 ^ b : Nat) = 2 ^ w * 2 ^ (b - w) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit] at h1 h2
  constructor
  · have h1' : ((2 ^ w : Nat) : Int) * -((2 ^ (b - w) : Nat) : Int)
        ≤ ((2 ^ w : Nat) : Int) * (2 * q) := by
      calc ((2 ^ w : Nat) : Int) * -((2 ^ (b - w) : Nat) : Int)
          = -(((2 ^ w * 2 ^ (b - w) : Nat) : Int)) := by
            rw [Int.natCast_mul]
            rw [Int.mul_neg]
        _ ≤ 2 * x := h1
        _ = ((2 ^ w : Nat) : Int) * (2 * q) := by rw [hq]; ac_rfl
    have := Int.le_of_mul_le_mul_left h1' hP
    omega
  · have h2' : ((2 ^ w : Nat) : Int) * (2 * q)
        < ((2 ^ w : Nat) : Int) * ((2 ^ (b - w) : Nat) : Int) := by
      calc ((2 ^ w : Nat) : Int) * (2 * q)
          = 2 * x := by rw [hq]; ac_rfl
        _ < ((2 ^ w * 2 ^ (b - w) : Nat) : Int) := h2
        _ = ((2 ^ w : Nat) : Int) * ((2 ^ (b - w) : Nat) : Int) := by
            rw [Int.natCast_mul]
    exact Int.lt_of_mul_lt_mul_left h2' (by omega)

theorem wastedDetect_lt (b : Nat) (hb : 1 ≤ b) (xs : List Int) :
    wastedDetect b xs < b := by
  unfold wastedDetect
  split
  · rename_i w hfind
    have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_reverse] at hmem
    exact List.mem_range.mp hmem
  · omega

theorem wastedDetect_dvd (b : Nat) (xs : List Int) :
    ∀ x ∈ xs, ((2 ^ wastedDetect b xs : Nat) : Int) ∣ x := by
  intro x hx
  unfold wastedDetect
  split
  · rename_i w hfind
    have hp := List.find?_some hfind
    have := List.all_eq_true.mp hp x hx
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  · simp

/-- The full chooser (wasted bits + subframe search) is always valid. -/
theorem defaultSubCfg_valid (b : Nat) (blk : List Int) (hb : 1 ≤ b)
    (hne : 1 ≤ blk.length) (hfit : ∀ x ∈ blk, FitsSInt b x) :
    (defaultSubCfg b blk).Valid b blk := by
  refine ⟨wastedDetect_lt b hb blk, wastedDetect_dvd b blk, ?_⟩
  apply defaultChooser_valid
  · simpa using hne
  · intro y hy
    obtain ⟨x, hxmem, hxy⟩ := List.mem_map.mp hy
    rw [← hxy]
    exact fitsSInt_shiftDown b _ (wastedDetect_lt b hb blk) x (hfit x hxmem)
      (wastedDetect_dvd b blk x hxmem)

/-- **Keystone corollary with the default heuristic**: no chooser
    hypothesis left — encode with `defaultSubCfg` (wasted-bit detection,
    LPC/fixed search), decode, get the input back, kernel-checked. -/
theorem _root_.Flac.Stream.decodeReference_encode_default
    (blockSize sampleRate b : Nat) (pcm : List Int)
    (hbs1 : 16 ≤ blockSize) (hbs2 : blockSize ≤ 65535)
    (hsr : sampleRate < 2 ^ 20) (hb1 : 1 ≤ b) (hb2 : b ≤ 32)
    (htot : pcm.length < 2 ^ 36)
    (hfit : ∀ x ∈ pcm, FitsSInt b x) :
    Stream.decodeReference (Stream.encode
      ⟨blockSize, sampleRate, b, defaultSubCfg b⟩ pcm) = some pcm :=
  Stream.decodeReference_encode _ pcm hbs1 hbs2 hsr hb1 hb2 htot
    (fun ys h1 _ hmem => defaultSubCfg_valid b ys hb1 h1
      (fun x hx => hfit x (hmem x hx)))

end Flac.Heuristics
