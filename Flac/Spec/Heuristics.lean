import Flac.Native.Heuristics
import Flac.Native.Stream
import Flac.Spec.Stream

/-!
# The heuristics' single proof obligation

`defaultChooser` always returns a valid subframe configuration — the only
fact the kernel ever needs about the heuristic layer.
With it, the reference capstone specializes to the corollary
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

/-- Every padded partition choice is a legal Rice parameter. -/
private theorem padChoices_mem (po : Nat) (ks : List Nat) :
    ∀ q ∈ padChoices po ks, ∃ k, q = .rice k ∧ k < 15 := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take h)
    exact ⟨min k 14, rfl, by omega⟩
  · rw [List.eq_of_mem_replicate h]
    exact ⟨10, rfl, by omega⟩

private theorem padChoices_length (po : Nat) (ks : List Nat) :
    (padChoices po ks).length = 2 ^ po := by
  simp only [padChoices, List.length_append, List.length_take,
    List.length_map, List.length_replicate]
  omega

/-- `riceCfg` is valid for any residual of the right length. -/
theorem riceCfg_valid (bs ord po : Nat) (ks : List Nat) (res : List Int)
    (hord : ord < bs) (hres : res.length = bs - ord) :
    (riceCfg bs ord po ks).Valid bs ord res := by
  unfold riceCfg
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h3, Nat.dvd_of_mod_eq_zero h1, h2, hres, padChoices_length po ks, ?_⟩
    intro p hp
    obtain ⟨k, hk, hk15⟩ := padChoices_mem po ks p.1 (List.of_mem_zip hp).1
    rw [hk]
    show k < 15
    omega
  · refine ⟨by simp, by simp, ?_, hres, by simp, ?_⟩
    · simp only [Nat.pow_zero, Nat.div_one]
      omega
    · intro p hp
      rw [mem_zip_singleton _ _ p hp]
      show min (ks.headD 10) 14 < 15
      omega

/-- `fixedCfg` is valid for every nonempty block whose samples fit. -/
theorem fixedCfg_valid (b : Nat) (blk : List Int) (ord po : Nat)
    (ks : List Nat)
    (hne : 1 ≤ blk.length) (hfit : ∀ x ∈ blk, FitsSInt b x) :
    (fixedCfg blk ord po ks).Valid b blk := by
  unfold fixedCfg
  refine ⟨by omega, fun x hx => hfit x (List.mem_of_mem_take hx), ?_⟩
  apply riceCfg_valid
  · omega
  · show (Fixed.diffN _ blk).length = _
    simp only [Fixed.length_diffN]

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
    (shift prec po : Nat) (ks : List Nat) (hne : 1 ≤ blk.length)
    (hfit : ∀ x ∈ blk, FitsSInt b x) :
    (lpcCfg blk cs shift prec po ks).Valid b blk := by
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
    · apply riceCfg_valid
      · omega
      · show (Lpc.residualAux _ _ _ _).length = _
        rw [Lpc.length_residualAux]
        simp only [List.length_drop]

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
      · exact lpcCfg_valid b blk _ _ _ _ _ hne hfit
      · exact hverb
    · split
      · exact fixedCfg_valid b blk _ _ _ hne hfit
      · exact hverb
    · split
      · split
        · exact lpcCfg_valid b blk _ _ _ _ _ hne hfit
        · exact hverb
      · split
        · exact fixedCfg_valid b blk _ _ _ hne hfit
        · exact hverb

/-! ## Wasted-bits detection -/

/-- Scaling down an exactly-divisible sample keeps it in the reduced
    width: the pointwise width bookkeeping of-/
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

/-! ## Channel-assignment chooser -/

private theorem exists_of_mem_zipWith {f : Int → Int → Int} :
    ∀ {l r : List Int} {x : Int}, x ∈ List.zipWith f l r →
      ∃ a ∈ l, ∃ b ∈ r, x = f a b := by
  intro l
  induction l with
  | nil => intro r x hx; simp at hx
  | cons a l ih =>
    intro r x hx
    match r with
    | [] => simp at hx
    | b :: r =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨a, by simp, b, by simp, rfl⟩
      · obtain ⟨a', ha', b', hb', rfl⟩ := ih hx
        exact ⟨a', by simp [ha'], b', by simp [hb'], rfl⟩

private theorem mem_zip_map_self {α β : Type} (f : α → β) :
    ∀ (l : List α) (p : β × α), p ∈ (l.map f).zip l → p.1 = f p.2 ∧ p.2 ∈ l := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons a l ih =>
    intro p hp
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨rfl, by simp⟩
    · obtain ⟨h1, h2⟩ := ih p hp
      exact ⟨h1, by simp [h2]⟩

/-- Side channels of fitting audio fit `b+1` bits. -/
private theorem side_all_fits (b : Nat) (l r : List Int)
    (hl : ∀ x ∈ l, FitsSInt b x) (hr : ∀ x ∈ r, FitsSInt b x) :
    ∀ x ∈ Stereo.side l r, FitsSInt (b + 1) x := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_of_mem_zipWith hx
  exact Stereo.side_fits b a c (hl a ha) (hr c hc)

/-- Mid channels of fitting audio fit `b` bits. -/
private theorem mid_all_fits (b : Nat) (l r : List Int)
    (hl : ∀ x ∈ l, FitsSInt b x) (hr : ∀ x ∈ r, FitsSInt b x) :
    ∀ x ∈ Stereo.mid l r, FitsSInt b x := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_of_mem_zipWith hx
  exact Stereo.mid_fits b a c (hl a ha) (hr c hc)

/-- The channel-assignment chooser is always valid. -/
theorem defaultAsgChooser_valid (b : Nat) (fr : List (List Int))
    (hb : 1 ≤ b) (hch1 : 1 ≤ fr.length) (hch8 : fr.length ≤ 8)
    (heqfr : ∀ c ∈ fr, c.length = (fr.headD []).length)
    (h1 : 1 ≤ (fr.headD []).length)
    (hfit : ∀ c ∈ fr, ∀ x ∈ c, FitsSInt b x) :
    (defaultAsgChooser b fr).Valid b (fr.headD []).length fr := by
  match fr with
  | [l, r] =>
    simp only [List.headD_cons] at heqfr h1 ⊢
    have hll : l.length = l.length := rfl
    have hrl : r.length = l.length := heqfr r (by simp)
    have hfl : ∀ x ∈ l, FitsSInt b x := hfit l (by simp)
    have hfr : ∀ x ∈ r, FitsSInt b x := hfit r (by simp)
    have hslen : 1 ≤ (Stereo.side l r).length := by
      simp only [Stereo.length_side]
      omega
    have hmlen : 1 ≤ (Stereo.mid l r).length := by
      simp only [Stereo.length_mid]
      omega
    have hsl : (Stereo.side l r).length = l.length := by
      simp only [Stereo.length_side]; omega
    have hml : (Stereo.mid l r).length = l.length := by
      simp only [Stereo.length_mid]; omega
    have hvl := defaultSubCfg_valid b l hb h1 hfl
    have hvr := defaultSubCfg_valid b r hb (by omega) hfr
    have hvs := defaultSubCfg_valid (b + 1) (Stereo.side l r) (by omega)
      hslen (side_all_fits b l r hfl hfr)
    have hvm := defaultSubCfg_valid b (Stereo.mid l r) hb hmlen
      (mid_all_fits b l r hfl hfr)
    unfold defaultAsgChooser
    have hlens : ∀ c ∈ [l, r], c.length = l.length := heqfr
    have hindep : (Frame.ChannelAsg.independent
        [defaultSubCfg b l, defaultSubCfg b r]).Valid b l.length [l, r] := by
      refine ⟨hlens, by simp, by simp, by simp, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hvl
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact hvr
        · simp at hp
    rcases hpick : stereoPick l r with - | - | - | - | n
    · simpa only [hpick] using hindep
    · simp only [hpick]
      exact ⟨hlens, hvl, hvs⟩
    · simp only [hpick]
      exact ⟨hlens, hvs, hvr⟩
    · simp only [hpick]
      exact ⟨hlens, hvm, hvs⟩
    · simpa only [hpick] using hindep
  | [c0] =>
    refine ⟨heqfr, by omega, by omega, by simp, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [List.headD_cons] at h1
      exact defaultSubCfg_valid b c0 hb h1 (hfit c0 (by simp))
    · simp at hp
  | c0 :: c1 :: c2 :: t =>
    refine ⟨heqfr, by simp, by simpa using hch8, by simp, ?_⟩
    intro p hp
    obtain ⟨h1', h2'⟩ := mem_zip_map_self (defaultSubCfg b) _ p hp
    rw [h1']
    exact defaultSubCfg_valid b p.2 hb
      (by rw [heqfr p.2 h2']; exact h1) (hfit p.2 h2')

/-- **Capstone corollary with the default heuristics**: wasted-bit
    detection, LPC/fixed search, and stereo-mode decision — no chooser
    hypothesis left. Encode any well-formed audio, decode, get the
    channels back, kernel-checked. -/
theorem _root_.Flac.Stream.decodeReference_encode_default
    (blockSize : Nat) (varBlk : Bool) (a : Stream.Audio)
    (hwf : a.WellFormed)
    (hbs1 : 16 ≤ blockSize) (hbs2 : blockSize ≤ 65535) :
    Stream.decodeReference (Stream.encode
      ⟨blockSize, varBlk, defaultAsgChooser a.bps⟩ a) = some a :=
  Stream.decodeReference_encode _ a hwf hbs1 hbs2

end Flac.Heuristics
