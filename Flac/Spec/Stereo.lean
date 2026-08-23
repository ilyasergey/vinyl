import Flac.Native.Stereo
import Flac.Spec.Bits

/-!
# L4 proofs — stereo decorrelation round-trips

One round-trip lemma per stereo mode, plus the
width fact that the side channel fits `b+1` bits. The mid/side parity
argument is `Flac.Bits.two_mul_sar_one` plus `omega`.
-/

namespace Flac.Stereo

open Flac.Bits

/-- Pointwise mid/side reconstruction, left channel. -/
theorem msl_point (a b : Int) :
    sar (2 * sar (a + b) 1 + (a - b) % 2 + (a - b)) 1 = a := by
  have h1 := two_mul_sar_one (a + b)
  have h2 := two_mul_sar_one (2 * sar (a + b) 1 + (a - b) % 2 + (a - b))
  omega

/-- Pointwise mid/side reconstruction, right channel. -/
theorem msr_point (a b : Int) :
    sar (2 * sar (a + b) 1 + (a - b) % 2 - (a - b)) 1 = b := by
  have h1 := two_mul_sar_one (a + b)
  have h2 := two_mul_sar_one (2 * sar (a + b) 1 + (a - b) % 2 - (a - b))
  omega

theorem decodeLS_side (l r : List Int) (h : l.length = r.length) :
    decodeLS l (side l r) = r := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | b :: r =>
      simp only [side, decodeLS, List.zipWith_cons_cons] at *
      rw [show a - (a - b) = b by omega, ih r (by simp only [List.length_cons] at h; omega)]

theorem decodeRS_side (l r : List Int) (h : l.length = r.length) :
    decodeRS (side l r) r = l := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | b :: r =>
      simp only [side, decodeRS, List.zipWith_cons_cons] at *
      rw [show b + (a - b) = a by omega, ih r (by simp only [List.length_cons] at h; omega)]

theorem decodeMSL_mid_side (l r : List Int) (h : l.length = r.length) :
    decodeMSL (mid l r) (side l r) = l := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | b :: r =>
      simp only [side, mid, decodeMSL, List.zipWith_cons_cons] at *
      rw [msl_point a b, ih r (by simp only [List.length_cons] at h; omega)]

theorem decodeMSR_mid_side (l r : List Int) (h : l.length = r.length) :
    decodeMSR (mid l r) (side l r) = r := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | b :: r =>
      simp only [side, mid, decodeMSR, List.zipWith_cons_cons] at *
      rw [msr_point a b, ih r (by simp only [List.length_cons] at h; omega)]

/-! ## Width bookkeeping (the `b+1` side channel) -/

/-- The side channel of `b`-bit audio fits `b+1` bits. -/
theorem side_fits (b : Nat) (x y : Int)
    (hx : FitsSInt b x) (hy : FitsSInt b y) : FitsSInt (b + 1) (x - y) := by
  unfold FitsSInt at *
  have h2 : (2 ^ (b + 1) : Nat) = 2 ^ b * 2 := Nat.pow_succ ..
  omega

/-- The mid channel of `b`-bit audio fits `b` bits. -/
theorem mid_fits (b : Nat) (x y : Int)
    (hx : FitsSInt b x) (hy : FitsSInt b y) : FitsSInt b (sar (x + y) 1) := by
  have hp := two_mul_sar_one (x + y)
  unfold FitsSInt at *
  omega

@[simp] theorem length_side (l r : List Int) :
    (side l r).length = min l.length r.length := by simp [side]

@[simp] theorem length_mid (l r : List Int) :
    (mid l r).length = min l.length r.length := by simp [mid]

end Flac.Stereo

/-! ## Array forms compute the list forms -/

namespace Flac.Stereo

@[simp] theorem decodeLSA_toList (l s : Array Int) :
    (decodeLSA l s).toList = decodeLS l.toList s.toList := by
  simp [decodeLSA, decodeLS]

@[simp] theorem decodeRSA_toList (s r : Array Int) :
    (decodeRSA s r).toList = decodeRS s.toList r.toList := by
  simp [decodeRSA, decodeRS]

@[simp] theorem decodeMSLA_toList (m s : Array Int) :
    (decodeMSLA m s).toList = decodeMSL m.toList s.toList := by
  simp [decodeMSLA, decodeMSL]

@[simp] theorem decodeMSRA_toList (m s : Array Int) :
    (decodeMSRA m s).toList = decodeMSR m.toList s.toList := by
  simp [decodeMSRA, decodeMSR]

end Flac.Stereo
