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

theorem decodeLS_side (b : Nat) (l r : List Int) (h : l.length = r.length)
    (hfr : ∀ x ∈ r, FitsSInt b x) :
    decodeLS b l (side l r) = r := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | y :: r =>
      simp only [side, decodeLS, List.zipWith_cons_cons] at *
      rw [show a - (a - y) = y by omega,
        wrapSInt_eq_of_fits b y (hfr y (List.mem_cons_self ..)),
        ih r (by simp only [List.length_cons] at h; omega)
          (fun x hx => hfr x (List.mem_cons_of_mem _ hx))]

theorem decodeRS_side (b : Nat) (l r : List Int) (h : l.length = r.length)
    (hfl : ∀ x ∈ l, FitsSInt b x) :
    decodeRS b (side l r) r = l := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | y :: r =>
      simp only [side, decodeRS, List.zipWith_cons_cons] at *
      rw [show y + (a - y) = a by omega,
        wrapSInt_eq_of_fits b a (hfl a (List.mem_cons_self ..)),
        ih r (by simp only [List.length_cons] at h; omega)
          (fun x hx => hfl x (List.mem_cons_of_mem _ hx))]

theorem decodeMSL_mid_side (b : Nat) (l r : List Int) (h : l.length = r.length)
    (hfl : ∀ x ∈ l, FitsSInt b x) :
    decodeMSL b (mid l r) (side l r) = l := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | y :: r =>
      simp only [side, mid, decodeMSL, List.zipWith_cons_cons] at *
      rw [msl_point a y,
        wrapSInt_eq_of_fits b a (hfl a (List.mem_cons_self ..)),
        ih r (by simp only [List.length_cons] at h; omega)
          (fun x hx => hfl x (List.mem_cons_of_mem _ hx))]

theorem decodeMSR_mid_side (b : Nat) (l r : List Int) (h : l.length = r.length)
    (hfr : ∀ x ∈ r, FitsSInt b x) :
    decodeMSR b (mid l r) (side l r) = r := by
  induction l generalizing r with
  | nil =>
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l ih =>
    match r with
    | [] => simp at h
    | y :: r =>
      simp only [side, mid, decodeMSR, List.zipWith_cons_cons] at *
      rw [msr_point a y,
        wrapSInt_eq_of_fits b y (hfr y (List.mem_cons_self ..)),
        ih r (by simp only [List.length_cons] at h; omega)
          (fun x hx => hfr x (List.mem_cons_of_mem _ hx))]

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

@[simp] theorem sideA_toList (l r : Array Int) :
    (sideA l r).toList = side l.toList r.toList := by
  simp [sideA, side]

@[simp] theorem midA_toList (l r : Array Int) :
    (midA l r).toList = mid l.toList r.toList := by
  simp [midA, mid]

@[simp] theorem decodeLSA_toList (b : Nat) (l s : Array Int) :
    (decodeLSA b l s).toList = decodeLS b l.toList s.toList := by
  simp [decodeLSA, decodeLS]

@[simp] theorem decodeRSA_toList (b : Nat) (s r : Array Int) :
    (decodeRSA b s r).toList = decodeRS b s.toList r.toList := by
  simp [decodeRSA, decodeRS]

@[simp] theorem decodeMSLA_toList (b : Nat) (m s : Array Int) :
    (decodeMSLA b m s).toList = decodeMSL b m.toList s.toList := by
  simp [decodeMSLA, decodeMSL]

@[simp] theorem decodeMSRA_toList (b : Nat) (m s : Array Int) :
    (decodeMSRA b m s).toList = decodeMSR b m.toList s.toList := by
  simp [decodeMSRA, decodeMSR]

end Flac.Stereo
