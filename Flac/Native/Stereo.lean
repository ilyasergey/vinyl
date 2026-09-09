import Flac.Native.Bits

/-!
# Stereo decorrelation (RFC 9639 §4.2, §9.1.3)

Left/side, right/side, and mid/side transforms. The side channel is
`L - R` (needs one extra bit of depth — the `b+1` bookkeeping at L5);
mid is `(L + R) >>ₐ 1`, recoverable exactly because `L+R` and `L-R`
share parity.

Decoding follows libFLAC's formulation: reconstruct `2·mid + parity(side)`
= `L + R`, then halve `(L+R) ± (L-R)` with an arithmetic shift.
-/

namespace Flac.Stereo

open Flac.Bits (sar)

/-- Side channel: `L - R`. -/
def side (l r : List Int) : List Int :=
  List.zipWith (fun a b => a - b) l r

/-- Mid channel: `(L + R) >>ₐ 1`. -/
def mid (l r : List Int) : List Int :=
  List.zipWith (fun a b => sar (a + b) 1) l r

/-- Left/side decode: `R = L - S`. -/
def decodeLS (b : Nat) (l s : List Int) : List Int :=
  List.zipWith (fun a v => Bits.wrapSInt b (a - v)) l s

/-- Right/side decode: `L = R + S`. -/
def decodeRS (b : Nat) (s r : List Int) : List Int :=
  List.zipWith (fun v rr => Bits.wrapSInt b (rr + v)) s r

/-- Mid/side decode, left: `L = (2·M + parity(S) + S) >>ₐ 1`. -/
def decodeMSL (b : Nat) (m s : List Int) : List Int :=
  List.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)) m s

/-- Mid/side decode, right: `R = (2·M + parity(S) - S) >>ₐ 1`. -/
def decodeMSR (b : Nat) (m s : List Int) : List Int :=
  List.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)) m s

/-! ### Array forms (the production codec's hot paths; proven equal to
the list forms in `Flac.Spec.Stereo`) -/

/-- Side channel over arrays: `L - R`. -/
def sideA (l r : Array Int) : Array Int :=
  Array.zipWith (fun a b => a - b) l r

/-- Mid channel over arrays: `(L + R) >>ₐ 1`. -/
def midA (l r : Array Int) : Array Int :=
  Array.zipWith (fun a b => sar (a + b) 1) l r

def decodeLSA (b : Nat) (l s : Array Int) : Array Int :=
  Array.zipWith (fun a v => Bits.wrapSInt b (a - v)) l s

def decodeRSA (b : Nat) (s r : Array Int) : Array Int :=
  Array.zipWith (fun v rr => Bits.wrapSInt b (rr + v)) s r

def decodeMSLA (b : Nat) (m s : Array Int) : Array Int :=
  Array.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)) m s

def decodeMSRA (b : Nat) (m s : Array Int) : Array Int :=
  Array.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)) m s

/-- Both mid/side outputs, `[left, right]` — what the frame reader consumes,
    so the kernel can produce them in one pass (`decodeMSA_eq_fast`). -/
def decodeMSA (b : Nat) (m s : Array Int) : List (Array Int) :=
  [decodeMSLA b m s, decodeMSRA b m s]

/-! ### The machine-word decorrelation kernels

`decodeLSA`/`decodeRSA`/`decodeMSLA`/`decodeMSRA` above are what the
theorems read; the decoder runs the `…Fast` twins below (`@[csimp]`). Each
is the same `zipWith` with the per-sample function on `Int64`: the sum or
difference is exact mod `2^64`, which is all the final `wrapSInt` reads
(`2^b ∣ 2^64`), so the side modes need no bound at all; the mid modes shift
after adding, which does not commute with wraparound, so they test the two
inputs against `2^30` first and fall back to the exact form otherwise (a
16- or 24-bit stream never does). The range test is written out at each
use rather than shared through a helper, so the exact fallback is only
computed on the branch that needs it. -/

/-- The wrap read off a machine word: when `y` is `x` mod `2^64` and in
    range, `y` is `wrapSInt b x` (`1 ≤ b ≤ 63`). -/
theorem wrap_if_eq (b : Nat) (hb0 : 1 ≤ b) (hb : b ≤ 63) (x : Int) (y : Int64)
    (hy : y.toInt = x.bmod (2 ^ 64)) :
    (if -(Int64.ofNat (Bits.p2 (b - 1))) ≤ y ∧ y < Int64.ofNat (Bits.p2 (b - 1)) then y.toInt
      else Bits.wrapSInt b x) = Bits.wrapSInt b x := by
  have hpow : Bits.p2 (b - 1) < 2 ^ 63 := by
    rw [Bits.p2_eq]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hPv : (Int64.ofNat (Bits.p2 (b - 1))).toInt = ((Bits.p2 (b - 1) : Nat) : Int) :=
    Int64.toInt_ofNat_of_lt hpow
  have hnegP : (-(Int64.ofNat (Bits.p2 (b - 1)))).toInt = -((Bits.p2 (b - 1) : Nat) : Int) :=
    Int64.toInt_neg_ofNat_of_le (Nat.le_of_lt hpow)
  split
  · next hin =>
    obtain ⟨h1, h2⟩ := hin
    rw [Int64.le_iff_toInt_le, hnegP, hy] at h1
    rw [Int64.lt_iff_toInt_lt, hPv, hy] at h2
    rw [hy, Bits.wrapSInt_eq_bmod,
      ← Int.bmod_bmod_of_dvd (a := x) (Nat.pow_dvd_pow 2 (show b ≤ 64 by omega))]
    symm
    have hb2 : (2 ^ b : Nat) = 2 * Bits.p2 (b - 1) := by
      rw [Bits.p2_eq, ← Nat.pow_succ']
      congr 1
      omega
    rw [hb2]
    generalize Bits.p2 (b - 1) = Q at h1 h2 ⊢
    apply Int.bmod_eq_of_le
    · have : ((2 * Q : Nat) : Int) / 2 = (Q : Int) := by omega
      omega
    · have : (((2 * Q : Nat) : Int) + 1) / 2 = (Q : Int) := by omega
      omega
  · rfl

/-- `2·m + s % 2 + s` on machine words; exact for `|m|, |s| < 2^30`
    (`s % 2 = s - 2·(s >>> 1)` keeps it to shifts and adds). -/
@[inline] def midSum64 (m s : Int64) : Int64 :=
  m + m + (s - (s >>> 1) - (s >>> 1)) + s

private theorem hsize : Int64.size = 2 ^ 64 := rfl

theorem midSum64_toInt (m s : Int) (hm : Bits.small31 m = true) (hs : Bits.small31 s = true) :
    (midSum64 m.toInt64 s.toInt64).toInt = 2 * m + s % 2 + s := by
  have hm' := Bits.toInt_toInt64_of_small31 hm
  have hs' := Bits.toInt_toInt64_of_small31 hs
  have hb := hm
  have hb2 := hs
  simp only [Bits.small31, decide_eq_true_eq] at hb hb2
  have hsh : (s.toInt64 >>> 1).toInt = s / 2 := by
    rw [show (1 : Int64) = Int64.ofNat 1 from rfl, Bits.toInt_shiftRight_ofNat _ _ (by decide),
      hs', Int.shiftRight_eq_div_pow]
    rfl
  unfold midSum64
  simp only [Int64.toInt_add, Int64.toInt_sub, hm', hs', hsh, Int.bmod_add_bmod,
    Int.add_bmod_bmod, Int.bmod_sub_bmod, Int.sub_bmod_bmod]
  rw [show m + m + (s - s / 2 - s / 2) + s = 2 * m + s % 2 + s by omega]
  apply Int.bmod_eq_of_le <;> omega

theorem sub64_bmod (a v : Int) : (a.toInt64 - v.toInt64).toInt = (a - v).bmod (2 ^ 64) := by
  simp only [Int64.toInt_sub, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod, Int.sub_bmod_bmod]

theorem add64_bmod (a v : Int) : (a.toInt64 + v.toInt64).toInt = (a + v).bmod (2 ^ 64) := by
  simp only [Int64.toInt_add, Int64.toInt_ofInt, hsize, Int.bmod_add_bmod, Int.add_bmod_bmod]

/-! #### The zips as loops with the bounds hoisted

`Array.zipWith` with the per-sample function written inline recomputed the
range bound `±2^(b-1)` — a `Nat` subtraction, a table lookup and two
`UInt64` conversions — on every sample, because the closure's free
variables are re-evaluated per call. `zipGo` takes the bounds as `Int64`
*parameters* and threads them into the element function, so they are
computed once per subframe; `zip2Go` produces both mid/side outputs in one
pass over the inputs. Both are equal to the plain `zipWith` (`zipGo_eq`,
`zip2Go_fst`, `zip2Go_snd`). -/

@[specialize] private def zipGo (f : Int64 → Int64 → Int → Int → Int) (negP P : Int64)
    (as bs : Array Int) (n : Nat) : (i : Nat) → Array Int → Array Int
  | i, out =>
    if h : i < n then
      zipGo f negP P as bs n (i + 1) (out.push (f negP P (as.getD i 0) (bs.getD i 0)))
    else out
  termination_by i => n - i

@[specialize] def zip2Go (f g : Int64 → Int64 → Int → Int → Int) (negP P : Int64)
    (as bs : Array Int) (n : Nat) : (i : Nat) → Array Int → Array Int → Array Int × Array Int
  | i, l, r =>
    if h : i < n then
      let a := as.getD i 0
      let b := bs.getD i 0
      zip2Go f g negP P as bs n (i + 1) (l.push (f negP P a b)) (r.push (g negP P a b))
    else (l, r)
  termination_by i => n - i

theorem zipGo_size (f : Int64 → Int64 → Int → Int → Int) (negP P : Int64) (as bs : Array Int)
    (n : Nat) : ∀ (m i : Nat) (out : Array Int), n - i = m →
      (zipGo f negP P as bs n i out).size = out.size + (n - i) := by
  intro m
  induction m with
  | zero => intro i out hm; rw [zipGo, dif_neg (by omega)]; omega
  | succ m ih =>
    intro i out hm
    rw [zipGo, dif_pos (by omega), ih (i + 1) _ (by omega), Array.size_push]
    omega

theorem zipGo_get (f : Int64 → Int64 → Int → Int → Int) (negP P : Int64) (as bs : Array Int)
    (n : Nat) : ∀ (m i : Nat) (out : Array Int), n - i = m →
      ∀ (k : Nat) (hk : k < (zipGo f negP P as bs n i out).size),
        (zipGo f negP P as bs n i out)[k]
          = if h : k < out.size then out[k]
            else f negP P (as.getD (i + (k - out.size)) 0) (bs.getD (i + (k - out.size)) 0) := by
  intro m
  induction m with
  | zero =>
    intro i out hm k hk
    have hsz := zipGo_size f negP P as bs n 0 i out hm
    have hk' : k < out.size := by rw [hsz] at hk; omega
    have heq : zipGo f negP P as bs n i out = out := by rw [zipGo, dif_neg (by omega)]
    rw [dif_pos hk']
    simp only [heq]
  | succ m ih =>
    intro i out hm k hk
    have heq : zipGo f negP P as bs n i out
        = zipGo f negP P as bs n (i + 1) (out.push (f negP P (as.getD i 0) (bs.getD i 0))) := by
      rw [zipGo, dif_pos (by omega)]
    simp only [heq]
    rw [ih (i + 1) _ (by omega) k]
    simp only [Array.getElem_push, Array.size_push]
    by_cases hko : k < out.size
    · rw [dif_pos (by omega), dif_pos hko, dif_pos hko]
    · rw [dif_neg hko]
      by_cases hk1 : k < out.size + 1
      · rw [dif_pos hk1, dif_neg hko]
        have h0 : k - out.size = 0 := by omega
        rw [h0, Nat.add_zero]
      · rw [dif_neg hk1]
        have h1 : i + 1 + (k - (out.size + 1)) = i + (k - out.size) := by omega
        rw [h1, dif_neg hko]

/-- **The loop is the zip.** -/
theorem zipGo_eq (f : Int64 → Int64 → Int → Int → Int) (negP P : Int64) (as bs : Array Int) :
    zipGo f negP P as bs (min as.size bs.size) 0 #[] = Array.zipWith (f negP P) as bs := by
  apply Array.ext
  · rw [zipGo_size f negP P as bs _ _ 0 #[] rfl, Array.size_zipWith]
    simp
  · intro k hk hk'
    rw [zipGo_get f negP P as bs _ _ 0 #[] rfl k hk, Array.getElem_zipWith]
    have hk2 : k < min as.size bs.size := by rwa [Array.size_zipWith] at hk'
    rw [dif_neg (by simp)]
    simp only [Array.size_empty, Nat.zero_add, Nat.sub_zero]
    unfold Array.getD
    rw [dif_pos (by omega), dif_pos (by omega)]
    rfl

theorem zip2Go_fst (f g : Int64 → Int64 → Int → Int → Int) (negP P : Int64) (as bs : Array Int)
    (n : Nat) : ∀ (m i : Nat) (l r : Array Int), n - i = m →
      (zip2Go f g negP P as bs n i l r).1 = zipGo f negP P as bs n i l := by
  intro m
  induction m with
  | zero => intro i l r hm; rw [zip2Go, zipGo, dif_neg (by omega), dif_neg (by omega)]
  | succ m ih =>
    intro i l r hm
    rw [zip2Go, zipGo, dif_pos (by omega), dif_pos (by omega)]
    exact ih (i + 1) _ _ (by omega)

theorem zip2Go_snd (f g : Int64 → Int64 → Int → Int → Int) (negP P : Int64) (as bs : Array Int)
    (n : Nat) : ∀ (m i : Nat) (l r : Array Int), n - i = m →
      (zip2Go f g negP P as bs n i l r).2 = zipGo g negP P as bs n i r := by
  intro m
  induction m with
  | zero => intro i l r hm; rw [zip2Go, zipGo, dif_neg (by omega), dif_neg (by omega)]
  | succ m ih =>
    intro i l r hm
    rw [zip2Go, zipGo, dif_pos (by omega), dif_pos (by omega)]
    exact ih (i + 1) _ _ (by omega)

/-- Left from left/side, on machine words. -/
@[inline] def lsElem (b : Nat) (negP P : Int64) (a v : Int) : Int :=
  let y := a.toInt64 - v.toInt64
  if negP ≤ y ∧ y < P then y.toInt else Bits.wrapSInt b (a - v)

/-- Left from side/right, on machine words. -/
@[inline] def rsElem (b : Nat) (negP P : Int64) (v rr : Int) : Int :=
  let y := rr.toInt64 + v.toInt64
  if negP ≤ y ∧ y < P then y.toInt else Bits.wrapSInt b (rr + v)

/-- Left from mid/side, on machine words (exact fallback outside `2^30`). -/
@[inline] def msLElem (b : Nat) (negP P : Int64) (mm ss : Int) : Int :=
  if Bits.small31 mm ∧ Bits.small31 ss then
    let y := midSum64 mm.toInt64 ss.toInt64 >>> 1
    if negP ≤ y ∧ y < P then y.toInt else Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)
  else Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)

/-- Right from mid/side, on machine words. -/
@[inline] def msRElem (b : Nat) (negP P : Int64) (mm ss : Int) : Int :=
  if Bits.small31 mm ∧ Bits.small31 ss then
    let y := (midSum64 mm.toInt64 ss.toInt64 - ss.toInt64 - ss.toInt64) >>> 1
    if negP ≤ y ∧ y < P then y.toInt else Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)
  else Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)

def decodeLSAFast (b : Nat) (l s : Array Int) : Array Int :=
  if 1 ≤ b ∧ b ≤ 63 then
    zipGo (lsElem b) (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))) l s
      (min l.size s.size) 0 (Array.emptyWithCapacity (min l.size s.size))
  else Array.zipWith (fun a v => Bits.wrapSInt b (a - v)) l s

def decodeRSAFast (b : Nat) (s r : Array Int) : Array Int :=
  if 1 ≤ b ∧ b ≤ 63 then
    zipGo (rsElem b) (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))) s r
      (min s.size r.size) 0 (Array.emptyWithCapacity (min s.size r.size))
  else Array.zipWith (fun v rr => Bits.wrapSInt b (rr + v)) s r

def decodeMSLAFast (b : Nat) (m s : Array Int) : Array Int :=
  if 1 ≤ b ∧ b ≤ 63 then
    zipGo (msLElem b) (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))) m s
      (min m.size s.size) 0 (Array.emptyWithCapacity (min m.size s.size))
  else Array.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 + ss) 1)) m s

def decodeMSRAFast (b : Nat) (m s : Array Int) : Array Int :=
  if 1 ≤ b ∧ b ≤ 63 then
    zipGo (msRElem b) (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))) m s
      (min m.size s.size) 0 (Array.emptyWithCapacity (min m.size s.size))
  else Array.zipWith (fun mm ss => Bits.wrapSInt b (sar (2 * mm + ss % 2 - ss) 1)) m s

/-- Both mid/side channels in one pass. The fallback names the `…Fast`
    twins, never the swapped `decodeMSLA`/`decodeMSRA`. -/
def decodeMSAFast (b : Nat) (m s : Array Int) : List (Array Int) :=
  if 1 ≤ b ∧ b ≤ 63 then
    let p := zip2Go (msLElem b) (msRElem b) (-(Int64.ofNat (Bits.p2 (b - 1))))
      (Int64.ofNat (Bits.p2 (b - 1))) m s (min m.size s.size) 0
      (Array.emptyWithCapacity (min m.size s.size)) (Array.emptyWithCapacity (min m.size s.size))
    [p.1, p.2]
  else [decodeMSLAFast b m s, decodeMSRAFast b m s]

/-! #### The kernels compute the zips -/

@[csimp] theorem decodeLSA_eq_fast : @decodeLSA = @decodeLSAFast := by
  funext b l s
  unfold decodeLSA decodeLSAFast
  split
  · next h =>
    rw [Array.emptyWithCapacity_eq, zipGo_eq]
    congr 1
    funext a v
    unfold lsElem
    exact (wrap_if_eq b h.1 h.2 _ _ (sub64_bmod a v)).symm
  · rfl

@[csimp] theorem decodeRSA_eq_fast : @decodeRSA = @decodeRSAFast := by
  funext b s r
  unfold decodeRSA decodeRSAFast
  split
  · next h =>
    rw [Array.emptyWithCapacity_eq, zipGo_eq]
    congr 1
    funext v rr
    unfold rsElem
    exact (wrap_if_eq b h.1 h.2 _ _ (add64_bmod rr v)).symm
  · rfl

@[csimp] theorem decodeMSLA_eq_fast : @decodeMSLA = @decodeMSLAFast := by
  funext b m s
  unfold decodeMSLA decodeMSLAFast
  split
  · next h =>
    rw [Array.emptyWithCapacity_eq, zipGo_eq]
    congr 1
    funext mm ss
    unfold msLElem
    split
    · next hsm =>
      obtain ⟨hm, hs⟩ := hsm
      have hb := hm
      have hb2 := hs
      simp only [Bits.small31, decide_eq_true_eq] at hb hb2
      have hx : (midSum64 mm.toInt64 ss.toInt64 >>> 1).toInt = sar (2 * mm + ss % 2 + ss) 1 := by
        rw [show (1 : Int64) = Int64.ofNat 1 from rfl, Bits.toInt_shiftRight_ofNat _ _ (by decide),
          midSum64_toInt mm ss hm hs, Bits.sar_eq_shiftRight]
      have hbnd : (sar (2 * mm + ss % 2 + ss) 1).bmod (2 ^ 64) = sar (2 * mm + ss % 2 + ss) 1 := by
        rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
        apply Int.bmod_eq_of_le <;> omega
      exact (wrap_if_eq b h.1 h.2 _ _ (by rw [hx, hbnd])).symm
    · rfl
  · rfl

@[csimp] theorem decodeMSRA_eq_fast : @decodeMSRA = @decodeMSRAFast := by
  funext b m s
  unfold decodeMSRA decodeMSRAFast
  split
  · next h =>
    rw [Array.emptyWithCapacity_eq, zipGo_eq]
    congr 1
    funext mm ss
    unfold msRElem
    split
    · next hsm =>
      obtain ⟨hm, hs⟩ := hsm
      have hs' := Bits.toInt_toInt64_of_small31 hs
      have hb := hm
      have hb2 := hs
      simp only [Bits.small31, decide_eq_true_eq] at hb hb2
      have hsum : (midSum64 mm.toInt64 ss.toInt64 - ss.toInt64 - ss.toInt64).toInt
          = 2 * mm + ss % 2 - ss := by
        rw [Int64.toInt_sub, Int64.toInt_sub, midSum64_toInt mm ss hm hs, hs',
          Int.bmod_sub_bmod, show 2 * mm + ss % 2 + ss - ss - ss = 2 * mm + ss % 2 - ss by omega]
        apply Int.bmod_eq_of_le <;> omega
      have hx : ((midSum64 mm.toInt64 ss.toInt64 - ss.toInt64 - ss.toInt64) >>> 1).toInt
          = sar (2 * mm + ss % 2 - ss) 1 := by
        rw [show (1 : Int64) = Int64.ofNat 1 from rfl, Bits.toInt_shiftRight_ofNat _ _ (by decide),
          hsum, Bits.sar_eq_shiftRight]
      have hbnd : (sar (2 * mm + ss % 2 - ss) 1).bmod (2 ^ 64) = sar (2 * mm + ss % 2 - ss) 1 := by
        rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
        apply Int.bmod_eq_of_le <;> omega
      exact (wrap_if_eq b h.1 h.2 _ _ (by rw [hx, hbnd])).symm
    · rfl
  · rfl

/-- **One pass gives both mid/side channels.** -/
@[csimp] theorem decodeMSA_eq_fast : @decodeMSA = @decodeMSAFast := by
  funext b m s
  unfold decodeMSA decodeMSAFast
  rw [decodeMSLA_eq_fast, decodeMSRA_eq_fast]
  unfold decodeMSLAFast decodeMSRAFast
  split
  · simp only [Array.emptyWithCapacity_eq, zip2Go_fst _ _ _ _ _ _ _ _ _ _ _ rfl,
      zip2Go_snd _ _ _ _ _ _ _ _ _ _ _ rfl]
  · rfl

end Flac.Stereo
