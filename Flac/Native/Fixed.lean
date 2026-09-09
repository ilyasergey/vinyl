import Flac.Native.Bits

/-!
# Fixed predictors, orders 0–4 (RFC 9639 §9.2.4)

The order-`n` fixed-predictor residual (with the alternating-binomial
coefficients from the RFC) is exactly the `n`-th finite difference of the
sample sequence, so it is defined here by iterating first differences —
which is what makes the L3 restore proof (`Flac.Spec.Fixed`) a clean
induction. Orders above 4 never appear in streams (the subframe header
cannot express them), but the definitions and proofs are uniform in `ord`.
-/

namespace Flac.Fixed

/-- First differences: `diff1 [x₀, x₁, …] = [x₁ - x₀, x₂ - x₁, …]`. -/
def diff1 : List Int → List Int
  | x :: y :: t => (y - x) :: diff1 (y :: t)
  | _ => []

/-- `diff1` with the differences accumulated, so the recursive call is in tail
    position: the residual length is the block size, which the unchecked encoder
    lets grow without bound, so the cons-after-return form kept one native stack
    frame per sample (audit finding C04 — `fuzz/findings/encoder-stack-overflow-CONFIRMED`;
    the encode-side residual analogue of the
    per-frame `writeFrames`/`chunkChannels` swaps). -/
def diff1Acc (acc : List Int) : List Int → List Int
  | x :: y :: t => diff1Acc ((y - x) :: acc) (y :: t)
  | _ => acc.reverse

theorem diff1Acc_eq (acc : List Int) (xs : List Int) :
    diff1Acc acc xs = acc.reverse ++ diff1 xs := by
  induction xs using diff1.induct generalizing acc with
  | case1 x y t ih => rw [diff1Acc, diff1, ih ((y - x) :: acc)]; simp
  | case2 xs => cases xs <;> simp [diff1Acc, diff1]

def diff1TR (xs : List Int) : List Int := diff1Acc [] xs

/-- Swap the compiled `diff1` for the tail form; every theorem keeps the
    structural definition via the kernel. -/
@[csimp] theorem diff1_eq_diff1TR : @diff1 = @diff1TR := by
  funext xs
  unfold diff1TR
  rw [diff1Acc_eq]
  simp

/-- `n`-th differences. -/
def diffN : Nat → List Int → List Int
  | 0, xs => xs
  | n + 1, xs => diff1 (diffN n xs)

/-- Fixed-predictor residual of order `ord`. Length `xs.length - ord`;
    the first `ord` samples are transmitted verbatim as warmup. -/
def residual (ord : Nat) (xs : List Int) : List Int :=
  diffN ord xs

/-- Undo one differencing step, given the first sample of the target. -/
def undiff1 (x0 : Int) : List Int → List Int
  | [] => [x0]
  | d :: ds => x0 :: undiff1 (x0 + d) ds

/-- Restore samples from `ord` warmup samples and an order-`ord` residual,
    reduced to `b`-bit two's complement (RFC-conformant fixed-width wrap).

    The wrap is a single pointwise pass at the end: every step of the
    undifferencing chain is an addition, and addition commutes with taking
    residues mod `2^b`, so wrapping only the final values computes exactly
    what a register decoder wrapping at every step would. On any stream
    the encoder produced the samples fit `b` bits and the wrap is the
    identity (`Flac.Spec.Fixed.restore_residual` carries the hypothesis). -/
def restore (b : Nat) : (ord : Nat) → (warmup : List Int) → (res : List Int) → List Int
  | 0, _, res => res.map (Bits.wrapSInt b)
  | ord + 1, warmup, res =>
    restore b ord (warmup.take ord) (undiff1 ((diffN ord warmup).headD 0) res)

/-! ### Array forms (the production decoder's hot path)

Residuals arrive as an `Array Int`; the undifferencing passes run as array
folds and are proven equal to the list forms in `Flac.Spec.Fixed`
(`restoreA_toList`). The tiny warmup stays a list. -/

/-- `undiff1` over an array residual: running prefix sums pushed after
    `x0`. -/
def undiffA (x0 : Int) (ds : Array Int) : Array Int :=
  ds.foldl (fun out d => out.push (out.getD (out.size - 1) 0 + d))
    ((Array.emptyWithCapacity (ds.size + 1)).push x0)

/-- `restore` with the residual (and result) as arrays. The final wrap
    pass runs in place when the array is uniquely owned (it always is on
    the decode path). -/
def restoreA (b : Nat) : (ord : Nat) → (warmup : List Int) → (res : Array Int) → Array Int
  | 0, _, res => res.map (Bits.wrapSInt b)
  | ord + 1, warmup, res =>
    restoreA b ord (warmup.take ord) (undiffA ((diffN ord warmup).headD 0) res)

/-! ### The machine-word restore kernel

`restoreA` above is what the theorems read; what the decoder *runs* is
`restoreFast` below, swapped in by `restoreA_eq_restoreFast` (`@[csimp]`).

Every undifferencing pass is a running sum, and the final `wrapSInt b`
reads only the residue mod `2^b`. Addition commutes with reduction mod
`2^64`, and `2^b ∣ 2^64` for every depth the wrap can be asked for, so the
passes may run on machine words that silently wrap — no bound on the
residual, the warmup or the intermediate sums is needed, only `b ≤ 63` so
the wrap's range test has a word-sized threshold. The bridging invariant is
elementwise congruence mod `2^64` (`Cong`). -/

/-- `Bits.wrapSInt b x` read off the residue of `x` mod `2^64`: in range it
    is that residue, otherwise the exact wrap (`wrap64_eq`). -/
@[inline] def wrap64 (b : Nat) (negP P : Int64) (x : Int) : Int :=
  let y := x.toInt64
  if negP ≤ y ∧ y < P then y.toInt else Bits.wrapSInt b x

/-- `undiffA`'s running sum on machine words. -/
def undiff64Go (ds : Array Int) : (i : Nat) → (last : Int64) → Array Int → Array Int
  | i, last, out =>
    if h : i < ds.size then
      let x := last + (ds[i]).toInt64
      undiff64Go ds (i + 1) x (out.push x.toInt)
    else out
  termination_by i => ds.size - i

/-- `undiffA` on machine words (congruent to it mod `2^64`, `undiff64_cong`). -/
def undiff64 (x0 : Int) (ds : Array Int) : Array Int :=
  undiff64Go ds 0 x0.toInt64 ((Array.emptyWithCapacity (ds.size + 1)).push x0)

def restoreFastGo (b : Nat) (negP P : Int64) :
    (ord : Nat) → (warmup : List Int) → (res : Array Int) → Array Int
  | 0, _, res => res.map (wrap64 b negP P)
  | ord + 1, warmup, res =>
    restoreFastGo b negP P ord (warmup.take ord) (undiff64 ((diffN ord warmup).headD 0) res)

/-- `restoreA` verbatim: the swap's fallback must not be the swapped name. -/
def restoreSlowGo (b : Nat) : (ord : Nat) → (warmup : List Int) → (res : Array Int) → Array Int
  | 0, _, res => res.map (Bits.wrapSInt b)
  | ord + 1, warmup, res =>
    restoreSlowGo b ord (warmup.take ord) (undiffA ((diffN ord warmup).headD 0) res)

/-- `restoreA` with the machine-word passes for every depth up to 63. -/
def restoreFast (b ord : Nat) (warmup : List Int) (res : Array Int) : Array Int :=
  if 1 ≤ b ∧ b ≤ 63 then
    let P : Int64 := Int64.ofNat (Bits.p2 (b - 1))
    restoreFastGo b (-P) P ord warmup res
  else restoreSlowGo b ord warmup res

/-! #### The kernel computes the fold -/

theorem wrap64_eq (b : Nat) (hb0 : 1 ≤ b) (hb : b ≤ 63) (x : Int) :
    wrap64 b (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))) x
      = Bits.wrapSInt b x := by
  have hpow : Bits.p2 (b - 1) < 2 ^ 63 := by
    rw [Bits.p2_eq]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hPv : (Int64.ofNat (Bits.p2 (b - 1))).toInt = ((Bits.p2 (b - 1) : Nat) : Int) :=
    Int64.toInt_ofNat_of_lt hpow
  have hnegP : (-(Int64.ofNat (Bits.p2 (b - 1)))).toInt = -((Bits.p2 (b - 1) : Nat) : Int) :=
    Int64.toInt_neg_ofNat_of_le (Nat.le_of_lt hpow)
  have hsize : Int64.size = 2 ^ 64 := rfl
  have hy : x.toInt64.toInt = x.bmod (2 ^ 64) := by rw [Int.toInt64, Int64.toInt_ofInt, hsize]
  unfold wrap64
  simp only []
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

/-- Elementwise congruence mod `2^64`. -/
def Cong (a b : Array Int) : Prop :=
  a.size = b.size ∧ ∀ (i : Nat) (h : i < a.size) (h' : i < b.size),
    a[i].bmod (2 ^ 64) = b[i].bmod (2 ^ 64)

theorem Cong.refl (a : Array Int) : Cong a a := ⟨rfl, fun _ _ _ => rfl⟩

theorem map_wrap64_of_cong (b : Nat) (hb0 : 1 ≤ b) (hb : b ≤ 63) (a a' : Array Int)
    (hc : Cong a a') :
    a.map (wrap64 b (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1))))
      = a'.map (Bits.wrapSInt b) := by
  obtain ⟨hsz, hel⟩ := hc
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    simp only [Array.size_map] at h1 h2
    simp only [Array.getElem_map]
    rw [wrap64_eq b hb0 hb, Bits.wrapSInt_eq_bmod, Bits.wrapSInt_eq_bmod,
      ← Int.bmod_bmod_of_dvd (a := a[i]) (Nat.pow_dvd_pow 2 (show b ≤ 64 by omega)),
      ← Int.bmod_bmod_of_dvd (a := a'[i]) (Nat.pow_dvd_pow 2 (show b ≤ 64 by omega)),
      hel i h1 h2]

/-- `Array.foldl` as an index loop, for relating the pushes to a walk. -/
def goF (f : Array Int → Int → Array Int) (as : Array Int) : (i : Nat) → Array Int → Array Int
  | i, acc => if h : i < as.size then goF f as (i + 1) (f acc as[i]) else acc
  termination_by i => as.size - i

theorem foldl_eq_goF (f : Array Int → Int → Array Int) (as : Array Int) :
    ∀ (n i : Nat) (acc : Array Int), as.size - i = n →
      (as.toList.drop i).foldl f acc = goF f as i acc := by
  intro n
  induction n with
  | zero =>
    intro i acc hn
    rw [goF, dif_neg (by omega), List.drop_eq_nil_of_le (by simpa using (by omega : as.size ≤ i))]
    rfl
  | succ n ih =>
    intro i acc hn
    have hi : i < as.size := by omega
    rw [goF, dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi), List.foldl_cons,
      Array.getElem_toList, ih (i + 1) _ (by omega)]

theorem undiffA_eq_goF (x0 : Int) (ds : Array Int) :
    undiffA x0 ds = goF (fun out d => out.push (out.getD (out.size - 1) 0 + d)) ds 0 #[x0] := by
  unfold undiffA
  rw [← Array.foldl_toList, ← foldl_eq_goF _ ds ds.size 0 _ rfl, List.drop_zero,
    Array.emptyWithCapacity_eq]
  rfl

private theorem undiff64Go_cong (ds ds' : Array Int) (hds : Cong ds ds') :
    ∀ (n i : Nat) (last : Int64) (out out' : Array Int), ds.size - i = n →
      Cong out out' → 0 < out.size →
      last.toInt = (out'.getD (out'.size - 1) 0).bmod (2 ^ 64) →
      Cong (undiff64Go ds i last out)
        (goF (fun out d => out.push (out.getD (out.size - 1) 0 + d)) ds' i out') := by
  obtain ⟨hdsz, hdel⟩ := hds
  intro n
  induction n with
  | zero =>
    intro i last out out' hn hc _ _
    rw [undiff64Go, dif_neg (by omega), goF, dif_neg (by omega)]
    exact hc
  | succ n ih =>
    intro i last out out' hn hc hpos hlast
    have hi : i < ds.size := by omega
    have hi' : i < ds'.size := by omega
    rw [undiff64Go, dif_pos hi, goF, dif_pos hi']
    obtain ⟨hsz, hel⟩ := hc
    have hsize : Int64.size = 2 ^ 64 := rfl
    have hx : (last + (ds[i]).toInt64).toInt
        = (out'.getD (out'.size - 1) 0 + ds'[i]).bmod (2 ^ 64) := by
      rw [Int64.toInt_add, hlast, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_add_bmod,
        Int.add_bmod_bmod, Int.add_bmod, hdel i hi hi', ← Int.add_bmod]
    apply ih (i + 1) _ _ _ (by omega)
    · refine ⟨by simp [hsz], ?_⟩
      intro j hj hj'
      simp only [Array.size_push] at hj hj'
      rcases Nat.lt_or_ge j out.size with hlt | hge
      · rw [Array.getElem_push_lt hlt, Array.getElem_push_lt (by omega)]
        exact hel j hlt (by omega)
      · have hj0 : j = out.size := by omega
        subst hj0
        rw [Array.getElem_push, Array.getElem_push, dif_neg (by omega), dif_neg (by omega), hx,
          Int.bmod_bmod]
    · simp
    · rw [hx]
      simp [Array.getD]

theorem undiff64_cong (x0 : Int) (ds ds' : Array Int) (hds : Cong ds ds') :
    Cong (undiff64 x0 ds) (undiffA x0 ds') := by
  rw [undiffA_eq_goF]
  unfold undiff64
  rw [Array.emptyWithCapacity_eq]
  apply undiff64Go_cong ds ds' hds ds.size 0 _ _ _ rfl (Cong.refl _) (by simp)
  simp [Int64.toInt_ofInt, Array.getD]

theorem restoreFastGo_eq (b : Nat) (hb0 : 1 ≤ b) (hb : b ≤ 63) :
    ∀ (ord : Nat) (warmup : List Int) (res res' : Array Int), Cong res res' →
      restoreFastGo b (-(Int64.ofNat (Bits.p2 (b - 1)))) (Int64.ofNat (Bits.p2 (b - 1)))
          ord warmup res
        = restoreSlowGo b ord warmup res' := by
  intro ord
  induction ord with
  | zero =>
    intro warmup res res' hc
    exact map_wrap64_of_cong b hb0 hb res res' hc
  | succ ord ih =>
    intro warmup res res' hc
    exact ih (warmup.take ord) _ _ (undiff64_cong _ res res' hc)

theorem restoreSlowGo_eq (b : Nat) :
    ∀ (ord : Nat) (warmup : List Int) (res : Array Int),
      restoreSlowGo b ord warmup res = restoreA b ord warmup res := by
  intro ord
  induction ord with
  | zero => intros; rfl
  | succ ord ih => intro warmup res; exact ih _ _

/-- **The kernel computes the fold.** -/
@[csimp] theorem restoreA_eq_restoreFast : @restoreA = @restoreFast := by
  funext b ord warmup res
  unfold restoreFast
  split
  · next h =>
    rw [restoreFastGo_eq b h.1 h.2 ord warmup res res (Cong.refl res), restoreSlowGo_eq]
  · rw [restoreSlowGo_eq]

end Flac.Fixed
