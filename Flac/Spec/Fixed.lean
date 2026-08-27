import Flac.Native.Fixed
import Flac.Spec.Bits

/-!
# L3-fixed proofs — fixed-predictor restore round-trip

Restoring from the warmup
samples and the order-`ord` residual recovers the original samples —
including the decoder's final `b`-bit wrap, which is the identity because
the original samples fit `b` bits. The
proof is an induction on `ord`, peeling one differencing step at a time;
the only interesting ingredients are that `diffN` commutes with `take` and
that `undiff1` inverts `diff1` given the correct first sample.
-/

namespace Flac.Fixed

open Flac.Bits (FitsSInt wrapSInt map_wrapSInt_of_fits)

@[simp] theorem diff1_nil : diff1 [] = [] := rfl
@[simp] theorem diff1_single (x : Int) : diff1 [x] = [] := rfl
theorem diff1_cons_cons (x y : Int) (t : List Int) :
    diff1 (x :: y :: t) = (y - x) :: diff1 (y :: t) := rfl

@[simp] theorem length_diff1 (xs : List Int) :
    (diff1 xs).length = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
    match t with
    | [] => rfl
    | y :: t' => simp only [diff1_cons_cons, List.length_cons] at ih ⊢; omega

@[simp] theorem length_diffN (n : Nat) (xs : List Int) :
    (diffN n xs).length = xs.length - n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [diffN, length_diff1, ih]; omega

/-- `diff1` only looks at the first `m` elements to produce the first
    `m - 1` differences. -/
theorem diff1_take (xs : List Int) (m : Nat) :
    diff1 (xs.take m) = (diff1 xs).take (m - 1) := by
  induction xs generalizing m with
  | nil => simp
  | cons x t ih =>
    match t, m with
    | _, 0 => simp
    | [], m + 1 => simp
    | y :: t', 1 => simp
    | y :: t', m + 2 =>
      simp only [List.take_succ_cons, diff1_cons_cons]
      rw [show m + 2 - 1 = m + 1 by omega, List.take_succ_cons]
      have := ih (m + 1)
      simp only [List.take_succ_cons, Nat.add_sub_cancel] at this
      rw [this]

theorem diffN_take (k : Nat) (xs : List Int) (m : Nat) :
    diffN k (xs.take m) = (diffN k xs).take (m - k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [diffN, ih, diff1_take]
    congr 1

@[simp] theorem headD_take_one (l : List Int) (d : Int) :
    (l.take 1).headD d = l.headD d := by
  cases l <;> rfl

/-- `undiff1` inverts `diff1`, given the head of the original list. -/
theorem undiff1_diff1 (xs : List Int) (h : xs ≠ []) :
    undiff1 (xs.headD 0) (diff1 xs) = xs := by
  induction xs with
  | nil => contradiction
  | cons x t ih =>
    match t with
    | [] => rfl
    | y :: t' =>
      rw [diff1_cons_cons]
      show x :: undiff1 (x + (y - x)) (diff1 (y :: t')) = x :: y :: t'
      rw [show x + (y - x) = y by omega]
      have := ih (by simp)
      simp only [List.headD_cons] at this
      rw [this]

/-- **L3-fixed keystone**:
    fixed-predictor decode inverts encode for every order, for every
    block whose samples fit the bit depth (which is when the decoder's
    wrap is the identity). -/
theorem restore_residual (b ord : Nat) (xs : List Int) (h : ord ≤ xs.length)
    (hfit : ∀ x ∈ xs, FitsSInt b x) :
    restore b ord (xs.take ord) (residual ord xs) = xs := by
  induction ord with
  | zero => exact map_wrapSInt_of_fits b xs hfit
  | succ ord ih =>
    have hne : diffN ord xs ≠ [] := by
      intro hc
      have hl := length_diffN ord xs
      rw [hc] at hl
      simp only [List.length_nil] at hl
      omega
    show restore b ord ((xs.take (ord + 1)).take ord)
      (undiff1 ((diffN ord (xs.take (ord + 1))).headD 0) (diff1 (diffN ord xs))) = xs
    rw [List.take_take, Nat.min_eq_left (by omega),
      diffN_take ord xs (ord + 1), show ord + 1 - ord = 1 by omega,
      headD_take_one, undiff1_diff1 _ hne]
    exact ih (by omega)

/-! ## Array forms compute the list forms -/

private theorem foldl_undiff :
    ∀ (l : List Int) (pre : Array Int) (x : Int),
      (l.foldl (fun out d => out.push (out.getD (out.size - 1) 0 + d))
        (pre.push x)).toList = pre.toList ++ undiff1 x l := by
  intro l
  induction l with
  | nil => intro pre x; simp [undiff1]
  | cons d ds ih =>
    intro pre x
    show (ds.foldl _ ((pre.push x).push ((pre.push x).getD ((pre.push x).size - 1) 0 + d))).toList = _
    have hget : (pre.push x).getD ((pre.push x).size - 1) 0 = x := by
      simp [Array.getD, Array.size_push]
    rw [hget, ih (pre.push x) (x + d)]
    simp [undiff1]

theorem undiffA_toList (x0 : Int) (ds : Array Int) :
    (undiffA x0 ds).toList = undiff1 x0 ds.toList := by
  unfold undiffA
  rw [← Array.foldl_toList, foldl_undiff ds.toList (Array.emptyWithCapacity (ds.size + 1)) x0]
  simp

/-- The array restore computes the list restore. -/
theorem restoreA_toList :
    ∀ (b ord : Nat) (warmup : List Int) (res : Array Int),
      (restoreA b ord warmup res).toList = restore b ord warmup res.toList := by
  intro b ord
  induction ord with
  | zero => intro w res; simp [restoreA, restore]
  | succ ord ih =>
    intro w res
    show (restoreA b ord (w.take ord) (undiffA ((diffN ord w).headD 0) res)).toList = _
    rw [ih, undiffA_toList]
    rfl

end Flac.Fixed
