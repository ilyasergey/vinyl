import Flac.Native.Lpc
import Flac.Spec.Bits

/-!
# L3-LPC proofs — quantized-LPC restore round-trip

The history-passing formulation
makes the key induction one line: decoded prefix = original prefix, hence
the decoder's prediction ≡ the encoder's, hence
`out[n] = p(n) + (xs[n] - p(n)) = xs[n]` — for *any* coefficients, shift,
and even any prediction function. The one hypothesis is that the samples
fit the bit depth, which is exactly where the decoder's per-sample wrap
(the anti-divergence bound) is the identity.
-/

namespace Flac.Lpc

open Flac.Bits (FitsSInt wrapSInt wrapSInt_eq_of_fits)

/-- `dot` computes the folded zip it replaced — pins the RFC 9639 §9.2.6
    prediction sum to the allocation-free implementation. -/
theorem dot_eq_zip_foldl (cs : List Int) (hs : List Int) :
    dot cs hs = (cs.zip hs).foldl (fun a p => a + p.1 * p.2) 0 := by
  suffices h : ∀ (cs hs : List Int) (acc : Int),
      acc + dot cs hs = (cs.zip hs).foldl (fun a p => a + p.1 * p.2) acc by
    have := h cs hs 0
    omega
  intro cs
  induction cs with
  | nil => intro hs acc; simp [dot]
  | cons c cs ih =>
    intro hs acc
    match hs with
    | [] => simp [dot]
    | h :: hs =>
      show acc + (c * h + dot cs hs) = (cs.zip hs).foldl _ (acc + c * h)
      rw [← ih hs (acc + c * h)]
      omega

theorem restoreAux_residualAux (b : Nat) (cs : List Int) (shift : Nat) :
    ∀ (ys hist : List Int), (∀ x ∈ ys, FitsSInt b x) →
      restoreAux b cs shift hist (residualAux cs shift hist ys) = ys := by
  intro ys
  induction ys with
  | nil => intro hist _; rfl
  | cons x ys ih =>
    intro hist hfit
    simp only [residualAux, restoreAux]
    rw [show x - predict cs shift hist + predict cs shift hist = x by omega,
      wrapSInt_eq_of_fits b x (hfit x (List.mem_cons_self ..)),
      ih (x :: hist) (fun y hy => hfit y (List.mem_cons_of_mem _ hy))]

/-- **L3-LPC keystone**. -/
theorem restore_residual (b : Nat) (cs : List Int) (shift : Nat) (xs : List Int)
    (hfit : ∀ x ∈ xs, FitsSInt b x) :
    restore b cs shift (xs.take cs.length) (residual cs shift xs) = xs := by
  unfold restore residual
  rw [restoreAux_residualAux b cs shift _ _
      (fun x hx => hfit x (List.drop_subset _ _ hx)),
    List.take_append_drop]

@[simp] theorem length_residualAux (cs : List Int) (shift : Nat) :
    ∀ (ys hist : List Int), (residualAux cs shift hist ys).length = ys.length := by
  intro ys
  induction ys with
  | nil => intro hist; rfl
  | cons x ys ih => intro hist; simp only [residualAux, List.length_cons, ih]

@[simp] theorem length_residual (cs : List Int) (shift : Nat) (xs : List Int) :
    (residual cs shift xs).length = xs.length - cs.length := by
  simp [residual]

/-! ## Array forms compute the list forms -/

private theorem dot_nil (cs : List Int) : dot cs [] = 0 := by
  cases cs <;> rfl

/-- The tail-recursive array loop is the list dot product against the
    corresponding reversed prefix, with its accumulator added in front. -/
private theorem dotAGo_eq (out : Array Int) :
    ∀ (cs : List Int) (n : Nat) (hn : n ≤ out.size) (acc : Int),
      dotAGo out cs n hn acc =
        acc + dot cs ((out.toList.take n).reverse) := by
  intro cs
  induction cs with
  | nil =>
    intro n hn acc
    simp [dotAGo, dot]
  | cons c cs ih =>
    intro n hn acc
    match n with
    | 0 => simp [dotAGo, dot]
    | n + 1 =>
      have hi : n < out.size := Nat.lt_of_succ_le hn
      have hsplit : (out.toList.take (n + 1)).reverse
          = out[n] :: (out.toList.take n).reverse := by
        rw [List.take_succ, List.reverse_append]
        simp [Array.getElem?_toList, Array.getElem?_eq_getElem hi]
      simp only [dotAGo]
      rw [ih n (Nat.le_of_lt hi) (acc + c * out[n]), hsplit]
      simp only [dot]
      omega

/-- Walking the array from index `i` downward is the dot product against
    the reversed prefix of length `i + 1`. -/
theorem dotA_take (out : Array Int) :
    ∀ (cs : List Int) (i : Nat), i < out.size →
      dotA cs out i = dot cs ((out.toList.take (i + 1)).reverse) := by
  intro cs i hi
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [dotA, dif_pos hi]
    rw [dotAGo_eq]
    simp

private theorem dotA_unfold1 (xs : Array Int) (c0 : Int) (m : Nat)
    (h : m + 1 ≤ xs.size) :
    dotA [c0] xs (m) = 0 + c0 * xs[m]'(by omega) := by
  have h1 : m < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold1 xs c0 m h 0

theorem dot1At_eq (xs : Array Int) (c0 : Int) (i : Nat) :
    dot1At xs c0 i = dotA [c0] xs (i - 1) := by
  match i with
  | 0 => rfl
  | m + 1 =>
    show dot1At xs c0 (m + 1) = dotA [c0] xs (m)
    -- reduce the match on `m + 1` first, or `split` picks it over the
    -- bounds test
    simp only [dot1At]
    split
    · next h => rw [dotA_unfold1 xs c0 m h]
    · rfl

private theorem dotA_unfold2 (xs : Array Int) (c0 c1 : Int) (m : Nat)
    (h : m + 2 ≤ xs.size) :
    dotA [c0, c1] xs (m + 1) = 0 + c0 * xs[m + 1]'(by omega) + c1 * xs[m]'(by omega) := by
  have h1 : m + 1 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold2 xs c0 c1 m h 0

theorem dot2At_eq (xs : Array Int) (c0 c1 : Int) (i : Nat) :
    dot2At xs c0 c1 i = dotA [c0, c1] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | m + 2 =>
    show dot2At xs c0 c1 (m + 2) = dotA [c0, c1] xs (m + 1)
    -- reduce the match on `m + 2` first, or `split` picks it over the
    -- bounds test
    simp only [dot2At]
    split
    · next h => rw [dotA_unfold2 xs c0 c1 m h]
    · rfl

private theorem dotA_unfold3 (xs : Array Int) (c0 c1 c2 : Int) (m : Nat)
    (h : m + 3 ≤ xs.size) :
    dotA [c0, c1, c2] xs (m + 2) = 0 + c0 * xs[m + 2]'(by omega) + c1 * xs[m + 1]'(by omega) + c2 * xs[m]'(by omega) := by
  have h1 : m + 2 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold3 xs c0 c1 c2 m h 0

theorem dot3At_eq (xs : Array Int) (c0 c1 c2 : Int) (i : Nat) :
    dot3At xs c0 c1 c2 i = dotA [c0, c1, c2] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | m + 3 =>
    show dot3At xs c0 c1 c2 (m + 3) = dotA [c0, c1, c2] xs (m + 2)
    -- reduce the match on `m + 3` first, or `split` picks it over the
    -- bounds test
    simp only [dot3At]
    split
    · next h => rw [dotA_unfold3 xs c0 c1 c2 m h]
    · rfl

private theorem dotA_unfold4 (xs : Array Int) (c0 c1 c2 c3 : Int) (m : Nat)
    (h : m + 4 ≤ xs.size) :
    dotA [c0, c1, c2, c3] xs (m + 3) = 0 + c0 * xs[m + 3]'(by omega) + c1 * xs[m + 2]'(by omega) + c2 * xs[m + 1]'(by omega) + c3 * xs[m]'(by omega) := by
  have h1 : m + 3 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold4 xs c0 c1 c2 c3 m h 0

theorem dot4At_eq (xs : Array Int) (c0 c1 c2 c3 : Int) (i : Nat) :
    dot4At xs c0 c1 c2 c3 i = dotA [c0, c1, c2, c3] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | m + 4 =>
    show dot4At xs c0 c1 c2 c3 (m + 4) = dotA [c0, c1, c2, c3] xs (m + 3)
    -- reduce the match on `m + 4` first, or `split` picks it over the
    -- bounds test
    simp only [dot4At]
    split
    · next h => rw [dotA_unfold4 xs c0 c1 c2 c3 m h]
    · rfl

private theorem dotA_unfold5 (xs : Array Int) (c0 c1 c2 c3 c4 : Int) (m : Nat)
    (h : m + 5 ≤ xs.size) :
    dotA [c0, c1, c2, c3, c4] xs (m + 4) = 0 + c0 * xs[m + 4]'(by omega) + c1 * xs[m + 3]'(by omega) + c2 * xs[m + 2]'(by omega) + c3 * xs[m + 1]'(by omega) + c4 * xs[m]'(by omega) := by
  have h1 : m + 4 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold5 xs c0 c1 c2 c3 c4 m h 0

theorem dot5At_eq (xs : Array Int) (c0 c1 c2 c3 c4 : Int) (i : Nat) :
    dot5At xs c0 c1 c2 c3 c4 i = dotA [c0, c1, c2, c3, c4] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | m + 5 =>
    show dot5At xs c0 c1 c2 c3 c4 (m + 5) = dotA [c0, c1, c2, c3, c4] xs (m + 4)
    -- reduce the match on `m + 5` first, or `split` picks it over the
    -- bounds test
    simp only [dot5At]
    split
    · next h => rw [dotA_unfold5 xs c0 c1 c2 c3 c4 m h]
    · rfl

private theorem dotA_unfold6 (xs : Array Int) (c0 c1 c2 c3 c4 c5 : Int) (m : Nat)
    (h : m + 6 ≤ xs.size) :
    dotA [c0, c1, c2, c3, c4, c5] xs (m + 5) = 0 + c0 * xs[m + 5]'(by omega) + c1 * xs[m + 4]'(by omega) + c2 * xs[m + 3]'(by omega) + c3 * xs[m + 2]'(by omega) + c4 * xs[m + 1]'(by omega) + c5 * xs[m]'(by omega) := by
  have h1 : m + 5 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold6 xs c0 c1 c2 c3 c4 c5 m h 0

theorem dot6At_eq (xs : Array Int) (c0 c1 c2 c3 c4 c5 : Int) (i : Nat) :
    dot6At xs c0 c1 c2 c3 c4 c5 i = dotA [c0, c1, c2, c3, c4, c5] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | m + 6 =>
    show dot6At xs c0 c1 c2 c3 c4 c5 (m + 6) = dotA [c0, c1, c2, c3, c4, c5] xs (m + 5)
    -- reduce the match on `m + 6` first, or `split` picks it over the
    -- bounds test
    simp only [dot6At]
    split
    · next h => rw [dotA_unfold6 xs c0 c1 c2 c3 c4 c5 m h]
    · rfl

private theorem dotA_unfold7 (xs : Array Int) (c0 c1 c2 c3 c4 c5 c6 : Int) (m : Nat)
    (h : m + 7 ≤ xs.size) :
    dotA [c0, c1, c2, c3, c4, c5, c6] xs (m + 6) = 0 + c0 * xs[m + 6]'(by omega) + c1 * xs[m + 5]'(by omega) + c2 * xs[m + 4]'(by omega) + c3 * xs[m + 3]'(by omega) + c4 * xs[m + 2]'(by omega) + c5 * xs[m + 1]'(by omega) + c6 * xs[m]'(by omega) := by
  have h1 : m + 6 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold7 xs c0 c1 c2 c3 c4 c5 c6 m h 0

theorem dot7At_eq (xs : Array Int) (c0 c1 c2 c3 c4 c5 c6 : Int) (i : Nat) :
    dot7At xs c0 c1 c2 c3 c4 c5 c6 i = dotA [c0, c1, c2, c3, c4, c5, c6] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | m + 7 =>
    show dot7At xs c0 c1 c2 c3 c4 c5 c6 (m + 7) = dotA [c0, c1, c2, c3, c4, c5, c6] xs (m + 6)
    -- reduce the match on `m + 7` first, or `split` picks it over the
    -- bounds test
    simp only [dot7At]
    split
    · next h => rw [dotA_unfold7 xs c0 c1 c2 c3 c4 c5 c6 m h]
    · rfl

private theorem dotA_unfold8 (xs : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (m : Nat)
    (h : m + 8 ≤ xs.size) :
    dotA [c0, c1, c2, c3, c4, c5, c6, c7] xs (m + 7) = 0 + c0 * xs[m + 7]'(by omega) + c1 * xs[m + 6]'(by omega) + c2 * xs[m + 5]'(by omega) + c3 * xs[m + 4]'(by omega) + c4 * xs[m + 3]'(by omega) + c5 * xs[m + 2]'(by omega) + c6 * xs[m + 1]'(by omega) + c7 * xs[m]'(by omega) := by
  have h1 : m + 7 < xs.size := by omega
  simp only [dotA, dif_pos h1]
  exact dotAGo_unfold8 xs c0 c1 c2 c3 c4 c5 c6 c7 m h 0

theorem dot8At_eq (xs : Array Int) (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (i : Nat) :
    dot8At xs c0 c1 c2 c3 c4 c5 c6 c7 i = dotA [c0, c1, c2, c3, c4, c5, c6, c7] xs (i - 1) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | m + 8 =>
    show dot8At xs c0 c1 c2 c3 c4 c5 c6 c7 (m + 8) = dotA [c0, c1, c2, c3, c4, c5, c6, c7] xs (m + 7)
    -- reduce the match on `m + 8` first, or `split` picks it over the
    -- bounds test
    simp only [dot8At]
    split
    · next h => rw [dotA_unfold8 xs c0 c1 c2 c3 c4 c5 c6 c7 m h]
    · rfl

theorem predictA_eq (cs : List Int) (shift : Nat) (out : Array Int) :
    predictA cs shift out = predict cs shift out.toList.reverse := by
  unfold predictA predict
  congr 1
  rw [dotAGo_eq]
  rw [show out.toList.take out.size = out.toList from
    List.take_of_length_le (by simp)]
  simp

private theorem foldl_restore (b : Nat) (cs : List Int) (shift : Nat) :
    ∀ (l : List Int) (out : Array Int),
      (l.foldl (fun out r => out.push (wrapSInt b (r + predictA cs shift out))) out).toList
        = out.toList ++ restoreAux b cs shift out.toList.reverse l := by
  intro l
  induction l with
  | nil => intro out; simp [restoreAux]
  | cons r l ih =>
    intro out
    show (l.foldl _ (out.push (wrapSInt b (r + predictA cs shift out)))).toList = _
    rw [ih (out.push (wrapSInt b (r + predictA cs shift out))), predictA_eq]
    simp only [Array.toList_push, restoreAux, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.append_assoc]

/-- The array restore computes the list restore. -/
theorem restoreA_toList (b : Nat) (cs : List Int) (shift : Nat) (warmup : List Int)
    (res : Array Int) :
    (restoreA b cs shift warmup res).toList = restore b cs shift warmup res.toList := by
  unfold restoreA restore
  rw [← Array.foldl_toList, foldl_restore]
  simp

end Flac.Lpc
