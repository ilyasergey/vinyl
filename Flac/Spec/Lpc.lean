import Flac.Native.Lpc

/-!
# L3-LPC proofs — quantized-LPC restore round-trip

`restoreLpc_residualLpc` fromThe history-passing formulation
makes the key induction one line: decoded prefix = original prefix, hence
the decoder's prediction ≡ the encoder's, hence
`out[n] = p(n) + (xs[n] - p(n)) = xs[n]` — for *any* coefficients, shift,
and even any prediction function. No hypotheses needed.
-/

namespace Flac.Lpc

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

theorem restoreAux_residualAux (cs : List Int) (shift : Nat) :
    ∀ (ys hist : List Int),
      restoreAux cs shift hist (residualAux cs shift hist ys) = ys := by
  intro ys
  induction ys with
  | nil => intro hist; rfl
  | cons x ys ih =>
    intro hist
    simp only [residualAux, restoreAux]
    rw [show x - predict cs shift hist + predict cs shift hist = x by omega, ih]

/-- **L3-LPC keystone**. -/
theorem restore_residual (cs : List Int) (shift : Nat) (xs : List Int) :
    restore cs shift (xs.take cs.length) (residual cs shift xs) = xs := by
  unfold restore residual
  rw [restoreAux_residualAux, List.take_append_drop]

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

theorem predictA_eq (cs : List Int) (shift : Nat) (out : Array Int) :
    predictA cs shift out = predict cs shift out.toList.reverse := by
  unfold predictA predict
  congr 1
  rw [dotAGo_eq]
  rw [show out.toList.take out.size = out.toList from
    List.take_of_length_le (by simp)]
  simp

private theorem foldl_restore (cs : List Int) (shift : Nat) :
    ∀ (l : List Int) (out : Array Int),
      (l.foldl (fun out r => out.push (r + predictA cs shift out)) out).toList
        = out.toList ++ restoreAux cs shift out.toList.reverse l := by
  intro l
  induction l with
  | nil => intro out; simp [restoreAux]
  | cons r l ih =>
    intro out
    show (l.foldl _ (out.push (r + predictA cs shift out))).toList = _
    rw [ih (out.push (r + predictA cs shift out)), predictA_eq]
    simp only [Array.toList_push, restoreAux, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.append_assoc]

/-- The array restore computes the list restore. -/
theorem restoreA_toList (cs : List Int) (shift : Nat) (warmup : List Int)
    (res : Array Int) :
    (restoreA cs shift warmup res).toList = restore cs shift warmup res.toList := by
  unfold restoreA restore
  rw [← Array.foldl_toList, foldl_restore]
  simp

end Flac.Lpc
