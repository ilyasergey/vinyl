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

end Flac.Lpc
