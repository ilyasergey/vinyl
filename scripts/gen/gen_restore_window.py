import sys
def gen(K):
    cs = [f"c{j}" for j in range(K)]
    hs = [f"h{j}" for j in range(K)]
    taps = " ".join(cs)
    win = " ".join(hs)
    # p: c0 * h(K-1) + c1 * h(K-2) + ... + c(K-1) * h0
    p = " + ".join(f"{cs[j]} * {hs[K-1-j]}" for j in range(K))
    def idx(j):
        return f"out.size - {K}" if j == 0 else f"out.size - {K} + {j}"
    def idxI(j):
        return f"init.size - {K}" if j == 0 else f"init.size - {K} + {j}"
    # window hypotheses
    hw = " →\n      ".join(f"{hs[j]} = (out.getD ({idx(j)}) 0).toInt64" for j in range(K))
    hwNames = " ".join(f"hw{j}" for j in range(K))
    initWin = " ".join(f"(init.getD ({idxI(j)}) 0).toInt64" for j in range(K))
    # histAt rewrites: j from K-1 down to 1 then tap0
    histRw = "\n".join(
        f"      rw [histAt_tap out out.size {K} {j} hK (Nat.le_refl _) (by omega) (by omega)]" for j in range(K-1, 0, -1))
    hist0 = f"      rw [histAt_tap0 out out.size {K} hK (Nat.le_refl _) (by omega) (by omega)]"
    substs = "\n".join(f"      subst hw{j}" for j in range(K))
    # IH window obligations
    def pidx(j):
        return f"out.size + 1 - {K}" if j == 0 else f"out.size + 1 - {K} + {j}"
    ihWin = []
    for j in range(K-1):
        ihWin.append(f"""      (by
        rw [Array.size_push, getD_push_lt _ _ _ (by omega),
          show {pidx(j)} = {idx(j+1)} by omega]
        exact hw{j+1})""")
    ihWin.append(f"""      (by
        rw [Array.size_push, show {pidx(K-1)} = out.size by omega, getD_push_eq])""")
    ihWinS = "\n".join(ihWin)
    newWin = " ".join(hs[1:] + ["v.toInt64"])
    return f'''
/-- `restoreFold{K}` with the last {K} outputs carried in registers (oldest
    first): one residual load and one conversion per sample instead of {K}
    history loads. -/
def restoreWin{K} (b : Nat) ({taps} sh negP P : Int64) (res : Array Int) (i : Nat)
    ({win} : Int64) (out : Array Int) : Array Int :=
  if hi : i < res.size then
    let r := res[i]
    let p := ({p}) >>> sh
    let x := r.toInt64 + p
    let v := if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (r + p.toInt)
    restoreWin{K} b {taps} sh negP P res (i + 1) {newWin} (out.push v)
  else out
termination_by res.size - i

/-- Entry: load the window from the warmup, or fall back when it is shorter
    than the order. -/
def restoreRoll{K} (b : Nat) ({taps} sh negP P : Int64) (res init : Array Int) : Array Int :=
  if {K} ≤ init.size then
    restoreWin{K} b {taps} sh negP P res 0 {initWin} init
  else restoreFold{K} b {taps} sh negP P res init

private theorem restoreWin{K}_eq (b : Nat) ({taps} sh negP P : Int64) (res : Array Int) :
    ∀ (n i : Nat) ({win} : Int64) (out : Array Int), res.size - i = n →
      {K} ≤ out.size → out.size + (res.size - i) < 4294967296 →
      {hw} →
      restoreWin{K} b {taps} sh negP P res i {win} out
        = (res.toList.drop i).foldl
            (fun out r => out.push (restoreStep{K} b {taps} sh negP P out r)) out := by
  intro n
  induction n with
  | zero =>
    intro i {win} out hn hK hs {hwNames}
    rw [restoreWin{K}, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    intro i {win} out hn hK hs {hwNames}
    have hi : i < res.size := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    simp only [Array.getElem_toList]
    have hstep : restoreStep{K} b {taps} sh negP P out res[i]
        = (let p := ({p}) >>> sh
           let x := res[i].toInt64 + p
           if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) := by
      unfold restoreStep{K}
      rw [if_pos hK]
      dsimp only
{histRw}
{hist0}
      simp only [getElem_eq_getD]
{substs}
      rfl
    rw [hstep]
    have heq : restoreWin{K} b {taps} sh negP P res i {win} out
        = restoreWin{K} b {taps} sh negP P res (i + 1) {newWin.replace("v.toInt64", "(let p := (" + p + ") >>> sh; let x := res[i].toInt64 + p; if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)).toInt64")}
            (out.push (let p := ({p}) >>> sh
              let x := res[i].toInt64 + p
              if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt))) := by
      rw [restoreWin{K}, dif_pos hi]
    rw [heq]
    generalize (let p := ({p}) >>> sh
      let x := res[i].toInt64 + p
      if negP ≤ x ∧ x < P then x.toInt else Bits.wrapSInt b (res[i] + p.toInt)) = v
    apply ih (i + 1) {newWin} (out.push v) (by omega) (by simp only [Array.size_push]; omega)
      (by simp only [Array.size_push]; omega)
{ihWinS}

private theorem restoreRoll{K}_eq_fold (b : Nat) ({taps} sh negP P : Int64) (res init : Array Int)
    (hs : init.size + res.size < 4294967296) :
    restoreRoll{K} b {taps} sh negP P res init = restoreFold{K} b {taps} sh negP P res init := by
  unfold restoreRoll{K}
  split
  · next hK =>
    rw [restoreWin{K}_eq b {taps} sh negP P res res.size 0 {initWin} init rfl hK (by omega)
      {" ".join("rfl" for _ in range(K))}]
    unfold restoreFold{K}
    rw [List.drop_zero, Array.foldl_toList]
  · rfl
'''

helpers = '''
theorem getElem_eq_getD (out : Array Int) (i : Nat) (h : i < out.size) : out[i] = out.getD i 0 := by
  unfold Array.getD
  rw [dif_pos h]
  rfl

theorem getD_push_lt (out : Array Int) (v : Int) (i : Nat) (h : i < out.size) :
    (out.push v).getD i 0 = out.getD i 0 := by
  rw [← getElem_eq_getD _ _ (by simp; omega), ← getElem_eq_getD _ _ h, Array.getElem_push_lt]

theorem getD_push_eq (out : Array Int) (v : Int) : (out.push v).getD out.size 0 = v := by
  rw [← getElem_eq_getD _ _ (by simp), Array.getElem_push_eq]
'''
if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]]
    print(helpers)
    for K in ks:
        print(gen(K))
