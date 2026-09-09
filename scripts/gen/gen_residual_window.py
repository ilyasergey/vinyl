def gen(K, slow_def="", slow_eq=""):
    cs = [f"c{j}" for j in range(K)]
    ws = [f"w{j}" for j in range(K)]
    taps = " ".join(cs)
    tapsList = ", ".join(cs)
    wins = " ".join(ws)
    wild = ", ".join("_" for _ in range(K))
    # p := d0 * w(K-1) + ... + d(K-1) * w0 with d_j = c_j.toInt64
    p = " + ".join(f"{cs[j]}.toInt64 * {ws[K-1-j]}" for j in range(K))
    newwins = " ".join(ws[1:] + ["xi"])
    def idx(j):  # window index relative to i
        return f"i - {K}" if j == 0 else f"i - {K} + {j}"
    def midx(j):  # after i = m + K
        return "m" if j == 0 else f"m + {j}"
    winsmall = " ∧\n      ".join(f"Bits.small31 (xs.getD ({idx(j)}) 0) = true" for j in range(K))
    initwins = " ".join(f"(xs.getD ({idx(j)}) 0).toInt64" for j in range(K))
    hw = " →\n      ".join(f"{ws[j]} = (xs.getD ({idx(j)}) 0).toInt64" for j in range(K))
    hsm = " →\n      ".join(f"Bits.small31 (xs.getD ({idx(j)}) 0) = true" for j in range(K))
    hwN = " ".join(f"hw{j}" for j in range(K))
    hsN = " ".join(f"hs{j}" for j in range(K))
    newwinsE = " ".join(ws[1:] + [f"((xs.getD (m + {K}) 0).toInt64)"])
    ihw = []
    ihs = []
    for j in range(K-1):
        src = f"m + {K} + 1 - {K}" if j == 0 else f"m + {K} + 1 - {K} + {j}"
        ihw.append(f"(by rw [show {src} = {midx(j+1)} by omega]; exact hw{j+1})")
        ihs.append(f"(by rw [show {src} = {midx(j+1)} by omega]; exact hs{j+1})")
    src = f"m + {K} + 1 - {K}" if K-1 == 0 else f"m + {K} + 1 - {K} + {K-1}"
    ihw.append(f"(by rw [show {src} = m + {K} by omega])")
    ihs.append(f"(by rw [show {src} = m + {K} by omega]; exact hx)")
    substs = "\n".join(f"      subst hw{j}" for j in range(K))
    getDrw = ", ".join(f"getD_lt xs (show {midx(j)} < xs.size by omega)" for j in range(K))
    sumX = " + ".join(f"{cs[j]}.toInt64 * (xs[{midx(K-1-j)}]'(by omega)).toInt64" for j in range(K))
    cases = " ∨ ".join(f"j = {midx(t)}" for t in range(K))
    rc = " | ".join("rfl" for _ in range(K))
    hwin_cases = "\n".join(
        f"""          · have := Bits.fitsSInt31_of_small31 hs{t}
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this""" for t in range(K))
    return f'''
{slow_def}
/-- `lpcResGo{K}` with the last {K} samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin{K} ({taps} : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → ({wins} : Int64) → Array Int → Array Int
  | _, 0, {wild}, out => out
  | i, rem + 1, {", ".join(ws)}, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := ({p}) >>> sh
      let xi := x.toInt64
      lpcResWin{K} {taps} sh shift xs (i + 1) rem {newwins} (out.push ((xi - p).toInt))
    else lpcResGo{K}Slow {taps} shift xs i (rem + 1) out

def lpcResGo{K}Fast ({taps} : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : {K} ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [{tapsList}], Bits.FitsSInt 16 c) ∧
      {winsmall} then
    lpcResWin{K} {taps} (Int64.ofNat shift) shift xs i rem {initwins} out
  else lpcResGo{K}Slow {taps} shift xs i rem out
'''.rstrip("\n") + "\n", f'''
{slow_eq}
theorem lpcResWin{K}_eq ({taps} : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [{tapsList}], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) ({wins} : Int64) (out : Array Int), {K} ≤ i → i + rem ≤ xs.size →
      {hw} →
      {hsm} →
      lpcResWin{K} {taps} (Int64.ofNat shift) shift xs i rem {wins} out
        = lpcResGo{K} {taps} shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i {wins} out hK hle {hwN} {hsN}
    obtain ⟨m, rfl⟩ : ∃ m, i = m + {K} := ⟨i - {K}, by omega⟩
    simp only [Nat.add_sub_cancel] at {hwN} {hsN}
    have hi : m + {K} < xs.size := by omega
    simp only [lpcResWin{K}]
    by_cases hx : Bits.small31 (xs.getD (m + {K}) 0) = true
    · rw [if_pos hx]
      rw [ih (m + {K} + 1) {newwinsE} (out.push _) (by omega) (by omega)
        {" ".join(ihw)}
        {" ".join(ihs)}]
      simp only [lpcResGo{K}]
{substs}
      have hstep : (((xs.getD (m + {K}) 0).toInt64
            - ({" + ".join(f"{cs[j]}.toInt64 * (xs.getD ({midx(K-1-j)}) 0).toInt64" for j in range(K))}) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + {K}) 0 - Flac.Bits.sar (Lpc.dot{K}At xs {taps} (m + {K})) shift := by
        rw [getD_lt xs hi, {getDrw}]
        have hd : {sumX} = Lpc.dot64 xs [{tapsList}] (m + {K}) (by omega) 0 := by
          rw [Lpc.dot64_unfold{K} xs {taps} (m + {K}) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + {K} ≤ j + [{tapsList}].length → j < m + {K} →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : {cases} := by omega
          rcases hj' with {rc}
{hwin_cases}
        have hb := Lpc.dotAGo_bound_range xs [{tapsList}] (m + {K}) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [{tapsList}] (m + {K}) (by omega) 0).toInt
            = Lpc.dotAGo xs [{tapsList}] (m + {K}) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [{tapsList}] (m + {K}) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [{tapsList}] (m + {K}) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [{tapsList}] (m + {K}) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [{tapsList}] (m + {K}) (by omega) 0) shift).natAbs
            ≤ {K} * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot{K}At]
        rw [dif_pos (show m + {K} ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold{K} xs {taps} m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo{K}Slow_eq {taps} shift xs (rem + 1) (m + {K}) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo{K}_eq_fast : @lpcResGo{K} = @lpcResGo{K}Fast := by
  funext {taps} shift xs i rem out
  unfold lpcResGo{K}Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, {", ".join(f"hs{j}" for j in range(K))}⟩ := h
    exact (lpcResWin{K}_eq {taps} shift xs hsh hc rem i {" ".join("_" for _ in range(K))} out hK hle
      {" ".join("rfl" for _ in range(K))} {hsN}).symm
  · exact (lpcResGo{K}Slow_eq {taps} shift xs rem i out).symm
'''
