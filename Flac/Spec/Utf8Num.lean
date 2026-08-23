import Flac.Native.Utf8Num
import Flac.Spec.Bits

/-!
# L1 proof — coded-number round-trip

`utf8NumDecode_encode` from PLAN.md §4: reading back an encoded coded number
returns it exactly, for every `n < 2^36`.
-/

namespace Flac.Utf8Num

open Flac.Bits

/-- Base-`b` analogue of `mod_two_pow_succ`: peel the top digit. -/
private theorem mod_pow_succ (n b k : Nat) :
    n % b ^ (k + 1) = b ^ k * (n / b ^ k % b) + n % b ^ k := by
  rw [Nat.pow_succ, Nat.mod_mul]; omega

/-- Positional-numeral step, stated so it rewrites the `readConts` goal
    directly (`P` will be `64^k`, `m` will be `n % 64^k`). -/
private theorem digit_step (acc x P m : Nat) :
    (acc * 64 + x) * P + m = acc * (P * 64) + (P * x + m) := by
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 64 P, Nat.mul_comm x P,
    Nat.add_assoc]

/-- Reading `k` continuation bytes after writing them accumulates the low
    `6*k` bits of `n` onto `acc`. -/
theorem readConts_writeConts (k acc n : Nat) (rest : BitStream) :
    readConts k acc (writeConts k n ++ rest)
      = some (acc * 64 ^ k + n % 64 ^ k, rest) := by
  induction k generalizing acc with
  | zero => simp [readConts, writeConts, Nat.mod_one]
  | succ k ih =>
    have hlt : 0x80 + n / 64 ^ k % 64 < 2 ^ 8 := by
      have : n / 64 ^ k % 64 < 64 := Nat.mod_lt _ (by omega)
      omega
    simp only [writeConts, writeContByte, List.append_assoc, readConts,
      readBits_writeBits _ _ _ hlt]
    have hcond : 0x80 ≤ 0x80 + n / 64 ^ k % 64 ∧ 0x80 + n / 64 ^ k % 64 < 0xC0 := by
      have : n / 64 ^ k % 64 < 64 := Nat.mod_lt _ (by omega)
      omega
    have hd : 0x80 + n / 64 ^ k % 64 - 0x80 = n / 64 ^ k % 64 := by omega
    rw [if_pos hcond, hd, ih, mod_pow_succ n 64 k, Nat.pow_succ, digit_step]

/-- **Coded-number round-trip** (PLAN.md §4, `utf8NumDecode_encode`). -/
theorem read_write (n : Nat) (h : n < 2 ^ 36) (rest : BitStream) :
    read (write n ++ rest) = some (n, rest) := by
  unfold write read
  by_cases h1 : n < 2 ^ 7
  · rw [if_pos h1, readBits_writeBits _ _ _ (by omega)]
    simp only []
    rw [if_pos (by omega : n < 0x80)]
  · rw [if_neg h1]
    by_cases h2 : n < 2 ^ 11
    · rw [if_pos h2, List.append_assoc,
        readBits_writeBits _ _ _ (by omega : 0xC0 + n / 2 ^ 6 < 2 ^ 8)]
      simp only []
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
        readConts_writeConts]
      congr 2
      omega
    · rw [if_neg h2]
      by_cases h3 : n < 2 ^ 16
      · rw [if_pos h3, List.append_assoc,
          readBits_writeBits _ _ _ (by omega : 0xE0 + n / 2 ^ 12 < 2 ^ 8)]
        simp only []
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), readConts_writeConts]
        congr 2
        omega
      · rw [if_neg h3]
        by_cases h4 : n < 2 ^ 21
        · rw [if_pos h4, List.append_assoc,
            readBits_writeBits _ _ _ (by omega : 0xF0 + n / 2 ^ 18 < 2 ^ 8)]
          simp only []
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos (by omega), readConts_writeConts]
          congr 2
          omega
        · rw [if_neg h4]
          by_cases h5 : n < 2 ^ 26
          · rw [if_pos h5, List.append_assoc,
              readBits_writeBits _ _ _ (by omega : 0xF8 + n / 2 ^ 24 < 2 ^ 8)]
            simp only []
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega), if_pos (by omega),
              readConts_writeConts]
            congr 2
            omega
          · rw [if_neg h5]
            by_cases h6 : n < 2 ^ 31
            · rw [if_pos h6, List.append_assoc,
                readBits_writeBits _ _ _ (by omega : 0xFC + n / 2 ^ 30 < 2 ^ 8)]
              simp only []
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_pos (by omega), readConts_writeConts]
              congr 2
              omega
            · rw [if_neg h6, List.append_assoc,
                readBits_writeBits _ _ _ (by omega : 0xFE < 2 ^ 8)]
              -- all guards are literal here (`b = 0xFE`); simp collapses them
              simp only [Nat.lt_irrefl, reduceIte, Nat.reduceLT]
              rw [readConts_writeConts]
              congr 2
              omega

end Flac.Utf8Num
