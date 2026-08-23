import Flac.Native.Bits

/-!
# L0 proofs — bit I/O round-trips

Round-trip lemmas for `Flac.Bits`: `readBits`/`writeBits`, unary codes,
byte-alignment padding, and byte packing. Everything above L0 uses these
opaquely (PLAN.md §4).
-/

namespace Flac.Bits

@[simp] theorem length_writeBits (n v : Nat) : (writeBits n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [writeBits, ih]

/-- Arithmetic core of the round-trip: peeling the top bit of `v % 2^(n+1)`. -/
theorem mod_two_pow_succ (v n : Nat) :
    v % 2 ^ (n + 1) = (if v / 2 ^ n % 2 = 1 then 2 ^ n else 0) + v % 2 ^ n := by
  rw [Nat.pow_succ, Nat.mod_mul]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h] <;> omega

/-- `readBits` inverts `writeBits`, leaving the rest of the stream intact.
    No side condition: reading back yields `v` reduced mod `2^n`. -/
theorem readBits_writeBits_append (n v : Nat) (rest : BitStream) :
    readBits n (writeBits n v ++ rest) = some (v % 2 ^ n, rest) := by
  induction n generalizing v with
  | zero => simp [writeBits, readBits, Nat.mod_one]
  | succ n ih =>
    simp only [writeBits, List.cons_append, readBits, ih]
    rw [mod_two_pow_succ]
    by_cases h : v / 2 ^ n % 2 = 1 <;> simp [h]

/-- **L0 keystone** (`readBits_writeBits` in PLAN.md §4): reading `n` bits
    just after writing `v < 2^n` returns exactly `v`. -/
theorem readBits_writeBits (n v : Nat) (rest : BitStream) (hv : v < 2 ^ n) :
    readBits n (writeBits n v ++ rest) = some (v, rest) := by
  rw [readBits_writeBits_append, Nat.mod_eq_of_lt hv]

/-- A successfully read value is in range. -/
theorem readBits_lt {n : Nat} {s s' : BitStream} {v : Nat}
    (h : readBits n s = some (v, s')) : v < 2 ^ n := by
  induction n generalizing s s' v with
  | zero => simp [readBits] at h; omega
  | succ n ih =>
    match s with
    | [] => simp [readBits] at h
    | b :: s =>
      simp only [readBits] at h
      match hr : readBits n s with
      | none => rw [hr] at h; simp at h
      | some (w, t) =>
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have := ih hr
        have h2 : (2 : Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by
          rw [Nat.pow_succ]; omega
        by_cases hb : b <;> simp [hb] at h <;> omega

/-- Reading consumes exactly `n` bits. -/
theorem readBits_length {n : Nat} {s s' : BitStream} {v : Nat}
    (h : readBits n s = some (v, s')) : s.length = n + s'.length := by
  induction n generalizing s s' v with
  | zero => simp [readBits] at h; simp [h]
  | succ n ih =>
    match s with
    | [] => simp [readBits] at h
    | b :: s =>
      simp only [readBits] at h
      match hr : readBits n s with
      | none => rw [hr] at h; simp at h
      | some (w, t) =>
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have := ih hr
        simp [← h.2] at *
        omega

/-- Unary round-trip (needed by Rice coding and wasted-bits, PLAN.md §4 L0). -/
theorem readUnary_writeUnary (q : Nat) (rest : BitStream) :
    readUnary (writeUnary q ++ rest) = some (q, rest) := by
  induction q with
  | zero => simp [writeUnary, readUnary]
  | succ q ih =>
    simp only [writeUnary, List.replicate_succ, List.cons_append, readUnary] at *
    rw [ih]

@[simp] theorem length_writeUnary (q : Nat) : (writeUnary q).length = q + 1 := by
  simp [writeUnary]

/-! ## Signed integers -/

/-- Two's-complement round-trip for `n`-bit signed integers. -/
theorem readSInt_writeSInt (n : Nat) (x : Int) (h : FitsSInt n x)
    (rest : BitStream) :
    readSInt n (writeSInt n x ++ rest) = some (x, rest) := by
  obtain ⟨h1, h2⟩ := h
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  unfold writeSInt readSInt
  rw [readBits_writeBits _ _ _ (Nat.mod_lt _ hP)]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  by_cases hx : 0 ≤ x
  · have hlt : (x + ((2 ^ n : Nat) : Int)).toNat = x.toNat + 2 ^ n := by omega
    rw [hlt, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
    omega

/-! ## Byte packing -/

/-- Unpacking one packed byte recovers its 8 bits (exhaustive check). -/
theorem byteToBits_bitsToByte (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    byteToBits (bitsToByte b0 b1 b2 b3 b4 b5 b6 b7)
      = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  revert b0 b1 b2 b3 b4 b5 b6 b7; decide

@[simp] theorem byteListToBits_nil : byteListToBits [] = [] := rfl

theorem byteListToBits_cons (b : UInt8) (bs : List UInt8) :
    byteListToBits (b :: bs) = byteToBits b ++ byteListToBits bs := by
  simp [byteListToBits]

/-- Packing to bytes and unpacking is the identity on byte-aligned streams. -/
theorem byteListToBits_bitsToByteList :
    ∀ (n : Nat) (s : BitStream), s.length = 8 * n →
      byteListToBits (bitsToByteList s) = s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ n ih =>
    intro s hs
    match s with
    | [] => simp at hs
    | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_]
    | [_,_,_,_,_,_,_] => simp at hs <;> omega
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      have hr : rest.length = 8 * n := by simp at hs; omega
      simp [bitsToByteList, byteListToBits_cons, byteToBits_bitsToByte, ih rest hr]

/-- **Byte-packing round-trip**: for byte-aligned bitstreams,
    `bytesToBits ∘ bitsToBytes = id`. -/
theorem bytesToBits_bitsToBytes (s : BitStream) (h : 8 ∣ s.length) :
    bytesToBits (bitsToBytes s) = s := by
  obtain ⟨n, hn⟩ := h
  simp only [bytesToBits, bitsToBytes, List.toList_data_toByteArray]
  exact byteListToBits_bitsToByteList n s hn

/-! ## Alignment -/

@[simp] theorem length_alignToByte (s : BitStream) :
    (alignToByte s).length = s.length + padLen s.length := by
  simp [alignToByte]

theorem alignToByte_dvd (s : BitStream) : 8 ∣ (alignToByte s).length := by
  simp [alignToByte, padLen]
  omega

end Flac.Bits
