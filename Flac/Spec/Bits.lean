import Flac.Native.Bits

/-!
# L0 proofs — bit I/O round-trips

Round-trip lemmas for `Flac.Bits`: `readBits`/`writeBits`, unary codes,
byte-alignment padding, and byte packing. Everything above L0 uses these
opaquely.
-/

namespace Flac.Bits

/-- The table-driven power of two computes `2 ^ ·` — the bridge that lets
    every hot path use `p2` under the unchanged round-trip theorems. -/
@[simp] theorem p2_eq (n : Nat) : p2 n = 2 ^ n := by
  unfold p2
  split
  · simp only [pow2Table, Array.getElem_ofFn]
  · rfl

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

/-- **L0 keystone**: reading `n` bits
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

/-- Unary round-trip (needed by Rice coding and wasted-bits). -/
theorem readUnary_writeUnary (q : Nat) (rest : BitStream) :
    readUnary (writeUnary q ++ rest) = some (q, rest) := by
  induction q with
  | zero => simp [writeUnary, readUnary]
  | succ q ih =>
    simp only [writeUnary, List.replicate_succ, List.cons_append, readUnary] at *
    rw [ih]

@[simp] theorem length_writeUnary (q : Nat) : (writeUnary q).length = q + 1 := by
  simp [writeUnary]

/-- All-zero bit runs read back as 0 (byte-alignment padding). -/
theorem readBits_replicate_false (n : Nat) (rest : BitStream) :
    readBits n (List.replicate n false ++ rest) = some (0, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, readBits, ih]

/-- The consumed prefix of a successful parse is recoverable by `take`. -/
theorem take_sub_length (pre tail : BitStream) :
    (pre ++ tail).take ((pre ++ tail).length - tail.length) = pre := by
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left' rfl

/-- Specification of `withConsumed`: if `f` parses exactly `pre`, the
    combinator returns `pre` as the consumed segment. -/
theorem withConsumed_spec {α : Type} (f : BitStream → Option (α × BitStream))
    (pre tail : BitStream) (a : α) (h : f (pre ++ tail) = some (a, tail)) :
    withConsumed f (pre ++ tail) = some (a, pre, tail) := by
  unfold withConsumed
  rw [h]
  simp only [take_sub_length]

/-! ## Arithmetic shift and wasted bits -/

@[simp] theorem sar_zero (x : Int) : sar x 0 = x := by
  unfold sar
  match x with
  | .ofNat m => simp [Nat.shiftRight_zero]
  | .negSucc m => simp [Nat.shiftRight_zero]

/-- `2 · (x >>ₐ 1) + x % 2 = x`: the parity decomposition used by
    mid/side stereo. -/
theorem two_mul_sar_one (x : Int) :
    2 * sar x 1 + x % 2 = x := by
  unfold sar
  match x with
  | .ofNat m =>
    show 2 * ((m >>> 1 : Nat) : Int) + ((m : Int)) % 2 = (m : Int)
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  | .negSucc m =>
    show 2 * (Int.negSucc (m >>> 1)) + (Int.negSucc m) % 2 = Int.negSucc m
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, Int.negSucc_eq]
    show 2 * (-(((m / 2 : Nat) : Int) + 1)) + (-((m : Int) + 1)) % 2 = -((m : Int) + 1)
    omega

@[simp] theorem map_shiftDown_zero (xs : List Int) :
    xs.map (shiftDown 0) = xs := by
  induction xs with
  | nil => rfl
  | cons x t ih => simp [shiftDown, ih]

/-- **Wasted-bits round-trip**:
    scaling back up after an exact scale-down is the identity. -/
theorem map_shiftUp_shiftDown (w : Nat) (xs : List Int)
    (h : ∀ x ∈ xs, ((2 ^ w : Nat) : Int) ∣ x) :
    (xs.map (shiftDown w)).map (shiftUp w) = xs := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
    have hx : ((2 ^ w : Nat) : Int) ∣ x := h x (List.mem_cons_self ..)
    simp only [List.map_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    show shiftUp w (shiftDown w x) :: t = x :: t
    unfold shiftUp shiftDown
    rw [p2_eq, Int.ediv_mul_cancel hx]

/-- Scaling down an exactly-divisible sample keeps it in the reduced
    width: the pointwise width bookkeeping of wasted bits. -/
theorem fitsSInt_shiftDown (b w : Nat) (hw : w < b) (x : Int)
    (hfit : FitsSInt b x) (hdvd : ((2 ^ w : Nat) : Int) ∣ x) :
    FitsSInt (b - w) (shiftDown w x) := by
  obtain ⟨q, hq⟩ := hdvd
  have hP : (0 : Int) < ((2 ^ w : Nat) : Int) := by
    have := Nat.two_pow_pos w
    omega
  have hqx : shiftDown w x = q := by
    rw [shiftDown, hq, Int.mul_ediv_cancel_left _ (by omega)]
  rw [hqx]
  obtain ⟨h1, h2⟩ := hfit
  have hsplit : (2 ^ b : Nat) = 2 ^ w * 2 ^ (b - w) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit] at h1 h2
  constructor
  · have h1' : ((2 ^ w : Nat) : Int) * -((2 ^ (b - w) : Nat) : Int)
        ≤ ((2 ^ w : Nat) : Int) * (2 * q) := by
      calc ((2 ^ w : Nat) : Int) * -((2 ^ (b - w) : Nat) : Int)
          = -(((2 ^ w * 2 ^ (b - w) : Nat) : Int)) := by
            rw [Int.natCast_mul]
            rw [Int.mul_neg]
        _ ≤ 2 * x := h1
        _ = ((2 ^ w : Nat) : Int) * (2 * q) := by rw [hq]; ac_rfl
    have := Int.le_of_mul_le_mul_left h1' hP
    omega
  · have h2' : ((2 ^ w : Nat) : Int) * (2 * q)
        < ((2 ^ w : Nat) : Int) * ((2 ^ (b - w) : Nat) : Int) := by
      calc ((2 ^ w : Nat) : Int) * (2 * q)
          = 2 * x := by rw [hq]; ac_rfl
        _ < ((2 ^ w * 2 ^ (b - w) : Nat) : Int) := h2
        _ = ((2 ^ w : Nat) : Int) * ((2 ^ (b - w) : Nat) : Int) := by
            rw [Int.natCast_mul]
    exact Int.lt_of_mul_lt_mul_left h2' (by omega)

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

/-- `wrapSInt` is the identity exactly where the value already fits —
    what makes the decoder's wrap invisible on every stream the encoder
    can produce. -/
theorem wrapSInt_eq_of_fits (n : Nat) (x : Int) (h : FitsSInt n x) :
    wrapSInt n x = x := by
  obtain ⟨h1, h2⟩ := h
  simp only [wrapSInt, p2_eq]
  rw [if_pos ⟨h1, h2⟩]

/-- The wrapped value always fits: the decoder-side bound that keeps
    predictor feedback from diverging on adversarial streams. -/
theorem fitsSInt_wrapSInt (n : Nat) (x : Int) : FitsSInt n (wrapSInt n x) := by
  have hP : (0 : Int) < ((2 ^ n : Nat) : Int) := by
    have := Nat.two_pow_pos n
    omega
  simp only [wrapSInt, p2_eq]
  split
  · next h => exact h
  · have h0 : 0 ≤ x % ((2 ^ n : Nat) : Int) := Int.emod_nonneg x (by omega)
    have hlt : x % ((2 ^ n : Nat) : Int) < ((2 ^ n : Nat) : Int) :=
      Int.emod_lt_of_pos x hP
    split <;> exact ⟨by omega, by omega⟩

/-- Pointwise wrap is the identity on lists of fitting values. -/
theorem map_wrapSInt_of_fits (n : Nat) (xs : List Int)
    (h : ∀ x ∈ xs, FitsSInt n x) : xs.map (wrapSInt n) = xs := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons]
    rw [wrapSInt_eq_of_fits n x (h x (List.mem_cons_self ..)),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

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
