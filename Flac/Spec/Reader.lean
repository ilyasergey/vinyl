import Flac.Native.Reader
import Flac.Spec.Bits

/-!
# Reader simulation — the production↔reference transfer, bit layer

`toStream br` is the model bitstream a reader denotes. Every `BitReader`
primitive returns exactly what the model reader returns on `toStream br`
(as an `Option.map` equation), so the layer-by-layer decoder ports compose
these without ever reasoning about bytes again.
-/

namespace Flac.Bits.BitReader

open Flac.Bits

/-- The model stream a reader position denotes. -/
def toStream (br : BitReader) : BitStream :=
  (bytesToBits br.data).drop br.pos

@[simp] theorem length_byteListToBits (l : List UInt8) :
    (byteListToBits l).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [byteListToBits_cons]
    simp only [List.length_append, ih, byteToBits, length_writeBits,
      List.length_cons]
    omega

@[simp] theorem length_bytesToBits (d : ByteArray) :
    (bytesToBits d).length = 8 * d.size := by
  show (byteListToBits d.data.toList).length = 8 * d.data.size
  simp only [length_byteListToBits, Array.length_toList]

@[simp] theorem length_toStream (br : BitReader) :
    (toStream br).length = br.size - br.pos := by
  simp [toStream, size]

/-- Dropping whole bytes off the bit expansion. -/
theorem drop_byteListToBits (a : Nat) :
    ∀ (l : List UInt8),
      (byteListToBits l).drop (8 * a) = byteListToBits (l.drop a) := by
  induction a with
  | zero => intro l; rfl
  | succ a ih =>
    intro l
    match l with
    | [] => simp [byteListToBits]
    | b :: t =>
      rw [byteListToBits_cons, show 8 * (a + 1) = 8 + 8 * a from by omega,
        ← List.drop_drop, List.drop_left' (by simp [byteToBits]),
        ih, List.drop_succ_cons]

/-- Indexing one bit inside `writeBits`. -/
theorem writeBits_drop_cons (v : Nat) :
    ∀ (n j : Nat), j < n →
      (writeBits n v).drop j
        = decide (v / 2 ^ (n - 1 - j) % 2 = 1) :: (writeBits n v).drop (j + 1) := by
  intro n
  induction n with
  | zero => intro j h; omega
  | succ n ih =>
    intro j h
    match j with
    | 0 =>
      rw [writeBits]
      simp
    | j + 1 =>
      show (writeBits (n + 1) v).drop (j + 1) = _
      rw [show n + 1 - 1 - (j + 1) = n - 1 - j from by omega, writeBits,
        List.drop_succ_cons, List.drop_succ_cons]
      exact ih j (by omega)

/-- One bit off the byte-list expansion, at any in-bounds bit index. -/
theorem byteListToBits_drop_cons (l : List UInt8) (i : Nat)
    (h : i < 8 * l.length) :
    (byteListToBits l).drop i
      = decide ((l[i / 8]?.getD 0).toNat / 2 ^ (7 - i % 8) % 2 = 1)
        :: (byteListToBits l).drop (i + 1) := by
  have h8 : i / 8 < l.length := by omega
  have hm : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have hb8 : (byteToBits (l[i / 8])).length = 8 := by
    simp [byteToBits]
  have hsplit : ∀ (j : Nat), j ≤ 8 →
      (byteListToBits l).drop (8 * (i / 8) + j)
        = (byteToBits l[i / 8]).drop j ++ byteListToBits (l.drop (i / 8 + 1)) := by
    intro j hj
    rw [← List.drop_drop, drop_byteListToBits, List.drop_eq_getElem_cons h8,
      byteListToBits_cons, List.drop_append_of_le_length (by omega)]
  have e1 := hsplit (i % 8) (by omega)
  have e2 := hsplit (i % 8 + 1) (by omega)
  rw [show 8 * (i / 8) + i % 8 = i from by omega] at e1
  rw [show 8 * (i / 8) + (i % 8 + 1) = i + 1 from by omega] at e2
  rw [show (7 : Nat) - i % 8 = 8 - 1 - i % 8 from by omega,
    List.getElem?_eq_getElem h8]
  simp only [Option.getD_some]
  rw [e1, e2, byteToBits, writeBits_drop_cons _ 8 (i % 8) hm, List.cons_append]

/-- The bit-cursor cons law: at an in-bounds position, the denoted stream
    starts with `bit data pos`. -/
theorem toStream_cons (br : BitReader) (h : br.pos < br.size) :
    toStream br = bit br.data br.pos :: toStream ⟨br.data, br.pos + 1⟩ := by
  have hk : br.pos / 8 < br.data.size := by
    simp only [size] at h
    omega
  have hlist : br.data.data.toList[br.pos / 8]? = some (br.data[br.pos / 8]) := by
    rw [Array.getElem?_toList]
    exact Array.getElem?_eq_getElem hk
  show (byteListToBits br.data.data.toList).drop br.pos
    = _ :: (byteListToBits br.data.data.toList).drop (br.pos + 1)
  rw [byteListToBits_drop_cons br.data.data.toList br.pos (by
      simp only [Array.length_toList]
      simp only [size] at h
      exact h),
    hlist]
  unfold bit
  rw [dif_pos hk, Option.getD_some]

/-! ## The fast bit paths compute the specification

`bitFast` and `extractBitsFast` are what the reader runs; `bit` and
`extractBits` are what the simulation lemmas below reason about. These
equalities are the whole bridge, and they are proved, not assumed. -/

theorem bitFast_eq (d : ByteArray) (i : Nat) : bitFast d i = bit d i := by
  unfold bitFast bit
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

/-- Splitting an extraction at any midpoint. -/
theorem extractBits_append (d : ByteArray) (pos m n : Nat) :
    extractBits d pos (m + n)
      = extractBits d pos m * 2 ^ n + extractBits d (pos + m) n := by
  induction m generalizing pos with
  | zero => simp [extractBits]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 from by omega]
    show (if bit d pos then 2 ^ (m + n) else 0) + extractBits d (pos + 1) (m + n)
      = ((if bit d pos then 2 ^ m else 0) + extractBits d (pos + 1) m) * 2 ^ n
        + extractBits d (pos + (m + 1)) n
    rw [ih (pos + 1), show pos + 1 + m = pos + (m + 1) from by omega, Nat.add_mul,
      Nat.pow_add]
    by_cases hb : bit d pos <;> simp [hb] <;> omega

theorem extractBits_lt (d : ByteArray) (pos n : Nat) :
    extractBits d pos n < 2 ^ n := by
  induction n generalizing pos with
  | zero => simp [extractBits]
  | succ n ih =>
    show (if bit d pos then 2 ^ n else 0) + extractBits d (pos + 1) n < 2 ^ (n + 1)
    have := ih (pos + 1)
    rw [Nat.pow_succ]
    by_cases hb : bit d pos <;> simp [hb] <;> omega

private theorem ite_bit (c k : Nat) :
    (if decide (c % 2 = 1) then k else 0) = k * (c % 2) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

/-- The low `j` bits of byte `i`, extracted bit-by-bit from its tail. -/
private theorem extractBits_within_byte (d : ByteArray) (i : Nat) :
    ∀ j, j ≤ 8 →
      extractBits d (8 * i + (8 - j)) j
        = (if h : i < d.size then d[i] else 0).toNat % 2 ^ j := by
  intro j
  induction j with
  | zero => intro _; simp [extractBits, Nat.mod_one]
  | succ j ih =>
    intro hj
    show (if bit d (8 * i + (8 - (j + 1))) then 2 ^ j else 0)
        + extractBits d (8 * i + (8 - (j + 1)) + 1) j = _
    have hbit : bit d (8 * i + (8 - (j + 1)))
        = decide ((if h : i < d.size then d[i] else 0).toNat / 2 ^ j % 2 = 1) := by
      have h1 : (8 * i + (8 - (j + 1))) / 8 = i := by omega
      have h2 : 7 - (8 * i + (8 - (j + 1))) % 8 = j := by omega
      unfold bit
      rw [h1, h2]
    rw [show 8 * i + (8 - (j + 1)) + 1 = 8 * i + (8 - j) from by omega,
      ih (by omega), hbit, ite_bit, Nat.mod_pow_succ]
    omega

/-- A whole aligned byte. -/
private theorem extractBits_byte (d : ByteArray) (i : Nat) :
    extractBits d (8 * i) 8 = (if h : i < d.size then d[i] else 0).toNat := by
  have h := extractBits_within_byte d i 8 (by omega)
  rw [show 8 * i + (8 - 8) = 8 * i from by omega] at h
  have hlt : (if h : i < d.size then d[i] else 0).toNat < 2 ^ 8 := by
    have h256 : (2 : Nat) ^ 8 = 256 := rfl
    rw [h256]
    split
    · exact UInt8.toNat_lt_size _
    · decide
  rw [h, Nat.mod_eq_of_lt hlt]

theorem accBytes_eq (d : ByteArray) :
    ∀ (k i acc : Nat),
      accBytes d i k acc = acc * 2 ^ (8 * k) + extractBits d (8 * i) (8 * k) := by
  intro k
  induction k with
  | zero => intro i acc; simp [accBytes, extractBits]
  | succ k ih =>
    intro i acc
    show accBytes d (i + 1) k
        (acc * 256 + (if h : i < d.size then d[i] else 0).toNat) = _
    rw [ih, show 8 * (k + 1) = 8 + 8 * k from by omega,
      extractBits_append d (8 * i) 8 (8 * k), extractBits_byte,
      Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl,
      show 8 * i + 8 = 8 * (i + 1) from by omega,
      Nat.add_mul, ← Nat.mul_assoc]
    omega

/-- **The word-level extraction computes the bit-level specification** —
    unconditionally (out-of-range bytes and bits both read as zero). -/
theorem extractBitsFast_eq (d : ByteArray) (pos n : Nat) :
    extractBitsFast d pos n = extractBits d pos n := by
  unfold extractBitsFast
  have hcount : 8 * ((pos + n + 7) / 8 - pos / 8)
      = pos % 8 + (n + (8 - (pos + n) % 8) % 8) := by omega
  rw [accBytes_eq, Nat.zero_mul, Nat.zero_add, hcount,
    extractBits_append d (8 * (pos / 8)) (pos % 8) _,
    show 8 * (pos / 8) + pos % 8 = pos from by omega,
    extractBits_append d pos n _,
    Nat.shiftRight_eq_div_pow, p2_eq, Nat.and_two_pow_sub_one_eq_mod,
    Nat.pow_add, ← Nat.mul_assoc]
  have h2 := extractBits_lt d pos n
  have h3 := extractBits_lt d (pos + n) ((8 - (pos + n) % 8) % 8)
  rw [show extractBits d (8 * (pos / 8)) (pos % 8) * 2 ^ n
          * 2 ^ ((8 - (pos + n) % 8) % 8)
        + (extractBits d pos n * 2 ^ ((8 - (pos + n) % 8) % 8)
          + extractBits d (pos + n) ((8 - (pos + n) % 8) % 8))
      = 2 ^ ((8 - (pos + n) % 8) % 8)
          * (extractBits d (8 * (pos / 8)) (pos % 8) * 2 ^ n + extractBits d pos n)
        + extractBits d (pos + n) ((8 - (pos + n) % 8) % 8) from by
        rw [Nat.mul_add, Nat.mul_comm (2 ^ ((8 - (pos + n) % 8) % 8))
          (extractBits d (8 * (pos / 8)) (pos % 8) * 2 ^ n),
          Nat.mul_comm (2 ^ ((8 - (pos + n) % 8) % 8)) (extractBits d pos n)]
        omega,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt h3, Nat.add_zero,
    Nat.mul_add_mod', Nat.mod_eq_of_lt h2]

/-! ## Primitive simulations -/

theorem readBits_none_of_short {n : Nat} {s : BitStream} (h : s.length < n) :
    Bits.readBits n s = none := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    match s with
    | [] => rfl
    | b :: t =>
      simp only [Bits.readBits, ih (by simpa using h)]

/-- Model `readBits` computes exactly `extractBits` at in-bounds positions. -/
theorem readBits_extract (d : ByteArray) :
    ∀ (n pos : Nat), pos + n ≤ 8 * d.size →
      Bits.readBits n ((bytesToBits d).drop pos)
        = some (extractBits d pos n, (bytesToBits d).drop (pos + n)) := by
  intro n
  induction n with
  | zero =>
    intro pos h
    simp [Bits.readBits, extractBits]
  | succ n ih =>
    intro pos h
    have hcons := toStream_cons ⟨d, pos⟩ (by simp only [size]; omega)
    simp only [toStream] at hcons
    rw [hcons]
    simp only [Bits.readBits, ih (pos + 1) (by omega), extractBits]
    rw [show pos + 1 + n = pos + (n + 1) from by omega]

theorem readBits_sim (n : Nat) (br : BitReader) :
    Bits.readBits n (toStream br)
      = (br.readBits n).map (fun p => (p.1, toStream p.2)) := by
  unfold BitReader.readBits
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl]
    rfl
  rw [if_neg h0]
  by_cases hb : br.pos + n ≤ br.size
  · rw [if_pos hb, extractBitsFast_eq]
    show Bits.readBits n ((bytesToBits br.data).drop br.pos) = _
    rw [readBits_extract br.data n br.pos (by simpa [size] using hb)]
    rfl
  · rw [if_neg hb]
    apply readBits_none_of_short
    simp only [length_toStream, size] at *
    omega

theorem readUnary_drop {s : BitStream} :
    ∀ {q : Nat} {s' : BitStream},
      Bits.readUnary s = some (q, s') → s' = s.drop (q + 1) := by
  induction s with
  | nil => intro q s' h; simp [Bits.readUnary] at h
  | cons b t ih =>
    intro q s' h
    match b with
    | true =>
      simp only [Bits.readUnary, Option.some.injEq, Prod.mk.injEq] at h
      simp [← h.1, ← h.2]
    | false =>
      simp only [Bits.readUnary] at h
      match hr : Bits.readUnary t with
      | none => rw [hr] at h; simp at h
      | some (q', s'') =>
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2, ih hr, List.drop_succ_cons]

/-- Reading a bit beyond the buffer yields `false`. -/
theorem bit_oob (d : ByteArray) (i : Nat) (h : 8 * d.size ≤ i) :
    bit d i = false := by
  unfold bit
  rw [dif_neg (by omega)]
  simp

theorem readUnaryGo_sim (d : ByteArray) :
    ∀ (fuel pos q : Nat), 8 * d.size - pos ≤ fuel →
      readUnaryGo d q pos fuel
        = (Bits.readUnary ((bytesToBits d).drop pos)).map
            (fun p => (q + p.1, pos + p.1 + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos q h
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ fuel ih =>
    intro pos q h
    by_cases hp : pos < 8 * d.size
    · have hcons := toStream_cons ⟨d, pos⟩ (by simp only [size]; omega)
      simp only [toStream] at hcons
      rw [hcons]
      unfold readUnaryGo
      rw [bitFast_eq]
      by_cases hbit : bit d pos
      · rw [if_pos hbit, hbit]
        show _ = (Bits.readUnary (true :: _)).map _
        simp [Bits.readUnary]
      · rw [if_neg hbit]
        rw [Bool.not_eq_true] at hbit
        rw [hbit]
        show _ = (Bits.readUnary (false :: _)).map _
        rw [ih (pos + 1) (q + 1) (by omega)]
        simp only [Bits.readUnary]
        match hr : Bits.readUnary ((bytesToBits d).drop (pos + 1)) with
        | none => rfl
        | some (c, s') =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          omega
    · unfold readUnaryGo
      rw [if_neg (by rw [bitFast_eq, bit_oob d pos (by omega)]; simp),
        ih (pos + 1) (q + 1) (by omega),
        List.drop_eq_nil_of_le (as := bytesToBits d)
          (by simp only [length_bytesToBits]; omega),
        List.drop_eq_nil_of_le (as := bytesToBits d)
          (by simp only [length_bytesToBits]; omega)]
      rfl

/-- The scalar unary scanner stays inside its searched interval. -/
theorem scanOne_bounds (d : ByteArray) : ∀ (fuel pos : Nat),
    pos ≤ scanOne d pos fuel ∧ scanOne d pos fuel ≤ pos + fuel := by
  intro fuel
  induction fuel with
  | zero => intro pos; simp [scanOne]
  | succ fuel ih =>
    intro pos
    unfold scanOne
    by_cases h : bitFast d pos
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      have hb := ih (pos + 1)
      omega

/-! ### Skipping known-zero bits

The shipped scan (`Flac.Decode.scanOneU`) decides a whole byte at a time,
so its correctness argument is: bits already known to be zero can be
stepped over in one go, and a bit known to be one ends the search. Both
are inductions on the number of bits skipped. -/

/-- A run of `s` zero bits is skipped in one step. -/
theorem scanOne_skip (d : ByteArray) : ∀ (s pos n : Nat), s ≤ n →
    (∀ j, j < s → bitFast d (pos + j) = false) →
    scanOne d pos n = scanOne d (pos + s) (n - s) := by
  intro s
  induction s with
  | zero => intro pos n _ _; rfl
  | succ s ih =>
    intro pos n hs hz
    cases n with
    | zero => omega
    | succ n =>
      have h0 : bitFast d pos = false := by
        have := hz 0 (by omega); rwa [Nat.add_zero] at this
      have hstep : scanOne d pos (n + 1) = scanOne d (pos + 1) n := by
        show (if bitFast d pos then pos else scanOne d (pos + 1) n) = _
        rw [if_neg (by rw [h0]; exact Bool.false_ne_true)]
      rw [hstep, ih (pos + 1) n (by omega) (fun j hj => by
          have := hz (j + 1) (by omega)
          rwa [show pos + (j + 1) = pos + 1 + j by omega] at this),
        show pos + 1 + s = pos + (s + 1) by omega, show n - s = n + 1 - (s + 1) by omega]

/-- Nothing to find: the scan runs out at the end of its interval. -/
theorem scanOne_all_zero (d : ByteArray) (pos n : Nat)
    (hz : ∀ j, j < n → bitFast d (pos + j) = false) :
    scanOne d pos n = pos + n := by
  rw [scanOne_skip d n pos n (Nat.le_refl _) hz, Nat.sub_self]
  rfl

/-- The first one bit is where the scan stops. -/
theorem scanOne_hit (d : ByteArray) (pos n t : Nat) (ht : t < n)
    (hz : ∀ j, j < t → bitFast d (pos + j) = false) (h1 : bitFast d (pos + t) = true) :
    scanOne d pos n = pos + t := by
  rw [scanOne_skip d t pos n (Nat.le_of_lt ht) hz]
  cases hnt : n - t with
  | zero => omega
  | succ m =>
    show (if bitFast d (pos + t) then pos + t else scanOne d (pos + t + 1) m) = _
    rw [if_pos (by rw [h1])]

/-- `scanOne` is `readUnaryGo` with the quotient recovered from the
    terminating-bit position.  Its right-hand side allocates only in this
    specification; the production Rice loop consumes `scanOne`'s scalar
    result directly. -/
theorem scanOne_spec (d : ByteArray) : ∀ (fuel pos q : Nat),
    readUnaryGo d q pos fuel =
      let onePos := scanOne d pos fuel
      if onePos < pos + fuel then
        some (q + (onePos - pos), onePos + 1)
      else none := by
  intro fuel
  induction fuel with
  | zero => intro pos q; simp [readUnaryGo, scanOne]
  | succ fuel ih =>
    intro pos q
    unfold readUnaryGo scanOne
    by_cases h : bitFast d pos
    · rw [if_pos h, if_pos h]
      simp
    · rw [if_neg h, if_neg h, ih]
      obtain ⟨hlo, hhi⟩ := scanOne_bounds d fuel (pos + 1)
      by_cases hs : scanOne d (pos + 1) fuel < pos + (fuel + 1)
      · have hsub : scanOne d (pos + 1) fuel - pos =
            (scanOne d (pos + 1) fuel - (pos + 1)) + 1 := by omega
        simp only [show pos + 1 + fuel = pos + (fuel + 1) by omega, hs, if_true,
          Option.some.injEq, Prod.mk.injEq]
        rw [hsub]
        simp [Nat.add_assoc, Nat.add_comm]
      · simp only [show pos + 1 + fuel = pos + (fuel + 1) by omega, hs, if_false]

theorem readUnary_sim (br : BitReader) :
    Bits.readUnary (toStream br)
      = (br.readUnary).map (fun p => (p.1, toStream p.2)) := by
  unfold BitReader.readUnary
  rw [readUnaryGo_sim br.data br.remaining br.pos 0 (by simp [remaining, size])]
  show Bits.readUnary ((bytesToBits br.data).drop br.pos) = _
  match hr : Bits.readUnary ((bytesToBits br.data).drop br.pos) with
  | none => rfl
  | some (q, s') =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    refine ⟨by omega, ?_⟩
    rw [readUnary_drop hr]
    show ((bytesToBits br.data).drop br.pos).drop (q + 1) = _
    rw [List.drop_drop]
    show (bytesToBits br.data).drop (br.pos + (q + 1)) = toStream _
    unfold toStream
    rw [show br.pos + (q + 1) = br.pos + q + 1 from by omega]

/-- `readUnaryGo` at *arbitrary* fuel, not just enough fuel: the fuel is
    exactly a cap on the run length. (`readUnaryGo_sim` is this with the
    cap discharged by the hypothesis `8 * d.size - pos ≤ fuel`.) -/
theorem readUnaryGo_sim_lt (d : ByteArray) :
    ∀ (fuel pos q : Nat),
      readUnaryGo d q pos fuel
        = (Bits.readUnary ((bytesToBits d).drop pos)).bind
            (fun p => if p.1 < fuel then some (q + p.1, pos + p.1 + 1) else none) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos q
    show none = _
    cases Bits.readUnary ((bytesToBits d).drop pos) with
    | none => rfl
    | some p => simp
  | succ fuel ih =>
    intro pos q
    by_cases hp : pos < 8 * d.size
    · have hcons := toStream_cons ⟨d, pos⟩ (by simp only [size]; omega)
      simp only [toStream] at hcons
      rw [hcons]
      unfold readUnaryGo
      rw [bitFast_eq]
      by_cases hbit : bit d pos
      · rw [if_pos hbit, hbit]
        show _ = (Bits.readUnary (true :: _)).bind _
        simp [Bits.readUnary]
      · rw [if_neg hbit]
        rw [Bool.not_eq_true] at hbit
        rw [hbit]
        show _ = (Bits.readUnary (false :: _)).bind _
        rw [ih (pos + 1) (q + 1)]
        simp only [Bits.readUnary]
        cases Bits.readUnary ((bytesToBits d).drop (pos + 1)) with
        | none => rfl
        | some p =>
          by_cases h : p.1 < fuel
          · simp only [Option.bind_some, h, if_true,
              show p.1 + 1 < fuel + 1 from by omega, if_true,
              Option.some.injEq, Prod.mk.injEq]
            omega
          · simp only [Option.bind_some, h, if_false, Option.bind_none,
              show ¬(p.1 + 1 < fuel + 1) from by omega, if_false]
    · unfold readUnaryGo
      rw [if_neg (by rw [bitFast_eq, bit_oob d pos (by omega)]; simp),
        ih (pos + 1) (q + 1),
        List.drop_eq_nil_of_le (as := bytesToBits d)
          (by simp only [length_bytesToBits]; omega),
        List.drop_eq_nil_of_le (as := bytesToBits d)
          (by simp only [length_bytesToBits]; omega)]
      rfl

theorem readUnaryUpTo_sim (lim : Nat) (br : BitReader) :
    Bits.readUnaryUpTo lim (toStream br)
      = (br.readUnaryUpTo lim).map (fun p => (p.1, toStream p.2)) := by
  unfold BitReader.readUnaryUpTo
  rw [Bits.readUnaryUpTo_eq, readUnaryGo_sim_lt br.data lim br.pos 0]
  show (Bits.readUnary ((bytesToBits br.data).drop br.pos)).bind _ = _
  match hr : Bits.readUnary ((bytesToBits br.data).drop br.pos) with
  | none => rfl
  | some (q, s') =>
    by_cases h : q < lim
    · simp only [Option.bind_some, h, if_true, Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      refine ⟨by omega, ?_⟩
      rw [readUnary_drop hr]
      show ((bytesToBits br.data).drop br.pos).drop (q + 1) = _
      rw [List.drop_drop]
      show (bytesToBits br.data).drop (br.pos + (q + 1)) = toStream _
      unfold toStream
      rw [show br.pos + (q + 1) = br.pos + q + 1 from by omega]
    · simp only [Option.bind_some, h, if_false, Option.map_none]

theorem readSInt_sim (n : Nat) (br : BitReader) :
    Bits.readSInt n (toStream br)
      = (br.readSInt n).map (fun p => (p.1, toStream p.2)) := by
  unfold Bits.readSInt BitReader.readSInt
  rw [readBits_sim n br]
  simp only [p2_eq]
  match br.readBits n with
  | none => rfl
  | some (v, br') => rfl

/-! ## Position tracking (for CRC byte-slice equalities) -/

theorem readBits_spec {n : Nat} {br br' : BitReader} {v : Nat}
    (h : br.readBits n = some (v, br')) :
    br'.data = br.data ∧ br'.pos = br.pos + n
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold BitReader.readBits at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    refine ⟨rfl, by omega, fun hb => by omega⟩
  · split at h
    · rename_i hbound
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbr⟩ := h
      subst hbr
      exact ⟨rfl, rfl, fun _ => hbound⟩
    · simp at h

theorem readUnaryGo_spec (d : ByteArray) :
    ∀ (fuel q pos q' pos' : Nat),
      readUnaryGo d q pos fuel = some (q', pos') →
      pos < pos' ∧ pos' ≤ 8 * d.size := by
  intro fuel
  induction fuel with
  | zero => intro q pos q' pos' h; simp [readUnaryGo] at h
  | succ fuel ih =>
    intro q pos q' pos' h
    unfold readUnaryGo at h
    rw [bitFast_eq] at h
    split at h
    · rename_i hbit
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hpos⟩ := h
      subst hpos
      by_cases hin : pos < 8 * d.size
      · exact ⟨by omega, by omega⟩
      · rw [bit_oob d pos (by omega)] at hbit
        simp at hbit
    · have := ih (q + 1) (pos + 1) q' pos' h
      exact ⟨by omega, this.2⟩

theorem readUnary_spec {br br' : BitReader} {q : Nat}
    (h : br.readUnary = some (q, br')) :
    br'.data = br.data ∧ br.pos < br'.pos ∧ br'.pos ≤ br.size := by
  unfold BitReader.readUnary at h
  match hg : readUnaryGo br.data 0 br.pos br.remaining with
  | none => rw [hg] at h; simp at h
  | some (q0, pos0) =>
    rw [hg] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    have := readUnaryGo_spec br.data br.remaining 0 br.pos q0 pos0 hg
    exact ⟨rfl, this.1, this.2⟩

theorem readUnaryUpTo_spec {lim : Nat} {br br' : BitReader} {q : Nat}
    (h : br.readUnaryUpTo lim = some (q, br')) :
    br'.data = br.data ∧ br.pos < br'.pos ∧ br'.pos ≤ br.size := by
  unfold BitReader.readUnaryUpTo at h
  match hg : readUnaryGo br.data 0 br.pos lim with
  | none => rw [hg] at h; simp at h
  | some (q0, pos0) =>
    rw [hg] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    have := readUnaryGo_spec br.data lim 0 br.pos q0 pos0 hg
    exact ⟨rfl, this.1, this.2⟩

theorem readSInt_spec {n : Nat} {br br' : BitReader} {v : Int}
    (h : br.readSInt n = some (v, br')) :
    br'.data = br.data ∧ br'.pos = br.pos + n
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold BitReader.readSInt at h
  match hb : br.readBits n with
  | none => rw [hb] at h; simp at h
  | some (w, br1) =>
    rw [hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hbr⟩ := h
    subst hbr
    exact readBits_spec hb

theorem skip_spec {n : Nat} {br br' : BitReader} (h : br.skip n = some br') :
    br'.data = br.data ∧ br'.pos = br.pos + n
      ∧ (br.pos ≤ br.size → br'.pos ≤ br.size) := by
  unfold BitReader.skip at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, by omega, fun hb => by omega⟩
  · split at h
    · rename_i hbound
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, fun _ => hbound⟩
    · simp at h

/-! ## Byte packing inverses (for the CRC byte slices) -/

/-- Taking whole bytes off the bit expansion. -/
theorem take_byteListToBits (a : Nat) :
    ∀ (l : List UInt8),
      (byteListToBits l).take (8 * a) = byteListToBits (l.take a) := by
  induction a with
  | zero => intro l; rfl
  | succ a ih =>
    intro l
    match l with
    | [] => simp [byteListToBits]
    | b :: t =>
      rw [List.take_succ_cons, byteListToBits_cons, byteListToBits_cons,
        show 8 * (a + 1) = 8 + 8 * a from by omega, List.take_append,
        List.take_of_length_le (by simp [byteToBits]),
        show 8 + 8 * a - (byteToBits b).length = 8 * a from by
          simp [byteToBits],
        ih]

/-- Reassembling one expanded byte. -/
private theorem head8 : ∀ b : UInt8,
    bitsToByte (decide (b.toNat / 2 ^ 7 % 2 = 1)) (decide (b.toNat / 2 ^ 6 % 2 = 1))
      (decide (b.toNat / 2 ^ 5 % 2 = 1)) (decide (b.toNat / 2 ^ 4 % 2 = 1))
      (decide (b.toNat / 2 ^ 3 % 2 = 1)) (decide (b.toNat / 2 ^ 2 % 2 = 1))
      (decide (b.toNat / 2 ^ 1 % 2 = 1)) (decide (b.toNat / 2 ^ 0 % 2 = 1)) = b := by
  intro b
  have hdec : ∀ y : Nat, (decide (y % 2 = 1) : Bool).toNat = y % 2 := by
    intro y
    rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  unfold bitsToByte
  have hX : 128 * (decide (b.toNat / 2 ^ 7 % 2 = 1) : Bool).toNat
      + 64 * (decide (b.toNat / 2 ^ 6 % 2 = 1) : Bool).toNat
      + 32 * (decide (b.toNat / 2 ^ 5 % 2 = 1) : Bool).toNat
      + 16 * (decide (b.toNat / 2 ^ 4 % 2 = 1) : Bool).toNat
      + 8 * (decide (b.toNat / 2 ^ 3 % 2 = 1) : Bool).toNat
      + 4 * (decide (b.toNat / 2 ^ 2 % 2 = 1) : Bool).toNat
      + 2 * (decide (b.toNat / 2 ^ 1 % 2 = 1) : Bool).toNat
      + (decide (b.toNat / 2 ^ 0 % 2 = 1) : Bool).toNat = b.toNat := by
    simp only [hdec]
    omega
  rw [hX, UInt8.ofNat_toNat]

theorem bitsToByteList_byteToBits (b : UInt8) (X : BitStream) :
    bitsToByteList (byteToBits b ++ X) = b :: bitsToByteList X := by
  rw [show bitsToByteList (byteToBits b ++ X)
      = bitsToByte (decide (b.toNat / 2 ^ 7 % 2 = 1)) (decide (b.toNat / 2 ^ 6 % 2 = 1))
          (decide (b.toNat / 2 ^ 5 % 2 = 1)) (decide (b.toNat / 2 ^ 4 % 2 = 1))
          (decide (b.toNat / 2 ^ 3 % 2 = 1)) (decide (b.toNat / 2 ^ 2 % 2 = 1))
          (decide (b.toNat / 2 ^ 1 % 2 = 1)) (decide (b.toNat / 2 ^ 0 % 2 = 1))
        :: bitsToByteList X from rfl,
    head8 b]

/-- Packing inverts expansion. -/
theorem bitsToByteList_byteListToBits :
    ∀ l : List UInt8, bitsToByteList (byteListToBits l) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [byteListToBits_cons, bitsToByteList_byteToBits, ih]

/-! ## The three-byte extraction window

`extractBits3` reads a fixed three bytes with the mask supplied by the
caller, where `extractBitsFast` computes a byte count with two `Nat`
divisions, loops `accBytes`, and rebuilds `2^n - 1`. They agree exactly
when the field fits in the window, `pos % 8 + n ≤ 24` — which every
`n ≤ 17` satisfies. -/

private theorem byte_lt (d : ByteArray) (i : Nat) :
    (if h : i < d.size then d[i] else 0).toNat < 256 := by
  split
  · exact UInt8.toNat_lt_size _
  · simp

private theorem shiftRight_mul_add (A r s t : Nat) (hr : r < 2 ^ s) :
    (A * 2 ^ s + r) >>> (t + s) = A >>> t := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h1 : (A * 2 ^ s + r) / 2 ^ s = A := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt hr]
    omega
  rw [show (2 : Nat) ^ (t + s) = 2 ^ s * 2 ^ t from by rw [Nat.pow_add, Nat.mul_comm],
    ← Nat.div_div_eq_div_mul, h1]

private theorem win16 (b0 b1 b2 t mask : Nat) (h1 : b1 < 256) (h2 : b2 < 256) :
    ((b0 * 256 + b1) * 256 + b2) >>> (t + 16) &&& mask = b0 >>> t &&& mask := by
  rw [show (b0 * 256 + b1) * 256 + b2 = b0 * 2 ^ 16 + (b1 * 256 + b2) from by omega,
    shiftRight_mul_add _ _ 16 _ (by omega)]

private theorem win8 (b0 b1 b2 t mask : Nat) (h2 : b2 < 256) :
    ((b0 * 256 + b1) * 256 + b2) >>> (t + 8) &&& mask = (b0 * 256 + b1) >>> t &&& mask := by
  rw [show (b0 * 256 + b1) * 256 + b2 = (b0 * 256 + b1) * 2 ^ 8 + b2 from by omega,
    shiftRight_mul_add _ _ 8 _ (by omega)]

private theorem acc1 (d : ByteArray) (p : Nat) :
    accBytes d p 1 0 = (if h : p < d.size then d[p] else 0).toNat := by simp [accBytes]

private theorem acc2 (d : ByteArray) (p : Nat) :
    accBytes d p 2 0 = (if h : p < d.size then d[p] else 0).toNat * 256
      + (if h : p + 1 < d.size then d[p + 1] else 0).toNat := by simp [accBytes]

private theorem acc3 (d : ByteArray) (p : Nat) :
    accBytes d p 3 0 = ((if h : p < d.size then d[p] else 0).toNat * 256
      + (if h : p + 1 < d.size then d[p + 1] else 0).toNat) * 256
      + (if h : p + 2 < d.size then d[p + 2] else 0).toNat := by simp [accBytes]

/-- **The three-byte window computes `extractBitsFast`** whenever the
    requested field fits in it. -/
theorem extractBits3_eq (d : ByteArray) (pos n : Nat) (h : pos % 8 + n ≤ 24) :
    extractBits3 d pos n (p2 n - 1) = extractBitsFast d pos n := by
  have hb : pos % 8 < 8 := Nat.mod_lt _ (by omega)
  have hcnt : (pos + n + 7) / 8 - pos / 8 = (pos % 8 + n + 7) / 8 := by omega
  have hsh : (8 - (pos + n) % 8) % 8 = 8 * ((pos % 8 + n + 7) / 8) - pos % 8 - n := by omega
  have h1 := byte_lt d (pos / 8 + 1)
  have h2 := byte_lt d (pos / 8 + 2)
  simp only [extractBits3, extractBitsFast]
  rw [hcnt, hsh]
  have hcase : (pos % 8 + n + 7) / 8 = 0 ∨ (pos % 8 + n + 7) / 8 = 1
      ∨ (pos % 8 + n + 7) / 8 = 2 ∨ (pos % 8 + n + 7) / 8 = 3 := by omega
  rcases hcase with hk | hk | hk | hk
  · have hn : n = 0 := by omega
    simp [hn]
  · rw [hk, acc1, show 24 - pos % 8 - n = (8 * 1 - pos % 8 - n) + 16 from by omega,
      win16 _ _ _ _ _ h1 h2]
  · rw [hk, acc2, show 24 - pos % 8 - n = (8 * 2 - pos % 8 - n) + 8 from by omega,
      win8 _ _ _ _ _ h2]
  · rw [hk, acc3, show 8 * 3 - pos % 8 - n = 24 - pos % 8 - n from by omega]

end Flac.Bits.BitReader
