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
  · rw [if_pos hb]
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
      rw [if_neg (by rw [bit_oob d pos (by omega)]; simp),
        ih (pos + 1) (q + 1) (by omega),
        List.drop_eq_nil_of_le (as := bytesToBits d)
          (by simp only [length_bytesToBits]; omega),
        List.drop_eq_nil_of_le (as := bytesToBits d)
          (by simp only [length_bytesToBits]; omega)]
      rfl

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

theorem readSInt_sim (n : Nat) (br : BitReader) :
    Bits.readSInt n (toStream br)
      = (br.readSInt n).map (fun p => (p.1, toStream p.2)) := by
  unfold Bits.readSInt BitReader.readSInt
  rw [readBits_sim n br]
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

end Flac.Bits.BitReader
