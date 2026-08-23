import Flac.Native.Emit
import Flac.Spec.Bits

/-!
# Emitter simulation — the production↔model transfer, writer side

`W.bits` is the model bitstream a writer state denotes. `Emits f bs`
says running `f` appends exactly `bs` to the denotation (and keeps the
accumulator normalized); every `W` primitive is proven to `Emits` its
`List Bool` model writer, and `Emits` composes along `++`, so the layers
above never reason about bytes again — the writer-side mirror of
`Flac.Spec.Reader`.
-/

namespace Flac.Emit

open Flac.Bits

/-- The model bitstream a writer state denotes: completed bytes, then
    the pending low `n` bits of `acc`. -/
def W.bits (w : W) : BitStream :=
  bytesToBits w.buf ++ writeBits w.n w.acc

/-- `f` appends exactly `bs` to the denotation (from any normalized
    state), leaving a normalized state. -/
def Emits (f : W → W) (bs : BitStream) : Prop :=
  ∀ w : W, w.n < 8 → (f w).bits = w.bits ++ bs ∧ (f w).n < 8

theorem emits_comp {f g : W → W} {bs cs : BitStream}
    (hf : Emits f bs) (hg : Emits g cs) :
    Emits (fun w => g (f w)) (bs ++ cs) := by
  intro w hw
  obtain ⟨hfb, hfn⟩ := hf w hw
  obtain ⟨hgb, hgn⟩ := hg (f w) hfn
  exact ⟨by rw [hgb, hfb, List.append_assoc], hgn⟩

theorem emits_congr {f g : W → W} {bs cs : BitStream}
    (hf : Emits f bs) (hfg : ∀ w, f w = g w) (hbc : bs = cs) :
    Emits g cs := by
  intro w hw
  rw [← hfg w, ← hbc]
  exact hf w hw

/-! ## Model `writeBits` arithmetic -/

/-- `writeBits` only reads the low `k` bits. -/
theorem writeBits_mod : ∀ (k v : Nat), writeBits k v = writeBits k (v % 2 ^ k) := by
  intro k
  induction k with
  | zero => intro v; rfl
  | succ k ih =>
    intro v
    have hhead : v % 2 ^ (k + 1) / 2 ^ k % 2 = v / 2 ^ k % 2 := by
      rw [Nat.mod_pow_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
        Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k))]
      omega
    show (decide (v / 2 ^ k % 2 = 1)) :: writeBits k v
      = (decide (v % 2 ^ (k + 1) / 2 ^ k % 2 = 1)) :: writeBits k (v % 2 ^ (k + 1))
    rw [hhead, ih v, ih (v % 2 ^ (k + 1)),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- Splitting a write at any midpoint (high bits first). -/
theorem writeBits_split : ∀ (m k v : Nat),
    writeBits (m + k) v = writeBits m (v >>> k) ++ writeBits k v := by
  intro m
  induction m with
  | zero =>
    intro k v
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    intro k v
    rw [show m + 1 + k = (m + k) + 1 from by omega]
    show (decide (v / 2 ^ (m + k) % 2 = 1)) :: writeBits (m + k) v = _
    show _ = (decide (v >>> k / 2 ^ m % 2 = 1)) :: writeBits m (v >>> k)
      ++ writeBits k v
    rw [ih k v, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add, Nat.add_comm k m]
    rfl

/-- All-zero writes are runs of zero bits. -/
theorem writeBits_zero : ∀ k, writeBits k 0 = List.replicate k false := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (decide (0 / 2 ^ k % 2 = 1)) :: writeBits k 0 = _
    rw [Nat.zero_div, ih]
    rfl

/-- A one in `q+1` bits is the unary code for `q`. -/
theorem writeBits_one (q : Nat) : writeBits (q + 1) 1 = writeUnary q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    show (decide (1 / 2 ^ (q + 1) % 2 = 1)) :: writeBits (q + 1) 1 = _
    rw [Nat.div_eq_of_lt (Nat.one_lt_two_pow_iff.mpr (by omega)), ih]
    rfl

/-- Unary codes chunk by 32 zero bits. -/
theorem writeUnary_chunk (q : Nat) (h : 32 ≤ q) :
    writeUnary q = writeBits 32 0 ++ writeUnary (q - 32) := by
  unfold writeUnary
  rw [writeBits_zero, show q = 32 + (q - 32) from by omega,
    ← List.replicate_append_replicate, List.append_assoc,
    show 32 + (q - 32) - 32 = q - 32 from by omega]

/-! ## Byte-level denotation -/

private theorem data_toList_push (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b
  simp [ByteArray.push]

theorem bytesToBits_push (buf : ByteArray) (b : UInt8) :
    bytesToBits (buf.push b) = bytesToBits buf ++ byteToBits b := by
  show byteListToBits (buf.push b).data.toList = _
  rw [data_toList_push]
  show (buf.data.toList ++ [b]).flatMap byteToBits = _
  rw [List.flatMap_append]
  rfl

/-! ## Primitive emissions -/

theorem flushGo_spec : ∀ (n : Nat) (buf : ByteArray) (acc : Nat),
    bytesToBits (W.flushGo buf acc n).1
        ++ writeBits (W.flushGo buf acc n).2.2 (W.flushGo buf acc n).2.1
      = bytesToBits buf ++ writeBits n acc
    ∧ (W.flushGo buf acc n).2.2 < 8 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro buf acc
    unfold W.flushGo
    by_cases h : n < 8
    · rw [dif_pos h]
      exact ⟨rfl, h⟩
    · rw [dif_neg h]
      obtain ⟨hb, hn⟩ := ih (n - 8) (by omega)
        (buf.push (UInt8.ofNat (acc >>> (n - 8)))) (acc &&& (p2 (n - 8) - 1))
      refine ⟨?_, hn⟩
      rw [hb, bytesToBits_push, List.append_assoc]
      congr 1
      show byteToBits (UInt8.ofNat (acc >>> (n - 8)))
          ++ writeBits (n - 8) (acc &&& (p2 (n - 8) - 1)) = writeBits n acc
      have hsplit : writeBits n acc
          = writeBits 8 (acc >>> (n - 8)) ++ writeBits (n - 8) acc := by
        rw [show writeBits n acc = writeBits (8 + (n - 8)) acc from by
              rw [show 8 + (n - 8) = n from by omega],
          writeBits_split]
      rw [hsplit]
      congr 1
      · show writeBits 8 (UInt8.ofNat (acc >>> (n - 8))).toNat = _
        rw [UInt8.toNat_ofNat']
        exact (writeBits_mod 8 (acc >>> (n - 8))).symm
      · rw [p2_eq, Nat.and_two_pow_sub_one_eq_mod]
        exact (writeBits_mod _ acc).symm

theorem emits_push (k v : Nat) : Emits (fun w => w.push k v) (writeBits k v) := by
  intro w hw
  unfold W.push
  obtain ⟨hb, hn⟩ := flushGo_spec (w.n + k) w.buf (w.acc * p2 k + (v &&& (p2 k - 1)))
  refine ⟨?_, hn⟩
  show bytesToBits _ ++ writeBits _ _ = _
  rw [hb]
  unfold W.bits
  rw [List.append_assoc]
  congr 1
  rw [writeBits_split w.n k, Nat.shiftRight_eq_div_pow, p2_eq,
    Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  · congr 1
    rw [Nat.mul_comm w.acc (2 ^ k), Nat.mul_add_div (Nat.two_pow_pos k),
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k)), Nat.add_zero]
  · rw [Nat.mul_comm w.acc (2 ^ k), writeBits_mod k (2 ^ k * w.acc + v % 2 ^ k),
      Nat.mul_add_mod, Nat.mod_mod, ← writeBits_mod]

theorem emits_pushBits (k v : Nat) :
    Emits (fun w => w.pushBits k v) (writeBits k v) := by
  induction k using Nat.strongRecOn generalizing v with
  | ind k ih =>
    intro w hw
    show (w.pushBits k v).bits = w.bits ++ writeBits k v ∧ (w.pushBits k v).n < 8
    unfold W.pushBits
    by_cases h : k ≤ 32
    · rw [dif_pos h]
      exact emits_push k v w hw
    · rw [dif_neg h]
      have h1 := ih (k - 32) (by omega) (v >>> 32) w hw
      have h2 := emits_push 32 (v &&& 0xFFFFFFFF) (w.pushBits (k - 32) (v >>> 32)) h1.2
      refine ⟨?_, h2.2⟩
      rw [h2.1, h1.1, List.append_assoc]
      congr 1
      rw [show writeBits k v = writeBits ((k - 32) + 32) v from by
            rw [show (k - 32) + 32 = k from by omega],
        writeBits_split (k - 32) 32 v]
      congr 1
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      exact (writeBits_mod 32 v).symm

theorem emits_pushUnary (q : Nat) :
    Emits (fun w => w.pushUnary q) (writeUnary q) := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro w hw
    show (w.pushUnary q).bits = w.bits ++ writeUnary q ∧ (w.pushUnary q).n < 8
    unfold W.pushUnary
    by_cases h : q < 32
    · rw [dif_pos h]
      have := emits_push (q + 1) 1 w hw
      rw [writeBits_one q] at this
      exact this
    · rw [dif_neg h]
      have h1 := emits_push 32 0 w hw
      have h2 := ih (q - 32) (by omega) (w.push 32 0) h1.2
      refine ⟨?_, h2.2⟩
      rw [h2.1, h1.1, List.append_assoc, writeUnary_chunk q (by omega)]

theorem emits_pushSInt (k : Nat) (x : Int) :
    Emits (fun w => w.pushSInt k x) (writeSInt k x) := by
  apply emits_congr
    (emits_pushBits k ((x + ((p2 k : Nat) : Int)).toNat &&& (p2 k - 1)))
    (fun w => rfl)
  unfold writeSInt
  rw [p2_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem emits_pushRice (k : Nat) (x : Int) :
    Emits (fun w => w.pushRice k x) (Rice.writeRice k x) := by
  intro w hw
  unfold W.pushRice Rice.writeRice Rice.writeRiceNat
  have h1 := emits_pushUnary (Rice.zigzag x >>> k) w hw
  have h2 := emits_push k (Rice.zigzag x &&& (p2 k - 1)) _ h1.2
  refine ⟨?_, h2.2⟩
  rw [h2.1, h1.1, List.append_assoc, Nat.shiftRight_eq_div_pow, p2_eq,
    Nat.and_two_pow_sub_one_eq_mod, ← writeBits_mod]


/-! ## Sequence and partition emissions -/

private theorem getD_lt (xs : Array Int) {i : Nat} (h : i < xs.size) :
    xs.getD i 0 = xs[i] := by
  simp [Array.getD, h]

private theorem drop_toList_cons (xs : Array Int) {i : Nat} (h : i < xs.size) :
    xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

private theorem drop_toList_nil (xs : Array Int) {i : Nat} (h : ¬ i < xs.size) :
    xs.toList.drop i = [] := by
  apply List.drop_eq_nil_of_le
  simpa using by omega

theorem emits_pushSIntSeg (b : Nat) (xs : Array Int) :
    ∀ (len start : Nat),
      Emits (fun w => W.pushSIntSeg b xs start len w)
        (Rice.writeSIntSeq b ((xs.toList.drop start).take len)) := by
  intro len
  induction len with
  | zero =>
    intro start w hw
    refine ⟨?_, hw⟩
    simp [W.pushSIntSeg, W.bits, Rice.writeSIntSeq]
  | succ len ih =>
    intro start
    by_cases h : start < xs.size
    · apply emits_congr
        (emits_comp (emits_pushSInt b (xs.getD start 0)) (ih (start + 1)))
        (fun w => by
          show _ = W.pushSIntSeg b xs start (len + 1) w
          simp only [W.pushSIntSeg, h, if_true])
      rw [drop_toList_cons xs h, List.take_succ_cons, getD_lt xs h]
      rfl
    · intro w hw
      have heq : W.pushSIntSeg b xs start (len + 1) w = w := by
        unfold W.pushSIntSeg
        rw [if_neg h]
      rw [drop_toList_nil xs h]
      refine ⟨?_, by rw [show ((fun w => W.pushSIntSeg b xs start (len + 1) w) w)
        = w from heq]; exact hw⟩
      rw [show ((fun w => W.pushSIntSeg b xs start (len + 1) w) w) = w from heq]
      simp [Rice.writeSIntSeq]

theorem emits_pushRiceSeg (k : Nat) (xs : Array Int) :
    ∀ (len start : Nat),
      Emits (fun w => W.pushRiceSeg k xs start len w)
        (Rice.writeRiceSeq k ((xs.toList.drop start).take len)) := by
  intro len
  induction len with
  | zero =>
    intro start w hw
    refine ⟨?_, hw⟩
    simp [W.pushRiceSeg, W.bits, Rice.writeRiceSeq]
  | succ len ih =>
    intro start
    by_cases h : start < xs.size
    · apply emits_congr
        (emits_comp (emits_pushRice k (xs.getD start 0)) (ih (start + 1)))
        (fun w => by
          show _ = W.pushRiceSeg k xs start (len + 1) w
          simp only [W.pushRiceSeg, h, if_true])
      rw [drop_toList_cons xs h, List.take_succ_cons, getD_lt xs h]
      rfl
    · intro w hw
      have heq : W.pushRiceSeg k xs start (len + 1) w = w := by
        unfold W.pushRiceSeg
        rw [if_neg h]
      rw [drop_toList_nil xs h]
      refine ⟨?_, by rw [show ((fun w => W.pushRiceSeg k xs start (len + 1) w) w)
        = w from heq]; exact hw⟩
      rw [show ((fun w => W.pushRiceSeg k xs start (len + 1) w) w) = w from heq]
      simp [Rice.writeRiceSeq]

theorem emits_pushSIntList (b : Nat) :
    ∀ (l : List Int),
      Emits (fun w => W.pushSIntList b l w) (Rice.writeSIntSeq b l) := by
  intro l
  induction l with
  | nil =>
    intro w hw
    refine ⟨?_, hw⟩
    simp [W.pushSIntList, Rice.writeSIntSeq]
  | cons x t ih =>
    apply emits_congr (emits_comp (emits_pushSInt b x) ih) (fun w => rfl)
    rfl

theorem emits_pushParts (m : Rice.Method) (res : Array Int) :
    ∀ (choices : List Rice.Partition) (sizes : List Nat) (start : Nat),
      Emits (fun w => W.pushParts m res choices sizes start w)
        (Rice.writeParts m
          (choices.zip (Rice.chunkBySizes sizes (res.toList.drop start)))) := by
  intro choices
  induction choices with
  | nil =>
    intro sizes start w hw
    refine ⟨?_, hw⟩
    simp [W.pushParts, Rice.writeParts]
  | cons ch choices ih =>
    intro sizes start
    match sizes with
    | [] =>
      intro w hw
      refine ⟨?_, hw⟩
      show w.bits = w.bits ++ Rice.writeParts m ((ch :: choices).zip
        (Rice.chunkBySizes [] (res.toList.drop start)))
      simp [W.pushParts, Rice.chunkBySizes, Rice.writeParts]
    | sz :: sizes =>
      have hrest : ∀ w', W.pushParts m res (ch :: choices) (sz :: sizes) start w'
          = W.pushParts m res choices sizes (start + sz)
              (match ch with
               | .rice k => W.pushRiceSeg k res start sz (w'.push m.paramBits k)
               | .escape bits =>
                 W.pushSIntSeg bits res start sz
                   ((w'.push m.paramBits m.escapeCode).push 5 bits)) :=
        fun w' => rfl
      have hchunk : Rice.chunkBySizes (sz :: sizes) (res.toList.drop start)
          = (res.toList.drop start).take sz
            :: Rice.chunkBySizes sizes (res.toList.drop (start + sz)) := by
        show (res.toList.drop start).take sz
            :: Rice.chunkBySizes sizes ((res.toList.drop start).drop sz) = _
        rw [List.drop_drop]
      match ch with
      | .rice k =>
        apply emits_congr
          (emits_comp
            (emits_comp (emits_push m.paramBits k) (emits_pushRiceSeg k res sz start))
            (ih sizes (start + sz)))
          (fun w => (hrest w).symm)
        rw [hchunk, List.zip_cons_cons]
        unfold Rice.writeParts
        rw [List.flatMap_cons]
        simp [Rice.writePart, List.append_assoc, Rice.writeParts]
      | .escape bits =>
        apply emits_congr
          (emits_comp
            (emits_comp
              (emits_comp (emits_push m.paramBits m.escapeCode) (emits_push 5 bits))
              (emits_pushSIntSeg bits res sz start))
            (ih sizes (start + sz)))
          (fun w => (hrest w).symm)
        rw [hchunk, List.zip_cons_cons]
        unfold Rice.writeParts
        rw [List.flatMap_cons]
        simp [Rice.writePart, List.append_assoc, Rice.writeParts]

theorem emits_pushResidual (bs ord : Nat) (cfg : Rice.ResidualCfg)
    (res : Array Int) :
    Emits (fun w => W.pushResidual bs ord cfg res w)
      (Rice.writeResidual bs ord cfg res.toList) := by
  apply emits_congr
    (emits_comp
      (emits_comp (emits_push 2 cfg.method.code) (emits_push 4 cfg.po))
      (emits_pushParts cfg.method res cfg.choices
        (Rice.partSizes bs cfg.po ord) 0))
    (fun w => rfl)
  unfold Rice.writeResidual
  rw [List.drop_zero, List.append_assoc]

end Flac.Emit
