import Flac.Native.Emit
import Flac.Spec.Bits
import Flac.Spec.Crc
import Flac.Spec.Fixed
import Flac.Spec.Lpc
import Flac.Spec.Stereo
import Flac.Spec.Stream

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

theorem bytesToBits_append (a b : ByteArray) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits, byteListToBits, List.flatMap_append]

private theorem byteToBits_injective : Function.Injective byteToBits := by
  intro a b h
  have ha : readBits 8 (byteToBits a) = some (a.toNat, []) := by
    unfold byteToBits
    exact readBits_writeBits 8 a.toNat [] (UInt8.toNat_lt_size a)
  have hb : readBits 8 (byteToBits b) = some (b.toNat, []) := by
    unfold byteToBits
    exact readBits_writeBits 8 b.toNat [] (UInt8.toNat_lt_size b)
  rw [h, hb] at ha
  exact UInt8.toNat.inj (congrArg Prod.fst (Option.some.inj ha)).symm

private theorem byteListToBits_injective : Function.Injective byteListToBits := by
  intro a
  induction a with
  | nil =>
    intro b h
    match b with
    | [] => rfl
    | x :: xs =>
      have hl := congrArg List.length h
      simp only [byteListToBits, List.flatMap_nil, List.flatMap_cons,
        List.length_nil, List.length_append, byteToBits, length_writeBits] at hl
      omega
  | cons x xs ih =>
    intro b h
    match b with
    | [] =>
      have hl := congrArg List.length h
      simp only [byteListToBits, List.flatMap_nil, List.flatMap_cons,
        List.length_nil, List.length_append, byteToBits, length_writeBits] at hl
      omega
    | y :: ys =>
      simp only [byteListToBits, List.flatMap_cons] at h
      have hh := congrArg (List.take 8) h
      have ht := congrArg (List.drop 8) h
      rw [List.take_left' (by simp [byteToBits]),
        List.take_left' (by simp [byteToBits])] at hh
      rw [List.drop_left' (by simp [byteToBits]),
        List.drop_left' (by simp [byteToBits])] at ht
      have hxy : x = y := byteToBits_injective hh
      subst y
      have hrest : xs = ys := ih ht
      subst ys
      rfl

theorem bytesToBits_injective : Function.Injective bytesToBits := by
  intro a b h
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact byteListToBits_injective h

@[simp] theorem length_byteListToBits (l : List UInt8) :
    (byteListToBits l).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [byteListToBits_cons]
    simp only [List.length_append, byteToBits, length_writeBits, ih,
      List.length_cons]
    omega

@[simp] theorem length_bytesToBits (d : ByteArray) :
    (bytesToBits d).length = 8 * d.size := by
  show (byteListToBits d.data.toList).length = 8 * d.data.size
  simp only [length_byteListToBits, Array.length_toList]

@[simp] theorem length_W_bits (w : W) :
    w.bits.length = 8 * w.buf.size + w.n := by
  simp [W.bits]

/-- An aligned emission materializes exactly the emitted model bits as a
    byte-array suffix. This is the bridge used by the frame CRCs. -/
theorem emits_aligned_buf {f : W → W} {bs : BitStream}
    (hf : Emits f bs) (w : W) (hw : w.n = 0) (hbs : 8 ∣ bs.length) :
    (f w).n = 0 ∧ (f w).buf = w.buf ++ bitsToBytes bs := by
  obtain ⟨hbits, hn⟩ := hf w (by omega)
  obtain ⟨k, hk⟩ := hbs
  have hlen := congrArg List.length hbits
  simp only [length_W_bits, List.length_append] at hlen
  have hout : (f w).n = 0 := by omega
  refine ⟨hout, ?_⟩
  apply bytesToBits_injective
  rw [bytesToBits_append, bytesToBits_bitsToBytes bs ⟨k, hk⟩]
  simpa [W.bits, writeBits, hw, hout] using hbits

/-- Pointwise form of `emits_aligned_buf`, useful for aligned emitters
    whose padding depends on their concrete input state. -/
theorem aligned_buf_of_bits {w out : W} {bs : BitStream}
    (hw : w.n = 0) (hout : out.n = 0)
    (hbits : out.bits = w.bits ++ bs) (hbs : 8 ∣ bs.length) :
    out.buf = w.buf ++ bitsToBytes bs := by
  obtain ⟨k, hk⟩ := hbs
  apply bytesToBits_injective
  rw [bytesToBits_append, bytesToBits_bitsToBytes bs ⟨k, hk⟩]
  simpa [W.bits, writeBits, hw, hout] using hbits

/-- From an aligned input, the pending-bit count is determined by the
    emitted model length. -/
theorem emits_pending_mod {f : W → W} {bs : BitStream}
    (hf : Emits f bs) (w : W) (hw : w.n = 0) :
    (f w).n = bs.length % 8 := by
  obtain ⟨hbits, hn⟩ := hf w (by omega)
  have hlen := congrArg List.length hbits
  simp only [length_W_bits, List.length_append] at hlen
  omega

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

/-! ## Array predictor residuals compute the list residuals -/

private theorem take_all_of_ge {l : List Int} {n : Nat} (h : l.length ≤ n) :
    l.take n = l :=
  List.take_of_length_le h

theorem diffGo_toList (xs : Array Int) :
    ∀ (rem i : Nat) (acc : Array Int), i + rem + 1 ≤ xs.size →
      (Flac.Emit.diffGo xs i rem acc).toList
        = acc.toList ++ (Fixed.diff1 (xs.toList.drop i)).take rem := by
  intro rem
  induction rem with
  | zero => intro i acc _; simp [Flac.Emit.diffGo]
  | succ rem ih =>
    intro i acc h
    have hi : i < xs.size := by omega
    have hi1 : i + 1 < xs.size := by omega
    show (Flac.Emit.diffGo xs (i + 1) rem
      (acc.push (xs.getD (i + 1) 0 - xs.getD i 0))).toList = _
    rw [ih (i + 1) _ (by omega), Array.toList_push, List.append_assoc]
    congr 1
    rw [getD_lt xs hi, getD_lt xs hi1, drop_toList_cons xs hi,
      drop_toList_cons xs hi1,
      show Fixed.diff1 (xs[i] :: xs[i + 1] :: xs.toList.drop (i + 1 + 1))
        = (xs[i + 1] - xs[i]) :: Fixed.diff1 (xs[i + 1] :: xs.toList.drop (i + 1 + 1))
        from rfl,
      List.take_succ_cons]
    rfl

theorem diffA_toList (xs : Array Int) :
    (Flac.Emit.diffA xs).toList = Fixed.diff1 xs.toList := by
  unfold Flac.Emit.diffA
  by_cases h : xs.size = 0
  · have hnil : xs.toList = [] := by
      have := Array.length_toList (xs := xs)
      rw [h] at this
      exact List.eq_nil_of_length_eq_zero this
    rw [h, hnil]
    show (Flac.Emit.diffGo xs 0 0 _).toList = Fixed.diff1 []
    simp [Flac.Emit.diffGo]
  · rw [diffGo_toList xs (xs.size - 1) 0 _ (by omega), List.drop_zero,
      take_all_of_ge (by rw [Fixed.length_diff1, Array.length_toList]; omega)]
    simp

theorem fixedResA_toList (xs : Array Int) :
    ∀ ord, (Flac.Emit.fixedResA ord xs).toList = Fixed.residual ord xs.toList := by
  intro ord
  induction ord with
  | zero => rfl
  | succ ord ih =>
    show (Flac.Emit.diffA (Flac.Emit.fixedResA ord xs)).toList = _
    rw [diffA_toList, ih]
    rfl

private theorem take_succ_reverse (xs : Array Int) {i : Nat} (hi : i < xs.size) :
    (xs.toList.take (i + 1)).reverse = xs[i] :: (xs.toList.take i).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem lpcResGo_toList (cs : List Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (acc : Array Int), cs.length ≤ i → i + rem ≤ xs.size →
      (Flac.Emit.lpcResGo cs shift xs i rem acc).toList
        = acc.toList
          ++ Lpc.residualAux cs shift (xs.toList.take i).reverse
              ((xs.toList.drop i).take rem) := by
  intro rem
  induction rem with
  | zero => intro i acc _ _; simp [Flac.Emit.lpcResGo, Lpc.residualAux]
  | succ rem ih =>
    intro i acc hord h
    have hi : i < xs.size := by omega
    have hpred : Flac.Bits.sar (Lpc.dotA cs xs (i - 1)) shift
        = Lpc.predict cs shift (xs.toList.take i).reverse := by
      unfold Lpc.predict
      congr 1
      match hcs : cs with
      | [] => rfl
      | c :: cs' =>
        have hi0 : 0 < i := by
          have := hord
          simp at this
          omega
        rw [Lpc.dotA_take xs (c :: cs') (i - 1) (by omega),
          show i - 1 + 1 = i from by omega]
    show (Flac.Emit.lpcResGo cs shift xs (i + 1) rem
      (acc.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dotA cs xs (i - 1)) shift))).toList = _
    rw [ih (i + 1) _ (by omega) (by omega), Array.toList_push, List.append_assoc]
    congr 1
    rw [getD_lt xs hi, hpred, drop_toList_cons xs hi, List.take_succ_cons,
      take_succ_reverse xs hi]
    rfl


/-! ### The tap-specialised residual loops are `lpcResGo` at a fixed list -/

private theorem lpcResGo1_eq (c0 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo1 c0 shift xs i rem out
        = Flac.Emit.lpcResGo [c0] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo1, Flac.Emit.lpcResGo, Lpc.dot1At_eq]
    exact ih _ _

private theorem lpcResGo2_eq (c0 c1 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo2 c0 c1 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo2, Flac.Emit.lpcResGo, Lpc.dot2At_eq]
    exact ih _ _

private theorem lpcResGo3_eq (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo3 c0 c1 c2 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1, c2] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo3, Flac.Emit.lpcResGo, Lpc.dot3At_eq]
    exact ih _ _

private theorem lpcResGo4_eq (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo4 c0 c1 c2 c3 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1, c2, c3] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo4, Flac.Emit.lpcResGo, Lpc.dot4At_eq]
    exact ih _ _

private theorem lpcResGo5_eq (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo5 c0 c1 c2 c3 c4 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1, c2, c3, c4] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo5, Flac.Emit.lpcResGo, Lpc.dot5At_eq]
    exact ih _ _

private theorem lpcResGo6_eq (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1, c2, c3, c4, c5] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo6, Flac.Emit.lpcResGo, Lpc.dot6At_eq]
    exact ih _ _

private theorem lpcResGo7_eq (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1, c2, c3, c4, c5, c6] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo7, Flac.Emit.lpcResGo, Lpc.dot7At_eq]
    exact ih _ _

private theorem lpcResGo8_eq (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      Flac.Emit.lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out
        = Flac.Emit.lpcResGo [c0, c1, c2, c3, c4, c5, c6, c7] shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intro i out; rfl
  | succ rem ih =>
    intro i out
    simp only [Flac.Emit.lpcResGo8, Flac.Emit.lpcResGo, Lpc.dot8At_eq]
    exact ih _ _

/-- The dispatching `lpcResA` is the generic loop it replaced. -/
theorem lpcResA_generic (cs : List Int) (shift : Nat) (xs : Array Int) :
    Flac.Emit.lpcResA cs shift xs
      = Flac.Emit.lpcResGo cs shift xs cs.length (xs.size - cs.length)
          (Array.emptyWithCapacity (xs.size - cs.length)) := by
  unfold Flac.Emit.lpcResA
  match cs with
  | [] => rfl
  | [c0] => exact lpcResGo1_eq _ _ _ _ _ _
  | [c0, c1] => exact lpcResGo2_eq _ _ _ _ _ _ _
  | [c0, c1, c2] => exact lpcResGo3_eq _ _ _ _ _ _ _ _
  | [c0, c1, c2, c3] => exact lpcResGo4_eq _ _ _ _ _ _ _ _ _
  | [c0, c1, c2, c3, c4] => exact lpcResGo5_eq _ _ _ _ _ _ _ _ _ _
  | [c0, c1, c2, c3, c4, c5] => exact lpcResGo6_eq _ _ _ _ _ _ _ _ _ _ _
  | [c0, c1, c2, c3, c4, c5, c6] => exact lpcResGo7_eq _ _ _ _ _ _ _ _ _ _ _ _
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
    exact lpcResGo8_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem lpcResA_toList (cs : List Int) (shift : Nat) (xs : Array Int) :
    (Flac.Emit.lpcResA cs shift xs).toList = Lpc.residual cs shift xs.toList := by
  rw [lpcResA_generic]
  unfold Lpc.residual
  by_cases h : cs.length ≤ xs.size
  · rw [lpcResGo_toList cs shift xs (xs.size - cs.length) cs.length _ (by omega)
      (by omega)]
    show (Array.emptyWithCapacity (xs.size - cs.length) : Array Int).toList ++ _ = _
    rw [Array.emptyWithCapacity_eq]
    show [] ++ _ = _
    rw [List.nil_append]
    congr 1
    apply take_all_of_ge
    rw [List.length_drop, Array.length_toList]
    omega
  · rw [show xs.size - cs.length = 0 from by omega]
    show (Flac.Emit.lpcResGo cs shift xs cs.length 0 _).toList = _
    have hdrop : xs.toList.drop cs.length = [] := by
      apply List.drop_eq_nil_of_le
      rw [Array.length_toList]
      omega
    rw [hdrop]
    simp [Flac.Emit.lpcResGo, Lpc.residualAux]

/-! ## Subframe emissions -/

private theorem getD_zero_headD (xs : Array Int) :
    xs.getD 0 0 = xs.toList.headD 0 := by
  by_cases h : 0 < xs.size
  · rw [getD_lt xs h, List.headD_eq_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h)]
    simp
  · have hnil : xs.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Array.length_toList]
      omega
    rw [hnil]
    simp [Array.getD, show ¬ 0 < xs.size from h]

private theorem seg_take (xs : Array Int) (len : Nat) :
    (xs.toList.drop 0).take len = xs.toList.take len := by
  rw [List.drop_zero]

theorem emits_pushContent (b : Nat) (cfg : Subframe.SubframeCfg)
    (xs : Array Int) :
    Emits (fun w => W.pushContent b cfg xs w)
      (Subframe.writeContent b cfg xs.toList) := by
  match cfg with
  | .constant =>
    apply emits_congr (emits_pushSInt b (xs.getD 0 0)) (fun w => rfl)
    unfold Subframe.writeContent
    rw [getD_zero_headD]
  | .verbatim =>
    apply emits_congr (emits_pushSIntSeg b xs xs.size 0) (fun w => rfl)
    unfold Subframe.writeContent
    rw [seg_take, take_all_of_ge (by rw [Array.length_toList]; omega)]
  | .fixed ord rcfg =>
    apply emits_congr
      (emits_comp (emits_pushSIntSeg b xs ord 0)
        (emits_pushResidual xs.size ord rcfg (fixedResA ord xs)))
      (fun w => rfl)
    unfold Subframe.writeContent
    rw [seg_take, fixedResA_toList, Array.length_toList]
  | .lpc cs shift prec rcfg =>
    apply emits_congr
      (emits_comp
        (emits_comp
          (emits_comp
            (emits_comp (emits_pushSIntSeg b xs cs.length 0)
              (emits_push 4 (prec - 1)))
            (emits_pushSInt 5 (shift : Int)))
          (emits_pushSIntList prec cs))
        (emits_pushResidual xs.size cs.length rcfg (lpcResA cs shift xs)))
      (fun w => rfl)
    unfold Subframe.writeContent
    rw [seg_take, lpcResA_toList, Array.length_toList]
    simp [List.append_assoc]

theorem emits_pushSubframe (b : Nat) (sc : Subframe.SubCfg) (xs : Array Int) :
    Emits (fun w => W.pushSubframe b sc xs w)
      (Subframe.write b sc xs.toList) := by
  unfold Subframe.write
  by_cases h : sc.wasted = 0
  · apply emits_congr
      (emits_comp
        (emits_comp (emits_comp (emits_push 1 0) (emits_push 6 sc.inner.typeCode))
          (emits_push 1 0))
        (emits_pushContent (b - sc.wasted) sc.inner xs))
      (fun w => by
        show _ = W.pushSubframe b sc xs w
        unfold W.pushSubframe
        simp only [h, if_true])
    rw [if_pos h, h, map_shiftDown_zero]
  · apply emits_congr
      (emits_comp
        (emits_comp
          (emits_comp (emits_comp (emits_push 1 0) (emits_push 6 sc.inner.typeCode))
            (emits_push 1 1))
          (emits_pushUnary (sc.wasted - 1)))
        (emits_pushContent (b - sc.wasted) sc.inner
          (xs.map (Flac.Bits.shiftDown sc.wasted))))
      (fun w => by
        show _ = W.pushSubframe b sc xs w
        unfold W.pushSubframe
        simp only [h, if_false])
    rw [if_neg h, Array.toList_map]
    simp [List.append_assoc]

/-! ## Coded numbers and frame headers -/

private theorem pow_64_eq (k : Nat) : 64 ^ k = 2 ^ (6 * k) := by
  rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.pow_mul]

theorem emits_pushConts (v : Nat) : ∀ k,
    Emits (fun w => W.pushConts v k w) (Utf8Num.writeConts k v) := by
  intro k
  induction k with
  | zero =>
    intro w hw
    exact ⟨by simp [W.pushConts, W.bits, Utf8Num.writeConts], hw⟩
  | succ k ih =>
    apply emits_congr
      (emits_comp
        (emits_push 8 (0x80 + v / p2 (6 * k) % 64)) ih)
      (fun w => rfl)
    change writeBits 8 (0x80 + v / p2 (6 * k) % 64) ++
        Utf8Num.writeConts k v =
      Utf8Num.writeContByte (v / 64 ^ k) ++ Utf8Num.writeConts k v
    unfold Utf8Num.writeContByte
    rw [p2_eq, ← pow_64_eq]

@[simp] theorem length_writeConts (k v : Nat) :
    (Utf8Num.writeConts k v).length = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Utf8Num.writeConts, Utf8Num.writeContByte, List.length_append,
      length_writeBits, ih]
    omega

theorem utf8_write_length_dvd (v : Nat) : 8 ∣ (Utf8Num.write v).length := by
  unfold Utf8Num.write
  by_cases h7 : v < 2 ^ 7
  · simp [h7]
  · simp only [h7, if_false]
    by_cases h11 : v < 2 ^ 11
    · simp [h11]
    · simp only [h11, if_false]
      by_cases h16 : v < 2 ^ 16
      · simp [h16]
      · simp only [h16, if_false]
        by_cases h21 : v < 2 ^ 21
        · simp [h21]
        · simp only [h21, if_false]
          by_cases h26 : v < 2 ^ 26
          · simp [h26]
          · simp only [h26, if_false]
            by_cases h31 : v < 2 ^ 31
            · simp [h31]
            · simp [h31]

theorem emits_pushUtf8 (v : Nat) :
    Emits (fun w => W.pushUtf8 v w) (Utf8Num.write v) := by
  unfold W.pushUtf8 Utf8Num.write
  simp only [p2_eq]
  by_cases h7 : v < 2 ^ 7
  · simp only [h7, if_true]
    exact emits_push 8 v
  · simp only [h7, if_false]
    by_cases h11 : v < 2 ^ 11
    · simp only [h11, if_true]
      exact emits_congr
        (emits_comp (emits_push 8 (0xC0 + v / 2 ^ 6)) (emits_pushConts v 1))
        (fun w => rfl) rfl
    · simp only [h11, if_false]
      by_cases h16 : v < 2 ^ 16
      · simp only [h16, if_true]
        exact emits_congr
          (emits_comp (emits_push 8 (0xE0 + v / 2 ^ 12)) (emits_pushConts v 2))
          (fun w => rfl) rfl
      · simp only [h16, if_false]
        by_cases h21 : v < 2 ^ 21
        · simp only [h21, if_true]
          exact emits_congr
            (emits_comp (emits_push 8 (0xF0 + v / 2 ^ 18)) (emits_pushConts v 3))
            (fun w => rfl) rfl
        · simp only [h21, if_false]
          by_cases h26 : v < 2 ^ 26
          · simp only [h26, if_true]
            exact emits_congr
              (emits_comp (emits_push 8 (0xF8 + v / 2 ^ 24)) (emits_pushConts v 4))
              (fun w => rfl) rfl
          · simp only [h26, if_false]
            by_cases h31 : v < 2 ^ 31
            · simp only [h31, if_true]
              exact emits_congr
                (emits_comp (emits_push 8 (0xFC + v / 2 ^ 30))
                  (emits_pushConts v 5))
                (fun w => rfl) rfl
            · simp only [h31, if_false]
              exact emits_congr
                (emits_comp (emits_push 8 0xFE) (emits_pushConts v 6))
                (fun w => rfl) rfl

theorem emits_pushHeaderCore (b : Nat) (strat : Bool) (num bs chCode : Nat) :
    Emits (fun w => W.pushHeaderCore b strat num bs chCode w)
      (Frame.headerCore b strat num bs chCode) := by
  let h0 := emits_push 14 0x3FFE
  let h1 := emits_comp h0 (emits_push 1 0)
  let h2 := emits_comp h1 (emits_push 1 (if strat then 1 else 0))
  let h3 := emits_comp h2 (emits_push 4 7)
  let h4 := emits_comp h3 (emits_push 4 0)
  let h5 := emits_comp h4 (emits_push 4 chCode)
  let h6 := emits_comp h5 (emits_push 3 (Frame.bpsCode b))
  let h7 := emits_comp h6 (emits_push 1 0)
  let h8 := emits_comp h7 (emits_pushUtf8 num)
  let h9 := emits_comp h8 (emits_push 16 (bs - 1))
  apply emits_congr h9 (fun w => rfl)
  simp [Frame.headerCore, List.append_assoc]

theorem headerCore_length_dvd (b : Nat) (strat : Bool) (num bs chCode : Nat) :
    8 ∣ (Frame.headerCore b strat num bs chCode).length := by
  obtain ⟨k, hk⟩ := utf8_write_length_dvd num
  refine ⟨k + 6, ?_⟩
  simp only [Frame.headerCore, List.length_append, length_writeBits]
  omega

/-! ## Frame subframe plans -/

private def planToLists
    (plan : List ((Nat × Subframe.SubCfg) × Array Int)) :
    List ((Nat × Subframe.SubCfg) × List Int) :=
  plan.map fun p => ((p.1.1, p.1.2), p.2.toList)

theorem planA_toLists (b : Nat) (asg : Frame.ChannelAsg)
    (chs : List (Array Int)) :
    planToLists (W.planA b asg chs) =
      Frame.subframePlan b asg (chs.map Array.toList) := by
  match asg, chs with
  | .independent cfgs, chs =>
    induction cfgs generalizing chs with
    | nil => simp [planToLists, W.planA, Frame.subframePlan]
    | cons cfg cfgs ih =>
      match chs with
      | [] => rfl
      | ch :: chs =>
        simp [planToLists, W.planA, Frame.subframePlan]
        exact ih chs
  | .leftSide c0 c1, [] => rfl
  | .leftSide c0 c1, [_] => rfl
  | .leftSide c0 c1, [l, r] =>
    simp [planToLists, W.planA, Frame.subframePlan]
  | .leftSide c0 c1, _ :: _ :: _ :: _ => rfl
  | .rightSide c0 c1, [] => rfl
  | .rightSide c0 c1, [_] => rfl
  | .rightSide c0 c1, [l, r] =>
    simp [planToLists, W.planA, Frame.subframePlan]
  | .rightSide c0 c1, _ :: _ :: _ :: _ => rfl
  | .midSide c0 c1, [] => rfl
  | .midSide c0 c1, [_] => rfl
  | .midSide c0 c1, [l, r] =>
    simp [planToLists, W.planA, Frame.subframePlan]
  | .midSide c0 c1, _ :: _ :: _ :: _ => rfl

theorem emits_pushPlan : ∀ plan : List ((Nat × Subframe.SubCfg) × Array Int),
    Emits (fun w => W.pushPlan plan w)
      (Frame.writeSubframes (planToLists plan)) := by
  intro plan
  induction plan with
  | nil =>
    intro w hw
    exact ⟨by simp [W.pushPlan, W.bits, Frame.writeSubframes, planToLists], hw⟩
  | cons p ps ih =>
    apply emits_congr
      (emits_comp (emits_pushSubframe p.1.1 p.1.2 p.2) ih)
      (fun w => rfl)
    rfl

theorem emits_pushPlanA (b : Nat) (asg : Frame.ChannelAsg)
    (chs : List (Array Int)) :
    Emits (fun w => W.pushPlan (W.planA b asg chs) w)
      (Frame.writeSubframes
        (Frame.subframePlan b asg (chs.map Array.toList))) := by
  apply emits_congr (emits_pushPlan (W.planA b asg chs)) (fun w => rfl)
  rw [planA_toLists]

/-! ## Complete frames -/

/-- On a byte-aligned input, the native frame emitter appends exactly the
    model frame and finishes byte-aligned. -/
theorem pushFrame_spec (b : Nat) (strat : Bool) (num : Nat)
    (asg : Frame.ChannelAsg) (chs : List (Array Int)) (w : W)
    (hw : w.n = 0) :
    (W.pushFrame b strat num asg chs w).bits =
        w.bits ++ Frame.write b strat num asg (chs.map Array.toList) ∧
      (W.pushFrame b strat num asg chs w).n = 0 := by
  let bs := (chs.headD #[]).size
  let code := asg.code chs.length
  let core := Frame.headerCore b strat num bs code
  let c8 := (Crc.crc8 (bitsToBytes core)).toNat
  let header := Frame.writeHeader b strat num bs code
  let subframes := Frame.writeSubframes
    (Frame.subframePlan b asg (chs.map Array.toList))
  let pre := header ++ subframes
  let pad := padLen pre.length
  let body := alignToByte pre

  have hcoreEmit : Emits (fun x => W.pushHeaderCore b strat num bs code x) core := by
    exact emits_pushHeaderCore b strat num bs code
  have hcoreDiv : 8 ∣ core.length := by
    exact headerCore_length_dvd b strat num bs code

  let w1 := W.pushHeaderCore b strat num bs code w
  have hw1 : w1.n = 0 ∧ w1.buf = w.buf ++ bitsToBytes core := by
    exact emits_aligned_buf hcoreEmit w hw hcoreDiv
  have hslice1 : w1.buf.extract w.buf.size w1.buf.size = bitsToBytes core := by
    rw [hw1.2]
    apply ByteArray.extract_append_eq_right
    · rfl
    · exact ByteArray.size_append

  have hheaderEmit :
      Emits (fun x => (W.pushHeaderCore b strat num bs code x).push 8 c8)
        header := by
    apply emits_congr (emits_comp hcoreEmit (emits_push 8 c8)) (fun _ => rfl)
    rfl

  have hpreEmit :
      Emits (fun x => W.pushPlan (W.planA b asg chs)
        ((W.pushHeaderCore b strat num bs code x).push 8 c8)) pre := by
    apply emits_congr (emits_comp hheaderEmit (emits_pushPlanA b asg chs))
      (fun _ => rfl)
    rfl

  let w3 := W.pushPlan (W.planA b asg chs) (w1.push 8 c8)
  have hw3 : w3.n = pre.length % 8 := by
    exact emits_pending_mod hpreEmit w hw
  have hpad : (8 - w3.n % 8) % 8 = pad := by
    rw [hw3]
    rw [Nat.mod_mod]
    rfl

  have hbodyEmit :
      Emits (fun x => (W.pushPlan (W.planA b asg chs)
        ((W.pushHeaderCore b strat num bs code x).push 8 c8)).push pad 0)
        body := by
    apply emits_congr (emits_comp hpreEmit (emits_push pad 0)) (fun _ => rfl)
    change pre ++ writeBits pad 0 = body
    rw [writeBits_zero]
    rfl

  let w4 := w3.push pad 0
  have hw4 : w4.n = 0 ∧ w4.buf = w.buf ++ bitsToBytes body := by
    exact emits_aligned_buf hbodyEmit w hw (alignToByte_dvd pre)
  have hslice4 : w4.buf.extract w.buf.size w4.buf.size = bitsToBytes body := by
    rw [hw4.2]
    apply ByteArray.extract_append_eq_right
    · rfl
    · exact ByteArray.size_append

  let c16 := (Crc.crc16 (bitsToBytes body)).toNat
  have hframeEmit := emits_comp hbodyEmit (emits_push 16 c16)

  have hc8 : (Crc.crc8Range w1.buf w.buf.size w1.buf.size).toNat = c8 := by
    rw [Crc.crc8Range_eq_extract, hslice1]
  have hc16 : (Crc.crc16Range w4.buf w.buf.size w4.buf.size).toNat = c16 := by
    rw [Crc.crc16Range_eq_extract, hslice4]

  let a1 := W.pushHeaderCore b strat num bs code w
  let a2 := a1.push 8 (Crc.crc8Range a1.buf w.buf.size a1.buf.size).toNat
  let a3 := W.pushPlan (W.planA b asg chs) a2
  let a4 := a3.push ((8 - a3.n % 8) % 8) 0
  have hnative : W.pushFrame b strat num asg chs w =
      a4.push 16 (Crc.crc16Range a4.buf w.buf.size a4.buf.size).toNat := by
    rfl
  have ha1 : a1 = w1 := rfl
  have ha2 : a2 = w1.push 8 c8 := by
    unfold a2
    rw [ha1, hc8]
  have ha3 : a3 = w3 := by
    unfold a3 w3
    rw [ha2]
  have ha4 : a4 = w4 := by
    unfold a4 w4
    rw [ha3, hpad]
  have hc16a : (Crc.crc16Range a4.buf w.buf.size a4.buf.size).toNat = c16 := by
    rw [ha4]
    exact hc16
  have hout : W.pushFrame b strat num asg chs w = w4.push 16 c16 := by
    calc
      W.pushFrame b strat num asg chs w =
          a4.push 16 (Crc.crc16Range a4.buf w.buf.size a4.buf.size).toNat := hnative
      _ = a4.push 16 c16 := congrArg (fun v => a4.push 16 v) hc16a
      _ = w4.push 16 c16 := congrArg (fun x => x.push 16 c16) ha4

  have hhead : bs = ((chs.map Array.toList).headD []).length := by
    cases chs <;> simp [bs]
  have hbody : body = Frame.body b strat num asg (chs.map Array.toList) := by
    unfold body pre header subframes Frame.body
    rw [hhead]
    simp only [List.length_map]
    rfl
  have hc16def : c16 = (Crc.crc16 (bitsToBytes body)).toNat := rfl
  have hwrite : body ++ writeBits 16 c16 =
      Frame.write b strat num asg (chs.map Array.toList) := by
    unfold Frame.write
    rw [← hbody, ← hc16def]

  obtain ⟨hbits, _⟩ := hframeEmit w (by omega)
  have hn : (w4.push 16 c16).n = 0 := by
    have := emits_pending_mod (emits_push 16 c16) w4 hw4.1
    simpa only [length_writeBits, Nat.reduceMod] using this
  constructor
  · rw [hout, ← hwrite]
    exact hbits
  · rw [hout]
    exact hn

/-! ## Streams -/

theorem emits_pushStreamInfo (bs sr ch b total md5 : Nat) :
    Emits (fun w => W.pushStreamInfo bs sr ch b total md5 w)
      (Stream.writeStreamInfo bs sr ch b total md5) := by
  let h0 := emits_push 16 bs
  let h1 := emits_comp h0 (emits_push 16 bs)
  let h2 := emits_comp h1 (emits_push 24 0)
  let h3 := emits_comp h2 (emits_push 24 0)
  let h4 := emits_comp h3 (emits_push 20 sr)
  let h5 := emits_comp h4 (emits_push 3 (ch - 1))
  let h6 := emits_comp h5 (emits_push 5 (b - 1))
  let h7 := emits_comp h6 (emits_pushBits 36 total)
  let h8 := emits_comp h7 (emits_pushBits 128 md5)
  apply emits_congr h8 (fun _ => rfl)
  simp only [Stream.writeStreamInfo, List.append_assoc]

private def streamPrefixBits (cfg : Stream.EncoderCfg) (a : Stream.Audio) :
    BitStream :=
  writeBits 32 0x664C6143 ++ writeBits 1 1 ++ writeBits 7 0 ++
    writeBits 24 34 ++
    Stream.writeStreamInfo cfg.blockSize a.sampleRate a.channels.length a.bps
      a.numSamples
      (Stream.md5Nat (Md5.md5 (Stream.pcmBytes a.bps a.channels)))

theorem emits_pushStreamPrefix (cfg : Stream.EncoderCfg) (a : Stream.Audio) :
    Emits (fun w => W.pushStreamPrefix cfg a w) (streamPrefixBits cfg a) := by
  let h0 := emits_push 32 0x664C6143
  let h1 := emits_comp h0 (emits_push 1 1)
  let h2 := emits_comp h1 (emits_push 7 0)
  let h3 := emits_comp h2 (emits_push 24 34)
  let h4 := emits_comp h3 (emits_pushStreamInfo cfg.blockSize a.sampleRate
    a.channels.length a.bps a.numSamples
    (Stream.md5Nat (Md5.md5 (Stream.pcmBytes a.bps a.channels))))
  apply emits_congr h4 (fun _ => rfl)
  simp only [streamPrefixBits, List.append_assoc]

theorem streamPrefixBits_length_dvd (cfg : Stream.EncoderCfg) (a : Stream.Audio) :
    8 ∣ (streamPrefixBits cfg a).length := by
  refine ⟨42, ?_⟩
  simp only [streamPrefixBits, Stream.writeStreamInfo, List.length_append,
    length_writeBits]

private theorem map_toList_map_toArray (fr : List (List Int)) :
    (fr.map List.toArray).map Array.toList = fr := by
  induction fr with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, ih]

/-- Sequential frame emission preserves byte alignment and matches the
    model frame sequence exactly. -/
theorem pushFrames_spec (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    ∀ (frs : List (List (List Int))) (i : Nat) (w : W), w.n = 0 →
      (W.pushFrames b varBlk blockSize chooser i frs w).bits =
          w.bits ++ Stream.writeFrames b varBlk blockSize chooser i frs ∧
        (W.pushFrames b varBlk blockSize chooser i frs w).n = 0 := by
  intro frs
  induction frs with
  | nil =>
    intro i w hw
    exact ⟨by simp [W.pushFrames, Stream.writeFrames], by simpa [W.pushFrames] using hw⟩
  | cons fr frs ih =>
    intro i w hw
    let num := if varBlk then i * blockSize else i
    let arrs := fr.map List.toArray
    let w' := W.pushFrame b varBlk num (chooser fr) arrs w
    have hf0 := pushFrame_spec b varBlk num (chooser fr) arrs w hw
    have harr : arrs.map Array.toList = fr := map_toList_map_toArray fr
    rw [harr] at hf0
    have hf : w'.bits = w.bits ++ Frame.write b varBlk num (chooser fr) fr ∧
        w'.n = 0 := by
      exact hf0
    have hr := ih (i + 1) w' hf.2
    change (W.pushFrames b varBlk blockSize chooser (i + 1) frs w').bits =
        w.bits ++ (Frame.write b varBlk num (chooser fr) fr ++
          Stream.writeFrames b varBlk blockSize chooser (i + 1) frs) ∧
      (W.pushFrames b varBlk blockSize chooser (i + 1) frs w').n = 0
    refine ⟨?_, hr.2⟩
    rw [hr.1, hf.1, List.append_assoc]

/-- Complete native stream emission matches `Stream.writeStream` and
    finishes aligned. -/
theorem pushStream_spec (cfg : Stream.EncoderCfg) (a : Stream.Audio)
    (w : W) (hw : w.n = 0) :
    (W.pushStream cfg a w).bits = w.bits ++ Stream.writeStream cfg a ∧
      (W.pushStream cfg a w).n = 0 := by
  let wp := W.pushStreamPrefix cfg a w
  have hpEmit := emits_pushStreamPrefix cfg a
  have hp := hpEmit w (by omega)
  have hpa := emits_aligned_buf hpEmit w hw (streamPrefixBits_length_dvd cfg a)
  have hframes := pushFrames_spec a.bps cfg.variableBlocking cfg.blockSize
    (cfg.safeChooser a.bps) (Stream.chunkChannels cfg.blockSize a.channels) 0
    wp hpa.1
  change (W.pushFrames a.bps cfg.variableBlocking cfg.blockSize
      (cfg.safeChooser a.bps) 0 (Stream.chunkChannels cfg.blockSize a.channels)
      wp).bits = w.bits ++ Stream.writeStream cfg a ∧
    (W.pushFrames a.bps cfg.variableBlocking cfg.blockSize
      (cfg.safeChooser a.bps) 0 (Stream.chunkChannels cfg.blockSize a.channels)
      wp).n = 0
  refine ⟨?_, hframes.2⟩
  rw [hframes.1, hp.1]
  unfold Stream.writeStream streamPrefixBits
  simp only [List.append_assoc]

/-- The verified byte emitter computes the reference encoder exactly. -/
theorem encode_eq (cfg : Stream.EncoderCfg) (a : Stream.Audio) :
    W.encode cfg a = Stream.Unchecked.encode cfg a := by
  let w := W.empty (64 + 2 * a.channels.length * a.numSamples)
  have hs := pushStream_spec cfg a w (by rfl)
  have hb := aligned_buf_of_bits (w := w) (out := W.pushStream cfg a w)
    (by rfl) hs.2 hs.1 (Stream.writeStream_length_dvd cfg a)
  unfold W.encode Stream.Unchecked.encode
  rw [hb]
  have hempty : ByteArray.emptyWithCapacity
      (64 + 2 * a.channels.length * a.numSamples) = ByteArray.empty := by
    apply ByteArray.ext
    rfl
  change ByteArray.emptyWithCapacity
      (64 + 2 * a.channels.length * a.numSamples) ++ _ = _
  rw [hempty, ByteArray.empty_append]

/-- Public capstone for the fast emitter: byte-for-byte equality with
    the verified reference encoder, without a runtime certificate. -/
theorem emitFast_eq_encode (cfg : Stream.EncoderCfg) (a : Stream.Audio) :
    emitFast cfg a = Stream.Unchecked.encode cfg a :=
  encode_eq cfg a

/-- Swap the compiled `Unchecked.encode` for the tail-recursive `emitFast`
    (a `ByteArray` writer whose `pushFrames` loop is in tail position). The
    reference `writeStream`/`writeFrames` fold is non-tail — `Frame.write … ++
    writeFrames … frs` keeps one native stack frame per frame — and overflows
    the runtime stack on a many-frame encode (audit finding P6, encoder side).
    Value-identical by `emitFast_eq_encode`, so every theorem and capstone keeps
    the reference definition; only the compiled implementation changes. -/
@[csimp] theorem Unchecked_encode_eq_emitFast :
    @Flac.Stream.Unchecked.encode = @Flac.Emit.emitFast := by
  funext cfg a
  exact (emitFast_eq_encode cfg a).symm

end Flac.Emit
