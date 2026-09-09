import Flac.Native.Bits

/-!
# CRC-8 and CRC-16

FLAC frame-header CRC-8 (polynomial `x^8 + x^2 + x^1 + x^0`, i.e. `0x07`) and
frame-footer CRC-16 (polynomial `x^16 + x^15 + x^2 + x^0`, i.e. `0x8005`),
both with initial value 0, MSB-first, not reflected (RFC 9639 §9.3).

The range variants below avoid allocating `ByteArray.extract` results.  Their
equivalence to the original whole-array functions is proved in
`Flac.Spec.Crc`.  Correctness against the standard is covered by test vectors
and by differential testing against libFLAC.

The byte updates are table-driven (the classic 256-entry construction);
`crc8UpdateBitwise`/`crc16UpdateBitwise` are the direct shift-register
definitions the tables are built from, kept as the reference the test
suite compares the table path against on every byte value.
-/

namespace Flac.Crc

/-- One byte step of CRC-8, polynomial `0x07`, as a shift register. -/
def crc8UpdateBitwise (crc b : UInt8) : UInt8 :=
  let x := crc ^^^ b
  (List.range 8).foldl
    (fun c _ => if c &&& 0x80 ≠ 0 then (c <<< 1) ^^^ 0x07 else c <<< 1) x

def crc8Table : Array UInt8 :=
  Array.ofFn (n := 256) fun i => crc8UpdateBitwise (UInt8.ofNat i.val) 0

/-- One byte step of CRC-8, via the table. -/
def crc8Update (crc b : UInt8) : UInt8 :=
  crc8Table[(crc ^^^ b).toNat]'(by
    simp only [crc8Table, Array.size_ofFn]; exact UInt8.toNat_lt_size _)

def crc8List (bs : List UInt8) : UInt8 :=
  bs.foldl crc8Update 0

def crc8 (bs : ByteArray) : UInt8 :=
  bs.foldl crc8Update 0

/-- CRC-8 over `bs[start...stop]`, without allocating the corresponding
`ByteArray.extract`.  The upper endpoint is clamped to the input size, matching
`ByteArray.extract`; an empty or reversed range has CRC zero. -/
@[inline] def crc8Range (bs : ByteArray) (start stop : Nat) : UInt8 :=
  bs.foldl crc8Update 0 start (min stop bs.size)

/-- One byte step of CRC-16, polynomial `0x8005`, as a shift register. -/
def crc16UpdateBitwise (crc : UInt16) (b : UInt8) : UInt16 :=
  let x := crc ^^^ (b.toUInt16 <<< 8)
  (List.range 8).foldl
    (fun c _ => if c &&& 0x8000 ≠ 0 then (c <<< 1) ^^^ 0x8005 else c <<< 1) x

def crc16Table : Array UInt16 :=
  Array.ofFn (n := 256) fun i => crc16UpdateBitwise 0 (UInt8.ofNat i.val)

/-- One byte step of CRC-16, via the table. -/
def crc16Update (crc : UInt16) (b : UInt8) : UInt16 :=
  (crc <<< 8) ^^^ crc16Table[((crc >>> 8).toUInt8 ^^^ b).toNat]'(by
    simp only [crc16Table, Array.size_ofFn]; exact UInt8.toNat_lt_size _)

def crc16List (bs : List UInt8) : UInt16 :=
  bs.foldl crc16Update 0

def crc16 (bs : ByteArray) : UInt16 :=
  bs.foldl crc16Update 0

/-- CRC-16 over `bs[start...stop]`, without allocating the corresponding
`ByteArray.extract`.  The upper endpoint is clamped to the input size, matching
`ByteArray.extract`; an empty or reversed range has CRC zero. -/
def crc16Range (bs : ByteArray) (start stop : Nat) : UInt16 :=
  bs.foldl crc16Update 0 start (min stop bs.size)

/-! ### Slicing-by-four

`crc16Update` is a dependent chain — table load, unbox, shift, xor — of
about eight cycles per byte, and a frame's CRC-16 runs over every byte of
the stream in both directions. The kernel below consumes four bytes per
step with four *independent* table lookups, which is exact because the
CRC is linear over GF(2): the table `tab` satisfies
`tab (x ^^^ y) = tab x ^^^ tab y`, so the sixteen bits of state and the
four bytes contribute separately (`update4`). Linearity is proved from the
shift-register definition, not checked by evaluation. -/

/-- One shift-register step of CRC-16. -/
private def step (c : UInt16) : UInt16 := if c &&& 0x8000 ≠ 0 then (c <<< 1) ^^^ 0x8005 else c <<< 1

theorem crc16UpdateBitwise_eq (crc : UInt16) (b : UInt8) :
    crc16UpdateBitwise crc b = (List.range 8).foldl (fun c _ => step c) (crc ^^^ (b.toUInt16 <<< 8)) := rfl

theorem shl_xor (a b : UInt16) (n : UInt16) : (a ^^^ b) <<< n = (a <<< n) ^^^ (b <<< n) :=
  UInt16.toBitVec_inj.1 (by simp [BitVec.shiftLeft_xor_distrib])

theorem shr_xor (a b : UInt16) (n : UInt16) : (a ^^^ b) >>> n = (a >>> n) ^^^ (b >>> n) :=
  UInt16.toBitVec_inj.1 (by simp [BitVec.ushiftRight_xor_distrib])

theorem and_xor (a b m : UInt16) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) :=
  UInt16.toBitVec_inj.1 (by
    simp only [UInt16.toBitVec_and, UInt16.toBitVec_xor]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
    cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl)

theorem and_msb (x : UInt16) : x &&& 0x8000 = 0 ∨ x &&& 0x8000 = 0x8000 := by
  have h := BitVec.and_twoPow x.toBitVec 15
  have h2 : (0x8000 : UInt16).toBitVec = BitVec.twoPow 16 15 := by decide
  rcases Bool.eq_false_or_eq_true (x.toBitVec.getLsbD 15) with hb | hb
  · right
    apply UInt16.toBitVec_inj.1
    rw [UInt16.toBitVec_and, h2, h, if_pos hb]
  · left
    apply UInt16.toBitVec_inj.1
    rw [UInt16.toBitVec_and, h2, h, if_neg (by rw [hb]; exact Bool.false_ne_true)]
    rfl

theorem xor_xor_cancel (x y k : UInt16) : (x ^^^ k) ^^^ (y ^^^ k) = x ^^^ y := by
  rw [UInt16.xor_assoc, UInt16.xor_comm y k, ← UInt16.xor_assoc k, UInt16.xor_self, UInt16.zero_xor]

theorem step_xor (a b : UInt16) : step (a ^^^ b) = step a ^^^ step b := by
  unfold step
  rw [and_xor, shl_xor]
  have hp : (0x8000 : UInt16) ≠ 0 := by decide
  have hn : ¬ ((0 : UInt16) ≠ 0) := by decide
  rcases and_msb a with ha | ha <;> rcases and_msb b with hb | hb <;>
    simp only [ha, hb, UInt16.xor_zero, UInt16.zero_xor, UInt16.xor_self, if_pos hp, if_neg hn]
  · exact UInt16.xor_assoc _ _ _
  · rw [UInt16.xor_assoc, UInt16.xor_assoc, UInt16.xor_comm (b <<< 1)]
  · exact (xor_xor_cancel _ _ _).symm

theorem step_zero : step 0 = 0 := by decide

theorem fold_step_xor (l : List Nat) (a b : UInt16) :
    l.foldl (fun c _ => step c) (a ^^^ b) = l.foldl (fun c _ => step c) a ^^^ l.foldl (fun c _ => step c) b := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; rw [step_xor]; exact ih _ _

theorem fold_step_zero (l : List Nat) : l.foldl (fun c _ => step c) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, step_zero]; exact ih

/-- The table, as a function. -/
private def tab (x : UInt8) : UInt16 :=
  crc16Table[x.toNat]'(by simp only [crc16Table, Array.size_ofFn]; exact UInt8.toNat_lt_size _)

theorem tab_eq (x : UInt8) : tab x = crc16UpdateBitwise 0 x := by
  simp only [tab, crc16Table, Array.getElem_ofFn, UInt8.ofNat_toNat]

theorem tab_xor (x y : UInt8) : tab (x ^^^ y) = tab x ^^^ tab y := by
  simp only [tab_eq, crc16UpdateBitwise_eq, UInt16.zero_xor, UInt8.toUInt16_xor, shl_xor]
  exact fold_step_xor _ _ _

theorem tab_zero : tab 0 = 0 := by
  rw [tab_eq, crc16UpdateBitwise_eq]
  simp only [UInt16.zero_xor]
  have : (0 : UInt8).toUInt16 <<< 8 = 0 := by decide
  rw [this]
  exact fold_step_zero _

theorem crc16Update_eq (c : UInt16) (b : UInt8) :
    crc16Update c b = (c <<< 8) ^^^ tab ((c >>> 8).toUInt8 ^^^ b) := rfl

theorem shl8_shl8 (c : UInt16) : (c <<< 8) <<< 8 = 0 :=
  UInt16.toBitVec_inj.1 (by
    simp only [UInt16.toBitVec_shiftLeft]
    show c.toBitVec <<< 8 <<< 8 = 0#16
    rw [← BitVec.shiftLeft_add]
    exact BitVec.shiftLeft_eq_zero (by decide))

theorem hi_shl8 (c : UInt16) : ((c <<< 8) >>> 8).toUInt8 = c.toUInt8 :=
  UInt8.toBitVec_inj.1 (by
    simp only [UInt16.toBitVec_toUInt8, UInt16.toBitVec_shiftRight, UInt16.toBitVec_shiftLeft]
    show (c.toBitVec <<< 8 >>> 8).setWidth 8 = c.toBitVec.setWidth 8
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    simp [hi]
    omega)

private theorem xor4_swap8 (a b c d : UInt8) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [UInt8.xor_assoc, UInt8.xor_assoc, ← UInt8.xor_assoc b, UInt8.xor_comm b c, UInt8.xor_assoc]

private theorem xor4_swap16 (a b c d : UInt16) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [UInt16.xor_assoc, UInt16.xor_assoc, ← UInt16.xor_assoc b, UInt16.xor_comm b c, UInt16.xor_assoc]

/-- The high byte is linear. -/
theorem hi_xor (x y : UInt16) : ((x ^^^ y) >>> 8).toUInt8 = (x >>> 8).toUInt8 ^^^ (y >>> 8).toUInt8 := by
  rw [shr_xor, UInt16.toUInt8_xor]

/-- **The byte update is linear** in state and byte together. -/
theorem update_xor (x y : UInt16) (p q : UInt8) :
    crc16Update (x ^^^ y) (p ^^^ q) = crc16Update x p ^^^ crc16Update y q := by
  simp only [crc16Update_eq]
  rw [shl_xor, hi_xor, xor4_swap8, tab_xor, xor4_swap16]

theorem update_zero_byte (b : UInt8) : crc16Update 0 b = tab b := by
  rw [crc16Update_eq]
  have h1 : (0 : UInt16) <<< 8 = 0 := by decide
  have h2 : ((0 : UInt16) >>> 8).toUInt8 = 0 := by decide
  rw [h1, h2, UInt16.zero_xor, UInt8.zero_xor]

theorem update_split (t : UInt16) (b : UInt8) : crc16Update t b = crc16Update t 0 ^^^ tab b := by
  have := update_xor t 0 0 b
  rw [UInt16.xor_zero, UInt8.zero_xor, update_zero_byte] at this
  exact this

theorem update_xor_state (x y : UInt16) (b : UInt8) :
    crc16Update (x ^^^ y) b = crc16Update x 0 ^^^ crc16Update y b := by
  have := update_xor x y 0 b
  rwa [UInt8.zero_xor] at this

theorem update_shl8 (c : UInt16) : crc16Update (c <<< 8) 0 = tab c.toUInt8 := by
  rw [crc16Update_eq, shl8_shl8, hi_shl8, UInt16.zero_xor, UInt8.xor_zero]

/-- `tab` followed by one, two, three zero bytes. -/
private def tab1 (x : UInt8) : UInt16 := crc16Update (tab x) 0
private def tab2 (x : UInt8) : UInt16 := crc16Update (tab1 x) 0
private def tab3 (x : UInt8) : UInt16 := crc16Update (tab2 x) 0

private theorem xor_left_comm (a b c : UInt16) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt16.xor_assoc, UInt16.xor_comm a, UInt16.xor_assoc]

/-- **Four bytes at once.** -/
theorem update4 (c : UInt16) (b0 b1 b2 b3 : UInt8) :
    crc16Update (crc16Update (crc16Update (crc16Update c b0) b1) b2) b3
      = tab3 ((c >>> 8).toUInt8 ^^^ b0)
        ^^^ (tab2 (c.toUInt8 ^^^ b1) ^^^ (tab1 b2 ^^^ tab b3)) := by
  have h1 : crc16Update c b0 = (c <<< 8) ^^^ tab ((c >>> 8).toUInt8 ^^^ b0) := crc16Update_eq c b0
  have h2 : crc16Update ((c <<< 8) ^^^ tab ((c >>> 8).toUInt8 ^^^ b0)) b1
      = tab1 ((c >>> 8).toUInt8 ^^^ b0) ^^^ tab (c.toUInt8 ^^^ b1) := by
    rw [update_xor_state, update_shl8, update_split (tab _) b1, tab_xor c.toUInt8 b1, xor_left_comm]
    simp only [tab1]
  have h3 : crc16Update (tab1 ((c >>> 8).toUInt8 ^^^ b0) ^^^ tab (c.toUInt8 ^^^ b1)) b2
      = tab2 ((c >>> 8).toUInt8 ^^^ b0) ^^^ (tab1 (c.toUInt8 ^^^ b1) ^^^ tab b2) := by
    rw [update_xor_state, update_split (tab _) b2]
    simp only [tab2, tab1]
  have h4 : crc16Update (tab2 ((c >>> 8).toUInt8 ^^^ b0) ^^^ (tab1 (c.toUInt8 ^^^ b1) ^^^ tab b2)) b3
      = tab3 ((c >>> 8).toUInt8 ^^^ b0) ^^^ (tab2 (c.toUInt8 ^^^ b1) ^^^ (tab1 b2 ^^^ tab b3)) := by
    rw [update_xor_state, update_xor_state, update_split (tab _) b3]
    simp only [tab3, tab2, tab1]
  rw [h1, h2, h3, h4]

/-- The three shifted tables, built once. -/
def crc16Table1 : Array UInt16 := Array.ofFn (n := 256) fun i => tab1 (UInt8.ofNat i.val)
def crc16Table2 : Array UInt16 := Array.ofFn (n := 256) fun i => tab2 (UInt8.ofNat i.val)
def crc16Table3 : Array UInt16 := Array.ofFn (n := 256) fun i => tab3 (UInt8.ofNat i.val)

@[inline] def tabA1 (x : UInt8) : UInt16 :=
  crc16Table1[x.toNat]'(by simp only [crc16Table1, Array.size_ofFn]; exact UInt8.toNat_lt_size _)
@[inline] def tabA2 (x : UInt8) : UInt16 :=
  crc16Table2[x.toNat]'(by simp only [crc16Table2, Array.size_ofFn]; exact UInt8.toNat_lt_size _)
@[inline] def tabA3 (x : UInt8) : UInt16 :=
  crc16Table3[x.toNat]'(by simp only [crc16Table3, Array.size_ofFn]; exact UInt8.toNat_lt_size _)

theorem tabA1_eq (x : UInt8) : tabA1 x = tab1 x := by
  simp only [tabA1, crc16Table1, Array.getElem_ofFn, UInt8.ofNat_toNat]
theorem tabA2_eq (x : UInt8) : tabA2 x = tab2 x := by
  simp only [tabA2, crc16Table2, Array.getElem_ofFn, UInt8.ofNat_toNat]
theorem tabA3_eq (x : UInt8) : tabA3 x = tab3 x := by
  simp only [tabA3, crc16Table3, Array.getElem_ofFn, UInt8.ofNat_toNat]

/-! #### The loops -/

/-- Byte `j`, or zero past the end. -/
private def byteAt (bs : ByteArray) (j : Nat) : UInt8 := if h : j < bs.size then bs[j] else 0

/-- `n` steps of `f` from index `j` — the shape of `ByteArray.foldlM.loop`. -/
private def foldFrom {β : Type} (f : β → UInt8 → β) (bs : ByteArray) : (n j : Nat) → β → β
  | 0, _, b => b
  | n + 1, j, b => foldFrom f bs n (j + 1) (f b (byteAt bs j))

theorem foldFrom_add {β : Type} (f : β → UInt8 → β) (bs : ByteArray) (a b j : Nat) (c : β) :
    foldFrom f bs (a + b) j c = foldFrom f bs b (j + a) (foldFrom f bs a j c) := by
  induction a generalizing j c with
  | zero => simp [foldFrom]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [foldFrom]
    rw [ih]
    congr 1
    omega

/-- A bounded `ByteArray.foldl` is `foldFrom`. -/
theorem foldl_eq_foldFrom {β : Type} (f : β → UInt8 → β) (b : β) (bs : ByteArray) (start stop : Nat)
    (h1 : start ≤ stop) (h2 : stop ≤ bs.size) :
    bs.foldl f b start stop = foldFrom f bs (stop - start) start b := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [Id.run, dif_pos h2]
  suffices ∀ (i j : Nat) (b : β), i + j ≤ stop →
      ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) bs stop h2 i j b = foldFrom f bs i j b from
    this _ _ _ (by omega)
  intro i
  induction i with
  | zero =>
    intro j b _
    unfold ByteArray.foldlM.loop
    split <;> rfl
  | succ i ih =>
    intro j b hij
    unfold ByteArray.foldlM.loop
    rw [dif_pos (by omega)]
    show ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) bs stop h2 i (j + 1) (f b bs[j]) = _
    rw [ih (j + 1) _ (by omega)]
    simp only [foldFrom, byteAt, dif_pos (show j < bs.size by omega)]

theorem uget_eq_byteAt (bs : ByteArray) (i : USize) (h : i.toNat < bs.size) :
    bs.uget i h = byteAt bs i.toNat := by
  unfold byteAt
  rw [dif_pos h]
  rfl

/-- `n` four-byte blocks from byte `i`. -/
def crcBlocks (bs : ByteArray) : (n : Nat) → (i : USize) → UInt16 →
    i.toNat + 4 * n ≤ bs.size → bs.size < USize.size → UInt16
  | 0, _, c, _, _ => c
  | n + 1, i, c, hn, hs =>
    have e1 := Flac.Bits.usize_add_toNat i 1 bs.size (by omega) hs
    have e2 := Flac.Bits.usize_add_toNat i 2 bs.size (by omega) hs
    have e3 := Flac.Bits.usize_add_toNat i 3 bs.size (by omega) hs
    have e4 := Flac.Bits.usize_add_toNat i 4 bs.size (by omega) hs
    let b0 := bs.uget i (by omega)
    let b1 := bs.uget (i + USize.ofNat 1) (by omega)
    let b2 := bs.uget (i + USize.ofNat 2) (by omega)
    let b3 := bs.uget (i + USize.ofNat 3) (by omega)
    crcBlocks bs n (i + USize.ofNat 4)
      (tabA3 ((c >>> 8).toUInt8 ^^^ b0) ^^^ (tabA2 (c.toUInt8 ^^^ b1) ^^^ (tabA1 b2 ^^^ tab b3)))
      (by omega) hs

/-- The last `n < 4` bytes, one at a time. -/
def crcTail (bs : ByteArray) : (n : Nat) → (i : USize) → UInt16 →
    i.toNat + n ≤ bs.size → bs.size < USize.size → UInt16
  | 0, _, c, _, _ => c
  | n + 1, i, c, hn, hs =>
    have e1 := Flac.Bits.usize_add_toNat i 1 bs.size (by omega) hs
    crcTail bs n (i + USize.ofNat 1) (crc16Update c (bs.uget i (by omega))) (by omega) hs

theorem crcTail_eq (bs : ByteArray) : ∀ (n : Nat) (i : USize) (c : UInt16) hn hs,
    crcTail bs n i c hn hs = foldFrom crc16Update bs n i.toNat c := by
  intro n
  induction n with
  | zero => intro i c hn hs; rfl
  | succ n ih =>
    intro i c hn hs
    have e1 := Flac.Bits.usize_add_toNat i 1 bs.size (by omega) hs
    simp only [crcTail, foldFrom]
    rw [ih, e1, uget_eq_byteAt]

theorem crcBlocks_eq (bs : ByteArray) : ∀ (n : Nat) (i : USize) (c : UInt16) hn hs,
    crcBlocks bs n i c hn hs = foldFrom crc16Update bs (4 * n) i.toNat c := by
  intro n
  induction n with
  | zero => intro i c hn hs; rfl
  | succ n ih =>
    intro i c hn hs
    have e1 : (i + USize.ofNat 1).toNat = i.toNat + 1 := Flac.Bits.usize_add_toNat i 1 bs.size (by omega) hs
    have e2 : (i + USize.ofNat 2).toNat = i.toNat + 1 + 1 := by
      rw [Flac.Bits.usize_add_toNat i 2 bs.size (by omega) hs]
    have e3 : (i + USize.ofNat 3).toNat = i.toNat + 1 + 1 + 1 := by
      rw [Flac.Bits.usize_add_toNat i 3 bs.size (by omega) hs]
    have e4 : (i + USize.ofNat 4).toNat = i.toNat + 4 := Flac.Bits.usize_add_toNat i 4 bs.size (by omega) hs
    simp only [crcBlocks]
    rw [ih, e4, show 4 * (n + 1) = 4 + 4 * n by omega, foldFrom_add]
    simp only [foldFrom, uget_eq_byteAt, e1, e2, e3, tabA1_eq, tabA2_eq, tabA3_eq, update4]

/-- The slicing-by-four range CRC; outside its domain (a range that does
    not fit a machine word) the byte loop verbatim. -/
def crc16RangeFast (bs : ByteArray) (start stop : Nat) : UInt16 :=
  if h : start ≤ min stop bs.size ∧ bs.size < USize.size then
    crcTail bs ((min stop bs.size - start) % 4)
      (USize.ofNat (start + 4 * ((min stop bs.size - start) / 4)))
      (crcBlocks bs ((min stop bs.size - start) / 4) (USize.ofNat start) 0
        (by rw [USize.toNat_ofNat_of_lt' (by omega)]; omega) h.2)
      (by rw [USize.toNat_ofNat_of_lt' (by omega)]; omega) h.2
  else bs.foldl crc16Update 0 start (min stop bs.size)

/-- **Slicing-by-four computes the byte fold.** -/
@[csimp] theorem crc16Range_eq_fast : @crc16Range = @crc16RangeFast := by
  funext bs start stop
  unfold crc16Range crc16RangeFast
  split
  · next h =>
    rw [crcTail_eq, crcBlocks_eq, USize.toNat_ofNat_of_lt' (by omega),
      USize.toNat_ofNat_of_lt' (by omega), ← foldFrom_add, Nat.div_add_mod,
      foldl_eq_foldFrom _ _ _ _ _ h.1 (Nat.min_le_right _ _)]
  · rfl

end Flac.Crc
