/-!
# L0 — Bit-level model (MSB-first)

FLAC is big-endian / MSB-first throughout (RFC 9639 §1.1). The bitstream
model is `List Bool` (`true` = 1 bit). Writers are pure functions returning
bit lists; readers are structural-recursive consumers returning
`Option (α × List Bool)` (no `partial`, no panicking access — decoder
totality by construction).

This representation is the *proof* backbone; buffered production bit I/O
will later be proven equivalent to (transferred against) this model. Round-trip theorems
live in `Flac.Spec.Bits`.
-/

namespace Flac

/-- MSB-first bitstream: `true` is a 1 bit. -/
abbrev BitStream := List Bool

namespace Bits

/-! ## Fast powers of two

The Lean runtime evaluates `Nat.pow` and `Nat.shiftLeft` through GMP even
for word-sized values (only `>>>`, `&&&`, `+`, `*`, … have scalar fast
paths), so `2 ^ k` in a per-sample loop allocates. `p2` is a table lookup
for the word-sized range, proven equal to `2 ^ ·` (`Flac.Spec.Bits.p2_eq`),
so hot paths can use it under the unchanged theorems. -/

/-- The first 64 powers of two, computed once. -/
def pow2Table : Array Nat := Array.ofFn (n := 64) fun i => 2 ^ i.val

/-- `2 ^ n` without GMP traffic for `n < 64`. -/
@[inline] def p2 (n : Nat) : Nat :=
  if h : n < 64 then
    pow2Table[n]'(by simp only [pow2Table, Array.size_ofFn]; exact h)
  else 2 ^ n

/-- The table-driven power of two computes `2 ^ ·` — the bridge that lets
    every hot path use `p2` under the unchanged round-trip theorems. -/
@[simp] theorem p2_eq (n : Nat) : p2 n = 2 ^ n := by
  unfold p2
  split
  · simp only [pow2Table, Array.getElem_ofFn]
  · rfl

/-- Write the low `n` bits of `v`, most significant bit first. -/
def writeBits : (n : Nat) → (v : Nat) → BitStream
  | 0, _ => []
  | n+1, v => (decide (v / 2 ^ n % 2 = 1)) :: writeBits n v

/-- Read `n` bits MSB-first into a `Nat`. -/
def readBits : (n : Nat) → BitStream → Option (Nat × BitStream)
  | 0, s => some (0, s)
  | _+1, [] => none
  | n+1, b :: s =>
    match readBits n s with
    | none => none
    | some (v, s') => some ((if b then 2 ^ n else 0) + v, s')

/-- FLAC unary code: `q` zero bits followed by a single one bit
    (RFC 9639 §9.2.7). -/
def writeUnary (q : Nat) : BitStream :=
  List.replicate q false ++ [true]

def readUnary : BitStream → Option (Nat × BitStream)
  | [] => none
  | true :: s => some (0, s)
  | false :: s =>
    match readUnary s with
    | none => none
    | some (q, s') => some (q + 1, s')

/-- `readUnary` with the run counted in an accumulator, so the recursive
    call is in tail position: a Rice-residual run can be as long as the
    remaining input (its enclosing partition bounds the *value*, not the
    reader's recursion depth), so the reader must not keep a stack frame
    per zero bit (audit finding P6). -/
def readUnaryAcc : Nat → BitStream → Option (Nat × BitStream)
  | _, [] => none
  | q, true :: s => some (q, s)
  | q, false :: s => readUnaryAcc (q + 1) s

theorem readUnaryAcc_eq (q : Nat) (s : BitStream) :
    readUnaryAcc q s
      = (readUnary s).map fun p : Nat × BitStream => (q + p.1, p.2) := by
  induction s generalizing q with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | true => simp [readUnaryAcc, readUnary]
    | false =>
      show readUnaryAcc (q + 1) s = _
      rw [ih]
      show _ = (match readUnary s with
        | none => none
        | some (r, s') => some (r + 1, s')).map
          fun p : Nat × BitStream => (q + p.1, p.2)
      cases readUnary s with
      | none => rfl
      | some p =>
        show some (q + 1 + p.1, p.2) = some (q + (p.1 + 1), p.2)
        rw [Nat.add_assoc, Nat.add_comm 1 p.1]

def readUnaryTR (s : BitStream) : Option (Nat × BitStream) :=
  readUnaryAcc 0 s

/-- Swap the compiled implementation of `readUnary` for the accumulator
    form. Kernel-checked, so every theorem keeps reading the structural
    definition above while the executable runs the constant-stack loop. -/
@[csimp] theorem readUnary_eq_readUnaryTR : @readUnary = @readUnaryTR := by
  funext s
  unfold readUnaryTR
  rw [readUnaryAcc_eq]
  cases readUnary s <;> simp

/-- Unary read with an a-priori cap on the run length: `none` unless the
    terminating one bit lies within the next `lim` bits.

    `readUnary` is the RFC's code, and it is right for Rice residuals,
    where a run is bounded by the partition it sits in. A wasted-bits
    count has no such enclosing bound (RFC 9639 §9.2.2 constrains only the
    resulting depth), so reading it needs the cap supplied here — reading
    the field must not cost more than the field is allowed to mean.
    Characterized by `Flac.Spec.Bits.readUnaryUpTo_eq`. -/
def readUnaryUpTo : (lim : Nat) → BitStream → Option (Nat × BitStream)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, true :: s => some (0, s)
  | lim + 1, false :: s =>
    match readUnaryUpTo lim s with
    | none => none
    | some (q, s') => some (q + 1, s')

/-- Zero-bits needed to pad `len` bits to a byte boundary. -/
def padLen (len : Nat) : Nat := (8 - len % 8) % 8

/-- Pad a bitstream to byte alignment with zero bits (frame footers are
    byte-aligned before the CRC-16, RFC 9639 §9.3). -/
def alignToByte (s : BitStream) : BitStream :=
  s ++ List.replicate (padLen s.length) false

/-- Run a reader and also return the bits it consumed — the FLAC frame
    CRCs are recomputed by the decoder over exactly the bytes it has read
    (RFC 9639 §9.3), and this combinator makes that both executable and
    proof-friendly (`Flac.Bits.withConsumed_spec`). -/
def withConsumed (f : BitStream → Option (α × BitStream)) (s : BitStream) :
    Option (α × BitStream × BitStream) :=
  match f s with
  | none => none
  | some (a, s') => some (a, s.take (s.length - s'.length), s')

/-! ## Arithmetic shift -/

/-- Arithmetic shift right on ℤ (floor division by `2^s`): the exact
    semantics of a two's-complement `>>`, matching what production Int64
    code will do at M5. -/
@[inline] def sar (x : Int) (s : Nat) : Int :=
  match x with
  | .ofNat m => .ofNat (m >>> s)
  | .negSucc m => .negSucc (m >>> s)

/-- Undo `w` wasted bits (RFC 9639 §9.2.2): scale back up.
    (`p2`, not `2 ^ ·`: `Nat.pow` goes through GMP on the hot path.) -/
def shiftUp (w : Nat) (x : Int) : Int :=
  x * ((p2 w : Nat) : Int)

/-- Scale a sample down by `w` wasted bits (exact for valid inputs;
    `/` on ℤ is Euclidean division = floor for positive divisors). -/
def shiftDown (w : Nat) (x : Int) : Int :=
  x / ((2 ^ w : Nat) : Int)

/-! ## Signed integers (two's complement, MSB-first) -/

/-- `x` is representable as an `n`-bit two's-complement integer.
    Stated via `2*x` to avoid `n-1` underflow at `n = 0` (an escaped
    partition may store residuals with 0 bits, RFC 9639 §9.2.7.1);
    for `n ≥ 1` this is the usual `-2^(n-1) ≤ x < 2^(n-1)`. -/
def FitsSInt (n : Nat) (x : Int) : Prop :=
  -((2 ^ n : Nat) : Int) ≤ 2 * x ∧ 2 * x < ((2 ^ n : Nat) : Int)

instance (n : Nat) (x : Int) : Decidable (FitsSInt n x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Write `x` as an `n`-bit two's-complement integer. Callers guarantee
    `FitsSInt n x` (garbage-in tolerated; the round-trip theorem carries
    the hypothesis). -/
def writeSInt (n : Nat) (x : Int) : BitStream :=
  writeBits n ((x + ((2 ^ n : Nat) : Int)).toNat % 2 ^ n)

def readSInt (n : Nat) (s : BitStream) : Option (Int × BitStream) :=
  match readBits n s with
  | none => none
  | some (v, s') =>
    some (if 2 * v < 2 ^ n then (v : Int) else (v : Int) - ((2 ^ n : Nat) : Int), s')

/-- Reduce `x` to the `n`-bit two's-complement representative of its
    residue class mod `2^n` — what a conformant fixed-width decoder's
    register arithmetic computes. Identity on values that already fit
    (`Flac.Spec.Bits.wrapSInt_eq_of_fits`), and the result always fits
    (`Flac.Spec.Bits.fitsSInt_wrapSInt`). Applied inside the predictor
    restore loops so that reconstructed samples can never outgrow the
    subframe's bit depth on adversarial streams; the in-range test comes
    first so the hot path never divides. -/
@[inline] def wrapSInt (n : Nat) (x : Int) : Int :=
  let P : Int := ((p2 n : Nat) : Int)
  if -P ≤ 2 * x ∧ 2 * x < P then x
  else
    let m := x % P
    if 2 * m < P then m else m - P

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

/-- `wrapSInt` is the balanced residue: the `[-2^(n-1), 2^(n-1))`
    representative of `x mod 2^n`, i.e. `Int.bmod` at a power of two. This is
    the form the machine-word restore kernels reason through: a value
    computed mod `2^64` and found in range is the wrap itself. -/
theorem wrapSInt_eq_bmod (n : Nat) (x : Int) : wrapSInt n x = x.bmod (2 ^ n) := by
  simp only [wrapSInt, p2_eq]
  cases n with
  | zero =>
    simp only [Nat.pow_zero, Int.bmod_one, Int.natCast_one]
    split
    · omega
    · simp
  | succ n =>
    rw [Int.bmod_def]
    have hQ : (0 : Int) < ((2 ^ n : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos n)
    have hM : ((2 ^ (n + 1) : Nat) : Int) = 2 * ((2 ^ n : Nat) : Int) := by
      rw [Nat.pow_succ, Int.natCast_mul]; omega
    rw [hM]
    generalize ((2 ^ n : Nat) : Int) = Q at hQ ⊢
    have hr0 : 0 ≤ x % (2 * Q) := Int.emod_nonneg x (by omega)
    have hrlt : x % (2 * Q) < 2 * Q := Int.emod_lt_of_pos x (by omega)
    have hdiv : (2 * Q + 1) / 2 = Q := by omega
    rw [hdiv]
    split
    · next h =>
      rcases Int.lt_or_le x 0 with hneg | hnn
      · have h1 := Int.add_mul_emod_self_left x (2 * Q) 1
        rw [Int.emod_eq_of_lt (by omega) (by omega)] at h1
        rw [← h1]
        omega
      · rw [Int.emod_eq_of_lt hnn (by omega)]
        omega
    · split <;> omega

/-- `FitsSInt` is monotone in the width. -/
theorem fitsSInt_mono {m n : Nat} (h : m ≤ n) {x : Int} (hx : FitsSInt m x) :
    FitsSInt n x := by
  obtain ⟨h1, h2⟩ := hx
  have hle : (2 ^ m : Nat) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) h
  exact ⟨by omega, by omega⟩

/-! ## Word-sized byte access

`i < d.usize` puts `i` inside the buffer on every platform: the machine-word
size is the true size reduced mod the word, never more. The kernels index
`ByteArray`s with `USize` behind this one comparison instead of a proof. -/

/-- `USize` addition below a bound that fits the word is exact. -/
theorem usize_add_toNat (i : USize) (k n : Nat) (h : i.toNat + k ≤ n) (hn : n < USize.size) :
    (i + USize.ofNat k).toNat = i.toNat + k := by
  simp only [USize.size_eq_two_pow] at hn ⊢
  rw [USize.toNat_add, USize.toNat_ofNat', Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_lt_of_lt_usize {d : ByteArray} {i : USize} (h : i < d.usize) :
    i.toNat < d.size := by
  have := USize.lt_iff_toNat_lt.1 h
  simp only [ByteArray.usize, Nat.toUSize_eq, USize.toNat_ofNat'] at this
  exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)

/-- The same bound with the buffer's size carried as a *word parameter*
    rather than read from the object header.

    The distinction is invisible single-threaded and decisive with several
    decoding threads: a `ByteArray`'s size word sits in the same cache line
    as its reference count, and every worker that builds or drops a reader
    over the shared input updates that count atomically. A hot loop that
    bounds-checks against `d.usize` therefore reloads a line other cores keep
    invalidating — one coherence miss per byte read. Hoisting the size into a
    loop parameter (this hypothesis is what keeps the access safe) leaves the
    loop reading nothing but the data itself. -/
theorem toNat_lt_of_lt_size {d : ByteArray} {sz i : USize} (hsz : sz ≤ d.usize)
    (h : i < sz) : i.toNat < d.size :=
  toNat_lt_of_lt_usize (USize.lt_iff_toNat_lt.2
    (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.1 h) (USize.le_iff_toNat_le.1 hsz)))

theorem floatArray_toNat_lt_of_lt_usize {d : FloatArray} {i : USize} (h : i < d.usize) :
    i.toNat < d.size := by
  have := USize.lt_iff_toNat_lt.1 h
  simp only [FloatArray.usize, Nat.toUSize_eq, USize.toNat_ofNat'] at this
  exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)

/-! ## Machine-word bridges

Facts relating `Int64` operations to the exact `Int` ones. They belong here
rather than in one kernel's module: the LPC restore, the residual emitter,
the stereo decorrelations and the bit writer all reason through them, and
having them here is what lets `Stereo` stop importing `Lpc` for two generic
arithmetic lemmas. -/

/-- `Bits.sar` is `Int`'s arithmetic shift. -/
theorem sar_eq_shiftRight (x : Int) (s : Nat) : sar x s = x >>> s := by
  cases x <;> rfl

/-- An `Int64` arithmetic shift by a word-sized count is the `Int` shift. -/
theorem toInt_shiftRight_ofNat (a : Int64) (s : Nat) (hs : s < 64) :
    (a >>> Int64.ofNat s).toInt = a.toInt >>> s := by
  show (a >>> Int64.ofNat s).toBitVec.toInt = _
  rw [Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight']
  have hmsb : (BitVec.ofNat 64 s).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  change a.toBitVec.toInt >>> ((BitVec.ofNat 64 s).smod 64).toNat = a.toInt >>> s
  simp only [BitVec.toNat_smod, hmsb, show (64 : BitVec 64).msb = false from by decide]
  change a.toBitVec.toInt >>> ((BitVec.ofNat 64 s).toNat % (64 : BitVec 64).toNat) = a.toInt >>> s
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega),
    show (64 : BitVec 64).toNat = 64 from by decide, Nat.mod_eq_of_lt hs]
  rfl

theorem toInt_toInt64_of_fits16 {c : Int} (h : FitsSInt 16 c) : c.toInt64.toInt = c := by
  obtain ⟨h1, h2⟩ := h
  simp only [Nat.reducePow] at h1 h2
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

theorem toInt_toInt64_of_fits34 {x : Int} (h : FitsSInt 34 x) : x.toInt64.toInt = x := by
  obtain ⟨h1, h2⟩ := h
  simp only [Nat.reducePow] at h1 h2
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

/-- `FitsSInt 31` with the bound as a literal: two scalar compares per sample
    where `2 ^ 31` would be a `Nat.pow` call. The encoder tests it per residual
    and the stereo decorrelation per sample, so it is here rather than in either
    of them. -/
@[inline] def small31 (x : Int) : Bool := decide (-1073741824 ≤ x ∧ x < 1073741824)

theorem fitsSInt31_of_small31 {x : Int} (h : small31 x = true) : FitsSInt 31 x := by
  simp only [small31, decide_eq_true_eq] at h
  simp only [FitsSInt, Nat.reducePow]
  omega

theorem toInt_toInt64_of_small31 {x : Int} (h : small31 x = true) : x.toInt64.toInt = x := by
  simp only [small31, decide_eq_true_eq] at h
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

/-! ## Bytes ↔ bits -/

/-- One byte as 8 bits, MSB first. -/
def byteToBits (b : UInt8) : BitStream := writeBits 8 b.toNat

/-- Assemble one byte from 8 bits, MSB first. -/
def bitsToByte (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : UInt8 :=
  UInt8.ofNat (128 * b0.toNat + 64 * b1.toNat + 32 * b2.toNat + 16 * b3.toNat
    + 8 * b4.toNat + 4 * b5.toNat + 2 * b6.toNat + b7.toNat)

def byteListToBits (bs : List UInt8) : BitStream :=
  bs.flatMap byteToBits

/-- Pack bits into bytes, 8 at a time, MSB first. Callers guarantee
    `8 ∣ length`; a trailing partial byte is dropped. -/
def bitsToByteList : BitStream → List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    bitsToByte b0 b1 b2 b3 b4 b5 b6 b7 :: bitsToByteList rest
  | _ => []

/-- `bitsToByteList` with the packed bytes collected in an accumulator, so the
    recursive call is in tail position: the output-byte count is encoder-chosen
    and unbounded, so the packer must not keep a native stack frame per byte
    (audit finding P6, encoder side). -/
def bitsToByteListAcc : List UInt8 → BitStream → List UInt8
  | acc, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    bitsToByteListAcc (bitsToByte b0 b1 b2 b3 b4 b5 b6 b7 :: acc) rest
  | acc, _ => acc.reverse

theorem bitsToByteListAcc_eq (acc : List UInt8) (s : BitStream) :
    bitsToByteListAcc acc s = acc.reverse ++ bitsToByteList s := by
  induction s using bitsToByteList.induct generalizing acc with
  | case1 b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
    rw [bitsToByteListAcc, bitsToByteList,
      ih (bitsToByte b0 b1 b2 b3 b4 b5 b6 b7 :: acc)]
    simp
  | case2 s => cases s <;> simp [bitsToByteListAcc, bitsToByteList]

def bitsToByteListTR (s : BitStream) : List UInt8 :=
  bitsToByteListAcc [] s

/-- Swap the compiled `bitsToByteList` for the tail form; theorems (and the whole
    round-trip stack) keep the structural definition via the kernel. -/
@[csimp] theorem bitsToByteList_eq_bitsToByteListTR :
    @bitsToByteList = @bitsToByteListTR := by
  funext s
  unfold bitsToByteListTR
  rw [bitsToByteListAcc_eq]
  simp

def bytesToBits (bs : ByteArray) : BitStream :=
  byteListToBits bs.data.toList

def bitsToBytes (s : BitStream) : ByteArray :=
  (bitsToByteList s).toByteArray

end Bits
end Flac
