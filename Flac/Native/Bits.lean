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

def bytesToBits (bs : ByteArray) : BitStream :=
  byteListToBits bs.data.toList

def bitsToBytes (s : BitStream) : ByteArray :=
  (bitsToByteList s).toByteArray

end Bits
end Flac
