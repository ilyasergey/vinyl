import Flac.Native.Bits

/-!
# Buffered bit reader — the production decoder's input layer

`BitReader` reads MSB-first bits directly from a `ByteArray` at a bit
position, with no intermediate `List Bool`. Every primitive is proven to
simulate the model reader in `Flac.Spec.Reader`: for a reader `br`,
`toStream br = (bytesToBits br.data).drop br.pos`, and each production
read returns exactly what the model read returns on `toStream br`.

Bit extraction has two layers: `bit`/`extractBits` are the bit-at-a-time
*specification*, structured like the model's `readBits` so the simulation
proofs stay one-induction affairs; `bitFast`/`extractBitsFast` are the
byte-at-a-time implementations the reader actually runs, each proven equal
to its specification in `Flac.Spec.Reader` (`bitFast_eq`,
`extractBitsFast_eq`) — the fast path replaces the slow one *under the
same theorems*.
-/

namespace Flac.Bits

/-- A byte buffer with a bit cursor. -/
structure BitReader where
  data : ByteArray
  pos : Nat

namespace BitReader

/-- The `i`-th bit of the buffer, MSB-first within each byte.
    (Indexes the `ByteArray` directly — `.data` would copy.) -/
def bit (d : ByteArray) (i : Nat) : Bool :=
  decide ((if h : i / 8 < d.size then d[i / 8] else 0).toNat
    / 2 ^ (7 - i % 8) % 2 = 1)

/-- Read `n` bits starting at `pos` (callers check bounds). This is the
    *specification*; the reader runs `extractBitsFast`. -/
def extractBits (d : ByteArray) (pos : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if bit d pos then 2 ^ n else 0) + extractBits d (pos + 1) n

/-- The `i`-th bit by shift and mask — no `Nat.pow` in the hot path.
    Proven equal to `bit` (`Flac.Spec.Reader.bitFast_eq`). -/
@[inline] def bitFast (d : ByteArray) (i : Nat) : Bool :=
  decide ((if h : i / 8 < d.size then d[i / 8] else 0).toNat >>> (7 - i % 8) &&& 1 = 1)

/-- Big-endian accumulation of the `k` bytes starting at index `i`
    (out-of-range bytes read as 0, matching `bit`). -/
@[inline] def accBytes (d : ByteArray) : (i k acc : Nat) → Nat
  | _, 0, acc => acc
  | i, k + 1, acc =>
    accBytes d (i + 1) k (acc * 256 + (if h : i < d.size then d[i] else 0).toNat)

/-- Byte-at-a-time bit extraction: fetch the covering bytes, drop the
    trailing bits, mask to `n`. Proven equal to `extractBits`
    (`Flac.Spec.Reader.extractBitsFast_eq`). -/
@[inline] def extractBitsFast (d : ByteArray) (pos n : Nat) : Nat :=
  accBytes d (pos / 8) ((pos + n + 7) / 8 - pos / 8) 0
    >>> ((8 - (pos + n) % 8) % 8) &&& (p2 n - 1)

/-- `extractBitsFast` over a fixed three-byte window, with the `2^n - 1`
    mask supplied by the caller. Valid exactly when `pos % 8 + n ≤ 24`,
    which holds for every `n ≤ 17` — so every RICE partition parameter
    (`k < 15`) and all but the widest RICE2 ones.

    What it avoids is the point: `extractBitsFast` computes its byte count
    with two `Nat` divisions, runs `accBytes` as a loop, and rebuilds
    `2^n - 1` on every call. Three straight-line byte loads against a
    hoisted mask measured **1.35x** on a 2M-sample Rice run — and the Rice
    reader is ~22% of decode and ~20% of the encoder's certificate.
    Proven equal to `extractBitsFast` by
    `Flac.Spec.Reader.extractBits3_eq`.

    (A libFLAC-style *windowed* reader — a cached 64-bit word plus a
    leading-zero count — was prototyped and measured **5.7x slower**:
    Lean boxes `UInt64` values carried across control flow, so word
    refills and `clz` cost far more than the scalar `Nat` path they were
    meant to replace. Three-byte extraction is what is left of that idea.) -/
@[inline] def extractBits3 (d : ByteArray) (pos n mask : Nat) : Nat :=
  let p := pos / 8
  let b0 := (if h : p < d.size then d[p] else 0).toNat
  let b1 := (if h : p + 1 < d.size then d[p + 1] else 0).toNat
  let b2 := (if h : p + 2 < d.size then d[p + 2] else 0).toNat
  ((b0 * 256 + b1) * 256 + b2) >>> (24 - pos % 8 - n) &&& mask

/-- Total bit count of the buffer. -/
def size (br : BitReader) : Nat := 8 * br.data.size

/-- Bits left to read. -/
def remaining (br : BitReader) : Nat := br.size - br.pos

def readBits (n : Nat) (br : BitReader) : Option (Nat × BitReader) :=
  if n = 0 then some (0, br)
  else if br.pos + n ≤ br.size then
    some (extractBitsFast br.data br.pos n, ⟨br.data, br.pos + n⟩)
  else none

/-- Unary code: count zero bits up to the terminating one bit. -/
def readUnaryGo (d : ByteArray) (q : Nat) (pos : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    if bitFast d pos then some (q, pos + 1)
    else readUnaryGo d (q + 1) (pos + 1) fuel

/-- Position of the next one bit, or `pos + fuel` when the searched range
    contains only zeroes.  Unlike `readUnaryGo`, the successful hot path
    returns one scalar `Nat`: Rice sequence readers recover the quotient as
    `onePos - pos` and avoid allocating an `Option (Nat × Nat)` for every
    sample.  Proven equivalent to `readUnaryGo` in `Flac.Spec.Reader`. -/
@[inline] def scanOne (d : ByteArray) : (pos fuel : Nat) → Nat
  | pos, 0 => pos
  | pos, fuel + 1 =>
    if bitFast d pos then pos else scanOne d (pos + 1) fuel

def readUnary (br : BitReader) : Option (Nat × BitReader) :=
  match readUnaryGo br.data 0 br.pos br.remaining with
  | none => none
  | some (q, pos') => some (q, ⟨br.data, pos'⟩)

def readSInt (n : Nat) (br : BitReader) : Option (Int × BitReader) :=
  match readBits n br with
  | none => none
  | some (v, br') =>
    some (if 2 * v < p2 n then (v : Int) else (v : Int) - ((p2 n : Nat) : Int), br')

/-- Skip `n` bits. -/
def skip (n : Nat) (br : BitReader) : Option BitReader :=
  if n = 0 then some br
  else if br.pos + n ≤ br.size then some ⟨br.data, br.pos + n⟩ else none

end BitReader
end Flac.Bits
