import Flac.Native.Md5

/-!
# MD5 against RFC 1321

`Flac.Md5.Rfc1321.md5` is a direct, table-free transcription of RFC 1321 §3:
the four auxiliary functions, the 64 literal operations of Appendix A with
their constants and shift amounts written out, the §3.1 padding, and the
§3.5 little-endian output.  No lookup tables and no reuse of the optimized
encoder path.

`md5_eq_rfc1321` proves the shipped `Flac.Md5.md5` computes exactly this
digest, unconditionally over every `ByteArray`.
-/

namespace Flac.Md5.Rfc1321

abbrev State := UInt32 × UInt32 × UInt32 × UInt32

/-- RFC 1321 §3.4 auxiliary functions. -/
@[inline] def f (x y z : UInt32) : UInt32 := (x &&& y) ||| (~~~x &&& z)
@[inline] def g (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& ~~~z)
@[inline] def h (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
@[inline] def i (x y z : UInt32) : UInt32 := y ^^^ (x ||| ~~~z)

/-- Left rotation of a 32-bit word by `s` bits. -/
@[inline] def rotateLeft (x s : UInt32) : UInt32 :=
  (x <<< s) ||| (x >>> (32 - s))

/-- One MD5 operation: `b + ((a + mix + word + constant) <<<< shift)`. -/
@[inline] def roundStep (a b mix word constant shift : UInt32) : UInt32 :=
  b + rotateLeft (a + mix + word + constant) shift

/-- Byte `j` of the message, defaulting to `0` past the end. -/
@[inline] def byteAt (msg : ByteArray) (j : Nat) : UInt32 :=
  if h : j < msg.size then msg[j].toUInt32 else 0

/-- The little-endian 32-bit word at byte offset `j`. -/
@[inline] def wordAt (msg : ByteArray) (j : Nat) : UInt32 :=
  byteAt msg j ||| (byteAt msg (j + 1) <<< 8) ||| (byteAt msg (j + 2) <<< 16)
    ||| (byteAt msg (j + 3) <<< 24)

/-- The 64 operations of RFC 1321 Appendix A on sixteen message words. -/
def compressWords (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : UInt32)
    (a0 b0 c0 d0 : UInt32) : State :=
  -- Round 1.
  let a := roundStep a0 b0 (f b0 c0 d0) m0  0xd76aa478 7
  let d := roundStep d0 a (f a b0 c0) m1  0xe8c7b756 12
  let c := roundStep c0 d (f d a b0) m2  0x242070db 17
  let b := roundStep b0 c (f c d a) m3  0xc1bdceee 22
  let a := roundStep a b (f b c d) m4  0xf57c0faf 7
  let d := roundStep d a (f a b c) m5  0x4787c62a 12
  let c := roundStep c d (f d a b) m6  0xa8304613 17
  let b := roundStep b c (f c d a) m7  0xfd469501 22
  let a := roundStep a b (f b c d) m8  0x698098d8 7
  let d := roundStep d a (f a b c) m9  0x8b44f7af 12
  let c := roundStep c d (f d a b) m10 0xffff5bb1 17
  let b := roundStep b c (f c d a) m11 0x895cd7be 22
  let a := roundStep a b (f b c d) m12 0x6b901122 7
  let d := roundStep d a (f a b c) m13 0xfd987193 12
  let c := roundStep c d (f d a b) m14 0xa679438e 17
  let b := roundStep b c (f c d a) m15 0x49b40821 22
  -- Round 2.
  let a := roundStep a b (g b c d) m1  0xf61e2562 5
  let d := roundStep d a (g a b c) m6  0xc040b340 9
  let c := roundStep c d (g d a b) m11 0x265e5a51 14
  let b := roundStep b c (g c d a) m0  0xe9b6c7aa 20
  let a := roundStep a b (g b c d) m5  0xd62f105d 5
  let d := roundStep d a (g a b c) m10 0x02441453 9
  let c := roundStep c d (g d a b) m15 0xd8a1e681 14
  let b := roundStep b c (g c d a) m4  0xe7d3fbc8 20
  let a := roundStep a b (g b c d) m9  0x21e1cde6 5
  let d := roundStep d a (g a b c) m14 0xc33707d6 9
  let c := roundStep c d (g d a b) m3  0xf4d50d87 14
  let b := roundStep b c (g c d a) m8  0x455a14ed 20
  let a := roundStep a b (g b c d) m13 0xa9e3e905 5
  let d := roundStep d a (g a b c) m2  0xfcefa3f8 9
  let c := roundStep c d (g d a b) m7  0x676f02d9 14
  let b := roundStep b c (g c d a) m12 0x8d2a4c8a 20
  -- Round 3.
  let a := roundStep a b (h b c d) m5  0xfffa3942 4
  let d := roundStep d a (h a b c) m8  0x8771f681 11
  let c := roundStep c d (h d a b) m11 0x6d9d6122 16
  let b := roundStep b c (h c d a) m14 0xfde5380c 23
  let a := roundStep a b (h b c d) m1  0xa4beea44 4
  let d := roundStep d a (h a b c) m4  0x4bdecfa9 11
  let c := roundStep c d (h d a b) m7  0xf6bb4b60 16
  let b := roundStep b c (h c d a) m10 0xbebfbc70 23
  let a := roundStep a b (h b c d) m13 0x289b7ec6 4
  let d := roundStep d a (h a b c) m0  0xeaa127fa 11
  let c := roundStep c d (h d a b) m3  0xd4ef3085 16
  let b := roundStep b c (h c d a) m6  0x04881d05 23
  let a := roundStep a b (h b c d) m9  0xd9d4d039 4
  let d := roundStep d a (h a b c) m12 0xe6db99e5 11
  let c := roundStep c d (h d a b) m15 0x1fa27cf8 16
  let b := roundStep b c (h c d a) m2  0xc4ac5665 23
  -- Round 4.
  let a := roundStep a b (i b c d) m0  0xf4292244 6
  let d := roundStep d a (i a b c) m7  0x432aff97 10
  let c := roundStep c d (i d a b) m14 0xab9423a7 15
  let b := roundStep b c (i c d a) m5  0xfc93a039 21
  let a := roundStep a b (i b c d) m12 0x655b59c3 6
  let d := roundStep d a (i a b c) m3  0x8f0ccc92 10
  let c := roundStep c d (i d a b) m10 0xffeff47d 15
  let b := roundStep b c (i c d a) m1  0x85845dd1 21
  let a := roundStep a b (i b c d) m8  0x6fa87e4f 6
  let d := roundStep d a (i a b c) m15 0xfe2ce6e0 10
  let c := roundStep c d (i d a b) m6  0xa3014314 15
  let b := roundStep b c (i c d a) m13 0x4e0811a1 21
  let a := roundStep a b (i b c d) m4  0xf7537e82 6
  let d := roundStep d a (i a b c) m11 0xbd3af235 10
  let c := roundStep c d (i d a b) m2  0x2ad7d2bb 15
  let b := roundStep b c (i c d a) m9  0xeb86d391 21
  (a0 + a, b0 + b, c0 + c, d0 + d)

/-- The RFC compression function on the 64-byte block at `base`. -/
def compress (msg : ByteArray) (base : Nat) (a0 b0 c0 d0 : UInt32) : State :=
  compressWords (wordAt msg base) (wordAt msg (base + 4)) (wordAt msg (base + 8))
    (wordAt msg (base + 12)) (wordAt msg (base + 16)) (wordAt msg (base + 20))
    (wordAt msg (base + 24)) (wordAt msg (base + 28)) (wordAt msg (base + 32))
    (wordAt msg (base + 36)) (wordAt msg (base + 40)) (wordAt msg (base + 44))
    (wordAt msg (base + 48)) (wordAt msg (base + 52)) (wordAt msg (base + 56))
    (wordAt msg (base + 60)) a0 b0 c0 d0

/-- `n` consecutive blocks from `base`, in Merkle–Damgård chaining order. -/
def blocks (msg : ByteArray) : (n : Nat) → (base : Nat) → (a b c d : UInt32) → State
  | 0, _, a, b, c, d => (a, b, c, d)
  | n + 1, base, a, b, c, d =>
    match compress msg base a b c d with
    | (a', b', c', d') => blocks msg n (base + 64) a' b' c' d'

/-- RFC 1321 §3.1 padding of the unprocessed suffix: the `0x80` byte, zero
    padding, and the 64-bit little-endian bit length, yielding one or two
    complete 64-byte blocks. -/
def finalBlocks (msg : ByteArray) (fullBytes : Nat) : ByteArray := Id.run do
  let rem := msg.size - fullBytes
  let tailSize := if rem < 56 then 64 else 128
  let mut tail := ByteArray.emptyWithCapacity tailSize
  for i in [fullBytes : msg.size] do
    tail := tail.push (if h : i < msg.size then msg[i] else 0)
  tail := tail.push 0x80
  for _ in [0 : tailSize - tail.size - 8] do
    tail := tail.push 0
  let bitLen : UInt64 := UInt64.ofNat msg.size * 8
  for i in [0 : 8] do
    tail := tail.push (bitLen >>> (8 * UInt64.ofNat i)).toUInt8
  return tail

/-- RFC 1321 §3.5 little-endian serialization of a state word. -/
def wordLittleEndian (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- The 16-byte MD5 digest of `msg`, RFC 1321. -/
def md5 (msg : ByteArray) : ByteArray :=
  let fullBlocks := msg.size / 64
  let (a1, b1, c1, d1) := blocks msg fullBlocks 0 0x67452301 0xefcdab89 0x98badcfe 0x10325476
  let tail := finalBlocks msg (64 * fullBlocks)
  let (a, b, c, d) := blocks tail (tail.size / 64) 0 a1 b1 c1 d1
  ⟨(wordLittleEndian a ++ wordLittleEndian b ++ wordLittleEndian c ++ wordLittleEndian d).toArray⟩

end Flac.Md5.Rfc1321

namespace Flac.Md5

/-! ## Bridge lemmas from the shipped definitions to the RFC transcription -/

/-- The fallback byte reader is the RFC's defaulting access. -/
theorem byteAt_eq (msg : ByteArray) (j : Nat) : byteAt msg j = Rfc1321.byteAt msg j := rfl

theorem wordAt_eq (msg : ByteArray) (j : Nat) : wordAt msg j = Rfc1321.wordAt msg j := rfl

theorem fF_eq (x y z : UInt32) : fF x y z = Rfc1321.f x y z := rfl
theorem fG_eq (x y z : UInt32) : fG x y z = Rfc1321.g x y z := rfl
theorem fH_eq (x y z : UInt32) : fH x y z = Rfc1321.h x y z := rfl
theorem fI_eq (x y z : UInt32) : fI x y z = Rfc1321.i x y z := rfl

theorem step_eq (a b mix word constant shift : UInt32) :
    step a b mix word constant shift = Rfc1321.roundStep a b mix word constant shift := rfl

set_option maxHeartbeats 2000000 in
theorem compressWords_eq (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : UInt32)
    (a b c d : UInt32) :
    compressWords m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 a b c d =
      Rfc1321.compressWords m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 a b c d := by
  simp (config := { zeta := false }) only [compressWords, Rfc1321.compressWords,
    step_eq, fF_eq, fG_eq, fH_eq, fI_eq]

set_option maxHeartbeats 2000000 in
theorem compress_eq (msg : ByteArray) (base : Nat) (a b c d : UInt32) :
    compress msg base a b c d = Rfc1321.compress msg base a b c d := by
  unfold compress Rfc1321.compress
  rw [compressWords_eq]
  simp only [wordAt_eq]

theorem blocks_eq (msg : ByteArray) : ∀ (n base : Nat) (a b c d : UInt32),
    blocks msg n base a b c d = Rfc1321.blocks msg n base a b c d := by
  intro n
  induction n with
  | zero => intro base a b c d; rfl
  | succ n ih =>
    intro base a b c d
    unfold blocks Rfc1321.blocks
    rw [compress_eq]
    generalize Rfc1321.compress msg base a b c d = st
    obtain ⟨a', b', c', d'⟩ := st
    exact ih (base + 64) a' b' c' d'

theorem blocksIn_eq_blocks (msg : ByteArray) (hs : msg.size < USize.size) :
    ∀ (n : Nat) (base : USize) (a b c d : UInt32) (hn : base.toNat + 64 * n ≤ msg.size),
      blocksIn msg hs n base a b c d hn = blocks msg n base.toNat a b c d := by
  intro n
  induction n with
  | zero => intro base a b c d hn; rfl
  | succ n ih =>
    intro base a b c d hn
    have e : (base + USize.ofNat 64).toNat = base.toNat + 64 :=
      Flac.Bits.usize_add_toNat base 64 msg.size (by omega) hs
    unfold blocksIn blocks
    rw [compressIn_eq_compress]
    generalize compress msg base.toNat a b c d = st
    obtain ⟨a', b', c', d'⟩ := st
    exact e ▸ ih (base + USize.ofNat 64) a' b' c' d' (by rw [e]; omega)

theorem blocksFrom_eq_blocks (msg : ByteArray) (n : Nat) (a b c d : UInt32) :
    blocksFrom msg n a b c d = blocks msg n 0 a b c d := by
  unfold blocksFrom
  split
  · next hs => rw [blocksIn_eq_blocks, USize.toNat_zero]
  · rfl

theorem finalBlocks_eq (msg : ByteArray) (fullBytes : Nat) :
    finalBlocks msg fullBytes = Rfc1321.finalBlocks msg fullBytes := rfl

theorem wordLE_eq (x : UInt32) : wordLE x = Rfc1321.wordLittleEndian x := rfl

/-- **The shipped MD5 computes the RFC 1321 digest.** -/
theorem md5_eq_rfc1321 (msg : ByteArray) : md5 msg = Rfc1321.md5 msg := by
  simp only [md5, Rfc1321.md5, blocksFrom_eq_blocks, blocks_eq, finalBlocks_eq, wordLE_eq]

end Flac.Md5
