import Flac.Native.Bits

/-!
# MD5 (RFC 1321)

Pure-Lean MD5 for the STREAMINFO checksum of the unencoded PCM
(RFC 9639 §8.2). Tested, not verified: it is a conformance checksum, not part of the
losslessness claim. Validated against the RFC 1321 test suite in `FlacTest`.

Encoder-side only (the decoder does not verify MD5 in v1). The block reads
are word-sized bounds tests, and the state travels unboxed through the
block loop; the digest is pinned by the RFC vectors in `FlacTest` and by
`flac -t` on every encoded stream in the benchmark corpus.
-/

namespace Flac.Md5

@[inline] private def fF (x y z : UInt32) : UInt32 := (x &&& y) ||| (~~~x &&& z)
@[inline] private def fG (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& ~~~z)
@[inline] private def fH (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
@[inline] private def fI (x y z : UInt32) : UInt32 := y ^^^ (x ||| ~~~z)

@[inline] private def rotl (x : UInt32) (s : UInt32) : UInt32 :=
  (x <<< s) ||| (x >>> (32 - s))

/-- One MD5 operation. The association is left as written: rewriting it as
    `a + x + k + f`, so the late-arriving `f` is added last, measured 1.10
    against 1.09 ns/byte — clang's reassociate pass already does it where it
    pays. The compiled loop emits one `rol` per step and merges each four-byte
    word read into a single 32-bit load, so ≈5.8 cycles/byte is the state
    chain's latency, not something a source rewrite reaches. -/
@[inline] private def step (a b f x k s : UInt32) : UInt32 :=
  b + rotl (a + f + x + k) s

/-- Byte `i` as a word, 0 past the end.

    Indexed by `Nat`, deliberately. This is the *cold* reader — it runs only
    for a buffer whose size does not fit a machine word — and a `USize` index
    would not merely be slow there, it would be wrong: `msg.usize` is
    `msg.size` reduced mod `USize.size`, so at `msg.size = USize.size` it is
    zero and every read would return 0 rather than the byte. The digest is
    specified over `ByteArray` with no size hypothesis, so the fallback has to
    agree with natural-index reads at every index, including those no machine
    word can name. -/
@[inline] private def byteAt (msg : ByteArray) (i : Nat) : UInt32 :=
  if h : i < msg.size then msg[i].toUInt32 else 0

/-- Little-endian 32-bit word at byte offset `i`. -/
@[inline] private def wordAt (msg : ByteArray) (i : Nat) : UInt32 :=
  byteAt msg i ||| (byteAt msg (i + 1) <<< 8) ||| (byteAt msg (i + 2) <<< 16)
    ||| (byteAt msg (i + 3) <<< 24)

/-- The compression function on sixteen little-endian words. Taking the
    words as parameters is what lets the bounds-checked reader and the
    proof-carrying one share it: both are `@[inline]`, so each call site
    gets the straight-line body with its own loads. -/
@[inline] private def compressWords (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : UInt32) (a0 b0 c0 d0 : UInt32) :
    UInt32 × UInt32 × UInt32 × UInt32 :=
  -- Round 1.
  let a := step a0 b0 (fF b0 c0 d0) m0  0xd76aa478 7
  let d := step d0 a (fF a b0 c0) m1  0xe8c7b756 12
  let c := step c0 d (fF d a b0) m2  0x242070db 17
  let b := step b0 c (fF c d a) m3  0xc1bdceee 22
  let a := step a b (fF b c d) m4  0xf57c0faf 7
  let d := step d a (fF a b c) m5  0x4787c62a 12
  let c := step c d (fF d a b) m6  0xa8304613 17
  let b := step b c (fF c d a) m7  0xfd469501 22
  let a := step a b (fF b c d) m8  0x698098d8 7
  let d := step d a (fF a b c) m9  0x8b44f7af 12
  let c := step c d (fF d a b) m10 0xffff5bb1 17
  let b := step b c (fF c d a) m11 0x895cd7be 22
  let a := step a b (fF b c d) m12 0x6b901122 7
  let d := step d a (fF a b c) m13 0xfd987193 12
  let c := step c d (fF d a b) m14 0xa679438e 17
  let b := step b c (fF c d a) m15 0x49b40821 22
  -- Round 2.
  let a := step a b (fG b c d) m1  0xf61e2562 5
  let d := step d a (fG a b c) m6  0xc040b340 9
  let c := step c d (fG d a b) m11 0x265e5a51 14
  let b := step b c (fG c d a) m0  0xe9b6c7aa 20
  let a := step a b (fG b c d) m5  0xd62f105d 5
  let d := step d a (fG a b c) m10 0x02441453 9
  let c := step c d (fG d a b) m15 0xd8a1e681 14
  let b := step b c (fG c d a) m4  0xe7d3fbc8 20
  let a := step a b (fG b c d) m9  0x21e1cde6 5
  let d := step d a (fG a b c) m14 0xc33707d6 9
  let c := step c d (fG d a b) m3  0xf4d50d87 14
  let b := step b c (fG c d a) m8  0x455a14ed 20
  let a := step a b (fG b c d) m13 0xa9e3e905 5
  let d := step d a (fG a b c) m2  0xfcefa3f8 9
  let c := step c d (fG d a b) m7  0x676f02d9 14
  let b := step b c (fG c d a) m12 0x8d2a4c8a 20
  -- Round 3.
  let a := step a b (fH b c d) m5  0xfffa3942 4
  let d := step d a (fH a b c) m8  0x8771f681 11
  let c := step c d (fH d a b) m11 0x6d9d6122 16
  let b := step b c (fH c d a) m14 0xfde5380c 23
  let a := step a b (fH b c d) m1  0xa4beea44 4
  let d := step d a (fH a b c) m4  0x4bdecfa9 11
  let c := step c d (fH d a b) m7  0xf6bb4b60 16
  let b := step b c (fH c d a) m10 0xbebfbc70 23
  let a := step a b (fH b c d) m13 0x289b7ec6 4
  let d := step d a (fH a b c) m0  0xeaa127fa 11
  let c := step c d (fH d a b) m3  0xd4ef3085 16
  let b := step b c (fH c d a) m6  0x04881d05 23
  let a := step a b (fH b c d) m9  0xd9d4d039 4
  let d := step d a (fH a b c) m12 0xe6db99e5 11
  let c := step c d (fH d a b) m15 0x1fa27cf8 16
  let b := step b c (fH c d a) m2  0xc4ac5665 23
  -- Round 4.
  let a := step a b (fI b c d) m0  0xf4292244 6
  let d := step d a (fI a b c) m7  0x432aff97 10
  let c := step c d (fI d a b) m14 0xab9423a7 15
  let b := step b c (fI c d a) m5  0xfc93a039 21
  let a := step a b (fI b c d) m12 0x655b59c3 6
  let d := step d a (fI a b c) m3  0x8f0ccc92 10
  let c := step c d (fI d a b) m10 0xffeff47d 15
  let b := step b c (fI c d a) m1  0x85845dd1 21
  let a := step a b (fI b c d) m8  0x6fa87e4f 6
  let d := step d a (fI a b c) m15 0xfe2ce6e0 10
  let c := step c d (fI d a b) m6  0xa3014314 15
  let b := step b c (fI c d a) m13 0x4e0811a1 21
  let a := step a b (fI b c d) m4  0xf7537e82 6
  let d := step d a (fI a b c) m11 0xbd3af235 10
  let c := step c d (fI d a b) m2  0x2ad7d2bb 15
  let b := step b c (fI c d a) m9  0xeb86d391 21
  (a0 + a, b0 + b, c0 + c, d0 + d)

/-- Compress the 64-byte block at `base`, bounds-testing every byte. The
    fallback path: `compressIn` below is what runs. -/
@[inline] private def compress (msg : ByteArray) (base : Nat) (a0 b0 c0 d0 : UInt32) :
    UInt32 × UInt32 × UInt32 × UInt32 :=
  compressWords (wordAt msg base) (wordAt msg (base + 4)) (wordAt msg (base + 8))
    (wordAt msg (base + 12)) (wordAt msg (base + 16)) (wordAt msg (base + 20))
    (wordAt msg (base + 24)) (wordAt msg (base + 28)) (wordAt msg (base + 32))
    (wordAt msg (base + 36)) (wordAt msg (base + 40)) (wordAt msg (base + 44))
    (wordAt msg (base + 48)) (wordAt msg (base + 52)) (wordAt msg (base + 56))
    (wordAt msg (base + 60)) a0 b0 c0 d0

/-! ### The block reads, without the per-byte test

`byteAt` costs a machine-word comparison *and a load of the `ByteArray`'s
size out of its object header* on every one of the sixty-four bytes of a
block. The header load is the expensive half: it sits in the same cache
line as the reference count, which every encoder worker touching the same
input updates atomically, so at sixteen threads it is a coherence miss.

One hypothesis removes both. `base + 64 ≤ size` is decided once per block
and carried down the loop exactly as `Crc.crcBlocks` carries its own, so
the sixty-four reads are plain `uget`s. The proofs are erased; what is
left is sixteen little-endian word loads. -/

/-- Byte `base + k` of a block known to be inside the buffer. -/
@[inline] private def byteIn (msg : ByteArray) (base : USize) (k : Nat)
    (hk : k < 64) (h : base.toNat + 64 ≤ msg.size) (hs : msg.size < USize.size) : UInt32 :=
  (msg.uget (base + USize.ofNat k)
    (by rw [Flac.Bits.usize_add_toNat base k msg.size (by omega) hs]; omega)).toUInt32

/-- Little-endian 32-bit word at `base + k`, inside a checked block. -/
@[inline] private def wordIn (msg : ByteArray) (base : USize) (k : Nat)
    (hk : k + 3 < 64) (h : base.toNat + 64 ≤ msg.size) (hs : msg.size < USize.size) : UInt32 :=
  byteIn msg base k (by omega) h hs
    ||| (byteIn msg base (k + 1) (by omega) h hs <<< 8)
    ||| (byteIn msg base (k + 2) (by omega) h hs <<< 16)
    ||| (byteIn msg base (k + 3) (by omega) h hs <<< 24)

/-- Compress the 64-byte block at `base`, reads unchecked under `h`. -/
@[inline] private def compressIn (msg : ByteArray) (base : USize) (a0 b0 c0 d0 : UInt32)
    (h : base.toNat + 64 ≤ msg.size) (hs : msg.size < USize.size) :
    UInt32 × UInt32 × UInt32 × UInt32 :=
  compressWords (wordIn msg base 0 (by omega) h hs) (wordIn msg base 4 (by omega) h hs)
    (wordIn msg base 8 (by omega) h hs) (wordIn msg base 12 (by omega) h hs)
    (wordIn msg base 16 (by omega) h hs) (wordIn msg base 20 (by omega) h hs)
    (wordIn msg base 24 (by omega) h hs) (wordIn msg base 28 (by omega) h hs)
    (wordIn msg base 32 (by omega) h hs) (wordIn msg base 36 (by omega) h hs)
    (wordIn msg base 40 (by omega) h hs) (wordIn msg base 44 (by omega) h hs)
    (wordIn msg base 48 (by omega) h hs) (wordIn msg base 52 (by omega) h hs)
    (wordIn msg base 56 (by omega) h hs) (wordIn msg base 60 (by omega) h hs) a0 b0 c0 d0

/-- **The two readers agree wherever both apply.** `byteIn`'s word-indexed
    `uget` is `byteAt`'s natural-index read, so the fast path computes the
    fallback. This is the property the cold path exists to preserve: a digest
    theorem quantifies over *every* `ByteArray`, including sizes no machine
    word can name, and it is the fallback that says what the digest means
    there. Indexing that path by `USize` would silently read zeros at
    `msg.size = USize.size`. -/
theorem byteIn_eq_byteAt (msg : ByteArray) (base : USize) (k : Nat)
    (hk : k < 64) (h : base.toNat + 64 ≤ msg.size) (hs : msg.size < USize.size) :
    byteIn msg base k hk h hs = byteAt msg (base.toNat + k) := by
  have hidx : (base + USize.ofNat k).toNat = base.toNat + k :=
    Flac.Bits.usize_add_toNat base k msg.size (by omega) hs
  unfold byteIn byteAt
  rw [dif_pos (by omega)]
  show ((msg[(base + USize.ofNat k).toNat]'(by omega)).toUInt32) = _
  rw [getElem_congr_idx hidx]

theorem wordIn_eq_wordAt (msg : ByteArray) (base : USize) (k : Nat)
    (hk : k + 3 < 64) (h : base.toNat + 64 ≤ msg.size) (hs : msg.size < USize.size) :
    wordIn msg base k hk h hs = wordAt msg (base.toNat + k) := by
  unfold wordIn wordAt
  rw [byteIn_eq_byteAt, byteIn_eq_byteAt, byteIn_eq_byteAt, byteIn_eq_byteAt,
    Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]

theorem compressIn_eq_compress (msg : ByteArray) (base : USize) (a0 b0 c0 d0 : UInt32)
    (h : base.toNat + 64 ≤ msg.size) (hs : msg.size < USize.size) :
    compressIn msg base a0 b0 c0 d0 h hs = compress msg base.toNat a0 b0 c0 d0 := by
  unfold compressIn compress
  simp only [wordIn_eq_wordAt, Nat.add_zero]

/-- `n` consecutive blocks from `base`, state as unboxed tail parameters.
    The fallback loop, for a buffer whose size does not fit a machine word:
    unreachable on any real platform, but it is what the digest *means* on
    such a value, so it reads and advances in `Nat`. -/
private def blocks (msg : ByteArray) : (n : Nat) → (base : Nat) → (a b c d : UInt32) →
    UInt32 × UInt32 × UInt32 × UInt32
  | 0, _, a, b, c, d => (a, b, c, d)
  | n + 1, base, a, b, c, d =>
    match compress msg base a b c d with
    | (a', b', c', d') => blocks msg n (base + 64) a' b' c' d'

/-- The shipped loop: the in-bounds hypothesis travels with the cursor, so
    no block read touches the buffer's header. -/
private def blocksIn (msg : ByteArray) (hs : msg.size < USize.size) :
    (n : Nat) → (base : USize) → (a b c d : UInt32) → base.toNat + 64 * n ≤ msg.size →
    UInt32 × UInt32 × UInt32 × UInt32
  | 0, _, a, b, c, d, _ => (a, b, c, d)
  | n + 1, base, a, b, c, d, hn =>
    match compressIn msg base a b c d (by omega) hs with
    | (a', b', c', d') =>
      blocksIn msg hs n (base + USize.ofNat 64) a' b' c' d'
        (by rw [Flac.Bits.usize_add_toNat base 64 msg.size (by omega) hs]; omega)

/-- `blocksIn` where the size fits a word, `blocks` otherwise. -/
@[inline] private def blocksFrom (msg : ByteArray) (n : Nat) (a b c d : UInt32) :
    UInt32 × UInt32 × UInt32 × UInt32 :=
  if hs : msg.size < USize.size ∧ 64 * n ≤ msg.size then
    blocksIn msg hs.1 n 0 a b c d (by rw [USize.toNat_zero]; omega)
  else blocks msg n 0 a b c d

/-- RFC 1321 §3.4 padding, but only for the final partial block. The result
    is one or two blocks (64 or 128 bytes), never a copy of the full input. -/
private def finalBlocks (msg : ByteArray) (fullBytes : Nat) : ByteArray := Id.run do
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

private def wordLE (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- The 16-byte MD5 digest of `msg`. -/
def md5 (msg : ByteArray) : ByteArray :=
  let fullBlocks := msg.size / 64
  let (a1, b1, c1, d1) := blocksFrom msg fullBlocks 0x67452301 0xefcdab89 0x98badcfe 0x10325476
  let tail := finalBlocks msg (64 * fullBlocks)
  let (a, b, c, d) := blocksFrom tail (tail.size / 64) a1 b1 c1 d1
  ⟨(wordLE a ++ wordLE b ++ wordLE c ++ wordLE d).toArray⟩

/-- Digest as a lowercase hex string (for tests and diagnostics). -/
def md5Hex (msg : ByteArray) : String :=
  let hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!
  String.ofList <| (md5 msg).toList.flatMap fun b =>
    [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

end Flac.Md5
