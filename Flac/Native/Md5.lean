/-!
# MD5 (RFC 1321)

Pure-Lean MD5 for the STREAMINFO checksum of the unencoded PCM
(RFC 9639 §8.2). Tested, not verified: it is a conformance checksum, not part of the
losslessness claim. Validated against the RFC 1321 test suite in `FlacTest`.

Encoder-side only (the decoder does not verify MD5 in v1). Complete-block
proofs make the hot-path byte reads unchecked without weakening memory safety.
-/

namespace Flac.Md5

@[inline] private def fF (x y z : UInt32) : UInt32 := (x &&& y) ||| (~~~x &&& z)
@[inline] private def fG (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& ~~~z)
@[inline] private def fH (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
@[inline] private def fI (x y z : UInt32) : UInt32 := y ^^^ (x ||| ~~~z)

@[inline] private def rotl (x : UInt32) (s : UInt32) : UInt32 :=
  (x <<< s) ||| (x >>> (32 - s))

@[inline] private def step (a b f x k s : UInt32) : UInt32 :=
  b + rotl (a + f + x + k) s

/-- Decode one little-endian 32-bit word directly from a 64-byte block.
    Reading on demand avoids allocating a generic `Array UInt32` (and its
    sixteen boxed elements) for every input block. -/
@[inline] private def blockWord (msg : ByteArray) (base g : Nat)
    (hg : g < 16) (hb : base + 64 ≤ msg.size) : UInt32 :=
  let o := base + 4 * g
  (msg[o]'(by omega)).toUInt32 ||| ((msg[o+1]'(by omega)).toUInt32 <<< 8)
    ||| ((msg[o+2]'(by omega)).toUInt32 <<< 16)
    ||| ((msg[o+3]'(by omega)).toUInt32 <<< 24)

/-- Compress one 64-byte block in place from `msg`, starting at `base`.
    Callers only pass complete blocks. -/
private def compress (st : UInt32 × UInt32 × UInt32 × UInt32)
    (msg : ByteArray) (base : Nat) (hb : base + 64 ≤ msg.size) :
    UInt32 × UInt32 × UInt32 × UInt32 := Id.run do
  let m0 := blockWord msg base 0 (by omega) hb
  let m1 := blockWord msg base 1 (by omega) hb
  let m2 := blockWord msg base 2 (by omega) hb
  let m3 := blockWord msg base 3 (by omega) hb
  let m4 := blockWord msg base 4 (by omega) hb
  let m5 := blockWord msg base 5 (by omega) hb
  let m6 := blockWord msg base 6 (by omega) hb
  let m7 := blockWord msg base 7 (by omega) hb
  let m8 := blockWord msg base 8 (by omega) hb
  let m9 := blockWord msg base 9 (by omega) hb
  let m10 := blockWord msg base 10 (by omega) hb
  let m11 := blockWord msg base 11 (by omega) hb
  let m12 := blockWord msg base 12 (by omega) hb
  let m13 := blockWord msg base 13 (by omega) hb
  let m14 := blockWord msg base 14 (by omega) hb
  let m15 := blockWord msg base 15 (by omega) hb
  let (a0, b0, c0, d0) := st
  let mut a := a0
  let mut b := b0
  let mut c := c0
  let mut d := d0
  -- Round 1.
  a := step a b (fF b c d) m0  0xd76aa478 7
  d := step d a (fF a b c) m1  0xe8c7b756 12
  c := step c d (fF d a b) m2  0x242070db 17
  b := step b c (fF c d a) m3  0xc1bdceee 22
  a := step a b (fF b c d) m4  0xf57c0faf 7
  d := step d a (fF a b c) m5  0x4787c62a 12
  c := step c d (fF d a b) m6  0xa8304613 17
  b := step b c (fF c d a) m7  0xfd469501 22
  a := step a b (fF b c d) m8  0x698098d8 7
  d := step d a (fF a b c) m9  0x8b44f7af 12
  c := step c d (fF d a b) m10 0xffff5bb1 17
  b := step b c (fF c d a) m11 0x895cd7be 22
  a := step a b (fF b c d) m12 0x6b901122 7
  d := step d a (fF a b c) m13 0xfd987193 12
  c := step c d (fF d a b) m14 0xa679438e 17
  b := step b c (fF c d a) m15 0x49b40821 22
  -- Round 2.
  a := step a b (fG b c d) m1  0xf61e2562 5
  d := step d a (fG a b c) m6  0xc040b340 9
  c := step c d (fG d a b) m11 0x265e5a51 14
  b := step b c (fG c d a) m0  0xe9b6c7aa 20
  a := step a b (fG b c d) m5  0xd62f105d 5
  d := step d a (fG a b c) m10 0x02441453 9
  c := step c d (fG d a b) m15 0xd8a1e681 14
  b := step b c (fG c d a) m4  0xe7d3fbc8 20
  a := step a b (fG b c d) m9  0x21e1cde6 5
  d := step d a (fG a b c) m14 0xc33707d6 9
  c := step c d (fG d a b) m3  0xf4d50d87 14
  b := step b c (fG c d a) m8  0x455a14ed 20
  a := step a b (fG b c d) m13 0xa9e3e905 5
  d := step d a (fG a b c) m2  0xfcefa3f8 9
  c := step c d (fG d a b) m7  0x676f02d9 14
  b := step b c (fG c d a) m12 0x8d2a4c8a 20
  -- Round 3.
  a := step a b (fH b c d) m5  0xfffa3942 4
  d := step d a (fH a b c) m8  0x8771f681 11
  c := step c d (fH d a b) m11 0x6d9d6122 16
  b := step b c (fH c d a) m14 0xfde5380c 23
  a := step a b (fH b c d) m1  0xa4beea44 4
  d := step d a (fH a b c) m4  0x4bdecfa9 11
  c := step c d (fH d a b) m7  0xf6bb4b60 16
  b := step b c (fH c d a) m10 0xbebfbc70 23
  a := step a b (fH b c d) m13 0x289b7ec6 4
  d := step d a (fH a b c) m0  0xeaa127fa 11
  c := step c d (fH d a b) m3  0xd4ef3085 16
  b := step b c (fH c d a) m6  0x04881d05 23
  a := step a b (fH b c d) m9  0xd9d4d039 4
  d := step d a (fH a b c) m12 0xe6db99e5 11
  c := step c d (fH d a b) m15 0x1fa27cf8 16
  b := step b c (fH c d a) m2  0xc4ac5665 23
  -- Round 4.
  a := step a b (fI b c d) m0  0xf4292244 6
  d := step d a (fI a b c) m7  0x432aff97 10
  c := step c d (fI d a b) m14 0xab9423a7 15
  b := step b c (fI c d a) m5  0xfc93a039 21
  a := step a b (fI b c d) m12 0x655b59c3 6
  d := step d a (fI a b c) m3  0x8f0ccc92 10
  c := step c d (fI d a b) m10 0xffeff47d 15
  b := step b c (fI c d a) m1  0x85845dd1 21
  a := step a b (fI b c d) m8  0x6fa87e4f 6
  d := step d a (fI a b c) m15 0xfe2ce6e0 10
  c := step c d (fI d a b) m6  0xa3014314 15
  b := step b c (fI c d a) m13 0x4e0811a1 21
  a := step a b (fI b c d) m4  0xf7537e82 6
  d := step d a (fI a b c) m11 0xbd3af235 10
  c := step c d (fI d a b) m2  0x2ad7d2bb 15
  b := step b c (fI c d a) m9  0xeb86d391 21
  return (a0 + a, b0 + b, c0 + c, d0 + d)

/-- RFC 1321 §3.4 padding, but only for the final partial block. The result
    is one or two blocks (64 or 128 bytes), never a copy of the full input. -/
private def finalBlocks (msg : ByteArray) (fullBytes : Nat) : ByteArray := Id.run do
  let rem := msg.size - fullBytes
  let tailSize := if rem < 56 then 64 else 128
  let mut tail := ByteArray.emptyWithCapacity tailSize
  for i in [fullBytes : msg.size] do
    tail := tail.push msg[i]!
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
def md5 (msg : ByteArray) : ByteArray := Id.run do
  let mut st : UInt32 × UInt32 × UInt32 × UInt32 :=
    (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)
  let fullBlocks := msg.size / 64
  for h : b in [0 : fullBlocks] do
    have hb : 64 * b + 64 ≤ msg.size := by
      have hdiv : fullBlocks * 64 ≤ msg.size :=
        Nat.div_mul_le_self msg.size 64
      have hlt : b < fullBlocks := h.2.1
      omega
    st := compress st msg (64 * b) hb
  let tail := finalBlocks msg (64 * fullBlocks)
  let tailBlocks := tail.size / 64
  for h : b in [0 : tailBlocks] do
    have hb : 64 * b + 64 ≤ tail.size := by
      have hdiv : tailBlocks * 64 ≤ tail.size :=
        Nat.div_mul_le_self tail.size 64
      have hlt : b < tailBlocks := h.2.1
      omega
    st := compress st tail (64 * b) hb
  let (a, b, c, d) := st
  return ⟨(wordLE a ++ wordLE b ++ wordLE c ++ wordLE d).toArray⟩

/-- Digest as a lowercase hex string (for tests and diagnostics). -/
def md5Hex (msg : ByteArray) : String :=
  let hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!
  String.ofList <| (md5 msg).toList.flatMap fun b =>
    [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

end Flac.Md5
