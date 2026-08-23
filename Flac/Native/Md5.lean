/-!
# MD5 (RFC 1321)

Pure-Lean MD5 for the STREAMINFO checksum of the unencoded PCM
(RFC 9639 §8.2). Tested, not verified: it is a conformance checksum, not part of the
losslessness claim. Validated against the RFC 1321 test suite in `FlacTest`.

Encoder-side only (the decoder does not verify MD5 in v1), so `!`-indexing
into arrays whose sizes are fixed by construction is acceptable here.
-/

namespace Flac.Md5

/-- Per-round left-rotation amounts. -/
private def shifts : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- Sine-derived constants: `K[i] = ⌊|sin(i+1)| · 2^32⌋`. -/
private def K : Array UInt32 := #[
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
    0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
    0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
    0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
    0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
    0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
    0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
    0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
    0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

private def rotl (x : UInt32) (s : UInt32) : UInt32 :=
  (x <<< s) ||| (x >>> (32 - s))

/-- RFC 1321 §3.4 padding: a 0x80 byte, zeros to 56 mod 64, then the
    original bit length as a 64-bit little-endian integer. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let mut out := msg
  out := out.push 0x80
  let zeros := (56 + 64 - (msg.size + 1) % 64) % 64
  out := out ++ ByteArray.mk (Array.replicate zeros 0x00)
  for i in [0:8] do
    out := out.push (UInt8.ofNat ((bitLen >>> (8 * UInt64.ofNat i)).toNat % 256))
  return out

/-- Decode 16 little-endian 32-bit words from `msg` starting at `base`. -/
private def block (msg : ByteArray) (base : Nat) : Array UInt32 := Id.run do
  let mut m : Array UInt32 := Array.mkEmpty 16
  for j in [0:16] do
    let o := base + 4 * j
    m := m.push <| msg[o]!.toUInt32 ||| (msg[o+1]!.toUInt32 <<< 8)
      ||| (msg[o+2]!.toUInt32 <<< 16) ||| (msg[o+3]!.toUInt32 <<< 24)
  return m

private def compress (st : UInt32 × UInt32 × UInt32 × UInt32) (m : Array UInt32) :
    UInt32 × UInt32 × UInt32 × UInt32 := Id.run do
  let (a0, b0, c0, d0) := st
  let mut a := a0
  let mut b := b0
  let mut c := c0
  let mut d := d0
  for i in [0:64] do
    let (f, g) :=
      if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
      else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
      else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (b ||| ~~~d), (7 * i) % 16)
    let tmp := d
    d := c
    c := b
    b := b + rotl (a + f + K[i]! + m[g]!) shifts[i]!
    a := tmp
  return (a0 + a, b0 + b, c0 + c, d0 + d)

private def wordLE (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- The 16-byte MD5 digest of `msg`. -/
def md5 (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st : UInt32 × UInt32 × UInt32 × UInt32 :=
    (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)
  for b in [0:padded.size / 64] do
    st := compress st (block padded (64 * b))
  let (a, b, c, d) := st
  return ⟨(wordLE a ++ wordLE b ++ wordLE c ++ wordLE d).toArray⟩

/-- Digest as a lowercase hex string (for tests and diagnostics). -/
def md5Hex (msg : ByteArray) : String :=
  let hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!
  String.ofList <| (md5 msg).toList.flatMap fun b =>
    [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

end Flac.Md5
