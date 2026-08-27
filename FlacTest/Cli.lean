import Flac
import Flac.Native.Decode

/-!
# Unit tests

Golden vectors for CRC-8/CRC-16, MD5 (the RFC 1321 test suite), coded
numbers (incl. the RFC 9639 §9.1.5 worked example), and executable
spot-checks of the bit-level round-trips (belt and braces on top of the
theorems in `Flac/Spec/`).
-/

open Flac

def strBytes (s : String) : ByteArray := s.toUTF8

structure TestState where
  failures : Nat := 0
  count : Nat := 0

abbrev TestM := StateT TestState IO

def check (name : String) (cond : Bool) : TestM Unit := do
  modify fun st => { st with count := st.count + 1 }
  unless cond do
    modify fun st => { st with failures := st.failures + 1 }
    IO.println s!"FAIL: {name}"

def checkEq [BEq α] [ToString α] (name : String) (got expected : α) : TestM Unit := do
  modify fun st => { st with count := st.count + 1 }
  unless got == expected do
    modify fun st => { st with failures := st.failures + 1 }
    IO.println s!"FAIL: {name}\n  expected {expected}\n  got      {got}"

/-! ## CRC vectors (poly 0x07 / 0x8005, init 0, MSB-first, unreflected) -/

def crcTests : TestM Unit := do
  checkEq "crc8 empty" (Crc.crc8 (strBytes "")) 0x00
  checkEq "crc8 check-string" (Crc.crc8 (strBytes "123456789")) 0xF4
  checkEq "crc8 fLaC" (Crc.crc8 (strBytes "fLaC")) 0x73
  checkEq "crc16 empty" (Crc.crc16 (strBytes "")) 0x0000
  checkEq "crc16 check-string" (Crc.crc16 (strBytes "123456789")) 0xFEE8
  checkEq "crc16 fLaC" (Crc.crc16 (strBytes "fLaC")) 0x3A6D
  -- the table-driven byte updates agree with the shift-register definition
  -- (crc8: exhaustive over the full state × byte space)
  check "crc8 table = bitwise (exhaustive)" ((List.range 256).all fun c =>
    (List.range 256).all fun b =>
      Crc.crc8Update (UInt8.ofNat c) (UInt8.ofNat b)
        == Crc.crc8UpdateBitwise (UInt8.ofNat c) (UInt8.ofNat b))
  -- (crc16: every byte against a 256-state sample covering both halves)
  check "crc16 table = bitwise (sampled states)" ((List.range 256).all fun s =>
    let c := UInt16.ofNat (s * 40503 + s)   -- spreads over all 16 bits
    (List.range 256).all fun b =>
      Crc.crc16Update c (UInt8.ofNat b)
        == Crc.crc16UpdateBitwise c (UInt8.ofNat b))

/-! ## MD5 — the full RFC 1321 §A.5 test suite -/

def md5Tests : TestM Unit := do
  let vectors : List (String × String) := [
    ("", "d41d8cd98f00b204e9800998ecf8427e"),
    ("a", "0cc175b9c0f1b6a831c399e269772661"),
    ("abc", "900150983cd24fb0d6963f7d28e17f72"),
    ("message digest", "f96b697d7cb7938d525a2f31aaf161d0"),
    ("abcdefghijklmnopqrstuvwxyz", "c3fcd3d76192e4007dfb496cca67e13b"),
    ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
     "d174ab98d277d9f5a5611c2c9f419d9f"),
    ("12345678901234567890123456789012345678901234567890123456789012345678901234567890",
     "57edf4a22be3c955ac49da2e2107b67a")]
  for (msg, expected) in vectors do
    checkEq s!"md5 {repr msg}" (Md5.md5Hex (strBytes msg)) expected
  -- exercise both sides of the 56-byte padding boundary
  checkEq "md5 55×'x'" (Md5.md5Hex (strBytes (String.ofList (List.replicate 55 'x'))))
    "04364420e25c512fd958a70738aa8f72"
  checkEq "md5 56×'x'" (Md5.md5Hex (strBytes (String.ofList (List.replicate 56 'x'))))
    "668a72d5ba17f08e62dabcafad6db14b"
  checkEq "md5 64×'x'" (Md5.md5Hex (strBytes (String.ofList (List.replicate 64 'x'))))
    "c1bb4f81d892b2d57947682aeb252456"

/-! ## Coded numbers -/

def utf8NumTests : TestM Unit := do
  -- RFC 9639 §9.1.5 worked example: 51 billion samples.
  checkEq "utf8num 51e9 bytes"
    ((Bits.bitsToBytes (Utf8Num.write 51000000000)).toList)
    [0xFE, 0xAF, 0x9F, 0xB5, 0xA3, 0xB8, 0x80]
  -- ASCII compatibility below 0x80.
  checkEq "utf8num 0x41 bytes" ((Bits.bitsToBytes (Utf8Num.write 0x41)).toList) [0x41]
  -- Executable round-trips at every length boundary.
  let boundaries : List Nat :=
    [0, 1, 0x7F, 0x80, 0x7FF, 0x800, 0xFFFF, 0x10000, 0x1FFFFF, 0x200000,
     0x3FFFFFF, 0x4000000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFFF]
  for n in boundaries do
    checkEq s!"utf8num roundtrip {n}" (Utf8Num.read (Utf8Num.write n)) (some (n, []))

/-! ## Rice coding and partitioned residuals -/

def riceTests : TestM Unit := do
  -- zigzag folding table (RFC 9639 §9.2.7.2)
  checkEq "zigzag table" ([0, -1, 1, -2, 2, -3].map Rice.zigzag) [0, 1, 2, 3, 4, 5]
  -- RFC worked example: parameter 3, folded value 38 ↦ 0b00001110
  checkEq "rice example 38/k=3" (Rice.writeRiceNat 3 38)
    [false, false, false, false, true, true, true, false]
  checkEq "riceNat roundtrip" (Rice.readRiceNat 5 (Rice.writeRiceNat 5 1234))
    (some (1234, []))
  checkEq "rice signed roundtrip" (Rice.readRice 2 (Rice.writeRice 2 (-37)))
    (some ((-37 : Int), []))
  -- signed fixed-width ints (escaped partitions / verbatim)
  for (n, x) in [(3, -1), (3, -4), (3, 3), (8, -128), (8, 127), (16, -32768)] do
    checkEq s!"sint roundtrip {n} {x}"
      (Bits.readSInt n (Bits.writeSInt n (x : Int))) (some ((x : Int), []))
  checkEq "sint -1 in 3 bits is 0b111" (Bits.writeSInt 3 (-1)) [true, true, true]
  -- a full coded residual: bs = 8, ord = 0, po = 1 (two partitions of 4),
  -- first Rice-coded with k = 2, second escaped at 4 bits
  let res : List Int := [0, -1, 3, -7, 2, -2, 7, -8]
  let cfg : Rice.ResidualCfg :=
    { method := .rice4, po := 1, choices := [.rice 2, .escape 4] }
  checkEq "residual roundtrip (rice+escape)"
    (Rice.readResidual 8 0 (Rice.writeResidual 8 0 cfg res)) (some (res, []))
  -- escaped partition with 0 bits: all-zero residuals cost nothing
  let zres : List Int := [0, 0, 0, 0]
  let zcfg : Rice.ResidualCfg := { method := .rice5, po := 0, choices := [.escape 0] }
  let zbits := Rice.writeResidual 4 0 zcfg zres
  checkEq "residual roundtrip (escape 0 bits)"
    (Rice.readResidual 4 0 zbits) (some (zres, []))
  checkEq "escape-0 partition is header-only" zbits.length (2 + 4 + 5 + 5)
  -- predictor order eats into the first partition: bs = 8, ord = 2, po = 1
  let pres : List Int := [5, -5, 1, 0, -1, 2]
  let pcfg : Rice.ResidualCfg := { method := .rice4, po := 1, choices := [.rice 1, .rice 3] }
  checkEq "residual roundtrip (ord=2)"
    (Rice.readResidual 8 2 (Rice.writeResidual 8 2 pcfg pres)) (some (pres, []))

/-! ## End-to-end: encode → decodeReference -/

/-- A mono test chooser exercising CONSTANT and FIXED subframes. -/
def testSubCfg (blk : List Int) : Subframe.SubCfg :=
  if blk.all (· == blk.headD 0) then ⟨0, .constant⟩
  else if 2 < blk.length then
    ⟨0, .fixed 2 { method := .rice4, po := 0, choices := [.rice 4] }⟩
  else ⟨0, .verbatim⟩

/-- Lift a per-block subframe chooser to a channel assignment. -/
def indep (f : List Int → Subframe.SubCfg) : List (List Int) → Frame.ChannelAsg :=
  fun fr => .independent (fr.map f)

def e2eTests : TestM Unit := do
  let mono (bs : Nat) (chooser : List (List Int) → Frame.ChannelAsg)
      (pcm : List Int) : Option (List (List Int)) :=
    (Stream.decodeReference
      (Stream.encode ⟨bs, false, chooser⟩ ⟨[pcm], 16, 44100⟩)).map (·.channels)
  -- 40 samples → frames of 16/16/8 (short last frame)
  let pcm : List Int := (List.range 40).map fun (i : Nat) =>
    (100 * (i : Int)) - 2000 + (if i % 3 == 0 then 7 else -5)
  checkEq "e2e verbatim 40 samples"
    (mono 16 Stream.verbatimChooser pcm) (some [pcm])
  checkEq "e2e fixed/constant 40 samples"
    (mono 16 (indep testSubCfg) pcm) (some [pcm])
  -- constant blocks
  let flat : List Int := List.replicate 48 (-12345)
  checkEq "e2e constant blocks" (mono 16 (indep testSubCfg) flat) (some [flat])
  -- empty stream (zero frames)
  checkEq "e2e empty pcm"
    (mono 16 Stream.verbatimChooser []) (some [[]])
  -- extreme 16-bit values
  let extremes : List Int := [32767, -32768, 0, -1, 1] ++ List.replicate 20 32767
  checkEq "e2e extreme values"
    (mono 16 Stream.verbatimChooser extremes) (some [extremes])
  -- 8-bit depth
  let pcm8 : List Int := (List.range 30).map fun (i : Nat) => ((i : Int) % 100) - 50
  checkEq "e2e 8-bit"
    ((Stream.decodeReference (Stream.encode ⟨16, false, Stream.verbatimChooser⟩
      ⟨[pcm8], 8, 8000⟩)).map (·.channels)) (some [pcm8])
  -- the certified default heuristics (wasted bits, LPC, fixed, stereo)
  checkEq "e2e defaultAsgChooser mono"
    (mono 16 (Heuristics.defaultAsgChooser 16) pcm) (some [pcm])
  checkEq "e2e defaultAsgChooser constant" (mono 16 (Heuristics.defaultAsgChooser 16) flat)
    (some [flat])
  -- wasted bits: all samples share 3 low zero bits
  let wpcm : List Int := (List.range 40).map fun (i : Nat) => ((i : Int) - 20) * 8
  checkEq "e2e wasted bits" (mono 16 (Heuristics.defaultAsgChooser 16) wpcm)
    (some [wpcm])
  checkEq "wastedDetect finds 3" (Heuristics.wastedDetect 16 wpcm) 3
  -- stereo: correlated channels (side should win), all four modes decode
  let left : List Int := (List.range 40).map fun (i : Nat) => 500 * (i : Int) - 9000
  let right : List Int := left.map (· + 37)
  let stereo (chooser : List (List Int) → Frame.ChannelAsg) :=
    (Stream.decodeReference (Stream.encode ⟨16, false, chooser⟩
      ⟨[left, right], 16, 44100⟩)).map (·.channels)
  checkEq "e2e stereo default" (stereo (Heuristics.defaultAsgChooser 16))
    (some [left, right])
  checkEq "e2e stereo leftSide"
    (stereo fun _ => .leftSide ⟨0, .verbatim⟩ ⟨0, .verbatim⟩) (some [left, right])
  checkEq "e2e stereo rightSide"
    (stereo fun _ => .rightSide ⟨0, .verbatim⟩ ⟨0, .verbatim⟩) (some [left, right])
  checkEq "e2e stereo midSide"
    (stereo fun _ => .midSide ⟨0, .verbatim⟩ ⟨0, .verbatim⟩) (some [left, right])
  -- 5 channels, independent
  let chans : List (List Int) := (List.range 5).map fun (c : Nat) =>
    (List.range 33).map fun (i : Nat) => ((c : Int) + 1) * ((i : Int) - 16)
  checkEq "e2e 5 channels"
    ((Stream.decodeReference (Stream.encode ⟨16, false, Heuristics.defaultAsgChooser 16⟩
      ⟨chans, 16, 44100⟩)).map (·.channels)) (some chans)
  -- variable-blocksize numbering strategy
  checkEq "e2e variable numbering"
    ((Stream.decodeReference (Stream.encode ⟨16, true, Heuristics.defaultAsgChooser 16⟩
      ⟨[pcm], 16, 44100⟩)).map (·.channels)) (some [pcm])

/-! ## The fast encoder mirrors the verified one, byte for byte

`Flac.Encode` runs its candidate searches in exact `Float` arithmetic over
unboxed `FloatArray`, `Flac.Heuristics` runs them in `Int` over lists.
Every value involved is an integer well inside `2^53`, so the two must
*choose the same subframes* and emit identical bytes.

That much is still not a theorem, and cannot be: it is a claim about what
`Float` computes. `Flac.Encode.encodePcm16_eq` proves the fast encoder
computes `Stream.encode` at the chooser its *own* search denotes, which
needs no such claim; whether that search agrees with the `Int` one is a
compression question, and it is pinned here as a test. -/

def fastMirrorTests : TestM Unit := do
  let mkPcm (f : Nat → Int) (n : Nat) : ByteArray :=
    Stream.pcmBytes 16 [(List.range n).map f]
  let mkPcm2 (f g : Nat → Int) (n : Nat) : ByteArray :=
    Stream.pcmBytes 16 [(List.range n).map f, (List.range n).map g]
  let cmp (name : String) (ch : Nat) (bytes : ByteArray) : TestM Unit := do
    let fast := Flac.Encode.encodePcm16 4096 ch 44100 bytes
    let slow := Flac.encodePcm16Cfg ⟨4096, false, Heuristics.defaultAsgChooser 16⟩
      ch 44100 bytes
    checkEq s!"fast mirrors verified encoder: {name}" (some fast) slow
  -- LPC territory (smooth, high order pays), FIXED territory (ramps),
  -- noise (verbatim/high Rice parameters), wasted bits, constant blocks
  cmp "sine" 1 (mkPcm (fun i => (9000.0 * Float.sin (Float.ofNat i * 0.01)).toInt64.toInt) 9000)
  cmp "chord" 1 (mkPcm (fun i =>
    (4000.0 * Float.sin (Float.ofNat i * 0.037)
      + 3000.0 * Float.sin (Float.ofNat i * 0.0047)).toInt64.toInt) 9000)
  cmp "ramp" 1 (mkPcm (fun i => ((i % 512 : Nat) : Int) * 60 - 15000) 9000)
  cmp "noise" 1 (mkPcm (fun i =>
    (((i * i * 2654435761 + i * 40503) % 65536 : Nat) : Int) - 32768) 9000)
  cmp "wasted3" 1 (mkPcm (fun i =>
    ((((i * 2654435761) % 8192 : Nat) : Int) - 4096) * 8) 9000)
  cmp "constant" 1 (mkPcm (fun _ => 4321) 9000)
  cmp "quiet" 1 (mkPcm (fun i => ((i % 7 : Nat) : Int) - 3) 9000)
  cmp "stereo" 2 (mkPcm2
    (fun i => (9000.0 * Float.sin (Float.ofNat i * 0.01)).toInt64.toInt)
    (fun i => (9000.0 * Float.sin (Float.ofNat i * 0.01)).toInt64.toInt / 8 + 77) 9000)

/-! ## The fused byte decoder engages, and agrees with the sample path

`Flac.Stream.decodeBytes_spec` says a `some` result is the right bytes. It
does *not* say the fused path ever returns `some` — a bug that made it
always decline would keep the CLI correct (it falls back) while silently
giving up the parallel serialization. These checks pin that it engages on
real streams, and that its bytes match the fallback's. -/

def fusedDecodeTests : TestM Unit := do
  let cases : List (String × Nat × List (List Int)) :=
    [("mono sine", 1, [(List.range 9000).map fun i =>
        (9000.0 * Float.sin (Float.ofNat i * 0.01)).toInt64.toInt]),
     ("mono noise", 1, [(List.range 9000).map fun i =>
        (((i * i * 2654435761 + i * 40503) % 65536 : Nat) : Int) - 32768]),
     ("mono constant", 1, [List.replicate 9000 (4321 : Int)]),
     ("stereo", 2, [(List.range 9000).map fun i =>
        (9000.0 * Float.sin (Float.ofNat i * 0.01)).toInt64.toInt,
       (List.range 9000).map fun i =>
        (9000.0 * Float.sin (Float.ofNat i * 0.01)).toInt64.toInt / 8 + 77]),
     ("short last frame", 1, [(List.range 5000).map fun i => ((i % 700 : Nat) : Int) - 350]),
     ("empty", 1, [[]])]
  for (name, ch, chans) in cases do
    let flac := Stream.encode ⟨4096, false, Heuristics.defaultAsgChooser 16⟩ ⟨chans, 16, 44100⟩
    match Flac.Decode.decodeBytes flac, Flac.Decode.decodeArrays flac with
    | some (pcm, _), some (arrs, bps, _) =>
      checkEq s!"fused decode = sample path: {name}" pcm
        (Stream.pcmBytesRange bps arrs 0 (arrs.headD #[]).size)
      checkEq s!"fused decode = original PCM: {name}" pcm (Stream.pcmBytes 16 chans)
    | none, _ => check s!"fused decode engages: {name}" false
    | _, none => check s!"sample path decodes: {name}" false
  -- the parallel branch is only taken above `parThreshold`, so exercise a
  -- stream large enough to cross it
  let big : List Int := (List.range 200000).map fun i =>
    (((i * i * 2654435761 + i * 40503) % 65536 : Nat) : Int) - 32768
  let bigFlac := Stream.encode ⟨4096, false, Heuristics.defaultAsgChooser 16⟩ ⟨[big], 16, 44100⟩
  check "fused decode crosses the parallel threshold"
    (Flac.Decode.parThreshold ≤ bigFlac.size)
  checkEq "fused decode = original PCM: 200k samples"
    (Flac.Decode.decodeBytes bigFlac) (some (Stream.pcmBytes 16 [big], 16))

/-! ## Interleaved PCM bytes at every bit depth

`Stream.pcmBytesRange` is deliberately outside every theorem
(`pcmBytesA_eq` cancels only the array/list conversion, and MD5 is a
conformance checksum, not part of the losslessness claim), so its
little-endian two's-complement arithmetic — which runs through the
`UInt64` lane — is pinned here instead. -/

def pcmBytesTests : TestM Unit := do
  let bytesOf (b : Nat) (chs : List (List Int)) : List UInt8 :=
    (Stream.pcmBytes b chs).toList
  -- 16-bit mono: sign boundary, extremes, zero
  checkEq "pcmBytes 16-bit mono"
    (bytesOf 16 [[0, 1, -1, 32767, -32768, 258]])
    [0x00, 0x00, 0x01, 0x00, 0xFF, 0xFF, 0xFF, 0x7F, 0x00, 0x80, 0x02, 0x01]
  -- 16-bit stereo interleaves sample-major
  checkEq "pcmBytes 16-bit stereo"
    (bytesOf 16 [[1, -1], [-2, 2]])
    [0x01, 0x00, 0xFE, 0xFF, 0xFF, 0xFF, 0x02, 0x00]
  -- 8-bit
  checkEq "pcmBytes 8-bit" (bytesOf 8 [[0, 1, -1, 127, -128]])
    [0x00, 0x01, 0xFF, 0x7F, 0x80]
  -- 24-bit (three bytes, little-endian)
  checkEq "pcmBytes 24-bit" (bytesOf 24 [[0, 1, -1, 8388607, -8388608]])
    [0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0xFF, 0xFF, 0xFF,
     0xFF, 0xFF, 0x7F, 0x00, 0x00, 0x80]
  -- three channels, 16-bit
  checkEq "pcmBytes 3 channels" (bytesOf 16 [[1], [2], [-1]])
    [0x01, 0x00, 0x02, 0x00, 0xFF, 0xFF]
  -- the windowed (parallel) path agrees with the single-window path
  let long : List Int := (List.range 200000).map fun i => ((i % 65536 : Nat) : Int) - 32768
  checkEq "pcmBytes windows agree" (Stream.pcmBytes 16 [long])
    (Stream.pcmBytesRange 16 [long.toArray] 0 long.length)
  -- and matches the verified byte-level serializer on the same samples
  checkEq "pcmBytes = pcm16Fast (16-bit)"
    (Stream.pcmBytes 16 [[0, 1, -1, 32767, -32768], [5, -5, 0, 1, -1]])
    (Flac.pcm16Fast [[0, 1, -1, 32767, -32768], [5, -5, 0, 1, -1]])

/-! ## Bit-level spot checks -/

def bitsTests : TestM Unit := do
  checkEq "writeBits 8 0xA5" (Bits.writeBits 8 0xA5)
    [true, false, true, false, false, true, false, true]
  checkEq "readBits inverts writeBits" (Bits.readBits 12 (Bits.writeBits 12 0xABC)) (some (0xABC, []))
  checkEq "unary roundtrip 5" (Bits.readUnary (Bits.writeUnary 5)) (some (5, []))
  checkEq "unary encoding 3" (Bits.writeUnary 3) [false, false, false, true]
  checkEq "pack/unpack" (Bits.bytesToBits (Bits.bitsToBytes (Bits.byteToBits 0x5A ++ Bits.byteToBits 0xFF)))
    (Bits.byteToBits 0x5A ++ Bits.byteToBits 0xFF)
  checkEq "align pads to byte" (Bits.alignToByte [true, true, false]).length 8
  checkEq "align keeps aligned" (Bits.alignToByte (Bits.byteToBits 1)).length 8

/-! ## Two's-complement wrap — the anti-divergence bound on predictor
    restore (P1 audit finding, issue #1) -/

def wrapTests : TestM Unit := do
  -- identity in range, two's-complement wrap out of range
  checkEq "wrapSInt id in range" (Bits.wrapSInt 16 32767) 32767
  checkEq "wrapSInt id at low end" (Bits.wrapSInt 16 (-32768)) (-32768)
  checkEq "wrapSInt wraps high" (Bits.wrapSInt 16 32768) (-32768)
  checkEq "wrapSInt wraps low" (Bits.wrapSInt 16 (-32769)) 32767
  checkEq "wrapSInt residue class" (Bits.wrapSInt 4 100) 4
  checkEq "wrapSInt width 0" (Bits.wrapSInt 0 (-7)) 0
  -- P1 regression: an order-1 predictor with coefficient 2^14-1 and
  -- shift 0 diverges as 16383^n in exact ℤ; the in-loop wrap must keep
  -- every reconstructed sample inside the 16-bit range instead (4096
  -- samples previously built multi-GB bignums and aborted in GMP)
  let out := Lpc.restoreA 16 [16383] 0 [1] (Array.replicate 4096 0)
  check "LPC divergence stays 16-bit bounded"
    (out.all fun x => -32768 ≤ x && x < 32768)
  checkEq "LPC divergence output size" out.size 4097
  -- the fixed-predictor restore wraps its output the same way
  check "fixed order-0 restore wraps to 8-bit"
    ((Fixed.restoreA 8 0 [] #[300, -300]).all fun x => -128 ≤ x && x < 128)

def bombTests : TestM Unit := do
  -- P2 regression: a conformant all-CONSTANT stream (eight channels of
  -- silence at block size 65535) amplifies ~50 input bytes into ~1 MB of
  -- output per frame. `Stream.encode` is total, so it writes such a
  -- stream happily; every decoder entry point must reject it against
  -- `Stream.decodeBudget` instead of materializing it.
  let silence8 : List (List Int) := List.replicate 8 (List.replicate 65535 0)
  let bomb := Stream.encode ⟨65535, false, Heuristics.defaultAsgChooser 16⟩
    ⟨silence8, 16, 44100⟩
  check "P2 bomb: reference decoder rejects"
    (Stream.decodeReference bomb).isNone
  check "P2 bomb: production decoder rejects"
    (match Flac.decode bomb with | .error _ => true | .ok _ => false)
  check "P2 bomb: fused byte decoder rejects"
    (Flac.Decode.decodeBytes bomb).isNone
  -- silence at the default block size is legitimately high-amplification
  -- (~1600×) and must keep decoding: the budget admits everything the
  -- guarded encoder can emit (`Flac.Spec.Stream.encode_cost_le_budget`)
  let silence : List (List Int) := List.replicate 8 (List.replicate 20000 0)
  let ok := Stream.encode ⟨4096, false, Heuristics.defaultAsgChooser 16⟩
    ⟨silence, 16, 44100⟩
  check "silence at default block size still decodes"
    (match Flac.decode ok with
     | .ok a => a.channels == silence
     | .error _ => false)
  -- the block-size guard is exactly where the budget proof stops
  let pcm : ByteArray := ByteArray.mk (Array.replicate 4000 0)
  check "fast encoder accepts block size 4608"
    (Flac.encodePcm16Fast 4608 2 44100 pcm).isSome
  check "fast encoder rejects block size 4609"
    (Flac.encodePcm16Fast 4609 2 44100 pcm).isNone
  -- P3 regression: STREAMINFO's totalSamples reaches the decoder only as
  -- a capacity hint, capped by `outCapacity` against the input size.
  -- Setting the 36-bit field to all-ones (file bytes 21–25: layout is 108
  -- header bits before it) must change nothing about the decode — and
  -- must not reserve ~1.1 TB, which is what this test used to request.
  let lying := ByteArray.mk <| ok.data.mapIdx fun i b =>
    if i = 21 then b ||| 0x0F
    else if 22 ≤ i ∧ i ≤ 25 then 0xFF
    else b
  check "P3: lying totalSamples decodes identically (byte path)"
    (Flac.Decode.decodeBytes lying == Flac.Decode.decodeBytes ok
      && (Flac.Decode.decodeBytes ok).isSome)
  check "P3: lying totalSamples decodes identically (sample path)"
    (match Flac.decode lying with
     | .ok a => a.channels == silence
     | .error _ => false)
  -- the audit's 42-byte shape: header only, no frames, maximal claim
  let frameless := lying.extract 0 42
  check "P3: frameless maximal-claim file decodes to empty"
    ((Flac.Decode.decodeBytes frameless).map (·.1.size) == some 0)
  -- P4 regression: a run of FF F8 pairs makes every second offset a sync
  -- candidate (density 1/2). The scan must not gather candidates or spawn
  -- tasks in proportion to that pattern; `syncCandidates` recognizes the
  -- impossible density and hands back nothing, so the frame loop rejects
  -- serially in O(1). Header (fLaC + STREAMINFO, last-block set) taken
  -- from the encoder, then 100 000 FF F8 pairs (~200 KB) appended.
  let header := ok.extract 0 42
  let stormTail : ByteArray := ByteArray.mk <|
    (List.range 200000).map (fun i => if i % 2 == 0 then (0xFF : UInt8) else 0xF8)
      |>.toArray
  let storm := header ++ stormTail
  check "P4: sync-storm yields no candidates (density bail)"
    ((Flac.Decode.syncCandidates storm 42).size == 0)
  check "P4: sync-storm rejected by the byte decoder"
    (Flac.Decode.decodeBytes storm).isNone
  check "P4: sync-storm rejected by the production decoder"
    (match Flac.decode storm with | .error _ => true | .ok _ => false)
  -- honest audio sits far below the density threshold, so speculation is
  -- kept (a nonempty candidate set) — the parallel path is not lost
  check "P4: honest stream keeps its sync candidates"
    (Flac.Decode.minFrameBytes * (Flac.Decode.syncCandidates ok 42).size < ok.size)
  -- the task count is bounded by input size, never by candidate density:
  -- however many candidates, the fan-out spawns at most `maxStepTasks`
  let n := 10 * Flac.Decode.maxStepTasks * Flac.Decode.stepChunkSize
  let chunk := Flac.Decode.stepChunkFor n
  check "P4: task count capped regardless of candidate count"
    ((n + chunk - 1) / chunk ≤ Flac.Decode.maxStepTasks)
  -- P5 regression, part one — the accept-set. RFC 9639 §9.2.2 requires the
  -- wasted count `w` to leave a positive subframe depth, and §5 lists a
  -- zero-or-negative resulting depth among the streams a decoder must
  -- refuse. `Nat` subtraction saturates, so `b - w` used to be 0 and the
  -- subframe decoded at depth 0 instead of being rejected. The writers are
  -- total and emit the invalid subframe happily; every reader must refuse.
  let p5 (w : Nat) : ByteArray :=
    Bits.bitsToBytes <|
      Bits.writeBits 32 0x664C6143 ++
      Bits.writeBits 1 1 ++ Bits.writeBits 7 0 ++ Bits.writeBits 24 34 ++
      Stream.writeStreamInfo 4096 44100 1 16 4096 0 ++
      Frame.write 16 false 0 (.independent [⟨w, .constant⟩])
        [List.replicate 4096 0]
  check "P5: wasted = depth rejected (reference decoder)"
    (Stream.decodeReference (p5 16)).isNone
  check "P5: wasted = depth rejected (production decoder)"
    (match Flac.decode (p5 16) with | .error _ => true | .ok _ => false)
  check "P5: wasted = depth rejected (fused byte decoder)"
    (Flac.Decode.decodeBytes (p5 16)).isNone
  -- `w = b - 1` is the largest count the RFC allows, and the largest the
  -- encoder's own `SubCfg.Valid` certificate permits: it must still decode
  check "P5: wasted = depth - 1 still decodes"
    (match Flac.decode (p5 15) with
     | .ok a => a.channels == [List.replicate 4096 0]
     | .error _ => false)
  -- P5 regression, part two — the cost of *reading* the count. The unary
  -- run has no enclosing bound (unlike a Rice residual's), so it is read
  -- with a cap (`readUnaryUpTo b`). A megabit run must be refused in O(b);
  -- before the cap it recursed once per zero bit in `Bits.readUnary` and
  -- overflowed the stack on the reference path.
  let longRun : BitStream :=
    Bits.writeBits 1 0 ++ Bits.writeBits 6 0 ++ Bits.writeBits 1 1 ++
      List.replicate 1000000 false ++ [true]
  check "P5: megabit wasted run refused by the model reader"
    (Subframe.read 4096 16 longRun).isNone
  check "P5: megabit wasted run refused by the production reader"
    (Flac.Decode.readSubframe 4096 16
      ⟨Bits.bitsToBytes (Bits.alignToByte longRun), 0⟩).isNone

/-! ## Encoder shape guards (audit findings P8 and P11)

Both byte-level encoders now run the shared O(1) `Pcm16ShapeOk` guard
before anything sized by its arguments exists. These pin the two incidents:
a channel count whose only rejection used to come from `Audio.WellFormed`,
checked *after* `ch` channel lists were materialized (P8 — the first check
below used to OOM), and `sampleRate = 0` stamped on nonempty audio, which
RFC 9639 §8.2 forbids (P11). -/

def encoderGuardTests : TestM Unit := do
  let cfg : Stream.EncoderCfg := ⟨4096, false, Heuristics.defaultAsgChooser 16⟩
  -- P8: empty input satisfies the divisibility guard for every `ch`, so
  -- `ch ≤ 8` must be part of the same O(1) conjunction
  check "P8: huge channels + empty input refused (slow)"
    (Flac.encodePcm16Cfg cfg 4000000000 44100 ByteArray.empty).isNone
  check "P8: huge channels + empty input refused (fast)"
    (Flac.encodePcm16Fast 4096 4000000000 44100 ByteArray.empty).isNone
  check "P8: nine channels refused (slow)"
    (Flac.encodePcm16Cfg cfg 9 44100 (ByteArray.mk (Array.replicate 18 0))).isNone
  check "P8: eight channels accepted (slow)"
    (Flac.encodePcm16Cfg cfg 8 44100 (ByteArray.mk (Array.replicate 16 0))).isSome
  -- P11: rate 0 is defensible only for empty content
  let audio := ByteArray.mk (Array.replicate 4000 0)
  check "P11: rate 0 with audio refused (fast)"
    (Flac.encodePcm16Fast 4096 1 0 audio).isNone
  check "P11: rate 0 with audio refused (slow)"
    (Flac.encodePcm16Cfg cfg 1 0 audio).isNone
  check "P11: rate 0 with empty input still encodes (fast)"
    (Flac.encodePcm16Fast 4096 1 0 ByteArray.empty).isSome
  check "P11: rate 1 with audio encodes (fast)"
    (Flac.encodePcm16Fast 4096 1 1 audio).isSome

/-- With an argument, write sample encoded streams into that directory
    (for differential testing against `flac`/`ffmpeg` from the shell). -/
def emitSamples (dir : String) : IO Unit := do
  let mk (name : String) (bs : Nat) (chooser : List (List Int) → Frame.ChannelAsg)
      (chans : List (List Int)) : IO Unit := do
    let a : Stream.Audio := ⟨chans, 16, 44100⟩
    IO.FS.writeBinFile s!"{dir}/{name}.flac" (Stream.encode ⟨bs, false, chooser⟩ a)
    -- raw PCM for byte-compare: interleaved signed little-endian
    IO.FS.writeBinFile s!"{dir}/{name}.pcm" (Stream.pcmBytes 16 chans)
  let sine : List Int := (List.range 4000).map fun (i : Nat) =>
    (8000 * Float.sin (Float.ofNat i * 0.05)).toInt64.toInt
  mk "sine-verbatim" 4096 Stream.verbatimChooser [sine]
  mk "sine-fixed" 4096 (indep testSubCfg) [sine]
  mk "wasted-bits" 4096 (Heuristics.defaultAsgChooser 16)
    [(List.range 3000).map fun (i : Nat) => (((i * i * 2654435761 + i * 40503) % 8192 : Nat) : Int) * 4 - 16384]
  mk "flat-constant" 4096 (indep testSubCfg) [List.replicate 10000 (1234 : Int)]
  mk "noise-small-blocks" 256 (Heuristics.defaultAsgChooser 16)
    [(List.range 5000).map fun (i : Nat) => ((i * i * 2654435761 + i * 40503) % 65536 : Int) - 32768]
  mk "empty" 4096 Stream.verbatimChooser [[]]
  -- stereo: correlated channels, default chooser picks a side mode
  let l : List Int := (List.range 4000).map fun (i : Nat) =>
    (9000 * Float.sin (Float.ofNat i * 0.02)).toInt64.toInt
  let r : List Int := l.map fun x => x - x / 8 + 100
  mk "stereo-corr" 4096 (Heuristics.defaultAsgChooser 16) [l, r]
  mk "stereo-ms" 4096 (fun _ => .midSide ⟨0, .verbatim⟩ ⟨0, .verbatim⟩) [l, r]

def usage : String :=
  "vinyl - a formally verified FLAC codec (see README.md)\n\n" ++
  "  vinyl --encode <in.pcm> <out.flac> <blockSize> <channels> [<sampleRate>]\n" ++
  "      encode raw interleaved signed 16-bit little-endian PCM\n" ++
  "      (fast encoder; proven to compute the reference encoder)\n" ++
  "      <sampleRate> only sets STREAMINFO and defaults to 44100\n" ++
  "  vinyl --encode-slow <in.pcm> <out.flac> <blockSize> <channels> [<sampleRate>]\n" ++
  "      encode with the fully verified encoder (the fast path's fallback)\n" ++
  "  vinyl --decode <in.flac> <out.pcm>\n" ++
  "      decode with the verified reference decoder (raw 16-bit LE out)\n" ++
  "  vinyl --decode-fast <in.flac> <out.pcm>\n" ++
  "      decode with the shipped buffered decoder (raw 16-bit LE out)\n" ++
  "  vinyl --decode-pcm16 <in.flac> <out.pcm>\n" ++
  "      decode via the verified byte-level pipeline (16-bit input only)\n" ++
  "  vinyl -j <n> <command...>   (also --threads <n>, --threads=<n>)\n" ++
  "      run <command...> with Lean's task pool capped at <n> workers,\n" ++
  "      the same knob `flac -j` turns; see the note on `withThreads`\n" ++
  "  vinyl --samples <dir>\n" ++
  "      write sample .flac/.pcm pairs into <dir> (must exist)\n" ++
  "  vinyl (no arguments)\n" ++
  "      run the unit-test suite"

/-- Run `args` in a copy of this process whose Lean task pool is capped at
    `n` workers, and return its exit code.

    Lean sizes the task pool from `LEAN_NUM_THREADS` when the runtime starts,
    which is before `main` is entered, so a flag cannot resize the pool of the
    process that parses it — hence the re-execution. The child never sees the
    flag again, so this recurses exactly once. It costs one extra process
    (~3 ms of Lean runtime init); `bench/real_run.py` sets the variable
    directly instead, so no benchmark pays it. -/
def withThreads (n : String) (args : List String) : IO UInt32 := do
  match n.toNat? with
  | none =>
    IO.eprintln s!"--threads: expected a worker count, got '{n}'"
    return 2
  | some workers =>
    if workers = 0 then
      IO.eprintln "--threads: worker count must be at least 1"
      return 2
    let self ← IO.appPath
    let child ← IO.Process.spawn
      { cmd := self.toString
        args := args.toArray
        env := #[("LEAN_NUM_THREADS", some (toString workers))] }
    child.wait

/-- Report a bad invocation: the message, then usage, exit 2. A typo in a
    numeric argument is a usage error, never a panic (audit finding P9,
    issue #9) — every argument is parsed with `toNat?` and funneled here
    on `none`. -/
def usageError (msg : String) : IO UInt32 := do
  IO.eprintln s!"{msg}\n"
  IO.eprintln usage
  return 2

/-- The fast encoder as a CLI action.  `sampleRate` reaches STREAMINFO only:
    `Flac.Stream.decodePcm16_encodePcm16Fast` holds at every rate the encoder
    accepts, so a 16 kHz corpus is encoded with honest metadata. -/
def encodeFastMain (inFile outFile : String) (blockSize ch sampleRate : Nat) :
    IO UInt32 := do
  let bytes ← IO.FS.readBinFile inFile
  -- the fast byte-level encoder, proven: whenever it returns
  -- bytes, `Flac.decodePcm16_encodePcm16Fast` guarantees decoding
  -- returns the input bytes exactly — no hypotheses
  match Flac.encodePcm16Fast blockSize ch sampleRate bytes with
  | some flacBytes =>
    IO.FS.writeBinFile outFile flacBytes
    IO.println s!"encoded {bytes.size / (2 * ch)} samples x {ch} channels @ {sampleRate} Hz (round-trip guaranteed by Flac.Stream.decodePcm16_encodePcm16Fast)"
    return 0
  | none =>
    IO.println "ENCODE ERROR: input not FLAC-representable (byte count not a multiple of 2x channels, channels/blockSize/sampleRate out of range, or sample rate 0 with nonempty audio)"
    return 1

/-- The fully verified encoder as a CLI action; kept for differential testing. -/
def encodeSlowMain (inFile outFile : String) (blockSize ch sampleRate : Nat) :
    IO UInt32 := do
  let bytes ← IO.FS.readBinFile inFile
  match Flac.encodePcm16Cfg ⟨blockSize, false, Heuristics.defaultAsgChooser 16⟩
      ch sampleRate bytes with
  | some flacBytes =>
    IO.FS.writeBinFile outFile flacBytes
    IO.println s!"encoded {bytes.size / (2 * ch)} samples x {ch} channels @ {sampleRate} Hz (checked: round-trip guaranteed by Flac.decodePcm16_encodePcm16Cfg)"
    return 0
  | none =>
    IO.println "ENCODE ERROR: input not FLAC-representable (byte count not a multiple of 2x channels, channels/blockSize/sampleRate out of range, or sample rate 0 with nonempty audio)"
    return 1

def cliMain (args : List String) : IO UInt32 := do
  -- the thread flag is leading and consumed here, so every branch below sees
  -- the command alone, exactly as if the flag had not been given
  match args with
  | "-j" :: n :: rest => return ← withThreads n rest
  | "--threads" :: n :: rest => return ← withThreads n rest
  | flag :: rest =>
    if flag.startsWith "--threads=" then
      return ← withThreads (flag.drop "--threads=".length).toString rest
  | [] => pure ()
  if args = ["--help"] ∨ args = ["-h"] then
    IO.println usage
    return 0
  if let ["--encode", inFile, outFile, bs, ch] := args then
    match bs.toNat?, ch.toNat? with
    | some bs, some ch => return ← encodeFastMain inFile outFile bs ch 44100
    | _, _ =>
      return ← usageError s!"--encode: blockSize and channels must be numbers, got '{bs}' '{ch}'"
  if let ["--encode", inFile, outFile, bs, ch, rate] := args then
    match bs.toNat?, ch.toNat?, rate.toNat? with
    | some bs, some ch, some rate => return ← encodeFastMain inFile outFile bs ch rate
    | _, _, _ =>
      return ← usageError s!"--encode: blockSize, channels and sampleRate must be numbers, got '{bs}' '{ch}' '{rate}'"
  if let ["--decode-pcm16", inFile, outFile] := args then
    let bytes ← IO.FS.readBinFile inFile
    -- `Flac.decodePcm16A_eq`: same bytes as `Flac.decodePcm16`, no list round-trip
    match Flac.decodePcm16A bytes with
    | .error e => IO.println s!"DECODE ERROR: {e}"; return 1
    | .ok pcm =>
      IO.FS.writeBinFile outFile pcm
      IO.println "decoded (byte-level pipeline)"
      return 0
  if let ["--encode-slow", inFile, outFile, bs, ch] := args then
    match bs.toNat?, ch.toNat? with
    | some bs, some ch => return ← encodeSlowMain inFile outFile bs ch 44100
    | _, _ =>
      return ← usageError s!"--encode-slow: blockSize and channels must be numbers, got '{bs}' '{ch}'"
  if let ["--encode-slow", inFile, outFile, bs, ch, rate] := args then
    match bs.toNat?, ch.toNat?, rate.toNat? with
    | some bs, some ch, some rate => return ← encodeSlowMain inFile outFile bs ch rate
    | _, _, _ =>
      return ← usageError s!"--encode-slow: blockSize, channels and sampleRate must be numbers, got '{bs}' '{ch}' '{rate}'"
  if let ["--decode-fast", inFile, outFile] := args then
    let bytes ← IO.FS.readBinFile inFile
    -- the fused path: each frame is serialized by the worker that decoded
    -- it, and `Flac.Stream.decodeBytes_spec` says a `some` result is
    -- exactly `Stream.pcmBytesRange` of what `Flac.Decode.decodeArrays`
    -- returns — so the bytes are the decoded samples, proven, with no
    -- appeal to how the windows were scheduled
    match Flac.Decode.decodeBytes bytes with
    | some (pcm, bps) =>
      IO.FS.writeBinFile outFile pcm
      IO.println s!"decoded ({bps}-bit, frame-parallel serialization)"
      return 0
    | none =>
      -- either the stream does not decode, or some frame is not the uniform
      -- channel shape the concatenation lemma covers: serialize the samples
      -- in one window instead, which is the form `decodeBytes_spec` is
      -- stated against
      match Flac.Decode.decodeArrays bytes with
      | none => IO.println "DECODE ERROR: not a decodable FLAC stream (within the v1 feature set)"; return 1
      | some (chs, bps, _) =>
        IO.FS.writeBinFile outFile (Stream.pcmBytesRange bps chs 0 (chs.headD #[]).size)
        IO.println s!"decoded {(chs.headD #[]).size} samples x {chs.length} channels ({bps}-bit)"
        return 0
  if let ["--decode", inFile, outFile] := args then
    let bytes ← IO.FS.readBinFile inFile
    match Stream.decodeReference bytes with
    | none => IO.println "DECODE ERROR"; return 1
    | some a =>
      IO.FS.writeBinFile outFile (Stream.pcmBytes a.bps a.channels)
      IO.println s!"decoded {a.numSamples} samples x {a.channels.length} channels ({a.bps}-bit)"
      return 0
  if let ["--samples", dir] := args then
    emitSamples dir
    IO.println s!"samples written to {dir}"
    return 0
  -- anything else (unknown flag, wrong argument count) is a usage error;
  -- never guess at a mode
  unless args.isEmpty do
    IO.eprintln s!"unrecognized or malformed arguments: {String.intercalate " " args}\n"
    IO.eprintln usage
    return 2
  let ((), st) ← (do crcTests; md5Tests; utf8NumTests; riceTests; bitsTests; wrapTests; bombTests; encoderGuardTests; e2eTests; fastMirrorTests; pcmBytesTests; fusedDecodeTests).run {}
  if st.failures == 0 then
    IO.println s!"ALL TESTS PASSED ({st.count} checks)"
    return 0
  else
    IO.println s!"{st.failures}/{st.count} TESTS FAILED"
    return 1
