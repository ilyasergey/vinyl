import Flac

/-!
# M0 unit tests

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

/-- A test chooser exercising CONSTANT and FIXED subframes. -/
def testChooser (blk : List Int) : Subframe.SubframeCfg :=
  if blk.all (· == blk.headD 0) then .constant
  else if 2 < blk.length then
    .fixed 2 { method := .rice4, po := 0, choices := [.rice 4] }
  else .verbatim

def e2eTests : TestM Unit := do
  let mkCfg (chooser : List Int → Subframe.SubframeCfg) : Stream.EncoderCfg :=
    { blockSize := 16, sampleRate := 44100, bps := 16, chooser := chooser }
  -- 40 samples → frames of 16/16/8 (short last frame)
  let pcm : List Int := (List.range 40).map fun (i : Nat) =>
    (100 * (i : Int)) - 2000 + (if i % 3 == 0 then 7 else -5)
  checkEq "e2e verbatim 40 samples"
    (Stream.decodeReference (Stream.encode (mkCfg Stream.verbatimChooser) pcm))
    (some pcm)
  checkEq "e2e fixed/constant 40 samples"
    (Stream.decodeReference (Stream.encode (mkCfg testChooser) pcm)) (some pcm)
  -- constant blocks
  let flat : List Int := List.replicate 48 (-12345)
  checkEq "e2e constant blocks"
    (Stream.decodeReference (Stream.encode (mkCfg testChooser) flat)) (some flat)
  -- empty stream (zero frames)
  checkEq "e2e empty pcm"
    (Stream.decodeReference (Stream.encode (mkCfg Stream.verbatimChooser) []))
    (some ([] : List Int))
  -- extreme 16-bit values
  let extremes : List Int := [32767, -32768, 0, -1, 1] ++ List.replicate 20 32767
  checkEq "e2e extreme values"
    (Stream.decodeReference (Stream.encode (mkCfg Stream.verbatimChooser) extremes))
    (some extremes)
  -- 8-bit depth
  let cfg8 : Stream.EncoderCfg :=
    { blockSize := 16, sampleRate := 8000, bps := 8, chooser := Stream.verbatimChooser }
  let pcm8 : List Int := (List.range 30).map fun (i : Nat) => ((i : Int) % 100) - 50
  checkEq "e2e 8-bit" (Stream.decodeReference (Stream.encode cfg8 pcm8)) (some pcm8)
  -- the certified default heuristic (M3)
  checkEq "e2e defaultChooser"
    (Stream.decodeReference (Stream.encode (mkCfg (Heuristics.defaultChooser 16)) pcm))
    (some pcm)
  checkEq "e2e defaultChooser constant blocks"
    (Stream.decodeReference (Stream.encode (mkCfg (Heuristics.defaultChooser 16)) flat))
    (some flat)

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

/-- With an argument, write sample encoded streams into that directory
    (for differential testing against `flac`/`ffmpeg` from the shell). -/
def emitSamples (dir : String) : IO Unit := do
  let mk (name : String) (cfg : Stream.EncoderCfg) (pcm : List Int) : IO Unit := do
    IO.FS.writeBinFile s!"{dir}/{name}.flac" (Stream.encode cfg pcm)
    -- raw PCM for byte-compare: signed little-endian, ⌈bps/8⌉ bytes/sample
    IO.FS.writeBinFile s!"{dir}/{name}.pcm" (Stream.pcmBytes cfg.bps pcm)
  let sine : List Int := (List.range 4000).map fun (i : Nat) =>
    (8000 * Float.sin (Float.ofNat i * 0.05)).toInt64.toInt
  let cfg16 : Stream.EncoderCfg :=
    { blockSize := 4096, sampleRate := 44100, bps := 16,
      chooser := Stream.verbatimChooser }
  mk "sine-verbatim" cfg16 sine
  mk "sine-fixed" { cfg16 with chooser := testChooser } sine
  mk "flat-constant" { cfg16 with chooser := testChooser }
    (List.replicate 10000 (1234 : Int))
  mk "noise-small-blocks" { cfg16 with blockSize := 256 }
    ((List.range 5000).map fun (i : Nat) => ((i * i * 2654435761 + i * 40503) % 65536 : Int) - 32768)
  mk "empty" cfg16 []

/-- Parse raw signed 16-bit little-endian mono PCM. -/
def pcm16OfBytes (b : ByteArray) : List Int :=
  (List.range (b.size / 2)).map fun i =>
    let u : Nat := b[2*i]!.toNat + 256 * b[2*i+1]!.toNat
    if u < 32768 then (u : Int) else (u : Int) - 65536

def main (args : List String) : IO UInt32 := do
  if let ["--encode", inFile, outFile, bs] := args then
    let bytes ← IO.FS.readBinFile inFile
    let pcm := pcm16OfBytes bytes
    let cfg : Stream.EncoderCfg :=
      { blockSize := bs.toNat!, sampleRate := 44100, bps := 16,
        chooser := Heuristics.defaultChooser 16 }
    IO.FS.writeBinFile outFile (Stream.encode cfg pcm)
    IO.println s!"encoded {pcm.length} samples"
    return 0
  if let ["--decode", inFile, outFile] := args then
    let bytes ← IO.FS.readBinFile inFile
    match Stream.decodeReference bytes with
    | none => IO.println "DECODE ERROR"; return 1
    | some pcm =>
      IO.FS.writeBinFile outFile (Stream.pcmBytes 16 pcm)
      IO.println s!"decoded {pcm.length} samples"
      return 0
  if let dir :: _ := args then
    emitSamples dir
    IO.println s!"samples written to {dir}"
    return 0
  let ((), st) ← (do crcTests; md5Tests; utf8NumTests; riceTests; bitsTests; e2eTests).run {}
  if st.failures == 0 then
    IO.println s!"ALL TESTS PASSED ({st.count} checks)"
    return 0
  else
    IO.println s!"{st.failures}/{st.count} TESTS FAILED"
    return 1
