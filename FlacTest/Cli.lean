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

/-- Parse raw signed 16-bit little-endian mono PCM. -/
def pcm16OfBytes (b : ByteArray) : List Int :=
  (List.range (b.size / 2)).map fun i =>
    let u : Nat := b[2*i]!.toNat + 256 * b[2*i+1]!.toNat
    if u < 32768 then (u : Int) else (u : Int) - 65536

/-- Deinterleave raw 16-bit LE PCM into `ch` channels. -/
def deinterleave (ch : Nat) (xs : List Int) : List (List Int) :=
  let arr := xs.toArray
  (List.range ch).map fun c =>
    (List.range (arr.size / ch)).map fun i => arr.getD (i * ch + c) 0

def usage : String :=
  "vinyl - a formally verified FLAC codec (see README.md)\n\n" ++
  "  vinyl --encode <in.pcm> <out.flac> <blockSize> <channels>\n" ++
  "      encode raw interleaved signed 16-bit little-endian PCM\n" ++
  "      (fast encoder; every call certified by the verified decoder)\n" ++
  "  vinyl --encode-slow <in.pcm> <out.flac> <blockSize> <channels>\n" ++
  "      encode with the fully verified encoder (the fast path's fallback)\n" ++
  "  vinyl --decode <in.flac> <out.pcm>\n" ++
  "      decode with the verified reference decoder (raw 16-bit LE out)\n" ++
  "  vinyl --decode-fast <in.flac> <out.pcm>\n" ++
  "      decode with the shipped buffered decoder (raw 16-bit LE out)\n" ++
  "  vinyl --samples <dir>\n" ++
  "      write sample .flac/.pcm pairs into <dir> (must exist)\n" ++
  "  vinyl (no arguments)\n" ++
  "      run the unit-test suite"

def cliMain (args : List String) : IO UInt32 := do
  if args = ["--help"] ∨ args = ["-h"] then
    IO.println usage
    return 0
  if let ["--encode", inFile, outFile, bs, ch] := args then
    let bytes ← IO.FS.readBinFile inFile
    -- the fast byte-level encoder, certified per call: whenever it returns
    -- bytes, `Flac.decodePcm16_encodePcm16Fast` guarantees decoding
    -- returns the input bytes exactly — no hypotheses
    match Flac.encodePcm16Fast bs.toNat! ch.toNat! 44100 bytes with
    | some flacBytes =>
      IO.FS.writeBinFile outFile flacBytes
      IO.println s!"encoded {bytes.size / (2 * ch.toNat!)} samples x {ch} channels (certified: round-trip guaranteed by Flac.decodePcm16_encodePcm16Fast)"
      return 0
    | none =>
      IO.println "ENCODE ERROR: input not FLAC-representable (byte count not a multiple of 2x channels, or channels/blockSize out of range)"
      return 1
  if let ["--encode-slow", inFile, outFile, bs, ch] := args then
    let bytes ← IO.FS.readBinFile inFile
    -- the fully verified encoder (the fast path's fallback), kept for
    -- differential testing
    match Flac.encodePcm16Cfg ⟨bs.toNat!, false, Heuristics.defaultAsgChooser 16⟩
        ch.toNat! 44100 bytes with
    | some flacBytes =>
      IO.FS.writeBinFile outFile flacBytes
      IO.println s!"encoded {bytes.size / (2 * ch.toNat!)} samples x {ch} channels (checked: round-trip guaranteed by Flac.decodePcm16_encodePcm16Cfg)"
      return 0
    | none =>
      IO.println "ENCODE ERROR: input not FLAC-representable"
      return 1
  if let ["--decode-fast", inFile, outFile] := args then
    let bytes ← IO.FS.readBinFile inFile
    match Flac.decode bytes with
    | .error e => IO.println s!"DECODE ERROR: {e}"; return 1
    | .ok a =>
      IO.FS.writeBinFile outFile (Stream.pcmBytes a.bps a.channels)
      IO.println s!"decoded {a.numSamples} samples x {a.channels.length} channels ({a.bps}-bit)"
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
  let ((), st) ← (do crcTests; md5Tests; utf8NumTests; riceTests; bitsTests; e2eTests).run {}
  if st.failures == 0 then
    IO.println s!"ALL TESTS PASSED ({st.count} checks)"
    return 0
  else
    IO.println s!"{st.failures}/{st.count} TESTS FAILED"
    return 1
