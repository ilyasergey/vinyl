import Flac.Native.Reader
import Flac.Native.Stream

/-!
# The production decoder

The shipped decoder: same ℤ sample arithmetic as the reference decoder
(Lean's `Int` is exact, so there is no overflow to defend against), but
reading bits directly from the `ByteArray` through `BitReader` instead of
materialising a `List Bool` — and computing frame CRCs over byte slices.

Structured function-for-function like the reference decoder so that
`Flac.Spec.Decode` can prove them extensionally equal
(`decode_eq_reference`), which yields the accept-set transfer
`decode_ok_iff_reference` and the shipped capstone `Flac.decode_encode`.

Totality by construction, as everywhere in the decode path: fuel-bounded
loops, no `partial`, no panicking indexing.
-/

namespace Flac.Decode

open Flac Flac.Bits Flac.Bits.BitReader

/-! ## Coded numbers -/

def readConts : (k : Nat) → (acc : Nat) → BitReader → Option (Nat × BitReader)
  | 0, acc, br => some (acc, br)
  | k + 1, acc, br =>
    match br.readBits 8 with
    | none => none
    | some (c, br) =>
      if 0x80 ≤ c ∧ c < 0xC0 then readConts k (acc * 64 + (c - 0x80)) br
      else none

def readUtf8 (br : BitReader) : Option (Nat × BitReader) :=
  match br.readBits 8 with
  | none => none
  | some (b, br) =>
    if b < 0x80 then some (b, br)
    else if b < 0xC0 then none
    else if b < 0xE0 then readConts 1 (b - 0xC0) br
    else if b < 0xF0 then readConts 2 (b - 0xE0) br
    else if b < 0xF8 then readConts 3 (b - 0xF0) br
    else if b < 0xFC then readConts 4 (b - 0xF8) br
    else if b < 0xFE then readConts 5 (b - 0xFC) br
    else if b = 0xFE then readConts 6 0 br
    else none

/-! ## Rice codes -/

def readRiceNat (k : Nat) (br : BitReader) : Option (Nat × BitReader) :=
  match br.readUnary with
  | none => none
  | some (q, br) =>
    match br.readBits k with
    | none => none
    | some (r, br) => some (q * p2 k + r, br)

def readRice (k : Nat) (br : BitReader) : Option (Int × BitReader) :=
  match readRiceNat k br with
  | none => none
  | some (u, br) => some (Rice.unzigzag u, br)

/-- Rice-coded run, accumulated into an array (no per-sample cons). This
    is the specification form; the reader runs `readRiceSeqGo` (raw bit
    positions, no intermediate `Option (_ × BitReader)` per sample),
    proven equal by `Flac.Spec.Decode.readRiceSeqFast_eq`. -/
def readRiceSeqA (k : Nat) : (count : Nat) → BitReader → Array Int →
    Option (Array Int × BitReader)
  | 0, br, acc => some (acc, br)
  | count + 1, br, acc =>
    match readRice k br with
    | none => none
    | some (x, br) => readRiceSeqA k count br (acc.push x)

/-- The fused Rice run: unary + remainder straight off the byte buffer. -/
def readRiceSeqGo (d : ByteArray) (k : Nat) : (count : Nat) → (pos : Nat) →
    Array Int → Option (Array Int × Nat)
  | 0, pos, acc => some (acc, pos)
  | count + 1, pos, acc =>
    match readUnaryGo d 0 pos (8 * d.size - pos) with
    | none => none
    | some (q, pos1) =>
      if k = 0 then
        readRiceSeqGo d k count pos1 (acc.push (Rice.unzigzag q))
      else if pos1 + k ≤ 8 * d.size then
        readRiceSeqGo d k count (pos1 + k)
          (acc.push (Rice.unzigzag (q * p2 k + extractBitsFast d pos1 k)))
      else none

@[inline] def readRiceSeqFast (k count : Nat) (br : BitReader) (acc : Array Int) :
    Option (Array Int × BitReader) :=
  match readRiceSeqGo br.data k count br.pos acc with
  | none => none
  | some (a, pos) => some (a, ⟨br.data, pos⟩)

/-- Fixed-width run, accumulated into an array (specification form; the
    reader runs `readSIntSeqGo`). -/
def readSIntSeqA (bits : Nat) : (count : Nat) → BitReader → Array Int →
    Option (Array Int × BitReader)
  | 0, br, acc => some (acc, br)
  | count + 1, br, acc =>
    match br.readSInt bits with
    | none => none
    | some (x, br) => readSIntSeqA bits count br (acc.push x)

/-- The fused fixed-width run, straight off the byte buffer. -/
def readSIntSeqGo (d : ByteArray) (bits : Nat) : (count : Nat) → (pos : Nat) →
    Array Int → Option (Array Int × Nat)
  | 0, pos, acc => some (acc, pos)
  | count + 1, pos, acc =>
    if bits = 0 then
      readSIntSeqGo d bits count pos (acc.push 0)
    else if pos + bits ≤ 8 * d.size then
      let v := extractBitsFast d pos bits
      readSIntSeqGo d bits count (pos + bits)
        (acc.push (if 2 * v < p2 bits then (v : Int) else (v : Int) - ((p2 bits : Nat) : Int)))
    else none

@[inline] def readSIntSeqFast (bits count : Nat) (br : BitReader) (acc : Array Int) :
    Option (Array Int × BitReader) :=
  match readSIntSeqGo br.data bits count br.pos acc with
  | none => none
  | some (a, pos) => some (a, ⟨br.data, pos⟩)

/-- Fixed-width run as a list (warmup samples and VERBATIM content). -/
def readSIntSeq (bits count : Nat) (br : BitReader) :
    Option (List Int × BitReader) :=
  match readSIntSeqFast bits count br #[] with
  | none => none
  | some (xs, br) => some (xs.toList, br)

/-! ## Partitioned residual (one accumulator across all partitions) -/

def readPartA (m : Rice.Method) (count : Nat) (br : BitReader) (acc : Array Int) :
    Option (Array Int × BitReader) :=
  match br.readBits m.paramBits with
  | none => none
  | some (k, br) =>
    if k = m.escapeCode then
      match br.readBits 5 with
      | none => none
      | some (bits, br) => readSIntSeqFast bits count br acc
    else
      readRiceSeqFast k count br acc

def readPartsA (m : Rice.Method) : (sizes : List Nat) → BitReader → Array Int →
    Option (Array Int × BitReader)
  | [], br, acc => some (acc, br)
  | sz :: sizes, br, acc =>
    match readPartA m sz br acc with
    | none => none
    | some (acc, br) => readPartsA m sizes br acc

def readResidualA (bs ord : Nat) (br : BitReader) : Option (Array Int × BitReader) :=
  match br.readBits 2 with
  | none => none
  | some (mc, br) =>
    match Rice.Method.ofCode mc with
    | none => none
    | some m =>
      match br.readBits 4 with
      | none => none
      | some (po, br) =>
        if bs % 2 ^ po = 0 ∧ ord < bs / 2 ^ po then
          readPartsA m (Rice.partSizes bs po ord) br
            (Array.emptyWithCapacity (bs - ord))
        else none

/-! ## Subframes -/

def readContent (bs b ty : Nat) (br : BitReader) : Option (Array Int × BitReader) :=
  if ty = 0 then
    match br.readSInt b with
    | none => none
    | some (v, br) => some (Array.replicate bs v, br)
  else if ty = 1 then
    readSIntSeqFast b bs br #[]
  else if 8 ≤ ty ∧ ty ≤ 12 then
    match readSIntSeq b (ty - 8) br with
    | none => none
    | some (warmup, br) =>
      match readResidualA bs (ty - 8) br with
      | none => none
      | some (res, br) => some (Fixed.restoreA (ty - 8) warmup res, br)
  else if 32 ≤ ty then
    match readSIntSeq b (ty - 31) br with
    | none => none
    | some (warmup, br) =>
      match br.readBits 4 with
      | none => none
      | some (pm1, br) =>
        if pm1 = 15 then none
        else
          match br.readSInt 5 with
          | none => none
          | some (sh, br) =>
            if 0 ≤ sh then
              match readSIntSeq (pm1 + 1) (ty - 31) br with
              | none => none
              | some (cs, br) =>
                match readResidualA bs (ty - 31) br with
                | none => none
                | some (res, br) =>
                  some (Lpc.restoreA cs sh.toNat warmup res, br)
            else none
  else none

def readSubframe (bs b : Nat) (br : BitReader) : Option (Array Int × BitReader) :=
  match br.readBits 1 with
  | none => none
  | some (r, br) =>
    if r = 0 then
      match br.readBits 6 with
      | none => none
      | some (ty, br) =>
        match br.readBits 1 with
        | none => none
        | some (wf, br) =>
          if wf = 0 then
            readContent bs b ty br
          else
            match br.readUnary with
            | none => none
            | some (k, br) =>
              match readContent bs (b - (k + 1)) ty br with
              | none => none
              | some (ys, br) => some (ys.map (shiftUp (k + 1)), br)
    else none

/-! ## Frames -/

def resolveBlockSize (code : Nat) (br : BitReader) : Option (Nat × BitReader) :=
  if code = 1 then some (192, br)
  else if 2 ≤ code ∧ code ≤ 5 then some (576 * 2 ^ (code - 2), br)
  else if code = 6 then
    match br.readBits 8 with
    | none => none
    | some (v, br) => some (v + 1, br)
  else if code = 7 then
    match br.readBits 16 with
    | none => none
    | some (v, br) => some (v + 1, br)
  else if 8 ≤ code ∧ code ≤ 15 then some (256 * 2 ^ (code - 8), br)
  else none

def skipSampleRate (code : Nat) (br : BitReader) : Option BitReader :=
  if code = 12 then
    match br.readBits 8 with
    | none => none
    | some (_, br) => some br
  else if code = 13 ∨ code = 14 then
    match br.readBits 16 with
    | none => none
    | some (_, br) => some br
  else if code = 15 then none
  else some br

def readFields (b0 : Nat) (br : BitReader) : Option (Frame.Fields × BitReader) :=
  match br.readBits 14 with
  | none => none
  | some (sync, br) =>
    if sync = 0x3FFE then
      match br.readBits 1 with
      | none => none
      | some (r0, br) =>
        if r0 = 0 then
          match br.readBits 1 with
          | none => none
          | some (_strat, br) =>
            match br.readBits 4 with
            | none => none
            | some (bsCode, br) =>
              match br.readBits 4 with
              | none => none
              | some (srCode, br) =>
                match br.readBits 4 with
                | none => none
                | some (chCode, br) =>
                  match br.readBits 3 with
                  | none => none
                  | some (bpsC, br) =>
                    match Frame.bpsOfCode bpsC b0 with
                    | none => none
                    | some b =>
                      match br.readBits 1 with
                      | none => none
                      | some (r1, br) =>
                        if r1 = 0 then
                          match readUtf8 br with
                          | none => none
                          | some (num, br) =>
                            match resolveBlockSize bsCode br with
                            | none => none
                            | some (bs, br) =>
                              match skipSampleRate srCode br with
                              | none => none
                              | some br =>
                                some (⟨bs, b, chCode, num⟩, br)
                        else none
        else none
    else none

/-- CRC input: the bytes between two byte-aligned bit positions. -/
def sliceBytes (br0 br1 : BitReader) : ByteArray :=
  br0.data.extract (br0.pos / 8) (br1.pos / 8)

def readHeader (b0 : Nat) (br0 : BitReader) : Option (Frame.Fields × BitReader) :=
  match readFields b0 br0 with
  | none => none
  | some (f, br1) =>
    match br1.readBits 8 with
    | none => none
    | some (c8, br2) =>
      if c8 = (Crc.crc8 (sliceBytes br0 br1)).toNat then some (f, br2)
      else none

def readSubframes (bs b : Nat) : Nat → BitReader → Option (List (Array Int) × BitReader)
  | 0, br => some ([], br)
  | n + 1, br =>
    match readSubframe bs b br with
    | none => none
    | some (c, br) =>
      match readSubframes bs b n br with
      | none => none
      | some (cs, br) => some (c :: cs, br)

def readChannels (bs b chCode : Nat) (br : BitReader) :
    Option (List (Array Int) × BitReader) :=
  if chCode ≤ 7 then
    readSubframes bs b (chCode + 1) br
  else if chCode = 8 then
    match readSubframe bs b br with
    | none => none
    | some (l, br) =>
      match readSubframe bs (b + 1) br with
      | none => none
      | some (sd, br) => some ([l, Stereo.decodeLSA l sd], br)
  else if chCode = 9 then
    match readSubframe bs (b + 1) br with
    | none => none
    | some (sd, br) =>
      match readSubframe bs b br with
      | none => none
      | some (r, br) => some ([Stereo.decodeRSA sd r, r], br)
  else if chCode = 10 then
    match readSubframe bs b br with
    | none => none
    | some (m, br) =>
      match readSubframe bs (b + 1) br with
      | none => none
      | some (sd, br) => some ([Stereo.decodeMSLA m sd, Stereo.decodeMSRA m sd], br)
  else none

def readHeaderChannels (b0 : Nat) (br : BitReader) :
    Option (List (Array Int) × BitReader) :=
  match readHeader b0 br with
  | none => none
  | some (f, br) => readChannels f.blockSize f.bps f.chCode br

def readBody (b0 : Nat) (br0 : BitReader) : Option (List (Array Int) × BitReader) :=
  match readHeaderChannels b0 br0 with
  | none => none
  | some (chs, br1) =>
    match br1.readBits (padLen (br1.pos - br0.pos)) with
    | none => none
    | some (z, br2) => if z = 0 then some (chs, br2) else none

def readFrame (b0 : Nat) (br0 : BitReader) : Option (List (Array Int) × BitReader) :=
  match readBody b0 br0 with
  | none => none
  | some (chs, br1) =>
    match br1.readBits 16 with
    | none => none
    | some (c16, br2) =>
      if c16 = (Crc.crc16 (sliceBytes br0 br1)).toNat then some (chs, br2)
      else none

/-! ## Stream -/

def readStreamInfo (br : BitReader) : Option (Stream.Info × BitReader) :=
  match br.readBits 16 with
  | none => none
  | some (minB, br) =>
    match br.readBits 16 with
    | none => none
    | some (maxB, br) =>
      match br.readBits 24 with
      | none => none
      | some (_, br) =>
        match br.readBits 24 with
        | none => none
        | some (_, br) =>
          match br.readBits 20 with
          | none => none
          | some (sr, br) =>
            match br.readBits 3 with
            | none => none
            | some (ch, br) =>
              match br.readBits 5 with
              | none => none
              | some (bm1, br) =>
                match br.readBits 36 with
                | none => none
                | some (total, br) =>
                  match br.readBits 128 with
                  | none => none
                  | some (_, br) =>
                    some (⟨minB, maxB, sr, ch + 1, bm1 + 1, total⟩, br)

def skipBlocks : Nat → BitReader → Option BitReader
  | 0, _ => none
  | fuel + 1, br =>
    match br.readBits 1 with
    | none => none
    | some (last, br) =>
      match br.readBits 7 with
      | none => none
      | some (_, br) =>
        match br.readBits 24 with
        | none => none
        | some (len, br) =>
          match br.skip (8 * len) with
          | none => none
          | some br => if last = 1 then some br else skipBlocks fuel br

def readMeta (fuel : Nat) (br : BitReader) : Option (Stream.Info × BitReader) :=
  match br.readBits 1 with
  | none => none
  | some (last, br) =>
    match br.readBits 7 with
    | none => none
    | some (ty, br) =>
      match br.readBits 24 with
      | none => none
      | some (len, br) =>
        if ty = 0 then
          if len = 34 then
            match readStreamInfo br with
            | none => none
            | some (si, br) =>
              if last = 1 then some (si, br)
              else
                match skipBlocks fuel br with
                | none => none
                | some br => some (si, br)
          else none
        else none

def readFrames (b0 : Nat) : Nat → BitReader → Option (List (List (Array Int)))
  | 0, br => if br.remaining = 0 then some [] else none
  | fuel + 1, br =>
    if br.remaining = 0 then some []
    else
      match readFrame b0 br with
      | none => none
      | some (chs, br') =>
        match readFrames b0 fuel br' with
        | none => none
        | some rest => some (chs :: rest)

/-- Reassemble channels from per-frame channel arrays, left to right (so
    each channel grows amortized-linearly). Computes exactly
    `Stream.recombine` on the underlying lists
    (`Flac.Spec.Decode.recombineA_toList`). -/
def recombineGo (ch : Nat) (acc : List (Array Int)) :
    List (List (Array Int)) → List (Array Int)
  | [] => List.zipWith (· ++ ·) acc (List.replicate ch #[])
  | fr :: frs => recombineGo ch (List.zipWith (· ++ ·) acc fr) frs

def recombineA (ch : Nat) : List (List (Array Int)) → List (Array Int)
  | [] => List.replicate ch #[]
  | fr :: frs => recombineGo ch fr frs

/-- The production decoder body (Option-typed, mirroring the reference). -/
def decodeOption (bytes : ByteArray) : Option Stream.Audio :=
  let br : BitReader := ⟨bytes, 0⟩
  match br.readBits 32 with
  | none => none
  | some (marker, br) =>
    if marker = 0x664C6143 then
      match readMeta br.remaining br with
      | none => none
      | some (si, br) =>
        match readFrames si.bps (br.remaining + 1) br with
        | none => none
        | some frames =>
          some ⟨(recombineA si.channels frames).map (·.toList), si.bps,
            si.sampleRate⟩
    else none

end Flac.Decode

namespace Flac

/-- **The shipped decoder**: total, buffered,
    diagnostic on failure. -/
def decode (bytes : ByteArray) : Except String Stream.Audio :=
  match Decode.decodeOption bytes with
  | some a => .ok a
  | none => .error "not a decodable FLAC stream (within the v1 feature set)"

end Flac
