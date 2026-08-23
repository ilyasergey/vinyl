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
    | some (r, br) => some (q * 2 ^ k + r, br)

def readRice (k : Nat) (br : BitReader) : Option (Int × BitReader) :=
  match readRiceNat k br with
  | none => none
  | some (u, br) => some (Rice.unzigzag u, br)

def readRiceSeq (k : Nat) : (count : Nat) → BitReader → Option (List Int × BitReader)
  | 0, br => some ([], br)
  | count + 1, br =>
    match readRice k br with
    | none => none
    | some (x, br) =>
      match readRiceSeq k count br with
      | none => none
      | some (xs, br) => some (x :: xs, br)

def readSIntSeq (bits : Nat) : (count : Nat) → BitReader → Option (List Int × BitReader)
  | 0, br => some ([], br)
  | count + 1, br =>
    match br.readSInt bits with
    | none => none
    | some (x, br) =>
      match readSIntSeq bits count br with
      | none => none
      | some (xs, br) => some (x :: xs, br)

/-! ## Partitioned residual -/

def readPart (m : Rice.Method) (count : Nat) (br : BitReader) :
    Option (List Int × BitReader) :=
  match br.readBits m.paramBits with
  | none => none
  | some (k, br) =>
    if k = m.escapeCode then
      match br.readBits 5 with
      | none => none
      | some (bits, br) => readSIntSeq bits count br
    else
      readRiceSeq k count br

def readParts (m : Rice.Method) : (sizes : List Nat) → BitReader → Option (List Int × BitReader)
  | [], br => some ([], br)
  | sz :: sizes, br =>
    match readPart m sz br with
    | none => none
    | some (p, br) =>
      match readParts m sizes br with
      | none => none
      | some (ps, br) => some (p ++ ps, br)

def readResidual (bs ord : Nat) (br : BitReader) : Option (List Int × BitReader) :=
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
          readParts m (Rice.partSizes bs po ord) br
        else none

/-! ## Subframes -/

def readContent (bs b ty : Nat) (br : BitReader) : Option (List Int × BitReader) :=
  if ty = 0 then
    match br.readSInt b with
    | none => none
    | some (v, br) => some (List.replicate bs v, br)
  else if ty = 1 then
    readSIntSeq b bs br
  else if 8 ≤ ty ∧ ty ≤ 12 then
    match readSIntSeq b (ty - 8) br with
    | none => none
    | some (warmup, br) =>
      match readResidual bs (ty - 8) br with
      | none => none
      | some (res, br) => some (Fixed.restore (ty - 8) warmup res, br)
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
                match readResidual bs (ty - 31) br with
                | none => none
                | some (res, br) =>
                  some (Lpc.restore cs sh.toNat warmup res, br)
            else none
  else none

def readSubframe (bs b : Nat) (br : BitReader) : Option (List Int × BitReader) :=
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

def readSubframes (bs b : Nat) : Nat → BitReader → Option (List (List Int) × BitReader)
  | 0, br => some ([], br)
  | n + 1, br =>
    match readSubframe bs b br with
    | none => none
    | some (c, br) =>
      match readSubframes bs b n br with
      | none => none
      | some (cs, br) => some (c :: cs, br)

def readChannels (bs b chCode : Nat) (br : BitReader) :
    Option (List (List Int) × BitReader) :=
  if chCode ≤ 7 then
    readSubframes bs b (chCode + 1) br
  else if chCode = 8 then
    match readSubframe bs b br with
    | none => none
    | some (l, br) =>
      match readSubframe bs (b + 1) br with
      | none => none
      | some (sd, br) => some ([l, Stereo.decodeLS l sd], br)
  else if chCode = 9 then
    match readSubframe bs (b + 1) br with
    | none => none
    | some (sd, br) =>
      match readSubframe bs b br with
      | none => none
      | some (r, br) => some ([Stereo.decodeRS sd r, r], br)
  else if chCode = 10 then
    match readSubframe bs b br with
    | none => none
    | some (m, br) =>
      match readSubframe bs (b + 1) br with
      | none => none
      | some (sd, br) => some ([Stereo.decodeMSL m sd, Stereo.decodeMSR m sd], br)
  else none

def readHeaderChannels (b0 : Nat) (br : BitReader) :
    Option (List (List Int) × BitReader) :=
  match readHeader b0 br with
  | none => none
  | some (f, br) => readChannels f.blockSize f.bps f.chCode br

def readBody (b0 : Nat) (br0 : BitReader) : Option (List (List Int) × BitReader) :=
  match readHeaderChannels b0 br0 with
  | none => none
  | some (chs, br1) =>
    match br1.readBits (padLen (br1.pos - br0.pos)) with
    | none => none
    | some (z, br2) => if z = 0 then some (chs, br2) else none

def readFrame (b0 : Nat) (br0 : BitReader) : Option (List (List Int) × BitReader) :=
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

def readFrames (b0 : Nat) : Nat → BitReader → Option (List (List (List Int)))
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
          some ⟨Stream.recombine si.channels frames, si.bps, si.sampleRate⟩
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
