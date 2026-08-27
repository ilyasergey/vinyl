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

/-- Allocation-free unary scan inside a Rice run.  `total` and `pk = 2^k`
    are loop invariants hoisted by the wrapper; `scanOne` returns the
    terminating-bit position as a scalar instead of allocating an option/pair
    per sample.  `Flac.Spec.Decode.readRiceSeqScan_eq` pins this to
    `readRiceSeqGo`. -/
def readRiceSeqScan (d : ByteArray) (k pk total : Nat) :
    (count : Nat) → (pos : Nat) → Array Int → Option (Array Int × Nat)
  | 0, pos, acc => some (acc, pos)
  | count + 1, pos, acc =>
    if pos < total then
      if bitFast d pos then
        let pos1 := pos + 1
        if k = 0 then
          readRiceSeqScan d k pk total count pos1
            (acc.push 0)
        else if pos1 + k ≤ total then
          readRiceSeqScan d k pk total count (pos1 + k)
            (acc.push (Rice.unzigzag (extractBitsFast d pos1 k)))
        else none
      else
        let onePos := scanOne d (pos + 1) (total - (pos + 1))
        if onePos < total then
          let q := onePos - pos
          let pos1 := onePos + 1
          if k = 0 then
            readRiceSeqScan d k pk total count pos1
              (acc.push (Rice.unzigzag q))
          else if pos1 + k ≤ total then
            readRiceSeqScan d k pk total count (pos1 + k)
              (acc.push (Rice.unzigzag (q * pk + extractBitsFast d pos1 k)))
          else none
        else none
    else none

/-- `readRiceSeqScan` with the remainder read through the three-byte
    window and the mask hoisted out of the loop. Identical in structure;
    `Flac.Spec.Decode.readRiceSeqScan3_eq` pins it to `readRiceSeqScan`
    for every `k ≤ 17`. -/
def readRiceSeqScan3 (d : ByteArray) (k pk mask total : Nat) :
    (count : Nat) → (pos : Nat) → Array Int → Option (Array Int × Nat)
  | 0, pos, acc => some (acc, pos)
  | count + 1, pos, acc =>
    if pos < total then
      if bitFast d pos then
        let pos1 := pos + 1
        if k = 0 then
          readRiceSeqScan3 d k pk mask total count pos1 (acc.push 0)
        else if pos1 + k ≤ total then
          readRiceSeqScan3 d k pk mask total count (pos1 + k)
            (acc.push (Rice.unzigzag (extractBits3 d pos1 k mask)))
        else none
      else
        let onePos := scanOne d (pos + 1) (total - (pos + 1))
        if onePos < total then
          let q := onePos - pos
          let pos1 := onePos + 1
          if k = 0 then
            readRiceSeqScan3 d k pk mask total count pos1
              (acc.push (Rice.unzigzag q))
          else if pos1 + k ≤ total then
            readRiceSeqScan3 d k pk mask total count (pos1 + k)
              (acc.push (Rice.unzigzag (q * pk + extractBits3 d pos1 k mask)))
          else none
        else none
    else none

/-- The byte-addressed Rice run (the form the simulation proof is phrased
    over). -/
@[inline] def readRiceSeqScanFast (k count : Nat) (br : BitReader) (acc : Array Int) :
    Option (Array Int × BitReader) :=
  let result :=
    readRiceSeqScan br.data k (p2 k) (8 * br.data.size) count br.pos acc
  match result with
  | none => none
  | some (a, pos) => some (a, ⟨br.data, pos⟩)

/-- The shipped Rice run: the three-byte window where it is valid
    (`k ≤ 17`, i.e. always in practice), the general reader otherwise.
    Equal to `readRiceSeqScanFast` either way
    (`Flac.Spec.Decode.readRiceSeqFast_eq_scanFast`). -/
@[inline] def readRiceSeqFast (k count : Nat) (br : BitReader) (acc : Array Int) :
    Option (Array Int × BitReader) :=
  let result :=
    if k ≤ 17 then
      readRiceSeqScan3 br.data k (p2 k) (p2 k - 1) (8 * br.data.size) count br.pos acc
    else
      readRiceSeqScan br.data k (p2 k) (8 * br.data.size) count br.pos acc
  match result with
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
      | some (res, br) => some (Fixed.restoreA b (ty - 8) warmup res, br)
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
                  some (Lpc.restoreA b cs sh.toNat warmup res, br)
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

/-- CRC-8 of `sliceBytes br0 br1` without allocating the slice
    (`Flac.Decode.crc8Slice_eq`). -/
def crc8Slice (br0 br1 : BitReader) : UInt8 :=
  Crc.crc8Range br0.data (br0.pos / 8) (br1.pos / 8)

/-- CRC-16 of `sliceBytes br0 br1` without allocating the slice
    (`Flac.Decode.crc16Slice_eq`). -/
def crc16Slice (br0 br1 : BitReader) : UInt16 :=
  Crc.crc16Range br0.data (br0.pos / 8) (br1.pos / 8)

def readHeader (b0 : Nat) (br0 : BitReader) : Option (Frame.Fields × BitReader) :=
  match readFields b0 br0 with
  | none => none
  | some (f, br1) =>
    match br1.readBits 8 with
    | none => none
    | some (c8, br2) =>
      if c8 = (crc8Slice br0 br1).toNat then some (f, br2)
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
      if c16 = (crc16Slice br0 br1).toNat then some (chs, br2)
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

/-! ## Frame-parallel decoding

FLAC frames are byte-aligned and self-contained, and `BitReader` reads a
*shared immutable* `ByteArray` at an absolute bit position — so decoding
the frame at position `p` on another thread runs literally the call the
serial loop would run there. That is what makes parallel decoding sound
here rather than merely plausible: each worker's result carries the frame
reader's own equation (`Step.ok`), so consuming a step needs no trust in
which thread produced it, and `readFramesSteps_eq` collapses the whole
parallel path back to the serial loop.

Frame *starts* are only guessed (a sync-code scan). A wrong guess costs
work, never correctness: a step is used only when its recorded position
matches, and its `ok` field then supplies the equation. Positions the
scan missed are decoded on the spot. -/

/-- The frame reader with the cursor as a plain position — the form the
    parallel machinery is phrased over. -/
def readFrameAt (b0 : Nat) (d : ByteArray) (pos : Nat) :
    Option (List (Array Int) × Nat) :=
  match readFrame b0 ⟨d, pos⟩ with
  | none => none
  | some (chs, br) => some (chs, br.pos)

/-- The serial frame loop over positions (equal to `readFrames` by
    `Flac.Spec.Decode.readFramesAt_eq`). -/
def readFramesAt (b0 : Nat) (d : ByteArray) :
    Nat → Nat → Option (List (List (Array Int)))
  | 0, pos => if 8 * d.size - pos = 0 then some [] else none
  | fuel + 1, pos =>
    if 8 * d.size - pos = 0 then some []
    else
      match readFrameAt b0 d pos with
      | none => none
      | some (chs, next) =>
        match readFramesAt b0 d fuel next with
        | none => none
        | some rest => some (chs :: rest)

/-- One frame decoded at a known position, **carrying the frame reader's
    own equation**. The proof field is erased at runtime, so a `Step` costs
    exactly the triple it stores. -/
structure Step (b0 : Nat) (d : ByteArray) where
  pos : Nat
  chs : List (Array Int)
  next : Nat
  ok : readFrameAt b0 d pos = some (chs, next)

/-- Decode the frame at `pos`, packaging its equation. -/
def stepAt (b0 : Nat) (d : ByteArray) (pos : Nat) : Option (Step b0 d) :=
  match h : readFrameAt b0 d pos with
  | none => none
  | some (chs, next) => some ⟨pos, chs, next, h⟩

/-- Candidate-density floor: at most one sync candidate per this many
    scanned bytes, per window (audit finding P4). A real frame costs at
    least ~13 input bytes (`Flac.Spec.Stream.frame_write_length_lb` gives
    `80 + 8·ch` bits), so genuine candidates sit near or below 1/13 only
    for the smallest legal block sizes and near 1/1000 at the default —
    while the attack pattern `FF F8 FF F8 …` has density 1/2. No honest
    stream reaches one candidate per this many bytes, so a scan denser
    than that is not a framed stream at all: `syncCandidates` throws its
    guesses away and lets the serial loop reject the first bogus frame in
    O(1), and each window stops scanning once it has collected this
    density (bounding even the collection). Guesses only *hint* frame
    starts, so dropping all of them costs correctness nothing. -/
def minFrameBytes : Nat := 16

/-- Byte offsets in `[lo, hi)` carrying a frame sync code (RFC 9639
    §9.1.1: fourteen one bits, a zero, then the blocking-strategy bit).
    Reads `d[i + 1]`, which may lie past `hi` — that is what makes windows
    of this scan lossless at their boundaries. Capped at the honest
    candidate density (one per `minFrameBytes`) so a pathological window
    cannot allocate an array proportional to an attacker's byte pattern:
    real audio sits well below the cap and never saturates, while a window
    that does saturate has already proved the stream is not honestly
    framed, which `syncCandidates` acts on. -/
def syncScan (d : ByteArray) (lo hi : Nat) : Array Nat := Id.run do
  let cap := (hi - lo) / minFrameBytes + 8
  let mut out : Array Nat := Array.emptyWithCapacity cap
  for i in [lo : hi] do
    if (if h : i < d.size then d[i] else 0) == 0xFF then
      if (if h : i + 1 < d.size then d[i + 1] else 0) &&& 0xFC == 0xF8 then
        if out.size < cap then
          out := out.push i
        else
          break
  return out

/-- Bytes per parallel scan window. -/
def syncWindow : Nat := 1 <<< 20

/-- Windows tiling `[lo, hi)`, ascending. -/
def syncWindows (lo hi : Nat) : List (Nat × Nat) :=
  go (hi - lo) lo
where
  go : Nat → Nat → List (Nat × Nat)
    | 0, _ => []
    | rem + 1, lo =>
      let len := max 1 (min (rem + 1) syncWindow)
      (lo, lo + len) :: go (rem + 1 - len) (lo + len)
  termination_by rem => rem
  decreasing_by omega

/-- Byte offsets carrying a frame sync code. A *guess*: every use is
    validated by the step's own `Step.ok`, so nothing here carries a proof
    obligation and the scan may be computed any way at all — including in
    parallel windows, since concatenating ascending windows stays
    ascending (which is all `findStep`'s binary search needs) and a sync
    code straddling a boundary is still found by the window that owns its
    first byte.

    The scan was the decoder's largest serial phase: one pass over the
    whole compressed stream, on the driver thread, before any frame worker
    could start.

    Candidates denser than one per `minFrameBytes` cannot come from an
    honestly framed stream (audit finding P4): such a scan is discarded
    (`#[]`), and the frame loop then decodes serially from `start`,
    rejecting the first non-frame in O(1) instead of speculating over
    millions of guesses. This costs correctness nothing — candidates are
    only hints — and real audio sits orders of magnitude below the
    threshold, so it never trips. -/
def syncCandidates (d : ByteArray) (start : Nat) : Array Nat :=
  if d.size = 0 then #[]
  else
    let hi := d.size - 1
    let cands :=
      if hi - start ≤ syncWindow then syncScan d start hi
      else
        let tasks := (syncWindows start hi).map fun w =>
          Task.spawn fun _ => syncScan d w.1 w.2
        tasks.foldl (fun acc t => acc ++ t.get)
          (Array.emptyWithCapacity ((hi - start) / minFrameBytes + 8))
    if minFrameBytes * cands.size ≥ d.size then #[] else cands

/-- What one decoded frame costs against the output budget — the arrays'
    measure of `Flac.Stream.frameCost`. -/
def frameCostA (chs : List (Array Int)) : Nat :=
  2 * (chs.map (·.size)).sum

/-- What a whole frame sequence costs against the budget — the arrays'
    measure of `Flac.Stream.frameCostTotal`. -/
def frameCostTotalA (frs : List (List (Array Int))) : Nat :=
  (frs.map frameCostA).sum

/-- A chunk's share of the output budget: proportional to the input bytes
    its candidates span. Chunk budgets are *heuristic* — a chunk that runs
    out just stops precomputing, and the serial loop decodes the rest of
    its frames under the global budget — but they are what keeps the
    parallel precompute itself from materializing a bomb before the serial
    loop ever checks anything. Spans of consecutive chunks tile the input,
    so the precompute's total output stays within `decodeAmpl · d.size`. -/
def chunkBudget (d : ByteArray) (cands : Array Nat) (lo hi : Nat) : Nat :=
  Flac.Stream.decodeAmpl * (cands.getD hi d.size - cands.getD lo 0)

/-- Candidates per parallel task: enough that task setup is negligible,
    small enough to keep every core fed. Re-measured for the byte-emitting
    workers (1/2/4/8/16 on an 8-core M2): 2 is best at both 1 MB and
    32 MB, though the spread is under 3%. -/
def stepChunkSize : Nat := 2

/-- Ceiling on speculative task objects per fan-out (audit finding P4):
    every task costs queue and closure memory *before* any work runs, so
    the count must not scale with how often an attacker-controlled byte
    pattern occurs. 1024 tasks keep every core fed at any input size. -/
def maxStepTasks : Nat := 1024

/-- Candidates per task: the tuned `stepChunkSize`, grown just enough
    that no candidate array — however dense the scan's guesses — spawns
    more than `maxStepTasks` tasks. -/
def stepChunkFor (ncands : Nat) : Nat :=
  max stepChunkSize ((ncands + maxStepTasks - 1) / maxStepTasks)

/-- Decode one chunk of candidate positions (the unit of parallel work). -/
def stepChunk (b0 : Nat) (d : ByteArray) (cands : Array Nat) (lo hi : Nat) :
    Array (Step b0 d) := Id.run do
  let mut out : Array (Step b0 d) := Array.emptyWithCapacity (hi - lo)
  let mut budget := chunkBudget d cands lo hi
  for i in [lo : hi] do
    match stepAt b0 d (8 * cands.getD i 0) with
    | some st =>
      let c := frameCostA st.chs
      if c ≤ budget then
        out := out.push st
        budget := budget - c
      else
        break
    | none => pure ()
  return out

/-- Decode all candidates, one task per chunk (at most `maxStepTasks`
    of them). Candidates are ascending, so the concatenated steps are
    ascending in `pos` too — which is what `findStep` binary-searches. -/
def stepsPar (b0 : Nat) (d : ByteArray) (cands : Array Nat) :
    Array (Step b0 d) := Id.run do
  let chunk := stepChunkFor cands.size
  let tasks := (List.range ((cands.size + chunk - 1) / chunk)).map fun c =>
    Task.spawn fun _ =>
      stepChunk b0 d cands (c * chunk) (min ((c + 1) * chunk) cands.size)
  let mut out : Array (Step b0 d) := Array.emptyWithCapacity cands.size
  for t in tasks do
    out := out ++ t.get
  return out

/-- Binary search for the step recorded at `pos`. Bounded by 64 iterations,
    so it is total; a miss just means the frame gets decoded on the spot. -/
def findStep {b0 : Nat} {d : ByteArray} (steps : Array (Step b0 d)) (pos : Nat) :
    Option (Step b0 d) := Id.run do
  let mut lo := 0
  let mut hi := steps.size
  for _ in [0 : 64] do
    if lo ≥ hi then
      break
    let mid := (lo + hi) / 2
    match steps[mid]? with
    | none => break
    | some st =>
      if st.pos = pos then
        return some st
      else if st.pos < pos then
        lo := mid + 1
      else
        hi := mid
  return none

/-- The frame at `pos`: a precomputed step when one is recorded there,
    otherwise decoded now. Equal to `readFrameAt` either way
    (`Flac.Spec.Decode.stepFor_eq`) — the precomputed branch is justified
    by the step's own `ok` field. -/
def stepFor (b0 : Nat) (d : ByteArray) (steps : Array (Step b0 d)) (pos : Nat) :
    Option (List (Array Int) × Nat) :=
  match findStep steps pos with
  | some st => if _h : st.pos = pos then some (st.chs, st.next)
               else readFrameAt b0 d pos
  | none => readFrameAt b0 d pos

/-- The frame loop reading precomputed steps where available. Proven equal
    to `readFramesAt` by `Flac.Spec.Decode.readFramesSteps_eq`. -/
def readFramesSteps (b0 : Nat) (d : ByteArray) (steps : Array (Step b0 d)) :
    Nat → Nat → Option (List (List (Array Int)))
  | 0, pos => if 8 * d.size - pos = 0 then some [] else none
  | fuel + 1, pos =>
    if 8 * d.size - pos = 0 then some []
    else
      match stepFor b0 d steps pos with
      | none => none
      | some (chs, next) =>
        match readFramesSteps b0 d steps fuel next with
        | none => none
        | some rest => some (chs :: rest)

/-- `readFramesSteps` with the decoded-output budget threaded through:
    identical results, except that a stream whose decoded size passes the
    budget is rejected (`Flac.Spec.Decode.readFramesStepsB_eq`). -/
def readFramesStepsB (b0 : Nat) (d : ByteArray) (steps : Array (Step b0 d)) :
    Nat → Nat → Nat → Option (List (List (Array Int)))
  | _, 0, pos => if 8 * d.size - pos = 0 then some [] else none
  | budget, fuel + 1, pos =>
    if 8 * d.size - pos = 0 then some []
    else
      match stepFor b0 d steps pos with
      | none => none
      | some (chs, next) =>
        if frameCostA chs ≤ budget then
          match readFramesStepsB b0 d steps (budget - frameCostA chs) fuel next with
          | none => none
          | some rest => some (chs :: rest)
        else none

/-- Streams below this many bytes decode serially — the scan and task
    setup would dominate. -/
def parThreshold : Nat := 1 <<< 16

/-- Frames from `pos`, in parallel when the stream is big enough to pay
    for it. Equal to `readFramesAt` (`Flac.Spec.Decode.readFramesFast_eq`)
    on either branch. -/
def readFramesFast (b0 : Nat) (d : ByteArray) (fuel pos : Nat) :
    Option (List (List (Array Int))) :=
  if d.size < parThreshold then readFramesAt b0 d fuel pos
  else
    readFramesSteps b0 d
      (stepsPar b0 d (syncCandidates d (pos / 8))) fuel pos

/-- `readFramesFast` with the decoded-output budget: the serial branch is
    the steps loop over no steps at all (same loop, so one bridging lemma
    covers both branches). -/
def readFramesFastB (b0 : Nat) (d : ByteArray) (budget fuel pos : Nat) :
    Option (List (List (Array Int))) :=
  if d.size < parThreshold then readFramesStepsB b0 d #[] budget fuel pos
  else
    readFramesStepsB b0 d
      (stepsPar b0 d (syncCandidates d (pos / 8))) budget fuel pos

/-! ## Frame-parallel *serialization*

Turning the decoded samples into interleaved PCM bytes was 46% of decode
wall time and none of it was decoding. On a 32 MB probe: `recombineA`
concatenated every frame's channel arrays into whole-file arrays (41 ms,
serial), and `Stream.pcmBytesA` then walked those again (61 ms — and its
task fan-out bought nothing, because marking the shared `Array Int`
channels multi-threaded cost about what the parallelism saved).

A frame covers a contiguous sample range, so a frame *is* a serialization
window: its bytes can be produced by the worker that decoded it, and the
frames concatenate (`Flac.Spec.Stream.recombineA_model`). That also
removes the marking cost outright — a worker returns a `ByteArray`, which
is O(1) to mark, where `Array Int` channels are O(samples).

A `ByteStep` carries the frame reader's own equation exactly as `Step`
does, except that the channel arrays are *existentially quantified*: proof
fields are erased, so they never exist at runtime and never cross the
thread boundary. The equation also records that the frame is uniform (all
channels the same length) and carries the stream's channel count, which is
what the concatenation lemma needs; a frame that is neither is simply
refused, and the caller falls back to the sample path. -/

/-- A frame's interleaved PCM bytes, with the equation they satisfy. The
    sample count is carried at runtime (the channel arrays are erased), so
    the byte loop charges the *same* output budget the sample loop does. -/
structure ByteStep (b0 bps ch : Nat) (d : ByteArray) where
  pos : Nat
  bytes : ByteArray
  next : Nat
  samples : Nat
  ok : ∃ chs, readFrameAt b0 d pos = some (chs, next)
        ∧ chs.length = ch
        ∧ (∀ a ∈ chs, a.size = (chs.headD #[]).size)
        ∧ bytes = Stream.pcmBytesRange bps chs 0 (chs.headD #[]).size
        ∧ samples = (chs.map (·.size)).sum

/-- Decode the frame at `pos` and serialize it, packaging the equation.
    `none` when the frame does not read, or is not a uniform `ch`-channel
    frame — the concatenation lemma needs both. -/
def byteStepAt (b0 bps ch : Nat) (d : ByteArray) (pos : Nat) :
    Option (ByteStep b0 bps ch d) :=
  match h : readFrameAt b0 d pos with
  | none => none
  | some (chs, next) =>
    if hu : chs.length = ch ∧ ∀ a ∈ chs, a.size = (chs.headD #[]).size then
      some ⟨pos, Stream.pcmBytesRange bps chs 0 (chs.headD #[]).size, next,
        (chs.map (·.size)).sum, ⟨chs, h, hu.1, hu.2, rfl, rfl⟩⟩
    else none

/-- Serialize one chunk of candidate positions (the unit of parallel
    work), within the chunk's share of the output budget (`chunkBudget`;
    a chunk that runs out just stops, and the serial loop decodes the rest
    of its frames under the global budget). -/
def byteStepChunk (b0 bps ch : Nat) (d : ByteArray) (cands : Array Nat) (lo hi : Nat) :
    Array (ByteStep b0 bps ch d) := Id.run do
  let mut out : Array (ByteStep b0 bps ch d) := Array.emptyWithCapacity (hi - lo)
  let mut budget := chunkBudget d cands lo hi
  for i in [lo : hi] do
    match byteStepAt b0 bps ch d (8 * cands.getD i 0) with
    | some st =>
      if 2 * st.samples ≤ budget then
        out := out.push st
        budget := budget - 2 * st.samples
      else
        break
    | none => pure ()
  return out

/-- One task per chunk (at most `maxStepTasks`); candidates ascend, so
    the steps do too. -/
def byteStepsPar (b0 bps ch : Nat) (d : ByteArray) (cands : Array Nat) :
    Array (ByteStep b0 bps ch d) := Id.run do
  let chunk := stepChunkFor cands.size
  let tasks := (List.range ((cands.size + chunk - 1) / chunk)).map fun c =>
    Task.spawn fun _ =>
      byteStepChunk b0 bps ch d cands (c * chunk) (min ((c + 1) * chunk) cands.size)
  let mut out : Array (ByteStep b0 bps ch d) := Array.emptyWithCapacity cands.size
  for t in tasks do
    out := out ++ t.get
  return out

/-- Binary search for the step recorded at `pos` (mirrors `findStep`). -/
def findByteStep {b0 bps ch : Nat} {d : ByteArray}
    (steps : Array (ByteStep b0 bps ch d)) (pos : Nat) :
    Option (ByteStep b0 bps ch d) := Id.run do
  let mut lo := 0
  let mut hi := steps.size
  for _ in [0 : 64] do
    if lo ≥ hi then
      break
    let mid := (lo + hi) / 2
    match steps[mid]? with
    | none => break
    | some st =>
      if st.pos = pos then
        return some st
      else if st.pos < pos then
        lo := mid + 1
      else
        hi := mid
  return none

/-- The frame's bytes at `pos`: a precomputed step when one is recorded
    there, otherwise decoded and serialized on the spot. -/
def byteStepFor (b0 bps ch : Nat) (d : ByteArray)
    (steps : Array (ByteStep b0 bps ch d)) (pos : Nat) :
    Option (ByteStep b0 bps ch d) :=
  match findByteStep steps pos with
  | some st => if st.pos = pos then some st else byteStepAt b0 bps ch d pos
  | none => byteStepAt b0 bps ch d pos

/-- The frame loop, accumulating bytes instead of samples. -/
def readBytesSteps (b0 bps ch : Nat) (d : ByteArray)
    (steps : Array (ByteStep b0 bps ch d)) :
    Nat → Nat → ByteArray → Option ByteArray
  | 0, pos, out => if 8 * d.size - pos = 0 then some out else none
  | fuel + 1, pos, out =>
    if 8 * d.size - pos = 0 then some out
    else
      match byteStepFor b0 bps ch d steps pos with
      | none => none
      | some st => readBytesSteps b0 bps ch d steps fuel st.next (out ++ st.bytes)

/-- The byte-accumulating loop with the decoded-output budget threaded
    through, charging exactly what the sample loop charges (each step
    carries its frame's sample count and the equation for it). -/
def readBytesStepsB (b0 bps ch : Nat) (d : ByteArray)
    (steps : Array (ByteStep b0 bps ch d)) :
    Nat → Nat → Nat → ByteArray → Option ByteArray
  | _, 0, pos, out => if 8 * d.size - pos = 0 then some out else none
  | budget, fuel + 1, pos, out =>
    if 8 * d.size - pos = 0 then some out
    else
      match byteStepFor b0 bps ch d steps pos with
      | none => none
      | some st =>
        if 2 * st.samples ≤ budget then
          readBytesStepsB b0 bps ch d steps (budget - 2 * st.samples) fuel
            st.next (out ++ st.bytes)
        else none

/-- The output buffer's capacity hint. STREAMINFO's `totalSamples` is a
    36-bit *untrusted* field read before any frame is parsed: taken
    verbatim it reserves up to ~1.1 TB for a 42-byte file (audit finding
    P3), aborting under any memory ceiling. Honest streams rarely
    decompress past 16×, so capping the hint at `16 · input + 64 KB`
    leaves it exact for real audio; a stream that genuinely beats 16×
    (heavy silence) merely grows the buffer by doubling. The hint is
    semantically erased — `emptyWithCapacity n` is definitionally the
    empty array — so this cap can change no decoded byte and no proof. -/
def outCapacity (declared inputBytes : Nat) : Nat :=
  min declared (16 * inputBytes + 65536)

/-- **Decode straight to interleaved PCM bytes**, one worker per frame
    chunk, returning the bytes and the stream's bit depth. A `some` result
    is exactly the serialization of what `decodeArrays` returns
    (`Flac.Stream.decodeBytes_spec`); `none` means the caller should use
    the sample path. -/
def decodeBytes (bytes : ByteArray) : Option (ByteArray × Nat) :=
  let br : BitReader := ⟨bytes, 0⟩
  match br.readBits 32 with
  | none => none
  | some (marker, br) =>
    if marker = 0x664C6143 then
      match readMeta br.remaining br with
      | none => none
      | some (si, br) =>
        (readBytesStepsB si.bps si.bps si.channels br.data
          (if br.data.size < parThreshold then #[]
           else byteStepsPar si.bps si.bps si.channels br.data
             (syncCandidates br.data (br.pos / 8)))
          (Flac.Stream.decodeBudget br.data)
          (br.remaining + 1) br.pos
          (ByteArray.emptyWithCapacity
            (outCapacity (2 * si.channels * si.totalSamples + 64)
              br.data.size))).map
          (fun out => (out, si.bps))
    else none

/-- The production decoder body, **array-typed**: reassembled channels stay
    `Array Int` (plus bit depth and sample rate). This is where the decoder
    actually stops; `decodeOption` only adds the `Array → List` conversion
    the *theorem statements* are phrased over, and consumers that want bytes
    (`Flac.decodePcm16`, the CLI) go through the arrays instead — the list
    round-trip allocated a cons cell per decoded sample and then rebuilt the
    very same arrays. -/
def decodeArrays (bytes : ByteArray) : Option (List (Array Int) × Nat × Nat) :=
  let br : BitReader := ⟨bytes, 0⟩
  match br.readBits 32 with
  | none => none
  | some (marker, br) =>
    if marker = 0x664C6143 then
      match readMeta br.remaining br with
      | none => none
      | some (si, br) =>
        match readFramesFastB si.bps br.data (Flac.Stream.decodeBudget br.data)
            (br.remaining + 1) br.pos with
        | none => none
        | some frames =>
          some (recombineA si.channels frames, si.bps, si.sampleRate)
    else none

/-- The production decoder body (Option-typed, mirroring the reference). -/
def decodeOption (bytes : ByteArray) : Option Stream.Audio :=
  (decodeArrays bytes).map fun p => ⟨p.1.map (·.toList), p.2.1, p.2.2⟩

end Flac.Decode

namespace Flac

/-- **The shipped decoder**: total, buffered,
    diagnostic on failure. -/
def decode (bytes : ByteArray) : Except String Stream.Audio :=
  match Decode.decodeOption bytes with
  | some a => .ok a
  | none => .error "not a decodable FLAC stream (within the v1 feature set)"

end Flac
