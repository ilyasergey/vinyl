import Flac.Native.Frame
import Flac.Native.Md5

/-!
# Stream layer (RFC 9639 §8) — multichannel

`fLaC` marker, STREAMINFO, frames. The encoder emits marker + a single
STREAMINFO metadata block + frames (fixed- or variable-blocksize
numbering); the reference decoder additionally skips unknown metadata
blocks by length, so foreign files with VORBIS_COMMENT etc. still decode.

`decodeReference` is the verified reference decoder: total by
construction (fuel-bounded loops, no `partial`, no `!`).
-/

namespace Flac.Stream

open Flac.Bits

def takeAll (n : Nat) (chs : List (List Int)) : List (List Int) :=
  chs.map (·.take n)

def dropAll (n : Nat) (chs : List (List Int)) : List (List Int) :=
  chs.map (·.drop n)

def tailAll (chs : List (List Int)) : List (List Int) :=
  chs.map (·.tail)

/-- Split all channels into consecutive frames of `n` samples; the last
    frame may be shorter. Channels are assumed equally long. -/
def chunkChannels (n : Nat) (chs : List (List Int)) : List (List (List Int)) :=
  if _h : (chs.headD []).length = 0 ∨ n = 0 then []
  else takeAll n chs :: chunkChannels n (dropAll n chs)
termination_by (chs.headD []).length
decreasing_by
  rcases chs with _ | ⟨c, t⟩
  · simp at _h
  · simp only [dropAll, List.map_cons, List.headD_cons, List.length_drop]
    simp only [List.headD_cons] at _h
    rw [not_or] at _h
    omega

/-- `chunkChannels` accumulating frames in reverse, so the recursive call is in
    tail position: frame count is attacker-chosen, so the cons-after-return form
    kept one native stack frame alive per frame (audit finding C04). -/
def chunkChannelsAcc (n : Nat) (acc : List (List (List Int)))
    (chs : List (List Int)) : List (List (List Int)) :=
  if _h : (chs.headD []).length = 0 ∨ n = 0 then acc.reverse
  else chunkChannelsAcc n (takeAll n chs :: acc) (dropAll n chs)
termination_by (chs.headD []).length
decreasing_by
  rcases chs with _ | ⟨c, t⟩
  · simp at _h
  · simp only [dropAll, List.map_cons, List.headD_cons, List.length_drop]
    simp only [List.headD_cons] at _h
    rw [not_or] at _h
    omega

/-- The bridging equation: the accumulator loop prepends the already-collected
    (reversed) frames onto the structural `chunkChannels`. -/
theorem chunkChannelsAcc_eq (n : Nat) :
    ∀ (chs : List (List Int)) (acc : List (List (List Int))),
      chunkChannelsAcc n acc chs = acc.reverse ++ chunkChannels n chs := by
  intro chs
  fun_induction chunkChannels n chs with
  | case1 chs h =>
    intro acc
    rw [chunkChannelsAcc, dif_pos h]
    simp
  | case2 chs h ih =>
    intro acc
    rw [chunkChannelsAcc, dif_neg h, ih (takeAll n chs :: acc)]
    simp [List.reverse_cons, List.append_assoc]

def chunkChannelsTR (n : Nat) (chs : List (List Int)) : List (List (List Int)) :=
  chunkChannelsAcc n [] chs

/-- Swap the compiled `chunkChannels` for the tail form; theorems keep the
    structural definition via the kernel. -/
@[csimp] theorem chunkChannels_eq_chunkChannelsTR : @chunkChannels = @chunkChannelsTR := by
  funext n chs
  unfold chunkChannelsTR
  rw [chunkChannelsAcc_eq]
  simp

/-- Reassemble channels from per-frame channel blocks (`ch` = channel
    count, used when there are zero frames). -/
def recombine (ch : Nat) : List (List (List Int)) → List (List Int)
  | [] => List.replicate ch []
  | fr :: frs => List.zipWith (· ++ ·) fr (recombine ch frs)

theorem recombine_eq_foldr (ch : Nat) (frs : List (List (List Int))) :
    recombine ch frs
      = frs.foldr (fun fr acc => List.zipWith (· ++ ·) fr acc)
          (List.replicate ch []) := by
  induction frs with
  | nil => rfl
  | cons fr frs ih => simp [recombine, ih]

/-- `recombine` as a left fold over the reversed frame list, so frame
    count (attacker-chosen: a frame can be ~13 bytes) costs no stack
    (audit finding P6). Same output-linear work — each step copies one
    block-bounded frame onto the front of its channel. -/
def recombineTR (ch : Nat) (frs : List (List (List Int))) : List (List Int) :=
  frs.reverse.foldl (fun acc fr => List.zipWith (· ++ ·) fr acc)
    (List.replicate ch [])

/-- Swap the compiled `recombine` for the fold form; theorems keep the
    structural definition. -/
@[csimp] theorem recombine_eq_recombineTR : @recombine = @recombineTR := by
  funext ch frs
  rw [recombine_eq_foldr]
  unfold recombineTR
  rw [List.foldl_reverse]

/-- Interleave channels sample-by-sample (the MD5 input order,
    RFC 9639 §8.2). -/
def interleave (chs : List (List Int)) : List Int :=
  if _h : (chs.headD []).isEmpty then []
  else chs.map (·.headD 0) ++ interleave (tailAll chs)
termination_by (chs.headD []).length
decreasing_by
  rcases chs with _ | ⟨c, t⟩
  · simp at _h
  · simp only [tailAll, List.map_cons, List.headD_cons, List.length_tail]
    simp only [List.headD_cons, List.isEmpty_iff] at _h
    have : 0 < c.length := List.length_pos_iff.mpr _h
    omega

/-! ### Interleaved PCM bytes

Little-endian two's complement, `⌈b/8⌉` bytes per sample (the MD5 input
format of RFC 9639 §8.2). Unverified — MD5 is a conformance checksum, not
part of the losslessness claim, and `pcmBytesA_eq` cancels only the
array/list conversion, so the byte arithmetic below carries no proof
obligation at all.

The arithmetic runs through `Int → Int64 → UInt64` and extracts bytes with
unboxed shifts, rather than `Int` addition followed by `Int.toNat` and
`Nat` masking. That is one runtime conversion per sample instead of three
plus two `Nat` division-family calls, and it measured 2.5x on a
4M-sample block (266 -> 666 MB/s), which matters because serializing the
decoded samples was ~27% of decode. Mono and stereo — the shapes that
occur — walk their channel arrays directly instead of iterating the
channel *list* per sample.

Out-of-range samples now wrap in two's complement rather than clamping at
zero, which is what RFC 9639 §8.2 asks for and what `Flac.pcm16Row`
already did; in-range samples (all a valid stream can hold) are
unaffected. -/

/-- `w` little-endian bytes of `u`. -/
def pushSampleLE : (w : Nat) → UInt64 → ByteArray → ByteArray
  | 0, _, out => out
  | w + 1, u, out => pushSampleLE w (u >>> 8) (out.push u.toUInt8)

/-- 16-bit mono: two pushes per sample, no per-sample channel-list walk. -/
def pcmMonoGo (a : Array Int) : (i stop : Nat) → ByteArray → ByteArray
  | i, stop, out =>
    if _h : i < stop then
      let u : UInt64 := (a.getD i 0).toInt64.toUInt64
      pcmMonoGo a (i + 1) stop ((out.push u.toUInt8).push (u >>> 8).toUInt8)
    else out
  termination_by i stop => stop - i

/-- 16-bit stereo: four pushes per sample frame. -/
def pcmStereoGo (a c : Array Int) : (i stop : Nat) → ByteArray → ByteArray
  | i, stop, out =>
    if _h : i < stop then
      let u : UInt64 := (a.getD i 0).toInt64.toUInt64
      let v : UInt64 := (c.getD i 0).toInt64.toUInt64
      pcmStereoGo a c (i + 1) stop
        ((((out.push u.toUInt8).push (u >>> 8).toUInt8).push v.toUInt8).push
          (v >>> 8).toUInt8)
    else out
  termination_by i stop => stop - i

/-- Any bit depth, any channel count. -/
def pcmRowsGo (w : Nat) (arrs : List (Array Int)) :
    (i stop : Nat) → ByteArray → ByteArray
  | i, stop, out =>
    if _h : i < stop then
      pcmRowsGo w arrs (i + 1) stop
        (arrs.foldl (fun o a => pushSampleLE w ((a.getD i 0).toInt64.toUInt64) o) out)
    else out
  termination_by i stop => stop - i

/-- Interleaved PCM bytes for the sample window `[lo, lo + len)`. -/
def pcmBytesRange (b : Nat) (arrs : List (Array Int)) (lo len : Nat) : ByteArray :=
  let w := (b + 7) / 8
  let out := ByteArray.emptyWithCapacity (arrs.length * len * w)
  if w = 2 then
    match arrs with
    | [a] => pcmMonoGo a lo (lo + len) out
    | [a, c] => pcmStereoGo a c lo (lo + len) out
    | _ => pcmRowsGo 2 arrs lo (lo + len) out
  else pcmRowsGo w arrs lo (lo + len) out

/-- Samples per parallel serialization window. -/
def pcmWindow : Nat := 1 <<< 16

/-- Sample windows tiling `[0, n)`, as `(lo, len)` pairs. -/
def pcmWindows (n : Nat) : List (Nat × Nat) :=
  go n 0
where
  go : Nat → Nat → List (Nat × Nat)
    | 0, _ => []
    | rem + 1, lo =>
      let len := max 1 (min (rem + 1) pcmWindow)
      (lo, len) :: go (rem + 1 - len) (lo + len)
  termination_by rem => rem
  decreasing_by omega

/-- Interleaved PCM bytes.

    This used to serialize windows in parallel and concatenate them, which
    is sound — the interleaved layout is sample-major, so windows serialize
    independently — but carried no theorem, because it reasons through
    `Task`. It is now the plain range, so `Flac.Spec.PcmBytes.pcmBytesRange_eq`
    characterises it and the STREAMINFO digest the reference encoder writes
    is a proven function of the samples. Nothing on a shipped fast path uses
    it: `--decode-fast` serializes with `Flac.Decode.decodeBytes`, whose
    per-frame steps carry their own equations, and the shipped encoder's
    digest is taken over the input bytes directly. What remains here serves
    `--decode` and `--encode-slow`, the reference pipelines. -/
def pcmBytesA (b : Nat) (arrs : List (Array Int)) : ByteArray :=
  pcmBytesRange b arrs 0 (arrs.headD #[]).size

/-- Interleaved PCM bytes from list-typed channels: the array serializer
    after one conversion (`Flac.Spec.Stream.pcmBytesA_eq` transfers between
    the two). -/
def pcmBytes (b : Nat) (chs : List (List Int)) : ByteArray :=
  pcmBytesA b (chs.map (List.toArray ·))

/-- A digest as a big-endian natural, for `writeBits 128`. -/
def md5Nat (d : ByteArray) : Nat :=
  d.foldl (fun a c => a * 256 + c.toNat) 0

/-- STREAMINFO for a fixed-blocksize stream: min = max block size,
    unknown (0) frame sizes. -/
def writeStreamInfo (bs sr ch b total md5 : Nat) : BitStream :=
  writeBits 16 bs ++ writeBits 16 bs ++
  writeBits 24 0 ++ writeBits 24 0 ++
  writeBits 20 sr ++ writeBits 3 (ch - 1) ++ writeBits 5 (b - 1) ++
  writeBits 36 total ++ writeBits 128 md5

/-- Parsed STREAMINFO fields the decoder consumes downstream. -/
structure Info where
  minBlock : Nat
  maxBlock : Nat
  sampleRate : Nat
  channels : Nat
  bps : Nat
  totalSamples : Nat
deriving Repr, DecidableEq

def readStreamInfo (s : BitStream) : Option (Info × BitStream) :=
  match readBits 16 s with
  | none => none
  | some (minB, s) =>
    match readBits 16 s with
    | none => none
    | some (maxB, s) =>
      match readBits 24 s with
      | none => none
      | some (_, s) =>
        match readBits 24 s with
        | none => none
        | some (_, s) =>
          match readBits 20 s with
          | none => none
          | some (sr, s) =>
            match readBits 3 s with
            | none => none
            | some (ch, s) =>
              match readBits 5 s with
              | none => none
              | some (bm1, s) =>
                match readBits 36 s with
                | none => none
                | some (total, s) =>
                  match readBits 128 s with
                  | none => none
                  | some (_, s) =>
                    some (⟨minB, maxB, sr, ch + 1, bm1 + 1, total⟩, s)

/-- Drop `n` bits (skipping metadata content by declared length). -/
def skipBits (n : Nat) (s : BitStream) : Option BitStream :=
  if n ≤ s.length then some (s.drop n) else none

/-- Skip metadata blocks until one is flagged last. -/
def skipBlocks : Nat → BitStream → Option BitStream
  | 0, _ => none
  | fuel + 1, s =>
    match readBits 1 s with
    | none => none
    | some (last, s) =>
      match readBits 7 s with
      | none => none
      | some (_, s) =>
        match readBits 24 s with
        | none => none
        | some (len, s) =>
          match skipBits (8 * len) s with
          | none => none
          | some s => if last = 1 then some s else skipBlocks fuel s

/-- Read the metadata section: a STREAMINFO block first (mandatory,
    RFC 9639 §8.1), then any other blocks skipped by length. -/
def readMeta (fuel : Nat) (s : BitStream) : Option (Info × BitStream) :=
  match readBits 1 s with
  | none => none
  | some (last, s) =>
    match readBits 7 s with
    | none => none
    | some (ty, s) =>
      match readBits 24 s with
      | none => none
      | some (len, s) =>
        if ty = 0 then
          if len = 34 then
            match readStreamInfo s with
            | none => none
            | some (si, s) =>
              if last = 1 then some (si, s)
              else
                match skipBlocks fuel s with
                | none => none
                | some s => some (si, s)
          else none
        else none

/-! ## Frame sequences -/

def writeFrames (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    Nat → List (List (List Int)) → BitStream
  | _, [] => []
  | i, fr :: frs =>
    Frame.write b varBlk (if varBlk then i * blockSize else i)
      (chooser fr) fr ++
    writeFrames b varBlk blockSize chooser (i + 1) frs

/-- `writeFrames` with the serialized bits collected in an accumulator, so the
    recursive call is in tail position: frame count is attacker-chosen (a frame
    can be ~13 bytes), so the append-after-return form kept one native stack
    frame alive per frame and overflowed on ordinary inputs (audit finding C04,
    the encode-side analogue of the P6 decode-loop swaps). -/
def writeFramesAcc (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) (acc : BitStream) :
    Nat → List (List (List Int)) → BitStream
  | _, [] => acc
  | i, fr :: frs =>
    writeFramesAcc b varBlk blockSize chooser
      (acc ++ Frame.write b varBlk (if varBlk then i * blockSize else i) (chooser fr) fr)
      (i + 1) frs

/-- The bridging equation: the accumulator loop computes `writeFrames` with the
    already-serialized prefix spliced onto the front. -/
theorem writeFramesAcc_eq (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) (acc : BitStream) (i : Nat)
    (frs : List (List (List Int))) :
    writeFramesAcc b varBlk blockSize chooser acc i frs
      = acc ++ writeFrames b varBlk blockSize chooser i frs := by
  induction frs generalizing acc i with
  | nil => simp [writeFramesAcc, writeFrames]
  | cons fr frs ih =>
    rw [writeFramesAcc, writeFrames, ih]
    simp [List.append_assoc]

def writeFramesTR (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) (i : Nat)
    (frs : List (List (List Int))) : BitStream :=
  writeFramesAcc b varBlk blockSize chooser [] i frs

/-- Swap the compiled `writeFrames` for the tail form; every theorem keeps the
    structural definition via the kernel. -/
@[csimp] theorem writeFrames_eq_writeFramesTR : @writeFrames = @writeFramesTR := by
  funext b varBlk blockSize chooser i frs
  unfold writeFramesTR
  rw [writeFramesAcc_eq]
  simp

/-- Decode frames until the stream is exhausted. Fuel bounds the loop
    (each frame consumes at least one bit, so `s.length + 1` suffices). -/
def readFrames (b0 : Nat) : Nat → BitStream → Option (List (List (List Int)))
  | 0, s => if s = [] then some [] else none
  | fuel + 1, s =>
    if s = [] then some []
    else
      match Frame.read b0 s with
      | none => none
      | some (chs, s') =>
        match readFrames b0 fuel s' with
        | none => none
        | some rest => some (chs :: rest)

/-- `readFrames` in accumulator form: the recursive call is in tail
    position, so recursion depth stays flat however many frames the input
    packs (audit finding P6 — the cons-after-return form keeps one native
    stack frame alive per pending frame, and frame count is
    attacker-chosen). -/
def readFramesAcc (b0 : Nat) (acc : List (List (List Int))) :
    Nat → BitStream → Option (List (List (List Int)))
  | 0, s => if s = [] then some acc.reverse else none
  | fuel + 1, s =>
    if s = [] then some acc.reverse
    else
      match Frame.read b0 s with
      | none => none
      | some (chs, s') => readFramesAcc b0 (chs :: acc) fuel s'

/-- The bridging equation: the accumulator loop computes `readFrames`
    with the already-collected frames spliced back on the front. -/
theorem readFramesAcc_eq (b0 : Nat) (acc : List (List (List Int)))
    (fuel : Nat) (s : BitStream) :
    readFramesAcc b0 acc fuel s
      = (readFrames b0 fuel s).map (acc.reverse ++ ·) := by
  induction fuel generalizing acc s with
  | zero =>
    unfold readFramesAcc readFrames
    by_cases hs : s = [] <;> simp [hs]
  | succ n ih =>
    unfold readFramesAcc readFrames
    by_cases hs : s = []
    · simp [hs]
    · rw [if_neg hs, if_neg hs]
      cases Frame.read b0 s with
      | none => rfl
      | some p =>
        obtain ⟨chs, s'⟩ := p
        show readFramesAcc b0 (chs :: acc) n s'
          = (match readFrames b0 n s' with
             | none => none
             | some rest => some (chs :: rest)).map (acc.reverse ++ ·)
        rw [ih]
        cases readFrames b0 n s' with
        | none => rfl
        | some rest => simp

def readFramesTR (b0 fuel : Nat) (s : BitStream) :
    Option (List (List (List Int))) :=
  readFramesAcc b0 [] fuel s

/-- Swap the compiled `readFrames` for the tail form; theorems keep the
    structural definition. -/
@[csimp] theorem readFrames_eq_readFramesTR : @readFrames = @readFramesTR := by
  funext b0 fuel s
  unfold readFramesTR
  rw [readFramesAcc_eq]
  cases readFrames b0 fuel s <;> simp

/-! ## Decoded-output budget

A CONSTANT subframe stores one value and materializes `blockSize` copies,
so decoded output is not bounded by input size: chaining maximal CONSTANT
frames amplifies a 150 KB stream into gigabytes and kills the process
(RFC 9639 §11, audit finding P2). The decoder therefore carries a *budget*
through its frame loop — a frame that would push cumulative output past
`decodeAmpl · input bytes + decodeFloor` makes the whole decode return
`none`, exactly like a corrupt stream.

`decodeAmpl` must admit everything the encoder can emit, or the round-trip
capstones break: an all-CONSTANT frame legitimately costs about
`80 + 8·ch` bits (`Flac.Spec.Stream.frame_write_length_lb`) for
`2·ch·blockSize` bytes of output, which at the default block size 4096 and
8 channels is a ratio of 3641. 4096 covers it; block sizes above 4608 can
exceed it, which is why the configurable-block-size guards stop there. -/

/-- Maximum decoded bytes (as `2 ·` samples) per input byte. -/
def decodeAmpl : Nat := 4096

/-- Absolute allowance on top of the proportional cap, so no small stream
    is ever rejected by rounding. -/
def decodeFloor : Nat := 65536

/-- The decoded-output budget for a stream. -/
def decodeBudget (bytes : ByteArray) : Nat :=
  decodeAmpl * bytes.size + decodeFloor

/-- What one decoded frame costs against the budget: two bytes per sample
    per channel (the interleaved 16-bit serialization's measure, used for
    every bit depth). -/
def frameCost (fr : List (List Int)) : Nat :=
  2 * (fr.map (·.length)).sum

/-- What a whole frame sequence costs against the budget. -/
def frameCostTotal (frs : List (List (List Int))) : Nat :=
  (frs.map frameCost).sum

/-- `readFrames` with the output budget threaded through: identical
    results, except that a stream whose decoded size passes the budget is
    rejected (`Flac.Spec.Decode.readFramesB_eq`). -/
def readFramesB (b0 : Nat) : Nat → Nat → BitStream →
    Option (List (List (List Int)))
  | _, 0, s => if s = [] then some [] else none
  | budget, fuel + 1, s =>
    if s = [] then some []
    else
      match Frame.read b0 s with
      | none => none
      | some (chs, s') =>
        if frameCost chs ≤ budget then
          match readFramesB b0 (budget - frameCost chs) fuel s' with
          | none => none
          | some rest => some (chs :: rest)
        else none

/-- `readFramesB` in accumulator form (audit finding P6): tail-recursive,
    so the reference decoder's frame loop runs in constant stack. -/
def readFramesBAcc (b0 : Nat) (acc : List (List (List Int))) :
    Nat → Nat → BitStream → Option (List (List (List Int)))
  | _, 0, s => if s = [] then some acc.reverse else none
  | budget, fuel + 1, s =>
    if s = [] then some acc.reverse
    else
      match Frame.read b0 s with
      | none => none
      | some (chs, s') =>
        if frameCost chs ≤ budget then
          readFramesBAcc b0 (chs :: acc) (budget - frameCost chs) fuel s'
        else none

theorem readFramesBAcc_eq (b0 : Nat) (acc : List (List (List Int)))
    (budget fuel : Nat) (s : BitStream) :
    readFramesBAcc b0 acc budget fuel s
      = (readFramesB b0 budget fuel s).map (acc.reverse ++ ·) := by
  induction fuel generalizing acc budget s with
  | zero =>
    unfold readFramesBAcc readFramesB
    by_cases hs : s = [] <;> simp [hs]
  | succ n ih =>
    unfold readFramesBAcc readFramesB
    by_cases hs : s = []
    · simp [hs]
    · rw [if_neg hs, if_neg hs]
      cases Frame.read b0 s with
      | none => rfl
      | some p =>
        obtain ⟨chs, s'⟩ := p
        show (if frameCost chs ≤ budget then
            readFramesBAcc b0 (chs :: acc) (budget - frameCost chs) n s'
          else none)
          = (if frameCost chs ≤ budget then
              match readFramesB b0 (budget - frameCost chs) n s' with
              | none => none
              | some rest => some (chs :: rest)
            else none).map (acc.reverse ++ ·)
        by_cases hb : frameCost chs ≤ budget
        · rw [if_pos hb, if_pos hb, ih]
          cases readFramesB b0 (budget - frameCost chs) n s' with
          | none => rfl
          | some rest => simp
        · rw [if_neg hb, if_neg hb]
          rfl

def readFramesBTR (b0 budget fuel : Nat) (s : BitStream) :
    Option (List (List (List Int))) :=
  readFramesBAcc b0 [] budget fuel s

/-- Swap the compiled `readFramesB` for the tail form; theorems (and the
    whole round-trip stack above them) keep the structural definition. -/
@[csimp] theorem readFramesB_eq_readFramesBTR :
    @readFramesB = @readFramesBTR := by
  funext b0 budget fuel s
  unfold readFramesBTR
  rw [readFramesBAcc_eq]
  cases readFramesB b0 budget fuel s <;> simp

/-! ## Top level -/

/-- Interleaved multichannel PCM. -/
structure Audio where
  channels : List (List Int)
  bps : Nat
  sampleRate : Nat

def Audio.numSamples (a : Audio) : Nat := (a.channels.headD []).length

/-- Well-formedness — exactly "this audio is representable as a FLAC
    stream": 1–8 equal-length channels, bit depth 1–32, samples in range
    for the bit depth, and the STREAMINFO field bounds on sample rate
    (20 bits) and total sample count (36 bits). Decidable, so encoders can
    check it at runtime (`Flac.encodeChecked`). -/
def Audio.WellFormed (a : Audio) : Prop :=
  1 ≤ a.channels.length ∧ a.channels.length ≤ 8 ∧
  1 ≤ a.bps ∧ a.bps ≤ 32 ∧
  (∀ c ∈ a.channels, c.length = a.numSamples) ∧
  (∀ c ∈ a.channels, ∀ x ∈ c, FitsSInt a.bps x) ∧
  a.sampleRate < 2 ^ 20 ∧ a.numSamples < 2 ^ 36

instance (a : Audio) : Decidable a.WellFormed := by
  unfold Audio.WellFormed
  exact inferInstance

/-- Encoder options: block size, numbering
    strategy, and the per-frame channel-assignment/subframe heuristic —
    every knob the capstone quantifies over. -/
structure EncoderCfg where
  blockSize : Nat
  variableBlocking : Bool
  chooser : List (List Int) → Frame.ChannelAsg

/-- The chooser as the encoder actually consults it: the heuristic's
    choice is kept only when its validity certificate checks out;
    otherwise the frame falls back to VERBATIM. -/
def EncoderCfg.safeChooser (cfg : EncoderCfg) (b : Nat)
    (fr : List (List Int)) : Frame.ChannelAsg :=
  (cfg.chooser fr).orVerbatim b (fr.headD []).length fr

def writeStream (cfg : EncoderCfg) (a : Audio) : BitStream :=
  writeBits 32 0x664C6143 ++
  writeBits 1 1 ++ writeBits 7 0 ++ writeBits 24 34 ++
  writeStreamInfo cfg.blockSize a.sampleRate a.channels.length a.bps
    a.numSamples (md5Nat (Md5.md5 (pcmBytes a.bps a.channels))) ++
  writeFrames a.bps cfg.variableBlocking cfg.blockSize (cfg.safeChooser a.bps) 0
    (chunkChannels cfg.blockSize a.channels)

/-- The **unchecked** reference encoder: its precondition,
    `Audio.WellFormed`, is the hypothesis of every round-trip theorem
    (`Flac.Stream.decodeReference_encode`, `Flac.decode_encode_cfg`) and
    is *not* tested here. The function is total, so off-domain audio does
    not fail: bit fields wrap modulo their width and the result is a
    syntactically valid stream — correct CRCs, decodable — denoting
    *different* audio (audit finding P7, issue #7). Call `Flac.encode` or
    `Flac.encodeCheckedCfg` (checked, `Option`-valued, hypothesis-free
    guarantees) unless you hold a `WellFormed` proof; this form exists
    because the capstones quantify over it and the checked wrappers run
    it. -/
def Unchecked.encode (cfg : EncoderCfg) (a : Audio) : ByteArray :=
  bitsToBytes (writeStream cfg a)

/-- Parse just the marker and STREAMINFO (for tools that need the
    stream parameters, e.g. to know the output bit depth). -/
def peekInfo (bytes : ByteArray) : Option Info :=
  let s := bytesToBits bytes
  match readBits 32 s with
  | none => none
  | some (marker, s) =>
    if marker = 0x664C6143 then
      match readMeta s.length s with
      | none => none
      | some (si, _) => some si
    else none

/-- **The verified reference decoder**: returns the decoded audio —
    channels, bit depth, and sample rate, as read from the stream. Decoded
    output is bounded by `decodeBudget bytes`; a stream that would exceed
    it (a decompression bomb) is rejected like a corrupt one. -/
def decodeReference (bytes : ByteArray) : Option Audio :=
  let s := bytesToBits bytes
  match readBits 32 s with
  | none => none
  | some (marker, s) =>
    if marker = 0x664C6143 then
      match readMeta s.length s with
      | none => none
      | some (si, s) =>
        match readFramesB si.bps (decodeBudget bytes) (s.length + 1) s with
        | none => none
        | some frames =>
          some ⟨recombine si.channels frames, si.bps, si.sampleRate⟩
    else none

/-! ## Default heuristics -/

/-- The safe fallback: independent channels, VERBATIM, no wasted bits. -/
def verbatimChooser : List (List Int) → Frame.ChannelAsg :=
  fun fr => .independent (fr.map fun _ => ⟨0, .verbatim⟩)

end Flac.Stream
