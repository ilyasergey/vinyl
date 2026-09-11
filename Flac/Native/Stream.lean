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
    kept one native stack frame alive per frame (audit finding C04,
    `fuzz/findings/encoder-stack-overflow-CONFIRMED`).

    The loop test is emptiness, not `length = 0`: the structural definition's
    `(chs.headD []).length = 0` walks the whole remaining first channel on
    *every* frame, which makes the reference encoder quadratic in the sample
    count. `List.isEmpty` is one pattern match. -/
def chunkChannelsAcc (n : Nat) (acc : List (List (List Int)))
    (chs : List (List Int)) : List (List (List Int)) :=
  if _h : (chs.headD []).isEmpty ∨ n = 0 then acc.reverse
  else chunkChannelsAcc n (takeAll n chs :: acc) (dropAll n chs)
termination_by (chs.headD []).length
decreasing_by
  rcases chs with _ | ⟨c, t⟩
  · simp at _h
  · simp only [dropAll, List.map_cons, List.headD_cons, List.length_drop]
    simp only [List.headD_cons, List.isEmpty_iff] at _h
    rw [not_or] at _h
    have : c ≠ [] := _h.1
    cases c with
    | nil => exact absurd rfl this
    | cons a as =>
      simp only [List.length_cons]
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
    rw [chunkChannelsAcc, dif_pos (by
      rcases h with h | h
      · exact Or.inl (List.isEmpty_iff.2 (List.eq_nil_of_length_eq_zero h))
      · exact Or.inr h)]
    simp
  | case2 chs h ih =>
    intro acc
    rw [chunkChannelsAcc, dif_neg (by
      rw [not_or] at h ⊢
      exact ⟨fun he => h.1 (by rw [List.isEmpty_iff.1 he]; rfl), h.2⟩), ih (takeAll n chs :: acc)]
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

/-! ### Pre-sized serialization

`pcmMonoGo`/`pcmStereoGo` above push one byte at a time — an out-of-line
runtime call per byte, four per stereo sample, a fifth of decode once the
predictors ran on machine words. The `…Fast` twins below (`@[csimp]`) grow
the buffer once (a copy out of a zero block) and fill it in place with
`USize`-indexed stores. The bridging lemmas characterise both loops byte by
byte (`pcmStereoGo_get`, `pcmStereoFill_get`) and meet in
`ByteArray.ext_getElem`. -/

/-- 256 KiB of zeroes, built once: a frame's worth of 16-bit PCM (up to
    65536 stereo samples) is copied out of it rather than pushed. -/
private def zeroBlock : ByteArray := ⟨Array.replicate 262144 0⟩

/-- `n` zero bytes. -/
private def zeros (n : Nat) : ByteArray :=
  if n ≤ 262144 then zeroBlock.extract 0 n else ⟨Array.replicate n 0⟩

theorem size_zeros (n : Nat) : (zeros n).size = n := by
  unfold zeros
  split
  · simp [zeroBlock, ByteArray.size_extract, ByteArray.size]
    omega
  · simp [ByteArray.size]

theorem getElem_zeros (n k : Nat) (hk : k < (zeros n).size) : (zeros n)[k] = 0 := by
  by_cases h : n ≤ 262144
  · simp only [zeros, h, if_true] at hk ⊢
    rw [ByteArray.getElem_extract]
    exact Array.getElem_replicate _
  · simp only [zeros, h, if_false] at hk ⊢
    exact Array.getElem_replicate _

private theorem usize_step (j : USize) (k n : Nat) (hj : j.toNat + k ≤ n) (hn : n < 4294967296) :
    (j + USize.ofNat k).toNat = j.toNat + k := by
  have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := by
    have := USize.le_size
    rwa [USize.size_eq_two_pow] at this
  rw [USize.toNat_add, USize.toNat_ofNat', Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem toNat_toUSize_of_lt (n : Nat) (hn : n < 4294967296) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by
    have := USize.le_size; rwa [USize.size_eq_two_pow] at this))

private theorem size_uset' (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a with
  | mk bs => simp [ByteArray.uset, ByteArray.size, Array.size_uset]

private theorem getElem_uset' (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size)
    (k : Nat) (hk : k < (a.uset i v h).size) (hk' : k < a.size) :
    (a.uset i v h)[k] = if i.toNat = k then v else a[k] := by
  cases a with
  | mk bs =>
    simp only [ByteArray.uset, Array.uset_eq_set]
    show (bs.set i.toNat v h)[k]'_ = if i.toNat = k then v else bs[k]'_
    simp only [Array.getElem_set]

private theorem getElem_push' (a : ByteArray) (b : UInt8) (k : Nat) (hk : k < (a.push b).size) :
    (a.push b)[k] = if h : k < a.size then a[k] else b := by
  cases a with
  | mk bs =>
    show (bs.push b)[k]'_ = if h : k < bs.size then bs[k] else b
    rw [Array.getElem_push]

/-- Split every `if` in the goal; each leaf is either syntactic or arithmetically impossible. -/
local macro "ifs_omega" : tactic => `(tactic| (repeat' split) <;> first | rfl | omega)

private theorem getElem_push2 (out : ByteArray) (b0 b1 : UInt8) (k : Nat)
    (hk : k < ((out.push b0).push b1).size) :
    ((out.push b0).push b1)[k]
      = if h : k < out.size then out[k] else if k = out.size then b0 else b1 := by
  simp only [ByteArray.size_push] at hk
  simp only [getElem_push', ByteArray.size_push]
  ifs_omega

private theorem getElem_push4 (out : ByteArray) (b0 b1 b2 b3 : UInt8) (k : Nat)
    (hk : k < ((((out.push b0).push b1).push b2).push b3).size) :
    ((((out.push b0).push b1).push b2).push b3)[k]
      = if h : k < out.size then out[k]
        else if k = out.size then b0 else if k = out.size + 1 then b1
        else if k = out.size + 2 then b2 else b3 := by
  simp only [ByteArray.size_push] at hk
  simp only [getElem_push', ByteArray.size_push]
  ifs_omega

private theorem getElem_append_left' (a b : ByteArray) (k : Nat) (hk : k < a.size) :
    (a ++ b)[k]'(by rw [ByteArray.size_append]; omega) = a[k] :=
  ByteArray.getElem_append_left hk

/-- Byte `r` (of four) of stereo sample `i`. -/
def stereoByte (a c : Array Int) (i r : Nat) : UInt8 :=
  let u : UInt64 := (a.getD i 0).toInt64.toUInt64
  let v : UInt64 := (c.getD i 0).toInt64.toUInt64
  if r = 0 then u.toUInt8 else if r = 1 then (u >>> 8).toUInt8
  else if r = 2 then v.toUInt8 else (v >>> 8).toUInt8

/-- Byte `r` (of two) of mono sample `i`. -/
def monoByte (a : Array Int) (i r : Nat) : UInt8 :=
  let u : UInt64 := (a.getD i 0).toInt64.toUInt64
  if r = 0 then u.toUInt8 else (u >>> 8).toUInt8

/-- Stereo sample `i` stored at byte offset `j`: four in-place stores. -/
@[inline] def stereoStore (a c : Array Int) (i : Nat) (j : USize) (out : ByteArray)
    (hj : j.toNat + 4 ≤ out.size) (hs : out.size < 4294967296) : ByteArray :=
  have e1 := usize_step j 1 out.size (by omega) hs
  have e2 := usize_step j 2 out.size (by omega) hs
  have e3 := usize_step j 3 out.size (by omega) hs
  let u : UInt64 := (a.getD i 0).toInt64.toUInt64
  let v : UInt64 := (c.getD i 0).toInt64.toUInt64
  let o1 := out.uset j u.toUInt8 (by omega)
  let o2 := o1.uset (j + USize.ofNat 1) (u >>> 8).toUInt8 (by rw [size_uset']; omega)
  let o3 := o2.uset (j + USize.ofNat 2) v.toUInt8 (by rw [size_uset', size_uset']; omega)
  o3.uset (j + USize.ofNat 3) (v >>> 8).toUInt8 (by rw [size_uset', size_uset', size_uset']; omega)

/-- Mono sample `i` stored at byte offset `j`: two in-place stores. -/
@[inline] def monoStore (a : Array Int) (i : Nat) (j : USize) (out : ByteArray)
    (hj : j.toNat + 2 ≤ out.size) (hs : out.size < 4294967296) : ByteArray :=
  have e1 := usize_step j 1 out.size (by omega) hs
  let u : UInt64 := (a.getD i 0).toInt64.toUInt64
  let o1 := out.uset j u.toUInt8 (by omega)
  o1.uset (j + USize.ofNat 1) (u >>> 8).toUInt8 (by rw [size_uset']; omega)

theorem size_stereoStore (a c : Array Int) (i : Nat) (j : USize) (out : ByteArray) hj hs :
    (stereoStore a c i j out hj hs).size = out.size := by
  simp only [stereoStore, size_uset']

theorem size_monoStore (a : Array Int) (i : Nat) (j : USize) (out : ByteArray) hj hs :
    (monoStore a i j out hj hs).size = out.size := by
  simp only [monoStore, size_uset']

theorem getElem_stereoStore (a c : Array Int) (i : Nat) (j : USize) (out : ByteArray) hj hs
    (k : Nat) (hk : k < (stereoStore a c i j out hj hs).size) (hk' : k < out.size) :
    (stereoStore a c i j out hj hs)[k]
      = if j.toNat ≤ k ∧ k < j.toNat + 4 then stereoByte a c i (k - j.toNat) else out[k] := by
  have e1 := usize_step j 1 out.size (by omega) hs
  have e2 := usize_step j 2 out.size (by omega) hs
  have e3 := usize_step j 3 out.size (by omega) hs
  simp only [stereoStore, stereoByte]
  rw [getElem_uset' _ _ _ _ k _ (by simp only [size_uset']; exact hk'),
    getElem_uset' _ _ _ _ k _ (by simp only [size_uset']; exact hk'),
    getElem_uset' _ _ _ _ k _ (by simp only [size_uset']; exact hk'),
    getElem_uset' _ _ _ _ k _ hk', e3, e2, e1]
  ifs_omega

theorem getElem_monoStore (a : Array Int) (i : Nat) (j : USize) (out : ByteArray) hj hs
    (k : Nat) (hk : k < (monoStore a i j out hj hs).size) (hk' : k < out.size) :
    (monoStore a i j out hj hs)[k]
      = if j.toNat ≤ k ∧ k < j.toNat + 2 then monoByte a i (k - j.toNat) else out[k] := by
  have e1 := usize_step j 1 out.size (by omega) hs
  simp only [monoStore, monoByte]
  rw [getElem_uset' _ _ _ _ k _ (by simp only [size_uset']; exact hk'),
    getElem_uset' _ _ _ _ k _ hk', e1]
  ifs_omega

/-- The stereo fill: four stores per sample into a pre-sized buffer. -/
def pcmStereoFill (a c : Array Int) : (i stop : Nat) → (j : USize) → (out : ByteArray) →
    j.toNat + 4 * (stop - i) ≤ out.size → out.size < 4294967296 → ByteArray
  | i, stop, j, out, hj, hs =>
    if h : i < stop then
      pcmStereoFill a c (i + 1) stop (j + USize.ofNat 4) (stereoStore a c i j out (by omega) hs)
        (by rw [size_stereoStore, usize_step j 4 out.size (by omega) hs]; omega)
        (by rw [size_stereoStore]; exact hs)
    else out
  termination_by i stop => stop - i

/-- The mono fill: two stores per sample. -/
def pcmMonoFill (a : Array Int) : (i stop : Nat) → (j : USize) → (out : ByteArray) →
    j.toNat + 2 * (stop - i) ≤ out.size → out.size < 4294967296 → ByteArray
  | i, stop, j, out, hj, hs =>
    if h : i < stop then
      pcmMonoFill a (i + 1) stop (j + USize.ofNat 2) (monoStore a i j out (by omega) hs)
        (by rw [size_monoStore, usize_step j 2 out.size (by omega) hs]; omega)
        (by rw [size_monoStore]; exact hs)
    else out
  termination_by i stop => stop - i

/-- `pcmStereoGo` verbatim: the swap's fallback must not be the swapped name. -/
def pcmStereoGoSlow (a c : Array Int) : (i stop : Nat) → ByteArray → ByteArray
  | i, stop, out =>
    if _h : i < stop then
      let u : UInt64 := (a.getD i 0).toInt64.toUInt64
      let v : UInt64 := (c.getD i 0).toInt64.toUInt64
      pcmStereoGoSlow a c (i + 1) stop
        ((((out.push u.toUInt8).push (u >>> 8).toUInt8).push v.toUInt8).push
          (v >>> 8).toUInt8)
    else out
  termination_by i stop => stop - i

def pcmMonoGoSlow (a : Array Int) : (i stop : Nat) → ByteArray → ByteArray
  | i, stop, out =>
    if _h : i < stop then
      let u : UInt64 := (a.getD i 0).toInt64.toUInt64
      pcmMonoGoSlow a (i + 1) stop ((out.push u.toUInt8).push (u >>> 8).toUInt8)
    else out
  termination_by i stop => stop - i

private theorem fill_bounds (out : ByteArray) (m : Nat) (hs : out.size + m < 4294967296) :
    out.size.toUSize.toNat + m ≤ (out ++ zeros m).size ∧ (out ++ zeros m).size < 4294967296 := by
  rw [ByteArray.size_append, size_zeros, toNat_toUSize_of_lt out.size (by omega)]
  omega

def pcmStereoGoFast (a c : Array Int) (i stop : Nat) (out : ByteArray) : ByteArray :=
  if h : i < stop ∧ out.size + 4 * (stop - i) < 4294967296 ∧ stop - i ≤ 65536 then
    pcmStereoFill a c i stop out.size.toUSize (out ++ zeros (4 * (stop - i)))
      (fill_bounds out _ h.2.1).1 (fill_bounds out _ h.2.1).2
  else pcmStereoGoSlow a c i stop out

def pcmMonoGoFast (a : Array Int) (i stop : Nat) (out : ByteArray) : ByteArray :=
  if h : i < stop ∧ out.size + 2 * (stop - i) < 4294967296 ∧ stop - i ≤ 65536 then
    pcmMonoFill a i stop out.size.toUSize (out ++ zeros (2 * (stop - i)))
      (fill_bounds out _ h.2.1).1 (fill_bounds out _ h.2.1).2
  else pcmMonoGoSlow a i stop out

/-! #### The fills compute the pushes -/

theorem pcmStereoGoSlow_eq (a c : Array Int) :
    ∀ (n i stop : Nat) (out : ByteArray), stop - i = n →
      pcmStereoGoSlow a c i stop out = pcmStereoGo a c i stop out := by
  intro n
  induction n with
  | zero =>
    intro i stop out hn
    rw [pcmStereoGoSlow, pcmStereoGo, dif_neg (by omega), dif_neg (by omega)]
  | succ n ih =>
    intro i stop out hn
    rw [pcmStereoGoSlow, pcmStereoGo, dif_pos (by omega), dif_pos (by omega)]
    exact ih (i + 1) stop _ (by omega)

theorem pcmMonoGoSlow_eq (a : Array Int) :
    ∀ (n i stop : Nat) (out : ByteArray), stop - i = n →
      pcmMonoGoSlow a i stop out = pcmMonoGo a i stop out := by
  intro n
  induction n with
  | zero =>
    intro i stop out hn
    rw [pcmMonoGoSlow, pcmMonoGo, dif_neg (by omega), dif_neg (by omega)]
  | succ n ih =>
    intro i stop out hn
    rw [pcmMonoGoSlow, pcmMonoGo, dif_pos (by omega), dif_pos (by omega)]
    exact ih (i + 1) stop _ (by omega)

theorem pcmStereoGo_size (a c : Array Int) :
    ∀ (n i stop : Nat) (out : ByteArray), stop - i = n →
      (pcmStereoGo a c i stop out).size = out.size + 4 * (stop - i) := by
  intro n
  induction n with
  | zero => intro i stop out hn; rw [pcmStereoGo, dif_neg (by omega)]; omega
  | succ n ih =>
    intro i stop out hn
    rw [pcmStereoGo, dif_pos (by omega), ih (i + 1) stop _ (by omega)]
    simp only [ByteArray.size_push]
    omega

theorem pcmMonoGo_size (a : Array Int) :
    ∀ (n i stop : Nat) (out : ByteArray), stop - i = n →
      (pcmMonoGo a i stop out).size = out.size + 2 * (stop - i) := by
  intro n
  induction n with
  | zero => intro i stop out hn; rw [pcmMonoGo, dif_neg (by omega)]; omega
  | succ n ih =>
    intro i stop out hn
    rw [pcmMonoGo, dif_pos (by omega), ih (i + 1) stop _ (by omega)]
    simp only [ByteArray.size_push]
    omega

theorem pcmStereoGo_get (a c : Array Int) :
    ∀ (n i stop : Nat) (out : ByteArray), stop - i = n →
      ∀ (k : Nat) (hk : k < (pcmStereoGo a c i stop out).size),
        (pcmStereoGo a c i stop out)[k]
          = if h : k < out.size then out[k]
            else stereoByte a c (i + (k - out.size) / 4) ((k - out.size) % 4) := by
  intro n
  induction n with
  | zero =>
    intro i stop out hn k hk
    have hsz := pcmStereoGo_size a c 0 i stop out hn
    have hk' : k < out.size := by rw [hsz] at hk; omega
    have heq : pcmStereoGo a c i stop out = out := by
      rw [pcmStereoGo, dif_neg (show ¬ i < stop by omega)]
    rw [dif_pos hk']
    simp only [heq]
  | succ n ih =>
    intro i stop out hn k hk
    have hlt : i < stop := by omega
    have heq : pcmStereoGo a c i stop out = pcmStereoGo a c (i + 1) stop
        ((((out.push ((a.getD i 0).toInt64.toUInt64).toUInt8).push
          (((a.getD i 0).toInt64.toUInt64) >>> 8).toUInt8).push
          ((c.getD i 0).toInt64.toUInt64).toUInt8).push
          (((c.getD i 0).toInt64.toUInt64) >>> 8).toUInt8) := by
      rw [pcmStereoGo, dif_pos hlt]
    simp only [heq]
    rw [ih (i + 1) stop _ (by omega) k]
    simp only [getElem_push4, ByteArray.size_push]
    by_cases hko : k < out.size
    · rw [dif_pos (show k < out.size + 1 + 1 + 1 + 1 by omega), dif_pos hko, dif_pos hko]
    · rw [dif_neg hko]
      by_cases hk4 : k < out.size + 4
      · rw [dif_pos (show k < out.size + 1 + 1 + 1 + 1 by omega), dif_neg hko]
        simp only [stereoByte]
        have hd : (k - out.size) / 4 = 0 := by omega
        rw [hd, Nat.add_zero]
        ifs_omega
      · rw [dif_neg (show ¬ k < out.size + 1 + 1 + 1 + 1 by omega)]
        have h1 : (k - (out.size + 1 + 1 + 1 + 1)) / 4 = (k - out.size) / 4 - 1 := by omega
        have h2 : (k - (out.size + 1 + 1 + 1 + 1)) % 4 = (k - out.size) % 4 := by omega
        have h3 : i + 1 + ((k - out.size) / 4 - 1) = i + (k - out.size) / 4 := by omega
        rw [h1, h2, h3, dif_neg hko]

theorem pcmMonoGo_get (a : Array Int) :
    ∀ (n i stop : Nat) (out : ByteArray), stop - i = n →
      ∀ (k : Nat) (hk : k < (pcmMonoGo a i stop out).size),
        (pcmMonoGo a i stop out)[k]
          = if h : k < out.size then out[k]
            else monoByte a (i + (k - out.size) / 2) ((k - out.size) % 2) := by
  intro n
  induction n with
  | zero =>
    intro i stop out hn k hk
    have hsz := pcmMonoGo_size a 0 i stop out hn
    have hk' : k < out.size := by rw [hsz] at hk; omega
    have heq : pcmMonoGo a i stop out = out := by
      rw [pcmMonoGo, dif_neg (show ¬ i < stop by omega)]
    rw [dif_pos hk']
    simp only [heq]
  | succ n ih =>
    intro i stop out hn k hk
    have hlt : i < stop := by omega
    have heq : pcmMonoGo a i stop out = pcmMonoGo a (i + 1) stop
        ((out.push ((a.getD i 0).toInt64.toUInt64).toUInt8).push
          (((a.getD i 0).toInt64.toUInt64) >>> 8).toUInt8) := by
      rw [pcmMonoGo, dif_pos hlt]
    simp only [heq]
    rw [ih (i + 1) stop _ (by omega) k]
    simp only [getElem_push2, ByteArray.size_push]
    by_cases hko : k < out.size
    · rw [dif_pos (show k < out.size + 1 + 1 by omega), dif_pos hko, dif_pos hko]
    · rw [dif_neg hko]
      by_cases hk2 : k < out.size + 2
      · rw [dif_pos (show k < out.size + 1 + 1 by omega), dif_neg hko]
        simp only [monoByte]
        have hd : (k - out.size) / 2 = 0 := by omega
        rw [hd, Nat.add_zero]
        ifs_omega
      · rw [dif_neg (show ¬ k < out.size + 1 + 1 by omega)]
        have h1 : (k - (out.size + 1 + 1)) / 2 = (k - out.size) / 2 - 1 := by omega
        have h2 : (k - (out.size + 1 + 1)) % 2 = (k - out.size) % 2 := by omega
        have h3 : i + 1 + ((k - out.size) / 2 - 1) = i + (k - out.size) / 2 := by omega
        rw [h1, h2, h3, dif_neg hko]

theorem pcmStereoFill_succ (a c : Array Int) (i stop : Nat) (j : USize) (out : ByteArray) hj hs
    (h : i < stop) (hj4 : j.toNat + 4 ≤ out.size) hj' hs' :
    pcmStereoFill a c i stop j out hj hs
      = pcmStereoFill a c (i + 1) stop (j + USize.ofNat 4) (stereoStore a c i j out hj4 hs) hj' hs' := by
  rw [pcmStereoFill, dif_pos h]

theorem pcmMonoFill_succ (a : Array Int) (i stop : Nat) (j : USize) (out : ByteArray) hj hs
    (h : i < stop) (hj2 : j.toNat + 2 ≤ out.size) hj' hs' :
    pcmMonoFill a i stop j out hj hs
      = pcmMonoFill a (i + 1) stop (j + USize.ofNat 2) (monoStore a i j out hj2 hs) hj' hs' := by
  rw [pcmMonoFill, dif_pos h]

theorem pcmStereoFill_size (a c : Array Int) :
    ∀ (n i stop : Nat) (j : USize) (out : ByteArray) hj hs, stop - i = n →
      (pcmStereoFill a c i stop j out hj hs).size = out.size := by
  intro n
  induction n with
  | zero => intro i stop j out hj hs hn; rw [pcmStereoFill, dif_neg (by omega)]
  | succ n ih =>
    intro i stop j out hj hs hn
    rw [pcmStereoFill, dif_pos (by omega), ih (i + 1) stop _ _ _ _ (by omega), size_stereoStore]

theorem pcmMonoFill_size (a : Array Int) :
    ∀ (n i stop : Nat) (j : USize) (out : ByteArray) hj hs, stop - i = n →
      (pcmMonoFill a i stop j out hj hs).size = out.size := by
  intro n
  induction n with
  | zero => intro i stop j out hj hs hn; rw [pcmMonoFill, dif_neg (by omega)]
  | succ n ih =>
    intro i stop j out hj hs hn
    rw [pcmMonoFill, dif_pos (by omega), ih (i + 1) stop _ _ _ _ (by omega), size_monoStore]

theorem pcmStereoFill_get (a c : Array Int) :
    ∀ (n i stop : Nat) (j : USize) (out : ByteArray) hj hs, stop - i = n →
      ∀ (k : Nat) (hk : k < (pcmStereoFill a c i stop j out hj hs).size) (hk' : k < out.size),
        (pcmStereoFill a c i stop j out hj hs)[k]
          = if j.toNat ≤ k ∧ k < j.toNat + 4 * (stop - i)
            then stereoByte a c (i + (k - j.toNat) / 4) ((k - j.toNat) % 4)
            else out[k] := by
  intro n
  induction n with
  | zero =>
    intro i stop j out hj hs hn k hk hk'
    have heq : pcmStereoFill a c i stop j out hj hs = out := by
      rw [pcmStereoFill, dif_neg (show ¬ i < stop by omega)]
    rw [if_neg (by omega)]
    simp only [heq]
  | succ n ih =>
    intro i stop j out hj hs hn k hk hk'
    have hlt : i < stop := by omega
    have e4 := usize_step j 4 out.size (by omega) hs
    have heq := pcmStereoFill_succ a c i stop j out hj hs hlt (by omega)
      (by rw [size_stereoStore, e4]; omega) (by rw [size_stereoStore]; exact hs)
    simp only [heq]
    rw [ih (i + 1) stop _ _ _ _ (by omega) k _ (by rw [size_stereoStore]; exact hk'),
      getElem_stereoStore _ _ _ _ _ _ _ k _ hk', e4]
    by_cases hin : j.toNat + 4 ≤ k ∧ k < j.toNat + 4 + 4 * (stop - (i + 1))
    · rw [if_pos hin, if_pos (by omega)]
      have h1 : (k - (j.toNat + 4)) / 4 = (k - j.toNat) / 4 - 1 := by omega
      have h2 : (k - (j.toNat + 4)) % 4 = (k - j.toNat) % 4 := by omega
      have h3 : i + 1 + ((k - j.toNat) / 4 - 1) = i + (k - j.toNat) / 4 := by omega
      rw [h1, h2, h3]
    · rw [if_neg hin]
      by_cases hk4 : j.toNat ≤ k ∧ k < j.toNat + 4
      · rw [if_pos hk4, if_pos (by omega)]
        have hd : (k - j.toNat) / 4 = 0 := by omega
        have hm : (k - j.toNat) % 4 = k - j.toNat := by omega
        rw [hd, hm, Nat.add_zero]
      · rw [if_neg hk4, if_neg (by omega)]

theorem pcmMonoFill_get (a : Array Int) :
    ∀ (n i stop : Nat) (j : USize) (out : ByteArray) hj hs, stop - i = n →
      ∀ (k : Nat) (hk : k < (pcmMonoFill a i stop j out hj hs).size) (hk' : k < out.size),
        (pcmMonoFill a i stop j out hj hs)[k]
          = if j.toNat ≤ k ∧ k < j.toNat + 2 * (stop - i)
            then monoByte a (i + (k - j.toNat) / 2) ((k - j.toNat) % 2)
            else out[k] := by
  intro n
  induction n with
  | zero =>
    intro i stop j out hj hs hn k hk hk'
    have heq : pcmMonoFill a i stop j out hj hs = out := by
      rw [pcmMonoFill, dif_neg (show ¬ i < stop by omega)]
    rw [if_neg (by omega)]
    simp only [heq]
  | succ n ih =>
    intro i stop j out hj hs hn k hk hk'
    have hlt : i < stop := by omega
    have e2 := usize_step j 2 out.size (by omega) hs
    have heq := pcmMonoFill_succ a i stop j out hj hs hlt (by omega)
      (by rw [size_monoStore, e2]; omega) (by rw [size_monoStore]; exact hs)
    simp only [heq]
    rw [ih (i + 1) stop _ _ _ _ (by omega) k _ (by rw [size_monoStore]; exact hk'),
      getElem_monoStore _ _ _ _ _ _ k _ hk', e2]
    by_cases hin : j.toNat + 2 ≤ k ∧ k < j.toNat + 2 + 2 * (stop - (i + 1))
    · rw [if_pos hin, if_pos (by omega)]
      have h1 : (k - (j.toNat + 2)) / 2 = (k - j.toNat) / 2 - 1 := by omega
      have h2 : (k - (j.toNat + 2)) % 2 = (k - j.toNat) % 2 := by omega
      have h3 : i + 1 + ((k - j.toNat) / 2 - 1) = i + (k - j.toNat) / 2 := by omega
      rw [h1, h2, h3]
    · rw [if_neg hin]
      by_cases hk2 : j.toNat ≤ k ∧ k < j.toNat + 2
      · rw [if_pos hk2, if_pos (by omega)]
        have hd : (k - j.toNat) / 2 = 0 := by omega
        have hm : (k - j.toNat) % 2 = k - j.toNat := by omega
        rw [hd, hm, Nat.add_zero]
      · rw [if_neg hk2, if_neg (by omega)]

/-- **The stereo fill computes the pushes.** -/
@[csimp] theorem pcmStereoGo_eq_fast : @pcmStereoGo = @pcmStereoGoFast := by
  funext a c i stop out
  unfold pcmStereoGoFast
  split
  · next h =>
    obtain ⟨hlt, hs, _⟩ := h
    have hj := toNat_toUSize_of_lt out.size (by omega)
    apply ByteArray.ext_getElem
    · rw [pcmStereoGo_size a c _ i stop out rfl, pcmStereoFill_size a c _ i stop _ _ _ _ rfl,
        ByteArray.size_append, size_zeros]
    · intro k hk hk'
      have hk'' : k < (out ++ zeros (4 * (stop - i))).size := by
        rw [pcmStereoFill_size a c _ i stop _ _ _ _ rfl] at hk'; exact hk'
      rw [pcmStereoGo_get a c _ i stop out rfl k hk,
        pcmStereoFill_get a c _ i stop _ _ _ _ rfl k hk' hk'', hj]
      by_cases hko : k < out.size
      · rw [dif_pos hko, if_neg (by omega), getElem_append_left' out _ k hko]
      · rw [dif_neg hko, if_pos (by
          have := hk
          rw [pcmStereoGo_size a c _ i stop out rfl] at this
          omega)]
  · exact (pcmStereoGoSlow_eq a c _ i stop out rfl).symm

/-- **The mono fill computes the pushes.** -/
@[csimp] theorem pcmMonoGo_eq_fast : @pcmMonoGo = @pcmMonoGoFast := by
  funext a i stop out
  unfold pcmMonoGoFast
  split
  · next h =>
    obtain ⟨hlt, hs, _⟩ := h
    have hj := toNat_toUSize_of_lt out.size (by omega)
    apply ByteArray.ext_getElem
    · rw [pcmMonoGo_size a _ i stop out rfl, pcmMonoFill_size a _ i stop _ _ _ _ rfl,
        ByteArray.size_append, size_zeros]
    · intro k hk hk'
      have hk'' : k < (out ++ zeros (2 * (stop - i))).size := by
        rw [pcmMonoFill_size a _ i stop _ _ _ _ rfl] at hk'; exact hk'
      rw [pcmMonoGo_get a _ i stop out rfl k hk,
        pcmMonoFill_get a _ i stop _ _ _ _ rfl k hk' hk'', hj]
      by_cases hko : k < out.size
      · rw [dif_pos hko, if_neg (by omega), getElem_append_left' out _ k hko]
      · rw [dif_neg hko, if_pos (by
          have := hk
          rw [pcmMonoGo_size a _ i stop out rfl] at this
          omega)]
  · exact (pcmMonoGoSlow_eq a _ i stop out rfl).symm

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
                    -- RFC 9639 Table 3: the bit depth field is 4-32. The 5-bit
                    -- encoding can represent 1-3, but no conforming stream uses
                    -- them; libFLAC and ffmpeg both reject. Rejecting here keeps
                    -- the decoder's accept set inside the format, and is safe for
                    -- the round-trip capstone because `Audio.WellFormed` now
                    -- carries `4 ≤ bps`, so the encoder never emits one.
                    if 4 ≤ bm1 + 1 then
                      some (⟨minB, maxB, sr, ch + 1, bm1 + 1, total⟩, s)
                    else none

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

/-- `writeFrames` with the serialized bits collected **reversed** in an
    accumulator, so the recursive call is in tail position: frame count is
    attacker-chosen (a frame can be ~13 bytes), so the append-after-return form
    kept one native stack frame alive per frame and overflowed on ordinary
    inputs (audit finding C04 — `fuzz/findings/encoder-stack-overflow-CONFIRMED`
    — the encode-side analogue of the P6 decode-loop swaps).

    The accumulator is extended with `List.reverseAux`, never `acc ++ …`.
    Appending each frame to the *tail* of a growing accumulator is also tail
    recursive, but recopies the whole prefix per frame and costs `Θ(E·F)` for
    `E` emitted bits over `F` frames; `writeFramesTR` reverses once at the end
    instead, so the loop stays linear. -/
def writeFramesRev (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) (acc : BitStream) :
    Nat → List (List (List Int)) → BitStream
  | _, [] => acc
  | i, fr :: frs =>
    writeFramesRev b varBlk blockSize chooser
      ((Frame.write b varBlk (if varBlk then i * blockSize else i) (chooser fr) fr).reverseAux acc)
      (i + 1) frs

/-- The bridging equation: the loop leaves the frames' bits reversed in front of
    whatever was already accumulated. -/
theorem writeFramesRev_eq (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) (acc : BitStream) (i : Nat)
    (frs : List (List (List Int))) :
    writeFramesRev b varBlk blockSize chooser acc i frs
      = (writeFrames b varBlk blockSize chooser i frs).reverse ++ acc := by
  induction frs generalizing acc i with
  | nil => simp [writeFramesRev, writeFrames]
  | cons fr frs ih =>
    rw [writeFramesRev, writeFrames, ih, List.reverseAux_eq, List.reverse_append,
      List.append_assoc]

def writeFramesTR (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) (i : Nat)
    (frs : List (List (List Int))) : BitStream :=
  (writeFramesRev b varBlk blockSize chooser [] i frs).reverse

/-- Swap the compiled `writeFrames` for the tail form; every theorem keeps the
    structural definition via the kernel. -/
@[csimp] theorem writeFrames_eq_writeFramesTR : @writeFrames = @writeFramesTR := by
  funext b varBlk blockSize chooser i frs
  unfold writeFramesTR
  rw [writeFramesRev_eq]
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
    stream": 1–8 equal-length channels, bit depth 4–32, samples in range
    for the bit depth, and the STREAMINFO field bounds on sample rate
    (20 bits) and total sample count (36 bits). Decidable, so encoders can
    check it at runtime (`Flac.encodeChecked`).

    The bit depth lower bound is 4, not 1: RFC 9639 Table 3 restricts the
    STREAMINFO bit-depth field to 4–32, so a `bps < 4` audio has no
    conforming encoding. Admitting it made `encodeChecked` emit streams that
    both reference decoders reject (`flac`: "bits per sample is 3, must be
    4-32"; `ffmpeg`: "invalid bps: 3") while Vinyl decoded them back, so the
    round-trip capstone held over artifacts that were not FLAC. -/
def Audio.WellFormed (a : Audio) : Prop :=
  1 ≤ a.channels.length ∧ a.channels.length ≤ 8 ∧
  4 ≤ a.bps ∧ a.bps ≤ 32 ∧
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
