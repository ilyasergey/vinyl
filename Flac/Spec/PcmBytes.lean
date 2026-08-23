import Flac.Spec.Decode

/-!
# Serializing decoded samples, and doing it one frame at a time

Turning decoded samples into interleaved PCM bytes was 46% of decode wall
time and none of it was decoding. This file proves the property that lets
it move into the frame workers: **a frame is a serialization window**.

`pcmModel` is the byte list the three serialization loops of
`Flac.Native.Stream` all compute (`pcmBytesRange_eq`), stated over lists so
that the two structural facts are list-append facts: serializing `l1 + l2`
samples is serializing `l1` then `l2` (`pcmModel_split`), and samples
before/after a frame boundary come from that frame alone
(`pcmModel_left`, `pcmModel_right`). From those, `recombineA_model` — the
keystone — says serializing the recombined whole-file channels is exactly
serializing each frame and concatenating, for any list of uniform frames
with the stream's channel count.

`decodeBytes_spec` is the capstone: whenever `Flac.Decode.decodeBytes`
returns bytes, they are precisely `pcmBytesRange` applied to the samples
`decodeArrays` returns. Note what this *replaces*: the shipped decoder
previously wrote `Stream.pcmBytesA`, whose window concatenation was
asserted in prose and never proved (and could not be, since it reasons
through `Task`). The fused path carries each frame's equation in the step
itself, so nothing here mentions `Task` — the same discipline the parallel
frame decoder uses.
-/

namespace Flac.Stream

open Flac Flac.Decode

/-! Model: the byte list a serialization loop computes. -/

/-- `w` little-endian bytes of `u`. -/
def sampleLE : (w : Nat) → UInt64 → List UInt8
  | 0, _ => []
  | w + 1, u => u.toUInt8 :: sampleLE w (u >>> 8)

/-- One interleaved sample row. -/
def rowModel (w : Nat) (arrs : List (Array Int)) (i : Nat) : List UInt8 :=
  arrs.flatMap (fun a => sampleLE w ((a.getD i 0).toInt64.toUInt64))

/-- Samples `[i, i + len)`, interleaved. -/
def pcmModel (w : Nat) (arrs : List (Array Int)) (i : Nat) : (len : Nat) → List UInt8
  | 0 => []
  | len + 1 => rowModel w arrs i ++ pcmModel w arrs (i + 1) len

private theorem data_toList_push (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b
  simp [ByteArray.push]

private theorem toByteArray_append (a b : List UInt8) :
    (a ++ b).toByteArray = a.toByteArray ++ b.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_append]
  simp [List.toList_data_toByteArray]

theorem pushSampleLE_eq (w : Nat) (u : UInt64) (out : ByteArray) :
    pushSampleLE w u out = out ++ (sampleLE w u).toByteArray := by
  induction w generalizing u out with
  | zero =>
    show out = out ++ ([] : List UInt8).toByteArray
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_append]
    simp [List.toList_data_toByteArray]
  | succ w ih =>
    show pushSampleLE w (u >>> 8) (out.push u.toUInt8) = _
    rw [ih]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_append, ByteArray.data_append, Array.toList_append,
      Array.toList_append, data_toList_push, List.toList_data_toByteArray,
      List.toList_data_toByteArray]
    simp [sampleLE]

private theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  apply ByteArray.ext
  exact Array.toList_inj.mp h

private theorem append_toList (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  rw [ByteArray.data_append]; simp

private theorem toByteArray_toList (l : List UInt8) : l.toByteArray.data.toList = l := by
  simp [List.toList_data_toByteArray]

/-- One interleaved row of samples, as a `ByteArray` append. -/
theorem rowFold_eq (w i : Nat) : ∀ (arrs : List (Array Int)) (out : ByteArray),
    arrs.foldl (fun o a => pushSampleLE w ((a.getD i 0).toInt64.toUInt64) o) out
      = out ++ (rowModel w arrs i).toByteArray := by
  intro arrs
  induction arrs with
  | nil =>
    intro out
    apply bytes_ext
    rw [append_toList, toByteArray_toList]
    simp [rowModel]
  | cons a as ih =>
    intro out
    show as.foldl _ (pushSampleLE w ((a.getD i 0).toInt64.toUInt64) out) = _
    rw [ih, pushSampleLE_eq]
    apply bytes_ext
    rw [append_toList, append_toList, append_toList, toByteArray_toList,
      toByteArray_toList, toByteArray_toList]
    simp [rowModel, List.append_assoc]

theorem pcmRowsGo_eq (w : Nat) (arrs : List (Array Int)) :
    ∀ (n i stop : Nat), stop - i = n → ∀ (out : ByteArray),
      pcmRowsGo w arrs i stop out = out ++ (pcmModel w arrs i n).toByteArray := by
  intro n
  induction n with
  | zero =>
    intro i stop hn out
    rw [pcmRowsGo]
    rw [dif_neg (by omega)]
    apply bytes_ext
    rw [append_toList, toByteArray_toList]
    simp [pcmModel]
  | succ n ih =>
    intro i stop hn out
    rw [pcmRowsGo]
    rw [dif_pos (by omega), rowFold_eq, ih (i + 1) stop (by omega)]
    apply bytes_ext
    rw [append_toList, append_toList, append_toList, toByteArray_toList,
      toByteArray_toList, toByteArray_toList]
    simp [pcmModel, List.append_assoc]

theorem pcmMonoGo_eq (a : Array Int) :
    ∀ (n i stop : Nat), stop - i = n → ∀ (out : ByteArray),
      pcmMonoGo a i stop out = out ++ (pcmModel 2 [a] i n).toByteArray := by
  intro n
  induction n with
  | zero =>
    intro i stop hn out
    rw [pcmMonoGo, dif_neg (by omega)]
    apply bytes_ext
    rw [append_toList, toByteArray_toList]
    simp [pcmModel]
  | succ n ih =>
    intro i stop hn out
    rw [pcmMonoGo, dif_pos (by omega), ih (i + 1) stop (by omega)]
    apply bytes_ext
    rw [append_toList, append_toList, toByteArray_toList, toByteArray_toList,
      data_toList_push, data_toList_push]
    simp [pcmModel, rowModel, sampleLE, List.append_assoc]

theorem pcmStereoGo_eq (a c : Array Int) :
    ∀ (n i stop : Nat), stop - i = n → ∀ (out : ByteArray),
      pcmStereoGo a c i stop out = out ++ (pcmModel 2 [a, c] i n).toByteArray := by
  intro n
  induction n with
  | zero =>
    intro i stop hn out
    rw [pcmStereoGo, dif_neg (by omega)]
    apply bytes_ext
    rw [append_toList, toByteArray_toList]
    simp [pcmModel]
  | succ n ih =>
    intro i stop hn out
    rw [pcmStereoGo, dif_pos (by omega), ih (i + 1) stop (by omega)]
    apply bytes_ext
    rw [append_toList, append_toList, toByteArray_toList, toByteArray_toList,
      data_toList_push, data_toList_push, data_toList_push, data_toList_push]
    simp [pcmModel, rowModel, sampleLE, List.append_assoc]

private theorem emptyCap_eq (n : Nat) : ByteArray.emptyWithCapacity n = ByteArray.empty := by
  apply ByteArray.ext; rfl

/-- **The serialization loops all compute `pcmModel`.** -/
theorem pcmBytesRange_eq (b : Nat) (arrs : List (Array Int)) (lo len : Nat) :
    pcmBytesRange b arrs lo len = (pcmModel ((b + 7) / 8) arrs lo len).toByteArray := by
  unfold pcmBytesRange
  by_cases hw : (b + 7) / 8 = 2
  · rw [hw]
    match arrs with
    | [a] =>
      dsimp only
      rw [pcmMonoGo_eq a len lo (lo + len) (by omega), emptyCap_eq, ByteArray.empty_append]
      simp
    | [a, c] =>
      dsimp only
      rw [pcmStereoGo_eq a c len lo (lo + len) (by omega), emptyCap_eq,
        ByteArray.empty_append]
      simp
    | [] =>
      dsimp only
      rw [pcmRowsGo_eq 2 [] len lo (lo + len) (by omega), emptyCap_eq,
        ByteArray.empty_append]
      simp
    | a :: c :: d :: t =>
      dsimp only
      rw [pcmRowsGo_eq 2 (a :: c :: d :: t) len lo (lo + len) (by omega), emptyCap_eq,
        ByteArray.empty_append]
      simp
  · rw [if_neg hw, pcmRowsGo_eq _ arrs len lo (lo + len) (by omega), emptyCap_eq,
      ByteArray.empty_append]

/-! ### The model splits along the sample index -/

private theorem getD_append_left (a b : Array Int) (i : Nat) (h : i < a.size) :
    (a ++ b).getD i 0 = a.getD i 0 := by
  simp only [Array.getD, h, dif_pos]
  rw [dif_pos (by simp; omega)]
  exact Array.getElem_append_left h

private theorem getD_append_right (a b : Array Int) (n0 i : Nat) (h : a.size = n0) :
    (a ++ b).getD (n0 + i) 0 = b.getD i 0 := by
  subst h; simp [Array.getD]

/-- Serializing `l1 + l2` samples is serializing `l1` then `l2`. -/
theorem pcmModel_split (w : Nat) (arrs : List (Array Int)) :
    ∀ (l1 : Nat) (lo l2 : Nat),
      pcmModel w arrs lo (l1 + l2)
        = pcmModel w arrs lo l1 ++ pcmModel w arrs (lo + l1) l2 := by
  intro l1
  induction l1 with
  | zero => intro lo l2; simp [pcmModel]
  | succ l1 ih =>
    intro lo l2
    have h : l1 + 1 + l2 = (l1 + l2) + 1 := by omega
    rw [h]
    show rowModel w arrs lo ++ pcmModel w arrs (lo + 1) (l1 + l2) = _
    rw [ih (lo + 1) l2]
    show _ = (rowModel w arrs lo ++ pcmModel w arrs (lo + 1) l1) ++ _
    have h2 : lo + 1 + l1 = lo + (l1 + 1) := by omega
    rw [h2, List.append_assoc]

/-! ### The model splits along a frame boundary -/

private theorem rowModel_left (w i : Nat) : ∀ (a b : List (Array Int)),
    a.length = b.length → (∀ x ∈ a, i < x.size) →
    rowModel w (List.zipWith (· ++ ·) a b) i = rowModel w a i := by
  intro a
  induction a with
  | nil => intro b _ _; simp [rowModel]
  | cons x xs ih =>
    intro b hlen hsz
    match b with
    | [] => simp at hlen
    | y :: ys =>
      have hx : i < x.size := hsz x (by simp)
      simp only [List.zipWith_cons_cons, rowModel, List.flatMap_cons]
      rw [getD_append_left x y i hx]
      congr 1
      exact ih ys (by simpa using hlen) (fun z hz => hsz z (by simp [hz]))

private theorem rowModel_right (w n0 i : Nat) : ∀ (a b : List (Array Int)),
    a.length = b.length → (∀ x ∈ a, x.size = n0) →
    rowModel w (List.zipWith (· ++ ·) a b) (n0 + i) = rowModel w b i := by
  intro a
  induction a with
  | nil => intro b hlen _; match b with
           | [] => simp [rowModel]
           | _ :: _ => simp at hlen
  | cons x xs ih =>
    intro b hlen hsz
    match b with
    | [] => simp at hlen
    | y :: ys =>
      have hx : x.size = n0 := hsz x (by simp)
      simp only [List.zipWith_cons_cons, rowModel, List.flatMap_cons]
      rw [getD_append_right x y n0 i hx]
      congr 1
      exact ih ys (by simpa using hlen) (fun z hz => hsz z (by simp [hz]))

/-- Samples before a frame boundary come from the first frame alone. -/
theorem pcmModel_left (w : Nat) : ∀ (len : Nat) (a b : List (Array Int)) (lo : Nat),
    a.length = b.length → (∀ x ∈ a, lo + len ≤ x.size) →
    pcmModel w (List.zipWith (· ++ ·) a b) lo len = pcmModel w a lo len := by
  intro len
  induction len with
  | zero => intro _ _ _ _ _; simp [pcmModel]
  | succ len ih =>
    intro a b lo hlen hsz
    show rowModel w (List.zipWith (· ++ ·) a b) lo ++ _ = rowModel w a lo ++ _
    rw [rowModel_left w lo a b hlen (fun x hx => by have := hsz x hx; omega),
      ih a b (lo + 1) hlen (fun x hx => by have := hsz x hx; omega)]

/-- Samples at and after a frame boundary come from the remaining frames. -/
theorem pcmModel_right (w n0 : Nat) : ∀ (len : Nat) (a b : List (Array Int)) (i : Nat),
    a.length = b.length → (∀ x ∈ a, x.size = n0) →
    pcmModel w (List.zipWith (· ++ ·) a b) (n0 + i) len = pcmModel w b i len := by
  intro len
  induction len with
  | zero => intro _ _ _ _ _; simp [pcmModel]
  | succ len ih =>
    intro a b i hlen hsz
    show rowModel w (List.zipWith (· ++ ·) a b) (n0 + i) ++ _ = rowModel w b i ++ _
    rw [rowModel_right w n0 i a b hlen hsz]
    congr 1
    have h : n0 + i + 1 = n0 + (i + 1) := by omega
    rw [h, ih a b (i + 1) hlen hsz]

/-! ### Serializing the recombination is serializing each frame -/

/-- Samples per frame (all channels of a frame agree). -/
def frLen (fr : List (Array Int)) : Nat := (fr.headD #[]).size

def totalLen (frs : List (List (Array Int))) : Nat := (frs.map frLen).sum

def framesModel (w : Nat) (frs : List (List (Array Int))) : List UInt8 :=
  (frs.map (fun fr => pcmModel w fr 0 (frLen fr))).flatten

private theorem zipWith_sizes (n m : Nat) : ∀ (acc fr : List (Array Int)),
    (∀ x ∈ acc, x.size = n) → (∀ y ∈ fr, y.size = m) →
    ∀ z ∈ List.zipWith (fun a b => a ++ b) acc fr, z.size = n + m := by
  intro acc
  induction acc with
  | nil => intro fr _ _ z hz; simp at hz
  | cons x xs ih =>
    intro fr hacc hfr z hz
    match fr with
    | [] => simp at hz
    | y :: ys =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with h | h
      · subst h
        rw [Array.size_append, hacc x (by simp), hfr y (by simp)]
      · exact ih ys (fun a ha => hacc a (by simp [ha])) (fun b hb => hfr b (by simp [hb])) z h

private theorem zipWith_replicate_empty : ∀ (acc : List (Array Int)) (ch : Nat),
    acc.length = ch → List.zipWith (fun a b => a ++ b) acc (List.replicate ch #[]) = acc := by
  intro acc
  induction acc with
  | nil => intro ch h; simp at h; subst h; rfl
  | cons x xs ih =>
    intro ch h
    match ch with
    | 0 => simp at h
    | ch + 1 =>
      simp only [List.replicate_succ, List.zipWith_cons_cons]
      rw [ih ch (by simpa using h)]
      simp

theorem recombineGo_model (w ch : Nat) :
    ∀ (frs : List (List (Array Int))) (acc : List (Array Int)) (n : Nat),
      acc.length = ch → (∀ a ∈ acc, a.size = n) →
      (∀ fr ∈ frs, fr.length = ch) →
      (∀ fr ∈ frs, ∀ a ∈ fr, a.size = frLen fr) →
      pcmModel w (Flac.Decode.recombineGo ch acc frs) 0 (n + totalLen frs)
        = pcmModel w acc 0 n ++ framesModel w frs := by
  intro frs
  induction frs with
  | nil =>
    intro acc n hlen _ _ _
    show pcmModel w (List.zipWith (fun a b => a ++ b) acc (List.replicate ch #[])) 0
        (n + totalLen []) = _
    rw [zipWith_replicate_empty acc ch hlen]
    simp [totalLen, framesModel]
  | cons fr frs ih =>
    intro acc n hlen hacc hch hunif
    have hfrlen : fr.length = ch := hch fr (by simp)
    have hfru : ∀ a ∈ fr, a.size = frLen fr := hunif fr (by simp)
    have hlenacc : acc.length = fr.length := by rw [hlen, hfrlen]
    have hlen' : (List.zipWith (fun a b => a ++ b) acc fr).length = ch := by
      rw [List.length_zipWith, hlen, hfrlen]; simp
    have hsz' : ∀ a ∈ List.zipWith (fun a b => a ++ b) acc fr, a.size = n + frLen fr :=
      zipWith_sizes n (frLen fr) acc fr hacc hfru
    show pcmModel w
        (Flac.Decode.recombineGo ch (List.zipWith (fun a b => a ++ b) acc fr) frs) 0
        (n + totalLen (fr :: frs)) = _
    have htot : n + totalLen (fr :: frs) = (n + frLen fr) + totalLen frs := by
      simp only [totalLen, List.map_cons, List.sum_cons]; omega
    rw [htot, ih (List.zipWith (fun a b => a ++ b) acc fr) (n + frLen fr) hlen' hsz'
      (fun f hf => hch f (by simp [hf])) (fun f hf => hunif f (by simp [hf]))]
    have hsplit : pcmModel w (List.zipWith (fun a b => a ++ b) acc fr) 0 (n + frLen fr)
        = pcmModel w acc 0 n ++ pcmModel w fr 0 (frLen fr) := by
      rw [pcmModel_split w (List.zipWith (fun a b => a ++ b) acc fr) n 0 (frLen fr)]
      congr 1
      · exact pcmModel_left w n acc fr 0 hlenacc (fun x hx => by rw [hacc x hx]; omega)
      · have h0 : (0 : Nat) + n = n + 0 := by omega
        rw [h0]
        exact pcmModel_right w n (frLen fr) acc fr 0 hlenacc hacc
    rw [hsplit]
    simp [framesModel, List.append_assoc]

/-- **The keystone**: serializing the recombined channels is serializing
    each frame and concatenating. -/
theorem recombineA_model (w ch : Nat) (frs : List (List (Array Int)))
    (hch : ∀ fr ∈ frs, fr.length = ch)
    (hunif : ∀ fr ∈ frs, ∀ a ∈ fr, a.size = frLen fr) :
    pcmModel w (Flac.Decode.recombineA ch frs) 0 (totalLen frs) = framesModel w frs := by
  match frs with
  | [] => simp [Flac.Decode.recombineA, totalLen, framesModel, pcmModel]
  | fr :: frs =>
    show pcmModel w (Flac.Decode.recombineGo ch fr frs) 0 (totalLen (fr :: frs)) = _
    have hfrlen : fr.length = ch := hch fr (by simp)
    have hfru : ∀ a ∈ fr, a.size = frLen fr := hunif fr (by simp)
    have htot : totalLen (fr :: frs) = frLen fr + totalLen frs := by simp [totalLen]
    rw [htot, recombineGo_model w ch frs fr (frLen fr) hfrlen hfru
      (fun f hf => hch f (by simp [hf])) (fun f hf => hunif f (by simp [hf]))]
    simp [framesModel]

/-! ### The fused byte path is sound -/

open Flac.Decode

private theorem byteStepAt_pos {b0 bps ch : Nat} {d : ByteArray} {pos : Nat}
    {st : ByteStep b0 bps ch d} (h : byteStepAt b0 bps ch d pos = some st) :
    st.pos = pos := by
  unfold byteStepAt at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · injection h with h; rw [← h]
    · exact absurd h (by simp)

private theorem byteStepFor_pos {b0 bps ch : Nat} {d : ByteArray}
    {steps : Array (ByteStep b0 bps ch d)} {pos : Nat} {st : ByteStep b0 bps ch d}
    (h : byteStepFor b0 bps ch d steps pos = some st) : st.pos = pos := by
  unfold byteStepFor at h
  split at h
  · split at h
    · injection h with h; rw [← h]; assumption
    · exact byteStepAt_pos h
  · exact byteStepAt_pos h

private theorem append_empty_bytes (out : ByteArray) :
    out ++ ([] : List UInt8).toByteArray = out := by
  apply bytes_ext
  rw [append_toList, toByteArray_toList]
  simp

/-- **Soundness of the fused byte path**: whenever it returns bytes, the
    serial frame loop returns frames that are uniform `ch`-channel frames,
    and the bytes are exactly those frames serialized in order. -/
theorem readBytesSteps_spec (b0 bps ch : Nat) (d : ByteArray)
    (steps : Array (ByteStep b0 bps ch d)) :
    ∀ (fuel pos : Nat) (out r : ByteArray),
      readBytesSteps b0 bps ch d steps fuel pos out = some r →
      ∃ frames, readFramesAt b0 d fuel pos = some frames
        ∧ (∀ fr ∈ frames, fr.length = ch)
        ∧ (∀ fr ∈ frames, ∀ a ∈ fr, a.size = frLen fr)
        ∧ r = out ++ (framesModel ((bps + 7) / 8) frames).toByteArray := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos out r h
    unfold readBytesSteps at h
    split at h
    · injection h with h
      refine ⟨[], ?_, by simp, by simp, ?_⟩
      · unfold readFramesAt; rw [if_pos (by assumption)]
      · rw [← h]; simp only [framesModel, List.map_nil, List.flatten_nil]
        exact (append_empty_bytes out).symm
    · exact absurd h (by simp)
  | succ fuel ih =>
    intro pos out r h
    unfold readBytesSteps at h
    split at h
    · injection h with h
      refine ⟨[], ?_, by simp, by simp, ?_⟩
      · unfold readFramesAt; rw [if_pos (by assumption)]
      · rw [← h]; simp only [framesModel, List.map_nil, List.flatten_nil]
        exact (append_empty_bytes out).symm
    · rename_i hne
      match hf : byteStepFor b0 bps ch d steps pos with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some st =>
        rw [hf] at h
        obtain ⟨chs, hread, hlen, hunif, hbytes⟩ := st.ok
        rw [byteStepFor_pos hf] at hread
        dsimp only at h
        obtain ⟨frames, hframes, hch', hun', hr⟩ := ih st.next (out ++ st.bytes) r h
        refine ⟨chs :: frames, ?_, ?_, ?_, ?_⟩
        · unfold readFramesAt
          rw [if_neg hne, hread]
          dsimp only
          rw [hframes]
        · intro fr hfr
          rcases List.mem_cons.mp hfr with h1 | h1
          · rw [h1]; exact hlen
          · exact hch' fr h1
        · intro fr hfr
          rcases List.mem_cons.mp hfr with h1 | h1
          · rw [h1]; exact hunif
          · exact hun' fr h1
        · rw [hr, hbytes, pcmBytesRange_eq]
          apply bytes_ext
          rw [append_toList, append_toList, append_toList, toByteArray_toList,
            toByteArray_toList, toByteArray_toList]
          simp only [framesModel, List.map_cons, List.flatten_cons, frLen,
            List.append_assoc]

/-! ### Sizes of the recombined channels -/

private theorem totalLen_zero : ∀ (frs : List (List (Array Int))),
    (∀ fr ∈ frs, fr.length = 0) → totalLen frs = 0 := by
  intro frs
  induction frs with
  | nil => intro _; rfl
  | cons fr frs ih =>
    intro h
    have hfr : fr = [] := List.eq_nil_of_length_eq_zero (h fr (by simp))
    have h1 : totalLen (fr :: frs) = frLen fr + totalLen frs := by simp [totalLen]
    rw [h1, ih (fun f hf => h f (by simp [hf]))]
    simp [frLen, hfr]

theorem recombineGo_sizes (ch : Nat) :
    ∀ (frs : List (List (Array Int))) (acc : List (Array Int)) (n : Nat),
      acc.length = ch → (∀ a ∈ acc, a.size = n) →
      (∀ fr ∈ frs, fr.length = ch) → (∀ fr ∈ frs, ∀ a ∈ fr, a.size = frLen fr) →
      (Flac.Decode.recombineGo ch acc frs).length = ch ∧
        ∀ a ∈ Flac.Decode.recombineGo ch acc frs, a.size = n + totalLen frs := by
  intro frs
  induction frs with
  | nil =>
    intro acc n hlen hacc _ _
    have hg : Flac.Decode.recombineGo ch acc [] = acc := by
      show List.zipWith (fun a b => a ++ b) acc (List.replicate ch #[]) = acc
      exact zipWith_replicate_empty acc ch hlen
    rw [hg]
    exact ⟨hlen, fun a ha => by rw [hacc a ha]; simp [totalLen]⟩
  | cons fr frs ih =>
    intro acc n hlen hacc hch hunif
    have hfrlen : fr.length = ch := hch fr (by simp)
    have hfru : ∀ a ∈ fr, a.size = frLen fr := hunif fr (by simp)
    have hlen' : (List.zipWith (fun a b => a ++ b) acc fr).length = ch := by
      rw [List.length_zipWith, hlen, hfrlen]; simp
    have hsz' : ∀ a ∈ List.zipWith (fun a b => a ++ b) acc fr, a.size = n + frLen fr :=
      zipWith_sizes n (frLen fr) acc fr hacc hfru
    show (Flac.Decode.recombineGo ch (List.zipWith (fun a b => a ++ b) acc fr) frs).length
        = ch ∧ _
    obtain ⟨h1, h2⟩ := ih (List.zipWith (fun a b => a ++ b) acc fr) (n + frLen fr) hlen' hsz'
      (fun f hf => hch f (by simp [hf])) (fun f hf => hunif f (by simp [hf]))
    refine ⟨h1, fun a ha => ?_⟩
    rw [h2 a ha]
    simp only [totalLen, List.map_cons, List.sum_cons]
    omega

theorem recombineA_headD_size (ch : Nat) (frs : List (List (Array Int)))
    (hch : ∀ fr ∈ frs, fr.length = ch)
    (hunif : ∀ fr ∈ frs, ∀ a ∈ fr, a.size = frLen fr) :
    ((Flac.Decode.recombineA ch frs).headD #[]).size = totalLen frs := by
  match frs with
  | [] =>
    show ((List.replicate ch #[]).headD #[]).size = totalLen ([] : List (List (Array Int)))
    match ch with
    | 0 => simp [totalLen]
    | ch + 1 => simp [List.replicate_succ, totalLen]
  | fr :: frs =>
    have hfrlen : fr.length = ch := hch fr (by simp)
    have hfru : ∀ a ∈ fr, a.size = frLen fr := hunif fr (by simp)
    obtain ⟨h1, h2⟩ := recombineGo_sizes ch frs fr (frLen fr) hfrlen hfru
      (fun f hf => hch f (by simp [hf])) (fun f hf => hunif f (by simp [hf]))
    have htot : frLen fr + totalLen frs = totalLen (fr :: frs) := by
      simp [totalLen]
    show ((Flac.Decode.recombineGo ch fr frs).headD #[]).size = _
    match hl : Flac.Decode.recombineGo ch fr frs with
    | [] =>
      -- the recombination is empty only when there are no channels at all
      have hch0 : ch = 0 := by rw [← h1, hl]; rfl
      have : ∀ f ∈ fr :: frs, f.length = 0 := fun f hf => by rw [hch f hf, hch0]
      rw [totalLen_zero (fr :: frs) this]
      simp
    | a :: t =>
      have ha : a ∈ Flac.Decode.recombineGo ch fr frs := by rw [hl]; simp
      show a.size = _
      rw [h2 a ha, htot]

/-! ### The fused decoder returns exactly the serialized samples -/

theorem readFramesFast_eq_At (b0 : Nat) (d : ByteArray) (fuel pos : Nat) :
    Flac.Decode.readFramesFast b0 d fuel pos = Flac.Decode.readFramesAt b0 d fuel pos := by
  unfold Flac.Decode.readFramesFast
  split
  · rfl
  · rw [Flac.Decode.readFramesSteps_eq]

/-- **Capstone for the fused decoder**: a `some` result is exactly the
    interleaved PCM serialization of the samples `decodeArrays` returns. -/
theorem decodeBytes_spec (bytes out : ByteArray) :
    Flac.Decode.decodeBytes bytes = some out →
      ∃ chs bps sr, Flac.Decode.decodeArrays bytes = some (chs, bps, sr)
        ∧ out = pcmBytesRange bps chs 0 (chs.headD #[]).size := by
  intro h
  simp only [Flac.Decode.decodeBytes] at h
  match hm : (⟨bytes, 0⟩ : Flac.Bits.BitReader).readBits 32 with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some (marker, br1) =>
    rw [hm] at h
    dsimp only at h
    by_cases hmk : marker = 0x664C6143
    · rw [if_pos hmk] at h
      match hme : Flac.Decode.readMeta br1.remaining br1 with
      | none => rw [hme] at h; exact absurd h (by simp)
      | some (si, br2) =>
        rw [hme] at h
        dsimp only at h
        obtain ⟨frames, hframes, hch, hunif, hr⟩ :=
          readBytesSteps_spec si.bps si.bps si.channels br2.data _
            (br2.remaining + 1) br2.pos _ out h
        refine ⟨Flac.Decode.recombineA si.channels frames, si.bps, si.sampleRate, ?_, ?_⟩
        · simp only [Flac.Decode.decodeArrays]
          rw [hm]
          dsimp only
          rw [if_pos hmk, hme]
          dsimp only
          rw [readFramesFast_eq_At, hframes]
        · rw [hr, pcmBytesRange_eq, recombineA_headD_size si.channels frames hch hunif,
            recombineA_model ((si.bps + 7) / 8) si.channels frames hch hunif]
          apply bytes_ext
          rw [append_toList, toByteArray_toList]
          simp [emptyCap_eq]
    · rw [if_neg hmk] at h; exact absurd h (by simp)


end Flac.Stream
