import Flac.Native.Stream
import Flac.Spec.Frame

/-!
# Stream round-trip — the reference capstone

For every well-formed audio (1–8 equal-length channels, bit depth 1–32,
in-range samples), every block size 16–65535, both numbering strategies,
and *every* channel-assignment/subframe heuristic that returns valid
configurations, decoding the encoded stream returns the original channels
exactly: `decodeReference_encode` at the bottom of this file.
-/

namespace Flac.Stream

open Flac.Bits

/-! ## Chunking -/

@[simp] theorem length_takeAll (n : Nat) (chs : List (List Int)) :
    (takeAll n chs).length = chs.length := by simp [takeAll]

@[simp] theorem length_dropAll (n : Nat) (chs : List (List Int)) :
    (dropAll n chs).length = chs.length := by simp [dropAll]

theorem headD_dropAll (n : Nat) (chs : List (List Int)) :
    ((dropAll n chs).headD []).length = (chs.headD []).length - n := by
  cases chs <;> simp [dropAll]

theorem heq_dropAll {n : Nat} {chs : List (List Int)}
    (heq : ∀ c ∈ chs, c.length = (chs.headD []).length) :
    ∀ c ∈ dropAll n chs, c.length = ((dropAll n chs).headD []).length := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  rw [headD_dropAll, List.length_drop, heq c' hc']

theorem chunkFrames_count (n : Nat) (chs : List (List Int)) :
    (chunkChannels n chs).length ≤ (chs.headD []).length := by
  fun_induction chunkChannels n chs with
  | case1 chs h => simp
  | case2 chs h ih =>
    rw [not_or] at h
    have hd := headD_dropAll n chs
    simp only [List.length_cons]
    omega

theorem chunkFrames_idx_mul (n : Nat) (chs : List (List Int)) :
    ∀ j, j < (chunkChannels n chs).length → j * n < (chs.headD []).length := by
  fun_induction chunkChannels n chs with
  | case1 chs h => intro j hj; simp at hj
  | case2 chs h ih =>
    rw [not_or] at h
    intro j hj
    match j with
    | 0 => simpa using Nat.pos_of_ne_zero h.1
    | j + 1 =>
      have hij := ih j (by simpa using hj)
      rw [headD_dropAll] at hij
      have : (j + 1) * n = j * n + n := Nat.succ_mul ..
      omega

private theorem eq_replicate_nil (chs : List (List Int))
    (h : ∀ c ∈ chs, c.length = 0) : chs = List.replicate chs.length [] := by
  induction chs with
  | nil => rfl
  | cons c t ih =>
    have hc : c = [] :=
      List.eq_nil_of_length_eq_zero (h c (List.mem_cons_self ..))
    simp only [List.length_cons, List.replicate_succ, hc]
    rw [← ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]

private theorem zipWith_takeAll_dropAll (n : Nat) :
    ∀ (l : List (List Int)),
      List.zipWith (· ++ ·) (takeAll n l) (dropAll n l) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [takeAll, dropAll, List.map_cons, List.zipWith_cons_cons,
      List.take_append_drop]
    simp only [takeAll, dropAll] at ih
    rw [ih]

/-- Reassembling the chunked frames recovers the channels. -/
theorem recombine_chunkChannels (n : Nat) (chs : List (List Int)) (hn : 0 < n) :
    (∀ c ∈ chs, c.length = (chs.headD []).length) →
    recombine chs.length (chunkChannels n chs) = chs := by
  fun_induction chunkChannels n chs with
  | case1 chs h =>
    intro heq
    have hzero : ∀ c ∈ chs, c.length = 0 := by
      intro c hc
      rcases h with h | h
      · rw [heq c hc, h]
      · omega
    show List.replicate chs.length [] = chs
    exact (eq_replicate_nil chs hzero).symm
  | case2 chs h ih =>
    intro heq
    show List.zipWith (· ++ ·) (takeAll n chs)
      (recombine chs.length (chunkChannels n (dropAll n chs))) = chs
    rw [show chs.length = (dropAll n chs).length from (length_dropAll n chs).symm,
      ih (heq_dropAll heq), zipWith_takeAll_dropAll]

/-- Every chunked frame is well-shaped and draws its samples from the
    original channels. -/
theorem chunkFrames_mem (n : Nat) (chs : List (List Int)) (hn : 0 < n) :
    (∀ c ∈ chs, c.length = (chs.headD []).length) →
    ∀ fr ∈ chunkChannels n chs,
      fr.length = chs.length ∧
      (∀ c ∈ fr, c.length = (fr.headD []).length) ∧
      1 ≤ (fr.headD []).length ∧ (fr.headD []).length ≤ n ∧
      (∀ c' ∈ fr, ∃ c ∈ chs, ∀ x ∈ c', x ∈ c) := by
  fun_induction chunkChannels n chs with
  | case1 chs h => intro _ fr hfr; simp at hfr
  | case2 chs h ih =>
    rw [not_or] at h
    intro heq fr hfr
    rcases List.mem_cons.mp hfr with rfl | hfr'
    · match chs, h with
      | c0 :: t, h =>
        simp only [List.headD_cons] at h heq
        refine ⟨by simp [takeAll], ?_, ?_, ?_, ?_⟩
        · intro c hc
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
          simp only [takeAll, List.map_cons, List.headD_cons,
            List.length_take]
          rw [heq c' hc']
        · simp only [takeAll, List.map_cons, List.headD_cons,
            List.length_take]
          omega
        · simp only [takeAll, List.map_cons, List.headD_cons,
            List.length_take]
          omega
        · intro c' hc'
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
          exact ⟨c, hc, fun x hx => List.mem_of_mem_take hx⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih (heq_dropAll heq) fr hfr'
      refine ⟨by rw [h1, length_dropAll], h2, h3, h4, ?_⟩
      intro c' hc'
      obtain ⟨c, hc, hsub⟩ := h5 c' hc'
      obtain ⟨corig, hcorig, rfl⟩ := List.mem_map.mp hc
      exact ⟨corig, hcorig, fun x hx => List.mem_of_mem_drop (hsub x hx)⟩

/-! ## Frame sequence lengths -/

theorem frame_write_length_pos (b : Nat) (strat : Bool) (num : Nat)
    (asg : Frame.ChannelAsg) (chs : List (List Int)) :
    0 < (Frame.write b strat num asg chs).length := by
  simp only [Frame.write, List.length_append, length_writeBits]
  omega

theorem writeFrames_length_ge (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    ∀ (frs : List (List (List Int))) (i : Nat),
      frs.length ≤ (writeFrames b varBlk blockSize chooser i frs).length := by
  intro frs
  induction frs with
  | nil => intro i; simp [writeFrames]
  | cons fr frs ih =>
    intro i
    have h1 := frame_write_length_pos b varBlk
      (if varBlk then i * blockSize else i) (chooser fr) fr
    have h2 := ih (i + 1)
    simp only [writeFrames, List.length_append, List.length_cons]
    omega

theorem writeFrames_length_dvd (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    ∀ (frs : List (List (List Int))) (i : Nat),
      8 ∣ (writeFrames b varBlk blockSize chooser i frs).length := by
  intro frs
  induction frs with
  | nil => intro i; simp [writeFrames]
  | cons fr frs ih =>
    intro i
    have h1 : 8 ∣ (Frame.body b varBlk (if varBlk then i * blockSize else i)
        (chooser fr) fr).length := alignToByte_dvd _
    have h2 := ih (i + 1)
    simp only [writeFrames, Frame.write, List.length_append, length_writeBits]
    omega

theorem writeStream_length_dvd (cfg : EncoderCfg) (a : Audio) :
    8 ∣ (writeStream cfg a).length := by
  have h := writeFrames_length_dvd a.bps cfg.variableBlocking cfg.blockSize
    cfg.chooser (chunkChannels cfg.blockSize a.channels) 0
  simp only [writeStream, writeStreamInfo, List.length_append, length_writeBits]
  omega

/-! ## STREAMINFO and metadata -/

theorem readStreamInfo_writeStreamInfo (bs sr ch b total md5 : Nat)
    (tail : BitStream) (hbs : bs < 2 ^ 16) (hsr : sr < 2 ^ 20)
    (hch1 : 1 ≤ ch) (hch8 : ch ≤ 8)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 32) (htot : total < 2 ^ 36) :
    readStreamInfo (writeStreamInfo bs sr ch b total md5 ++ tail)
      = some (⟨bs, bs, sr, ch, b, total⟩, tail) := by
  simp only [writeStreamInfo, readStreamInfo, List.append_assoc,
    readBits_writeBits _ _ _ hbs,
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 24),
    readBits_writeBits _ _ _ hsr,
    readBits_writeBits _ _ _ (show ch - 1 < 2 ^ 3 by omega),
    readBits_writeBits _ _ _ (by omega : b - 1 < 2 ^ 5),
    readBits_writeBits _ _ _ htot,
    readBits_writeBits_append 128 md5,
    Option.some.injEq, Prod.mk.injEq, Info.mk.injEq]
  refine ⟨⟨trivial, trivial, trivial, by omega, by omega, trivial⟩, trivial⟩

theorem readMeta_spec (fuel : Nat) (bs sr ch b total md5 : Nat)
    (tail : BitStream) (hbs : bs < 2 ^ 16) (hsr : sr < 2 ^ 20)
    (hch1 : 1 ≤ ch) (hch8 : ch ≤ 8)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 32) (htot : total < 2 ^ 36) :
    readMeta fuel (writeBits 1 1 ++ (writeBits 7 0 ++ (writeBits 24 34 ++
        (writeStreamInfo bs sr ch b total md5 ++ tail))))
      = some (⟨bs, bs, sr, ch, b, total⟩, tail) := by
  simp only [readMeta,
    readBits_writeBits _ _ _ (by omega : 1 < 2 ^ 1),
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 7),
    readBits_writeBits _ _ _ (by omega : 34 < 2 ^ 24),
    readStreamInfo_writeStreamInfo bs sr ch b total md5 tail hbs hsr hch1
      hch8 hb1 hb2 htot]
  rw [if_pos (by trivial), if_pos (by trivial), if_pos (by trivial)]

/-! ## Frame loop -/

theorem readFrames_writeFrames (b0 b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg)
    (hb : Frame.bpsOfCode (Frame.bpsCode b) b0 = some b) :
    ∀ (frs : List (List (List Int))) (i fuel : Nat),
      frs.length ≤ fuel →
      (∀ j, j < frs.length →
        (if varBlk then (i + j) * blockSize else i + j) < 2 ^ 36) →
      (∀ fr ∈ frs, 1 ≤ (fr.headD []).length ∧ (fr.headD []).length ≤ 65536 ∧
        (chooser fr).Valid b (fr.headD []).length fr) →
      readFrames b0 fuel (writeFrames b varBlk blockSize chooser i frs)
        = some frs := by
  intro frs
  induction frs with
  | nil =>
    intro i fuel _ _ _
    cases fuel <;> rfl
  | cons fr frs ih =>
    intro i fuel hfuel hnum hv
    match fuel with
    | 0 => simp only [List.length_cons] at hfuel; omega
    | fuel + 1 =>
      obtain ⟨hl1, hl2, hval⟩ := hv fr (List.mem_cons_self ..)
      have hnum0 : (if varBlk then i * blockSize else i) < 2 ^ 36 := by
        have h0 := hnum 0 (by simp)
        simpa using h0
      have hne : Frame.write b varBlk (if varBlk then i * blockSize else i)
          (chooser fr) fr
          ++ writeFrames b varBlk blockSize chooser (i + 1) frs ≠ [] := by
        apply List.ne_nil_of_length_pos
        have := frame_write_length_pos b varBlk
          (if varBlk then i * blockSize else i) (chooser fr) fr
        simp only [List.length_append]
        omega
      have hih := ih (i + 1) fuel
        (by simp only [List.length_cons] at hfuel; omega)
        (by
          intro j hj
          have := hnum (j + 1) (by simp only [List.length_cons]; omega)
          simpa [show i + (j + 1) = i + 1 + j from by omega] using this)
        (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      simp only [writeFrames, readFrames, if_neg hne,
        Frame.read_write b0 b varBlk (if varBlk then i * blockSize else i)
          (chooser fr) fr _ hb hnum0 hl1 hl2 hval,
        hih]

/-! ## The reference capstone -/

/-- **`decodeReference ∘ encode = id` over the full option space**: every
    well-formed audio, every block size 16–65535, both numbering
    strategies, and every valid channel-assignment heuristic. Heuristic
    knobs are correctness-irrelevant by construction: they choose *which*
    valid stream is emitted, never whether this theorem holds. -/
theorem decodeReference_encode (cfg : EncoderCfg) (a : Audio)
    (hwf : a.WellFormed)
    (hbs1 : 16 ≤ cfg.blockSize) (hbs2 : cfg.blockSize ≤ 65535)
    (hsr : a.sampleRate < 2 ^ 20) (htot : a.numSamples < 2 ^ 36)
    (hchooser : ∀ fr : List (List Int),
      fr.length = a.channels.length →
      (∀ c ∈ fr, c.length = (fr.headD []).length) →
      1 ≤ (fr.headD []).length → (fr.headD []).length ≤ cfg.blockSize →
      (∀ c ∈ fr, ∀ x ∈ c, FitsSInt a.bps x) →
      (cfg.chooser fr).Valid a.bps (fr.headD []).length fr) :
    decodeReference (encode cfg a) = some a.channels := by
  obtain ⟨hch1, hch8, hb1, hb2, heq, hfit⟩ := hwf
  have heq' : ∀ c ∈ a.channels, c.length = (a.channels.headD []).length := heq
  have hframes : ∀ fr ∈ chunkChannels cfg.blockSize a.channels,
      1 ≤ (fr.headD []).length ∧ (fr.headD []).length ≤ 65536 ∧
      (cfg.chooser fr).Valid a.bps (fr.headD []).length fr := by
    intro fr hfr
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      chunkFrames_mem cfg.blockSize a.channels (by omega) heq' fr hfr
    refine ⟨h3, by omega, ?_⟩
    apply hchooser fr h1 h2 h3 (by omega)
    intro c hc x hx
    obtain ⟨corig, hcorig, hsub⟩ := h5 c hc
    exact hfit corig hcorig x (hsub x hx)
  unfold encode decodeReference
  rw [bytesToBits_bitsToBytes _ (writeStream_length_dvd cfg a)]
  unfold writeStream
  simp only [List.append_assoc,
    readBits_writeBits _ _ _ (by omega : 0x664C6143 < 2 ^ 32),
    readMeta_spec _ cfg.blockSize a.sampleRate a.channels.length a.bps
      a.numSamples _ _ (by omega) hsr hch1 hch8 hb1 hb2 htot]
  rw [if_pos (by trivial)]
  simp only [readFrames_writeFrames a.bps a.bps cfg.variableBlocking
    cfg.blockSize cfg.chooser (Frame.bpsOfCode_bpsCode a.bps)
    (chunkChannels cfg.blockSize a.channels) 0
    ((writeFrames a.bps cfg.variableBlocking cfg.blockSize cfg.chooser 0
      (chunkChannels cfg.blockSize a.channels)).length + 1)
    (by
      have := writeFrames_length_ge a.bps cfg.variableBlocking cfg.blockSize
        cfg.chooser (chunkChannels cfg.blockSize a.channels) 0
      omega)
    (by
      intro j hj
      have hmul := chunkFrames_idx_mul cfg.blockSize a.channels j hj
      have hle := chunkFrames_count cfg.blockSize a.channels
      unfold Audio.numSamples at htot
      have hz : (0 + j) * cfg.blockSize = j * cfg.blockSize := by
        rw [Nat.zero_add]
      split
      · omega
      · omega)
    hframes]
  rw [recombine_chunkChannels cfg.blockSize a.channels (by omega) heq']

end Flac.Stream
