import Flac.Native.Stream
import Flac.Spec.Frame

/-!
# Stream round-trip — the reference capstone

For every well-formed audio (1–8 equal-length channels, bit depth 1–32,
in-range samples), every block size 16–4608, both numbering strategies,
and *every* channel-assignment/subframe heuristic — valid or not, thanks
to the encoder's certificate check with VERBATIM fallback — decoding the
encoded stream returns the original audio exactly:
`decodeReference_encode` at the bottom of this file. (Block sizes stop at
4608 because the decoder bounds decoded output against input size to
reject decompression bombs, and above 4608 an all-CONSTANT eight-channel
stream can legitimately exceed that bound.)
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
    (cfg.safeChooser a.bps) (chunkChannels cfg.blockSize a.channels) 0
  simp only [writeStream, writeStreamInfo, List.length_append, length_writeBits]
  omega

/-! ## The decoded-output budget

The decoder rejects streams whose decoded size passes
`decodeBudget bytes = decodeAmpl · bytes.size + decodeFloor`
(decompression bombs, audit finding P2). For the round-trip capstone to
survive *unconditionally*, the encoder's own output must always fit the
budget — which needs a lower bound on what a frame costs to *write*
(`frame_write_length_lb`: at least `80 + 8·ch` bits) against an upper
bound on what it costs to *decode* (`frameCost ≤ 2·ch·blockSize`). The
two meet exactly when `16 · ch · blockSize ≤ decodeAmpl · (80 + 8·ch)`,
which for 1–8 channels holds whenever `blockSize ≤ 4608` — the bound the
configurable-block-size guards enforce. -/

/-- The budgeted frame loop is the plain frame loop with one cumulative
    cost check on a `some` result. -/
theorem readFramesB_eq (b0 : Nat) :
    ∀ (budget fuel : Nat) (s : BitStream),
      readFramesB b0 budget fuel s
        = (readFrames b0 fuel s).bind
            (fun frs => if frameCostTotal frs ≤ budget then some frs else none) := by
  intro budget fuel
  induction fuel generalizing budget with
  | zero =>
    intro s
    unfold readFramesB readFrames
    by_cases h : s = []
    · rw [if_pos h]
      simp [frameCostTotal]
    · rw [if_neg h]
      rfl
  | succ fuel ih =>
    intro s
    unfold readFramesB readFrames
    by_cases h : s = []
    · rw [if_pos h, if_pos h]
      simp [frameCostTotal]
    · rw [if_neg h, if_neg h]
      match Frame.read b0 s with
      | none => rfl
      | some (chs, s') =>
        dsimp only
        rw [ih]
        by_cases hc : frameCost chs ≤ budget
        · rw [if_pos hc]
          match readFrames b0 fuel s' with
          | none => rfl
          | some rest =>
            show (match (if frameCostTotal rest ≤ budget - frameCost chs
                then some rest else none) with
              | none => none
              | some rest => some (chs :: rest))
              = if frameCostTotal (chs :: rest) ≤ budget then some (chs :: rest)
                else none
            have htot : frameCostTotal (chs :: rest)
                = frameCost chs + frameCostTotal rest := by
              simp [frameCostTotal]
            by_cases hr : frameCostTotal rest ≤ budget - frameCost chs
            · rw [if_pos hr, if_pos (by omega)]
            · rw [if_neg hr, if_neg (by omega)]
        · rw [if_neg hc]
          match readFrames b0 fuel s' with
          | none => rfl
          | some rest =>
            show none = if frameCostTotal (chs :: rest) ≤ budget
                then some (chs :: rest) else none
            have htot : frameCostTotal (chs :: rest)
                = frameCost chs + frameCostTotal rest := by
              simp [frameCostTotal]
            rw [if_neg (by omega)]

private theorem zipWith_append_lengths_le :
    ∀ (l₁ l₂ : List (List Int)),
      ((List.zipWith (· ++ ·) l₁ l₂).map (·.length)).sum
        ≤ (l₁.map (·.length)).sum + (l₂.map (·.length)).sum := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons c l₁ ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons d l₂ =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons,
        List.length_append]
      have := ih l₂
      omega

/-- Reassembled channels never hold more samples than the frames that
    produced them cost against the budget. -/
theorem recombine_total_le (ch : Nat) :
    ∀ (frs : List (List (List Int))),
      2 * ((recombine ch frs).map (·.length)).sum ≤ frameCostTotal frs := by
  intro frs
  induction frs with
  | nil =>
    show 2 * ((List.replicate ch []).map (·.length)).sum ≤ _
    simp [frameCostTotal, List.map_replicate]
  | cons fr frs ih =>
    have hz := zipWith_append_lengths_le fr (recombine ch frs)
    have htot : frameCostTotal (fr :: frs)
        = frameCost fr + frameCostTotal frs := by simp [frameCostTotal]
    unfold frameCost at htot
    show 2 * ((List.zipWith (· ++ ·) fr (recombine ch frs)).map (·.length)).sum
      ≤ _
    omega

/-- **The reference decoder cannot amplify**: whatever it accepts, the
    decoded samples (at two budget units apiece) are bounded linearly in
    the input size. This is the theorem audit finding P2 observed was
    missing — `decodeReference_encode` bounds nothing, because it only
    speaks about the encoder's image. -/
theorem decodeReference_size_le {bytes : ByteArray} {a : Audio}
    (h : decodeReference bytes = some a) :
    2 * (a.channels.map (·.length)).sum ≤ decodeBudget bytes := by
  unfold decodeReference at h
  dsimp only at h
  match h1 : readBits 32 (bytesToBits bytes) with
  | none => rw [h1] at h; exact absurd h (by simp)
  | some (marker, s) =>
    rw [h1] at h
    dsimp only at h
    by_cases hm : marker = 0x664C6143
    case neg => rw [if_neg hm] at h; exact absurd h (by simp)
    rw [if_pos hm] at h
    match h2 : readMeta s.length s with
    | none => rw [h2] at h; exact absurd h (by simp)
    | some (si, s') =>
      rw [h2] at h
      dsimp only at h
      rw [readFramesB_eq] at h
      match h3 : readFrames si.bps (s'.length + 1) s' with
      | none => rw [h3] at h; exact absurd h (by simp)
      | some frames =>
        rw [h3] at h
        dsimp only [Option.bind_some] at h
        by_cases hc : frameCostTotal frames ≤ decodeBudget bytes
        case neg => rw [if_neg hc] at h; exact absurd h (by simp)
        rw [if_pos hc] at h
        injection h with h
        rw [← h]
        have := recombine_total_le si.channels frames
        show 2 * ((recombine si.channels frames).map (·.length)).sum ≤ _
        omega

/-- A coded number is at least one byte. -/
private theorem utf8_write_length_ge (n : Nat) :
    8 ≤ (Utf8Num.write n).length := by
  have hconts : ∀ (k v : Nat), (Utf8Num.writeConts k v).length = 8 * k := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      simp only [Utf8Num.writeConts, Utf8Num.writeContByte, List.length_append,
        length_writeBits, ih]
      omega
  unfold Utf8Num.write
  repeat' split
  all_goals simp [hconts, length_writeBits]

/-- A subframe costs at least its one-byte header. -/
private theorem subframe_write_length_ge (b : Nat) (sc : Subframe.SubCfg)
    (xs : List Int) : 8 ≤ (Subframe.write b sc xs).length := by
  unfold Subframe.write
  split <;> simp <;> omega

/-- Each channel's subframe costs at least a byte. -/
private theorem writeSubframes_length_ge
    (plan : List ((Nat × Subframe.SubCfg) × List Int)) :
    8 * plan.length ≤ (Frame.writeSubframes plan).length := by
  induction plan with
  | nil => simp [Frame.writeSubframes]
  | cons p plan ih =>
    have h1 := subframe_write_length_ge p.1.1 p.1.2 p.2
    simp only [Frame.writeSubframes, List.flatMap_cons, List.length_append,
      List.length_cons]
    simp only [Frame.writeSubframes] at ih
    omega

/-- A valid channel assignment plans exactly one subframe per channel. -/
private theorem subframePlan_length_of_valid {asg : Frame.ChannelAsg}
    {b bs : Nat} {chs : List (List Int)} (hv : asg.Valid b bs chs) :
    (Frame.subframePlan b asg chs).length = chs.length := by
  obtain ⟨-, hm⟩ := hv
  rcases asg with cfgs | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨c0, c1⟩
  · obtain ⟨-, -, hlen, -⟩ := hm
    simp [Frame.subframePlan, List.length_zip, hlen]
  all_goals
    rcases chs with _ | ⟨l, _ | ⟨r, _ | t⟩⟩ <;> first
      | exact hm.elim
      | rfl

/-- **What a frame costs to write**: at least 80 bits (32 fixed header
    fields, a coded number, the explicit 16-bit block size, CRC-8,
    CRC-16), plus at least a byte per planned subframe. -/
theorem frame_write_length_lb (b : Nat) (strat : Bool) (num : Nat)
    (asg : Frame.ChannelAsg) (chs : List (List Int)) :
    80 + 8 * (Frame.subframePlan b asg chs).length
      ≤ (Frame.write b strat num asg chs).length := by
  have hutf := utf8_write_length_ge num
  have hsub := writeSubframes_length_ge (Frame.subframePlan b asg chs)
  simp only [Frame.write, Frame.body, List.length_append, length_writeBits,
    length_alignToByte, Frame.writeHeader, Frame.headerCore]
  omega

/-- Frame-sequence form of `frame_write_length_lb`, under the per-frame
    validity the encoder's sanitized chooser guarantees. -/
theorem writeFrames_length_lb (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    ∀ (frs : List (List (List Int))) (i : Nat),
      (∀ fr ∈ frs, (chooser fr).Valid b (fr.headD []).length fr) →
      (frs.map (fun fr => 80 + 8 * fr.length)).sum
        ≤ (writeFrames b varBlk blockSize chooser i frs).length := by
  intro frs
  induction frs with
  | nil => intro i _; simp [writeFrames]
  | cons fr frs ih =>
    intro i hv
    have h1 := frame_write_length_lb b varBlk
      (if varBlk then i * blockSize else i) (chooser fr) fr
    rw [subframePlan_length_of_valid (hv fr (List.mem_cons_self ..))] at h1
    have h2 := ih (i + 1) (fun f hf => hv f (List.mem_cons_of_mem _ hf))
    simp only [writeFrames, List.length_append, List.map_cons, List.sum_cons]
    omega

/-- Chunking covers the samples: `numSamples ≤ blockSize · frame count`. -/
theorem chunkFrames_count_mul (n : Nat) (chs : List (List Int)) (hn : 0 < n) :
    (chs.headD []).length ≤ n * (chunkChannels n chs).length := by
  fun_induction chunkChannels n chs with
  | case1 chs h =>
    rcases h with h | h <;> simp only [List.length_nil] <;> omega
  | case2 chs h ih =>
    rw [not_or] at h
    have hd := headD_dropAll n chs
    simp only [List.length_cons, Nat.mul_succ]
    omega

/-- **What a frame sequence costs to decode**: with every channel at most
    `n` samples and exactly `ch` channels per frame, at most `2·ch·n` per
    frame. -/
private theorem sum_lengths_le (fr : List (List Int)) (n : Nat)
    (hle : ∀ c ∈ fr, c.length ≤ n) :
    (fr.map (·.length)).sum ≤ fr.length * n := by
  induction fr with
  | nil => simp
  | cons c fr ih =>
    have hc := hle c (List.mem_cons_self ..)
    have ht := ih (fun c' hc' => hle c' (List.mem_cons_of_mem _ hc'))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem frameCostTotal_le (frs : List (List (List Int))) (ch n : Nat)
    (h : ∀ fr ∈ frs, fr.length = ch ∧ ∀ c ∈ fr, c.length ≤ n) :
    frameCostTotal frs ≤ frs.length * (2 * ch * n) := by
  induction frs with
  | nil => simp [frameCostTotal]
  | cons fr frs ih =>
    obtain ⟨hlen, hle⟩ := h fr (List.mem_cons_self ..)
    have h2 := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    have hfr : frameCost fr ≤ 2 * ch * n := by
      unfold frameCost
      calc 2 * (fr.map (·.length)).sum
          ≤ 2 * (fr.length * n) :=
            Nat.mul_le_mul_left 2 (sum_lengths_le fr n hle)
        _ = 2 * ch * n := by rw [hlen, Nat.mul_assoc]
    calc frameCostTotal (fr :: frs)
        = frameCost fr + frameCostTotal frs := by simp [frameCostTotal]
      _ ≤ 2 * ch * n + frs.length * (2 * ch * n) := Nat.add_le_add hfr h2
      _ = (frs.length + 1) * (2 * ch * n) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      _ = (fr :: frs).length * (2 * ch * n) := by rw [List.length_cons]

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
        (chooser fr).Valid b (fr.headD []).length fr ∧
        ∀ c ∈ fr, ∀ x ∈ c, FitsSInt b x) →
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
      obtain ⟨hl1, hl2, hval, hfitf⟩ := hv fr (List.mem_cons_self ..)
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
          (chooser fr) fr _ hb hnum0 hl1 hl2 hval hfitf,
        hih]

private theorem mem_zip_map_self {α β : Type} (f : α → β) :
    ∀ (l : List α) (p : β × α), p ∈ (l.map f).zip l → p.1 = f p.2 ∧ p.2 ∈ l := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons a l ih =>
    intro p hp
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨rfl, by simp⟩
    · obtain ⟨h1, h2⟩ := ih p hp
      exact ⟨h1, by simp [h2]⟩

/-- Sanitized choices are valid outright: either the heuristic's own
    certificate checks, or the VERBATIM fallback's certificate holds on
    any fitting audio. -/
theorem orVerbatim_valid {asg : Frame.ChannelAsg} {b bs : Nat}
    {chs : List (List Int)}
    (hb : 1 ≤ b) (hlen : ∀ c ∈ chs, c.length = bs)
    (hch1 : 1 ≤ chs.length) (hch8 : chs.length ≤ 8)
    (hfit : ∀ c ∈ chs, ∀ x ∈ c, FitsSInt b x) :
    (asg.orVerbatim b bs chs).Valid b bs chs := by
  unfold Frame.ChannelAsg.orVerbatim
  split
  case isTrue h => exact h
  case isFalse =>
    refine ⟨hlen, by simpa using hch1, by simpa using hch8, by simp, ?_⟩
    intro p hp
    obtain ⟨h1, h2⟩ := mem_zip_map_self _ _ p hp
    rw [h1]
    refine ⟨by show 0 < b; omega, fun x _ => ⟨x, (Int.one_mul x).symm⟩, ?_⟩
    show ∀ x ∈ p.2.map (shiftDown 0), FitsSInt (b - 0) x
    rw [map_shiftDown_zero, Nat.sub_zero]
    exact hfit p.2 h2

/-! ## The reference capstone -/

private theorem length_byteListToBits' (l : List UInt8) :
    (byteListToBits l).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [byteListToBits_cons]
    simp only [List.length_append, ih, byteToBits, length_writeBits,
      List.length_cons]
    omega

private theorem sum_map_const {α : Type _} (l : List α) (f : α → Nat) (v : Nat)
    (h : ∀ x ∈ l, f x = v) : (l.map f).sum = l.length * v := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      h x (List.mem_cons_self ..), List.length_cons, Nat.add_mul,
      Nat.one_mul, Nat.add_comm]

/-- **The encoder's output always fits the decoder's output budget** —
    what keeps the round-trip capstone hypothesis-free in the presence of
    the decompression-bomb cap. Writing a frame costs at least
    `80 + 8·ch` bits (`frame_write_length_lb`), decoding it at most
    `2·ch·blockSize` budget, and for `ch ≤ 8`, `blockSize ≤ 4608` the
    write side wins at `decodeAmpl = 4096`. -/
theorem encode_cost_le_budget (cfg : EncoderCfg) (a : Audio)
    (hch1 : 1 ≤ a.channels.length) (hch8 : a.channels.length ≤ 8)
    (hb1 : 1 ≤ a.bps)
    (heq' : ∀ c ∈ a.channels, c.length = (a.channels.headD []).length)
    (hfit : ∀ c ∈ a.channels, ∀ x ∈ c, FitsSInt a.bps x)
    (hbs1 : 16 ≤ cfg.blockSize) (hbs2 : cfg.blockSize ≤ 4608) :
    frameCostTotal (chunkChannels cfg.blockSize a.channels)
      ≤ decodeBudget (bitsToBytes (writeStream cfg a)) := by
  -- decode side: each frame costs at most 2·ch·blockSize
  have hcost : frameCostTotal (chunkChannels cfg.blockSize a.channels)
      ≤ (chunkChannels cfg.blockSize a.channels).length * (2 * a.channels.length * cfg.blockSize) := by
    apply frameCostTotal_le
    intro fr hfr
    obtain ⟨h1, h2, -, h4, -⟩ :=
      chunkFrames_mem cfg.blockSize a.channels (by omega) heq' fr hfr
    exact ⟨h1, fun c hc => by rw [h2 c hc]; exact h4⟩
  -- write side: each frame costs at least 80 + 8·ch bits
  have hvalid : ∀ fr ∈ (chunkChannels cfg.blockSize a.channels),
      (cfg.safeChooser a.bps fr).Valid a.bps (fr.headD []).length fr := by
    intro fr hfr
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      chunkFrames_mem cfg.blockSize a.channels (by omega) heq' fr hfr
    have hfitfr : ∀ c ∈ fr, ∀ x ∈ c, FitsSInt a.bps x := by
      intro c hc x hx
      obtain ⟨corig, hcorig, hsub⟩ := h5 c hc
      exact hfit corig hcorig x (hsub x hx)
    exact orVerbatim_valid (by omega) h2 (by omega) (by omega) hfitfr
  have hwlb := writeFrames_length_lb a.bps cfg.variableBlocking cfg.blockSize
    (cfg.safeChooser a.bps) (chunkChannels cfg.blockSize a.channels) 0 hvalid
  have hsum : ((chunkChannels cfg.blockSize a.channels).map (fun fr => 80 + 8 * fr.length)).sum
      = (chunkChannels cfg.blockSize a.channels).length * (80 + 8 * a.channels.length) := by
    apply sum_map_const
    intro fr hfr
    obtain ⟨h1, -, -, -, -⟩ :=
      chunkFrames_mem cfg.blockSize a.channels (by omega) heq' fr hfr
    rw [h1]
  rw [hsum] at hwlb
  -- the stream is at least its frames
  have hstream : (writeFrames a.bps cfg.variableBlocking cfg.blockSize
        (cfg.safeChooser a.bps) 0 (chunkChannels cfg.blockSize a.channels)).length
      ≤ (writeStream cfg a).length := by
    simp only [writeStream, writeStreamInfo, List.length_append,
      length_writeBits]
    omega
  -- bits to bytes
  have hsz : 8 * (bitsToBytes (writeStream cfg a)).size
      = (writeStream cfg a).length := by
    have hlen := congrArg List.length
      (bytesToBits_bitsToBytes _ (writeStream_length_dvd cfg a))
    have hb : (bytesToBits (bitsToBytes (writeStream cfg a))).length
        = 8 * (bitsToBytes (writeStream cfg a)).size := by
      show (byteListToBits _).length = _
      rw [length_byteListToBits', Array.length_toList]
      rfl
    omega
  -- per-frame: the decode cost is within 512 · the write cost
  have hchbs : 2 * a.channels.length * cfg.blockSize
      ≤ 512 * (80 + 8 * a.channels.length) := by
    have h := Nat.mul_le_mul_left (2 * a.channels.length) hbs2
    omega
  have hmul : (chunkChannels cfg.blockSize a.channels).length * (2 * a.channels.length * cfg.blockSize)
      ≤ 512 * ((chunkChannels cfg.blockSize a.channels).length * (80 + 8 * a.channels.length)) := by
    calc (chunkChannels cfg.blockSize a.channels).length * (2 * a.channels.length * cfg.blockSize)
        ≤ (chunkChannels cfg.blockSize a.channels).length * (512 * (80 + 8 * a.channels.length)) :=
          Nat.mul_le_mul_left _ hchbs
      _ = 512 * ((chunkChannels cfg.blockSize a.channels).length * (80 + 8 * a.channels.length)) := by
          rw [Nat.mul_left_comm]
  have h512 := Nat.mul_le_mul_left 512 hwlb
  unfold decodeBudget decodeAmpl decodeFloor
  omega

/-- **`decodeReference ∘ encode = id` over the full option space**: every
    well-formed audio, every block size 16–4608, both numbering
    strategies, and *every* channel-assignment heuristic — the encoder
    checks each heuristic choice's (decidable) certificate and falls back
    to VERBATIM when it fails, so heuristics are correctness-irrelevant
    outright: they choose *which* valid stream is emitted, never whether
    this theorem holds. Block sizes stop at 4608 because the decoder
    rejects decompression bombs (`decodeBudget`), and above 4608 an
    all-CONSTANT eight-channel stream can legitimately exceed that
    budget. -/
theorem decodeReference_encode (cfg : EncoderCfg) (a : Audio)
    (hwf : a.WellFormed)
    (hbs1 : 16 ≤ cfg.blockSize) (hbs2 : cfg.blockSize ≤ 4608) :
    decodeReference (Unchecked.encode cfg a) = some a := by
  obtain ⟨hch1, hch8, hb1, hb2, heq, hfit, hsr, htot⟩ := hwf
  have heq' : ∀ c ∈ a.channels, c.length = (a.channels.headD []).length := heq
  have hframes : ∀ fr ∈ chunkChannels cfg.blockSize a.channels,
      1 ≤ (fr.headD []).length ∧ (fr.headD []).length ≤ 65536 ∧
      (cfg.safeChooser a.bps fr).Valid a.bps (fr.headD []).length fr ∧
      ∀ c ∈ fr, ∀ x ∈ c, FitsSInt a.bps x := by
    intro fr hfr
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      chunkFrames_mem cfg.blockSize a.channels (by omega) heq' fr hfr
    have hfitfr : ∀ c ∈ fr, ∀ x ∈ c, FitsSInt a.bps x := by
      intro c hc x hx
      obtain ⟨corig, hcorig, hsub⟩ := h5 c hc
      exact hfit corig hcorig x (hsub x hx)
    exact ⟨h3, by omega,
      orVerbatim_valid (by omega) h2 (by omega) (by omega) hfitfr, hfitfr⟩
  have hcap := encode_cost_le_budget cfg a hch1 hch8 hb1 heq' hfit hbs1 hbs2
  unfold Unchecked.encode decodeReference
  rw [bytesToBits_bitsToBytes _ (writeStream_length_dvd cfg a)]
  unfold writeStream
  unfold writeStream at hcap
  simp only [List.append_assoc] at hcap
  simp only [List.append_assoc,
    readBits_writeBits _ _ _ (by omega : 0x664C6143 < 2 ^ 32),
    readMeta_spec _ cfg.blockSize a.sampleRate a.channels.length a.bps
      a.numSamples _ _ (by omega) hsr hch1 hch8 hb1 hb2 htot]
  rw [if_pos (by trivial)]
  rw [readFramesB_eq]
  simp only [readFrames_writeFrames a.bps a.bps cfg.variableBlocking
    cfg.blockSize (cfg.safeChooser a.bps) (Frame.bpsOfCode_bpsCode a.bps)
    (chunkChannels cfg.blockSize a.channels) 0
    ((writeFrames a.bps cfg.variableBlocking cfg.blockSize
      (cfg.safeChooser a.bps) 0
      (chunkChannels cfg.blockSize a.channels)).length + 1)
    (by
      have := writeFrames_length_ge a.bps cfg.variableBlocking cfg.blockSize
        (cfg.safeChooser a.bps) (chunkChannels cfg.blockSize a.channels) 0
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
    hframes, Option.bind_some]
  rw [if_pos hcap]
  dsimp only
  rw [recombine_chunkChannels cfg.blockSize a.channels (by omega) heq']

/-- The array serializer on decoded channels is the list serializer on the
    same samples: `pcmBytes` is `pcmBytesA` after a conversion, and the
    conversion cancels. -/
theorem pcmBytesA_eq (b : Nat) (arrs : List (Array Int)) :
    pcmBytesA b arrs = pcmBytes b (arrs.map (·.toList)) := by
  unfold pcmBytes
  rw [List.map_map]
  congr 1
  induction arrs with
  | nil => rfl
  | cons a as ih =>
    show a :: as = a.toList.toArray :: List.map _ as
    rw [Array.toArray_toList, ← ih]

end Flac.Stream
