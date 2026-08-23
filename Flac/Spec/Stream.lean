import Flac.Native.Stream
import Flac.Spec.Frame

/-!
# L6 (M2 profile) — stream round-trip keystone

**The first `decodeReference ∘ encode` theorem** (PLAN.md §8, M2): for
every mono PCM stream, every bit depth 1–32, every block size 16–65535,
and *every* subframe-choice heuristic that returns valid configurations,
decoding the encoded stream returns the original samples exactly.
-/

namespace Flac.Stream

open Flac.Bits

/-! ## Chunking -/

theorem chunkFixed_flatten (n : Nat) (xs : List Int) (hn : 0 < n) :
    (chunkFixed n xs).flatten = xs := by
  fun_induction chunkFixed n xs with
  | case1 xs h =>
    have hx : xs = [] := by
      rcases h with h | h
      · exact h
      · exact absurd h (by omega)
    subst hx; rfl
  | case2 xs h ih =>
    simp only [List.flatten_cons, ih, List.take_append_drop]

theorem chunkFixed_mem (n : Nat) (xs : List Int) :
    ∀ blk ∈ chunkFixed n xs,
      (1 ≤ blk.length ∧ blk.length ≤ n) ∧ ∀ x ∈ blk, x ∈ xs := by
  fun_induction chunkFixed n xs with
  | case1 xs h => intro blk hblk; simp at hblk
  | case2 xs h ih =>
    intro blk hblk
    have hx : xs ≠ [] := fun hc => h (Or.inl hc)
    have hn : n ≠ 0 := fun hc => h (Or.inr hc)
    have hxlen : 0 < xs.length := List.length_pos_iff.mpr hx
    rcases List.mem_cons.mp hblk with rfl | hblk'
    · refine ⟨⟨?_, ?_⟩, fun x hx => List.mem_of_mem_take hx⟩ <;>
        simp only [List.length_take] <;> omega
    · obtain ⟨hb, hmem⟩ := ih blk hblk'
      exact ⟨hb, fun x hx => List.mem_of_mem_drop (hmem x hx)⟩

theorem chunkFixed_count (n : Nat) (xs : List Int) :
    (chunkFixed n xs).length ≤ xs.length := by
  fun_induction chunkFixed n xs with
  | case1 xs h => simp
  | case2 xs h ih =>
    have hx : xs ≠ [] := fun hc => h (Or.inl hc)
    have hn : n ≠ 0 := fun hc => h (Or.inr hc)
    have hxlen : 0 < xs.length := List.length_pos_iff.mpr hx
    simp only [List.length_cons, List.length_drop] at ih ⊢
    omega

/-! ## Frame sequence lengths -/

theorem frame_write_length_pos (b idx : Nat) (cfg : Subframe.SubCfg)
    (xs : List Int) : 0 < (Frame.write b idx cfg xs).length := by
  simp only [Frame.write, List.length_append, length_writeBits]
  omega

theorem writeFrames_length_ge (b : Nat) (chooser : List Int → Subframe.SubCfg) :
    ∀ (blks : List (List Int)) (idx : Nat),
      blks.length ≤ (writeFrames b chooser idx blks).length := by
  intro blks
  induction blks with
  | nil => intro idx; simp [writeFrames]
  | cons blk blks ih =>
    intro idx
    have h1 := frame_write_length_pos b idx (chooser blk) blk
    have h2 := ih (idx + 1)
    simp only [writeFrames, List.length_append, List.length_cons]
    omega

theorem writeFrames_length_dvd (b : Nat) (chooser : List Int → Subframe.SubCfg) :
    ∀ (blks : List (List Int)) (idx : Nat),
      8 ∣ (writeFrames b chooser idx blks).length := by
  intro blks
  induction blks with
  | nil => intro idx; simp [writeFrames]
  | cons blk blks ih =>
    intro idx
    have h1 : 8 ∣ (Frame.body b idx (chooser blk) blk).length :=
      alignToByte_dvd _
    have h2 := ih (idx + 1)
    simp only [writeFrames, Frame.write, List.length_append, length_writeBits]
    omega

theorem writeStream_length_dvd (cfg : EncoderCfg) (pcm : List Int) :
    8 ∣ (writeStream cfg pcm).length := by
  have h := writeFrames_length_dvd cfg.bps cfg.chooser (chunkFixed cfg.blockSize pcm) 0
  simp only [writeStream, writeStreamInfo, List.length_append, length_writeBits]
  omega

/-! ## STREAMINFO and metadata -/

theorem readStreamInfo_writeStreamInfo (bs sr b total md5 : Nat)
    (tail : BitStream) (hbs : bs < 2 ^ 16) (hsr : sr < 2 ^ 20)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 32) (htot : total < 2 ^ 36) :
    readStreamInfo (writeStreamInfo bs sr b total md5 ++ tail)
      = some (⟨bs, bs, sr, 1, b, total⟩, tail) := by
  simp only [writeStreamInfo, readStreamInfo, List.append_assoc,
    readBits_writeBits _ _ _ hbs,
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 24),
    readBits_writeBits _ _ _ hsr,
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 3),
    readBits_writeBits _ _ _ (by omega : b - 1 < 2 ^ 5),
    readBits_writeBits _ _ _ htot,
    readBits_writeBits_append 128 md5,
    Option.some.injEq, Prod.mk.injEq, Info.mk.injEq]
  refine ⟨⟨trivial, trivial, trivial, trivial, by omega, trivial⟩, trivial⟩

theorem readMeta_spec (fuel : Nat) (bs sr b total md5 : Nat) (tail : BitStream)
    (hbs : bs < 2 ^ 16) (hsr : sr < 2 ^ 20)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 32) (htot : total < 2 ^ 36) :
    readMeta fuel (writeBits 1 1 ++ (writeBits 7 0 ++ (writeBits 24 34 ++
        (writeStreamInfo bs sr b total md5 ++ tail))))
      = some (⟨bs, bs, sr, 1, b, total⟩, tail) := by
  simp only [readMeta,
    readBits_writeBits _ _ _ (by omega : 1 < 2 ^ 1),
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 7),
    readBits_writeBits _ _ _ (by omega : 34 < 2 ^ 24),
    readStreamInfo_writeStreamInfo bs sr b total md5 tail hbs hsr hb1 hb2 htot]
  rw [if_pos (by trivial), if_pos (by trivial), if_pos (by trivial)]

/-! ## Frame loop -/

theorem readFrames_writeFrames (b0 b : Nat)
    (chooser : List Int → Subframe.SubCfg)
    (hb : Frame.bpsOfCode (Frame.bpsCode b) b0 = some b) :
    ∀ (blks : List (List Int)) (idx fuel : Nat),
      blks.length ≤ fuel →
      idx + blks.length < 2 ^ 36 →
      (∀ blk ∈ blks, 1 ≤ blk.length ∧ blk.length ≤ 65536 ∧
        (chooser blk).Valid b blk) →
      readFrames b0 fuel (writeFrames b chooser idx blks) = some blks.flatten := by
  intro blks
  induction blks with
  | nil =>
    intro idx fuel _ _ _
    cases fuel <;> rfl
  | cons blk blks ih =>
    intro idx fuel hfuel hidx hv
    match fuel with
    | 0 => simp only [List.length_cons] at hfuel; omega
    | fuel + 1 =>
      obtain ⟨hl1, hl2, hval⟩ := hv blk (List.mem_cons_self ..)
      have hne : Frame.write b idx (chooser blk) blk
          ++ writeFrames b chooser (idx + 1) blks ≠ [] := by
        apply List.ne_nil_of_length_pos
        have := frame_write_length_pos b idx (chooser blk) blk
        simp only [List.length_append]
        omega
      have hih := ih (idx + 1) fuel
        (by simp only [List.length_cons] at hfuel; omega)
        (by simp only [List.length_cons] at hidx; omega)
        (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      simp only [writeFrames, readFrames, if_neg hne,
        Frame.read_write b0 b idx (chooser blk) blk _ hb
          (by simp only [List.length_cons] at hidx; omega) hl1 hl2 hval,
        hih, List.flatten_cons]

/-! ## The M2 keystone -/

/-- **`decodeReference ∘ encode = id` (M2 profile).** Mono, any bit depth
    1–32, any block size 16–65535, any sample rate < 2^20, any total length
    < 2^36 samples, and — crucially — *any* subframe heuristic `chooser`
    that returns valid configurations (PLAN.md §1: heuristic knobs are
    correctness-irrelevant by construction). -/
theorem decodeReference_encode (cfg : EncoderCfg) (pcm : List Int)
    (hbs1 : 16 ≤ cfg.blockSize) (hbs2 : cfg.blockSize ≤ 65535)
    (hsr : cfg.sampleRate < 2 ^ 20)
    (hb1 : 1 ≤ cfg.bps) (hb2 : cfg.bps ≤ 32)
    (htot : pcm.length < 2 ^ 36)
    (hchooser : ∀ ys : List Int, 1 ≤ ys.length → ys.length ≤ 65535 →
      (∀ x ∈ ys, x ∈ pcm) → (cfg.chooser ys).Valid cfg.bps ys) :
    decodeReference (encode cfg pcm) = some pcm := by
  unfold encode decodeReference
  rw [bytesToBits_bitsToBytes _ (writeStream_length_dvd cfg pcm)]
  unfold writeStream
  simp only [List.append_assoc,
    readBits_writeBits _ _ _ (by omega : 0x664C6143 < 2 ^ 32),
    readMeta_spec _ cfg.blockSize cfg.sampleRate cfg.bps pcm.length _ _
      (by omega) hsr hb1 hb2 htot]
  rw [if_pos (by trivial)]
  rw [readFrames_writeFrames cfg.bps cfg.bps cfg.chooser
    (Frame.bpsOfCode_bpsCode cfg.bps)
    (chunkFixed cfg.blockSize pcm) 0 _
    (by
      have h1 := writeFrames_length_ge cfg.bps cfg.chooser
        (chunkFixed cfg.blockSize pcm) 0
      omega)
    (by
      have h1 := chunkFixed_count cfg.blockSize pcm
      omega)
    (fun blk hblk => by
      obtain ⟨⟨hl1, hl2⟩, hmem⟩ := chunkFixed_mem cfg.blockSize pcm blk hblk
      exact ⟨hl1, by omega, hchooser blk hl1 (by omega) hmem⟩)]
  rw [chunkFixed_flatten cfg.blockSize pcm (by omega)]

end Flac.Stream
