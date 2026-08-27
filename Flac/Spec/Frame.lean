import Flac.Native.Frame
import Flac.Spec.Bits
import Flac.Spec.Utf8Num
import Flac.Spec.Subframe
import Flac.Spec.Stereo
import Flac.Spec.Rice

/-!
# L5 (part 2) — multichannel frame round-trip

The frame round-trip over the full channel option
space: 1–8 independent channels and the three stereo-decorrelation modes
(side channel at `b+1` bits), both numbering strategies. CRC checks
discharge definitionally via `withConsumed_spec`.
-/

namespace Flac.Frame

open Flac.Bits

theorem bpsCode_lt (b : Nat) : bpsCode b < 2 ^ 3 := by
  unfold bpsCode; split <;> omega

theorem bpsOfCode_bpsCode (b : Nat) : bpsOfCode (bpsCode b) b = some b := by
  unfold bpsCode; split <;> rfl

theorem resolveBlockSize_seven (bs : Nat) (h1 : 1 ≤ bs) (h2 : bs ≤ 65536)
    (tail : BitStream) :
    resolveBlockSize 7 (writeBits 16 (bs - 1) ++ tail) = some (bs, tail) := by
  unfold resolveBlockSize
  rw [if_neg (by omega), if_neg (by omega : ¬(2 ≤ 7 ∧ 7 ≤ 5)), if_neg (by omega),
    if_pos (by trivial)]
  simp only [readBits_writeBits _ _ _ (by omega : bs - 1 < 2 ^ 16),
    Option.some.injEq, Prod.mk.injEq]
  exact ⟨by omega, trivial⟩

theorem skipSampleRate_zero (s : BitStream) : skipSampleRate 0 s = some s := by
  unfold skipSampleRate
  rw [if_neg (by omega), if_neg (by omega : ¬((0 : Nat) = 13 ∨ (0 : Nat) = 14)),
    if_neg (by omega)]

/-- A valid assignment's channel code fits the 4-bit field. -/
theorem code_lt {asg : ChannelAsg} {b bs : Nat} {chs : List (List Int)}
    (hv : asg.Valid b bs chs) : asg.code chs.length < 16 := by
  match asg with
  | .independent cfgs =>
    obtain ⟨_, _, h8, _⟩ := hv
    simp only [ChannelAsg.code]
    omega
  | .leftSide c0 c1 | .rightSide c0 c1 | .midSide c0 c1 =>
    simp only [ChannelAsg.code]
    omega

/-- Parsing the canonical header core recovers the fields. -/
theorem readFields_headerCore (b0 b : Nat) (strat : Bool) (num bs chCode : Nat)
    (tail : BitStream) (hb : bpsOfCode (bpsCode b) b0 = some b)
    (hnum : num < 2 ^ 36) (hbs1 : 1 ≤ bs) (hbs2 : bs ≤ 65536)
    (hch : chCode < 16) :
    readFields b0 (headerCore b strat num bs chCode ++ tail)
      = some (⟨bs, b, chCode, num⟩, tail) := by
  have hstrat : (if strat then 1 else 0) < 2 ^ 1 := by cases strat <;> decide
  simp only [headerCore, readFields, List.append_assoc,
    readBits_writeBits _ _ _ (by omega : 0x3FFE < 2 ^ 14),
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 1),
    readBits_writeBits _ _ _ hstrat,
    readBits_writeBits _ _ _ (by omega : 7 < 2 ^ 4),
    readBits_writeBits _ _ _ (by omega : 0 < 2 ^ 4),
    readBits_writeBits _ _ _ (show chCode < 2 ^ 4 by omega),
    readBits_writeBits _ _ _ (bpsCode_lt b),
    hb, Utf8Num.read_write num hnum,
    resolveBlockSize_seven bs hbs1 hbs2, skipSampleRate_zero]
  rw [if_pos (by trivial), if_pos (by trivial), if_pos (by trivial)]

/-- Header round-trip, CRC-8 verified. -/
theorem readHeader_writeHeader (b0 b : Nat) (strat : Bool) (num bs chCode : Nat)
    (tail : BitStream) (hb : bpsOfCode (bpsCode b) b0 = some b)
    (hnum : num < 2 ^ 36) (hbs1 : 1 ≤ bs) (hbs2 : bs ≤ 65536)
    (hch : chCode < 16) :
    readHeader b0 (writeHeader b strat num bs chCode ++ tail)
      = some (⟨bs, b, chCode, num⟩, tail) := by
  unfold writeHeader readHeader
  rw [List.append_assoc]
  simp only [withConsumed_spec (readFields b0) (headerCore b strat num bs chCode) _ _
      (readFields_headerCore b0 b strat num bs chCode _ hb hnum hbs1 hbs2 hch),
    readBits_writeBits _ _ _
      (show (Crc.crc8 (bitsToBytes (headerCore b strat num bs chCode))).toNat < 2 ^ 8 from
        UInt8.toNat_lt_size _)]
  rw [if_pos (by trivial)]

/-! ## Subframe sequences and channel decorrelation -/

private theorem zip_map_left' {α β γ : Type} (f : α → γ) :
    ∀ (l1 : List α) (l2 : List β),
      (l1.map f).zip l2 = (l1.zip l2).map (fun p => (f p.1, p.2)) := by
  intro l1
  induction l1 with
  | nil => intro l2; rfl
  | cons a l1 ih =>
    intro l2
    match l2 with
    | [] => rfl
    | b :: l2 => simp only [List.map_cons, List.zip_cons_cons, ih]

private theorem exists_of_mem_zipWith {f : Int → Int → Int} :
    ∀ {l r : List Int} {x : Int}, x ∈ List.zipWith f l r →
      ∃ a ∈ l, ∃ b ∈ r, x = f a b := by
  intro l
  induction l with
  | nil => intro r x hx; simp at hx
  | cons a l ih =>
    intro r x hx
    match r with
    | [] => simp at hx
    | b :: r =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨a, by simp, b, by simp, rfl⟩
      · obtain ⟨a', ha', b', hb', rfl⟩ := ih hx
        exact ⟨a', by simp [ha'], b', by simp [hb'], rfl⟩

/-- Side channels of fitting audio fit `b+1` bits. -/
private theorem side_all_fits (b : Nat) (l r : List Int)
    (hl : ∀ x ∈ l, FitsSInt b x) (hr : ∀ x ∈ r, FitsSInt b x) :
    ∀ x ∈ Stereo.side l r, FitsSInt (b + 1) x := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_of_mem_zipWith hx
  exact Stereo.side_fits b a c (hl a ha) (hr c hc)

/-- Mid channels of fitting audio fit `b` bits. -/
private theorem mid_all_fits (b : Nat) (l r : List Int)
    (hl : ∀ x ∈ l, FitsSInt b x) (hr : ∀ x ∈ r, FitsSInt b x) :
    ∀ x ∈ Stereo.mid l r, FitsSInt b x := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_of_mem_zipWith hx
  exact Stereo.mid_fits b a c (hl a ha) (hr c hc)

theorem readSubframes_pairs (b bs : Nat) :
    ∀ (pairs : List (Subframe.SubCfg × List Int)) (rest : BitStream),
      (∀ p ∈ pairs, p.2.length = bs ∧ p.1.Valid b p.2 ∧
        ∀ x ∈ p.2, FitsSInt b x) →
      readSubframes bs b pairs.length
        (writeSubframes (pairs.map (fun p => ((b, p.1), p.2))) ++ rest)
        = some (pairs.map Prod.snd, rest) := by
  intro pairs
  induction pairs with
  | nil => intro rest _; rfl
  | cons p ps ih =>
    intro rest hv
    obtain ⟨hlen, hval, hfitp⟩ := hv p (List.mem_cons_self ..)
    have hsub := Subframe.read_write b p.1 p.2 hval hfitp
      (writeSubframes (ps.map (fun p => ((b, p.1), p.2))) ++ rest)
    rw [hlen] at hsub
    simp only [writeSubframes] at hsub ih
    simp only [writeSubframes, List.map_cons, List.flatMap_cons, List.length_cons,
      readSubframes, List.append_assoc, hsub]
    rw [ih rest (fun q hq => hv q (List.mem_cons_of_mem _ hq))]

/-- Channel-sequence round-trip: reading back the written subframes and
    undoing decorrelation recovers the channels. -/
theorem readChannels_spec (b bs : Nat) (asg : ChannelAsg)
    (chs : List (List Int)) (rest : BitStream)
    (hv : asg.Valid b bs chs)
    (hfit : ∀ c ∈ chs, ∀ x ∈ c, FitsSInt b x) :
    readChannels bs b (asg.code chs.length)
      (writeSubframes (subframePlan b asg chs) ++ rest) = some (chs, rest) := by
  obtain ⟨hlens, hshape⟩ := hv
  match asg with
  | .independent cfgs =>
    obtain ⟨hch1, hch8, hclen, hpv⟩ := hshape
    have hziplen : (cfgs.zip chs).length = chs.length := by
      rw [List.length_zip]; omega
    have hpairs := readSubframes_pairs b bs (cfgs.zip chs) rest (fun p hp =>
      ⟨hlens p.2 (List.of_mem_zip hp).2, hpv p hp,
        hfit p.2 (List.of_mem_zip hp).2⟩)
    rw [hziplen, Rice.map_snd_zip_eq cfgs chs hclen] at hpairs
    simp only [ChannelAsg.code, subframePlan, zip_map_left']
    unfold readChannels
    rw [if_pos (by omega : chs.length - 1 ≤ 7),
      show chs.length - 1 + 1 = chs.length from by omega]
    exact hpairs
  | .leftSide c0 c1 =>
    match chs, hshape with
    | [l, r], hsh =>
      obtain ⟨hv0, hv1⟩ := hsh
      have hll : l.length = bs := hlens l (by simp)
      have hrl : r.length = bs := hlens r (by simp)
      have hfl : ∀ x ∈ l, FitsSInt b x := hfit l (by simp)
      have hfr : ∀ x ∈ r, FitsSInt b x := hfit r (by simp)
      have hs0 := Subframe.read_write b c0 l hv0 hfl
        (Subframe.write (b + 1) c1 (Stereo.side l r) ++ rest)
      rw [hll] at hs0
      have hs1 := Subframe.read_write (b + 1) c1 (Stereo.side l r) hv1
        (side_all_fits b l r hfl hfr) rest
      rw [show (Stereo.side l r).length = bs by
        simp only [Stereo.length_side]; omega] at hs1
      simp only [ChannelAsg.code, subframePlan, writeSubframes,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      unfold readChannels
      rw [if_neg (by omega : ¬(8 ≤ 7)), if_pos (by trivial)]
      simp only [hs0, hs1, Stereo.decodeLS_side l r (by omega)]
  | .rightSide c0 c1 =>
    match chs, hshape with
    | [l, r], hsh =>
      obtain ⟨hv0, hv1⟩ := hsh
      have hll : l.length = bs := hlens l (by simp)
      have hrl : r.length = bs := hlens r (by simp)
      have hfl : ∀ x ∈ l, FitsSInt b x := hfit l (by simp)
      have hfr : ∀ x ∈ r, FitsSInt b x := hfit r (by simp)
      have hs0 := Subframe.read_write (b + 1) c0 (Stereo.side l r) hv0
        (side_all_fits b l r hfl hfr) (Subframe.write b c1 r ++ rest)
      rw [show (Stereo.side l r).length = bs by
        simp only [Stereo.length_side]; omega] at hs0
      have hs1 := Subframe.read_write b c1 r hv1 hfr rest
      rw [hrl] at hs1
      simp only [ChannelAsg.code, subframePlan, writeSubframes,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      unfold readChannels
      rw [if_neg (by omega : ¬(9 ≤ 7)), if_neg (by omega : ¬(9 = 8)),
        if_pos (by trivial)]
      simp only [hs0, hs1, Stereo.decodeRS_side l r (by omega)]
  | .midSide c0 c1 =>
    match chs, hshape with
    | [l, r], hsh =>
      obtain ⟨hv0, hv1⟩ := hsh
      have hll : l.length = bs := hlens l (by simp)
      have hrl : r.length = bs := hlens r (by simp)
      have hfl : ∀ x ∈ l, FitsSInt b x := hfit l (by simp)
      have hfr : ∀ x ∈ r, FitsSInt b x := hfit r (by simp)
      have hs0 := Subframe.read_write b c0 (Stereo.mid l r) hv0
        (mid_all_fits b l r hfl hfr)
        (Subframe.write (b + 1) c1 (Stereo.side l r) ++ rest)
      rw [show (Stereo.mid l r).length = bs by
        simp only [Stereo.length_mid]; omega] at hs0
      have hs1 := Subframe.read_write (b + 1) c1 (Stereo.side l r) hv1
        (side_all_fits b l r hfl hfr) rest
      rw [show (Stereo.side l r).length = bs by
        simp only [Stereo.length_side]; omega] at hs1
      simp only [ChannelAsg.code, subframePlan, writeSubframes,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      unfold readChannels
      rw [if_neg (by omega : ¬(10 ≤ 7)), if_neg (by omega : ¬(10 = 8)),
        if_neg (by omega : ¬(10 = 9)), if_pos (by trivial)]
      simp only [hs0, hs1, Stereo.decodeMSL_mid_side l r (by omega),
        Stereo.decodeMSR_mid_side l r (by omega)]

/-! ## Frame assembly -/

theorem readHeaderChannels_spec (b0 b : Nat) (strat : Bool) (num : Nat)
    (asg : ChannelAsg) (chs : List (List Int)) (tail : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b) (hnum : num < 2 ^ 36)
    (hbs1 : 1 ≤ (chs.headD []).length) (hbs2 : (chs.headD []).length ≤ 65536)
    (hv : asg.Valid b (chs.headD []).length chs)
    (hfit : ∀ c ∈ chs, ∀ x ∈ c, FitsSInt b x) :
    readHeaderChannels b0
      ((writeHeader b strat num (chs.headD []).length (asg.code chs.length)
        ++ writeSubframes (subframePlan b asg chs)) ++ tail)
      = some (chs, tail) := by
  unfold readHeaderChannels
  rw [List.append_assoc]
  simp only [readHeader_writeHeader b0 b strat num (chs.headD []).length
    (asg.code chs.length) _ hb hnum hbs1 hbs2 (code_lt hv)]
  exact readChannels_spec b (chs.headD []).length asg chs tail hv hfit

theorem readBody_spec (b0 b : Nat) (strat : Bool) (num : Nat)
    (asg : ChannelAsg) (chs : List (List Int)) (tail : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b) (hnum : num < 2 ^ 36)
    (hbs1 : 1 ≤ (chs.headD []).length) (hbs2 : (chs.headD []).length ≤ 65536)
    (hv : asg.Valid b (chs.headD []).length chs)
    (hfit : ∀ c ∈ chs, ∀ x ∈ c, FitsSInt b x) :
    readBody b0 (body b strat num asg chs ++ tail) = some (chs, tail) := by
  unfold readBody body alignToByte
  rw [List.append_assoc]
  simp only [withConsumed_spec (readHeaderChannels b0)
      (writeHeader b strat num (chs.headD []).length (asg.code chs.length)
        ++ writeSubframes (subframePlan b asg chs)) _ _
      (readHeaderChannels_spec b0 b strat num asg chs _ hb hnum hbs1 hbs2 hv hfit),
    readBits_replicate_false]
  rw [if_pos (by trivial)]

/-- **Frame round-trip** over the full channel/stereo/numbering option
    space. -/
theorem read_write (b0 b : Nat) (strat : Bool) (num : Nat)
    (asg : ChannelAsg) (chs : List (List Int)) (rest : BitStream)
    (hb : bpsOfCode (bpsCode b) b0 = some b) (hnum : num < 2 ^ 36)
    (hbs1 : 1 ≤ (chs.headD []).length) (hbs2 : (chs.headD []).length ≤ 65536)
    (hv : asg.Valid b (chs.headD []).length chs)
    (hfit : ∀ c ∈ chs, ∀ x ∈ c, FitsSInt b x) :
    read b0 (write b strat num asg chs ++ rest) = some (chs, rest) := by
  unfold write read
  rw [List.append_assoc]
  simp only [withConsumed_spec (readBody b0) (body b strat num asg chs) _ _
      (readBody_spec b0 b strat num asg chs _ hb hnum hbs1 hbs2 hv hfit),
    readBits_writeBits _ _ _
      (show (Crc.crc16 (bitsToBytes (body b strat num asg chs))).toNat < 2 ^ 16 from
        UInt16.toNat_lt_size _)]
  rw [if_pos (by trivial)]

end Flac.Frame
