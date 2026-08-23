import Flac.Native.Rice
import Flac.Spec.Bits

/-!
# L1–L2 proofs — Rice coding and partitioned residuals

PLAN.md §4: `unzigzag_zigzag`, `riceDecode_riceEncode` (here
`readRice_writeRice`), `escapeDecode_escapeEncode` (here
`readSIntSeq_writeSIntSeq`, via `Flac.Bits.readSInt_writeSInt`), and the L2
`partitionsDecode_encode` (here `readResidual_writeResidual`), with the
partition-order certificates carried in `ResidualCfg.Valid` exactly as
PLAN.md §5.4 prescribes: the encoder's partition chooser must *return* them.
-/

namespace Flac.Rice

open Flac.Bits

/-! ## Zigzag -/

theorem unzigzag_zigzag (x : Int) : unzigzag (zigzag x) = x := by
  unfold zigzag unzigzag
  by_cases h : 0 ≤ x
  · rw [if_pos h]; split <;> omega
  · rw [if_neg h]; split <;> omega

/-! ## Single Rice codes -/

theorem readRiceNat_writeRiceNat (k u : Nat) (rest : BitStream) :
    readRiceNat k (writeRiceNat k u ++ rest) = some (u, rest) := by
  simp only [writeRiceNat, readRiceNat, List.append_assoc, readUnary_writeUnary,
    readBits_writeBits _ _ _ (Nat.mod_lt u (Nat.two_pow_pos k))]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  rw [Nat.mul_comm]
  exact Nat.div_add_mod u (2 ^ k)

theorem readRice_writeRice (k : Nat) (x : Int) (rest : BitStream) :
    readRice k (writeRice k x ++ rest) = some (x, rest) := by
  simp only [writeRice, readRice, readRiceNat_writeRiceNat, unzigzag_zigzag]

/-! ## Sequences -/

theorem readRiceSeq_writeRiceSeq (k : Nat) (xs : List Int) (rest : BitStream) :
    readRiceSeq k xs.length (writeRiceSeq k xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [writeRiceSeq, List.flatMap_cons, List.length_cons, readRiceSeq,
      List.append_assoc, readRice_writeRice]
    simp only [writeRiceSeq] at ih
    rw [ih]

theorem readSIntSeq_writeSIntSeq (bits : Nat) (xs : List Int) (rest : BitStream)
    (h : ∀ x ∈ xs, FitsSInt bits x) :
    readSIntSeq bits xs.length (writeSIntSeq bits xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : FitsSInt bits x := h x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, FitsSInt bits y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [writeSIntSeq, List.flatMap_cons, List.length_cons, readSIntSeq,
      List.append_assoc, readSInt_writeSInt bits x hx]
    simp only [writeSIntSeq] at ih
    rw [ih hxs]

/-! ## Partitions -/

theorem readPart_writePart (m : Method) (p : Partition) (xs : List Int)
    (rest : BitStream) (hv : p.Valid m xs) :
    readPart m xs.length (writePart m p xs ++ rest) = some (xs, rest) := by
  match p with
  | .rice k =>
    have hk : k < m.escapeCode := hv
    have hb : k < 2 ^ m.paramBits := by
      cases m <;> simp only [Method.escapeCode, Method.paramBits] at hk ⊢ <;> omega
    simp only [writePart, readPart, List.append_assoc,
      readBits_writeBits _ _ _ hb]
    rw [if_neg (by omega : ¬ k = m.escapeCode)]
    exact readRiceSeq_writeRiceSeq k xs rest
  | .escape bits =>
    obtain ⟨hb, hf⟩ := hv
    have he : m.escapeCode < 2 ^ m.paramBits := by cases m <;> decide
    simp only [writePart, readPart, List.append_assoc,
      readBits_writeBits _ _ _ he]
    rw [if_pos trivial]
    simp only [readBits_writeBits _ _ _ (show bits < 2 ^ 5 by omega)]
    exact readSIntSeq_writeSIntSeq bits xs rest hf

theorem readParts_writeParts (m : Method) :
    ∀ (parts : List (Partition × List Int)),
      (∀ p ∈ parts, Partition.Valid m p.1 p.2) →
      ∀ (rest : BitStream),
        readParts m (parts.map fun p => p.2.length) (writeParts m parts ++ rest)
          = some ((parts.map Prod.snd).flatten, rest) := by
  intro parts
  induction parts with
  | nil => intro _ rest; rfl
  | cons p ps ih =>
    intro hv rest
    have hp := hv p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, Partition.Valid m q.1 q.2 :=
      fun q hq => hv q (List.mem_cons_of_mem _ hq)
    simp only [writeParts, List.flatMap_cons, List.map_cons, readParts,
      List.append_assoc, readPart_writePart m p.1 p.2 _ hp, List.flatten_cons]
    simp only [writeParts] at ih
    rw [ih hps]

/-! ## Chunking -/

theorem chunkBySizes_length (sizes : List Nat) (xs : List Int) :
    (chunkBySizes sizes xs).length = sizes.length := by
  induction sizes generalizing xs with
  | nil => rfl
  | cons sz sizes ih => simp [chunkBySizes, ih]

theorem chunkBySizes_map_length :
    ∀ (sizes : List Nat) (xs : List Int), sizes.sum = xs.length →
      (chunkBySizes sizes xs).map List.length = sizes := by
  intro sizes
  induction sizes with
  | nil => intro xs _; rfl
  | cons sz sizes ih =>
    intro xs h
    simp only [List.sum_cons] at h
    have h2 : sizes.sum = (xs.drop sz).length := by
      simp only [List.length_drop]; omega
    simp only [chunkBySizes, List.map_cons, List.length_take, ih (xs.drop sz) h2]
    congr 1
    omega

theorem chunkBySizes_flatten :
    ∀ (sizes : List Nat) (xs : List Int), sizes.sum = xs.length →
      (chunkBySizes sizes xs).flatten = xs := by
  intro sizes
  induction sizes with
  | nil =>
    intro xs h
    have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons sz sizes ih =>
    intro xs h
    simp only [List.sum_cons] at h
    have h2 : sizes.sum = (xs.drop sz).length := by
      simp only [List.length_drop]; omega
    simp only [chunkBySizes, List.flatten_cons, ih (xs.drop sz) h2,
      List.take_append_drop]

theorem map_snd_zip_eq {α β : Type} :
    ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
      (l1.zip l2).map Prod.snd = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 h
    have : l2 = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst this; rfl
  | cons a l1 ih =>
    intro l2 h
    match l2 with
    | [] => simp at h
    | b :: l2 =>
      simp only [List.zip_cons_cons, List.map_cons, ih l2 (by simpa using h)]

/-! ## Partition geometry -/

private theorem sum_replicate (n c : Nat) : (List.replicate n c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

theorem partSizes_length (bs po ord : Nat) :
    (partSizes bs po ord).length = 2 ^ po := by
  simp only [partSizes, List.length_cons, List.length_replicate]
  have := Nat.two_pow_pos po
  omega

theorem partSizes_sum (bs po ord : Nat) (hdvd : 2 ^ po ∣ bs)
    (hord : ord < bs / 2 ^ po) :
    (partSizes bs po ord).sum = bs - ord := by
  have hc : bs / 2 ^ po * 2 ^ po = bs := Nat.div_mul_cancel hdvd
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ po = k + 1 :=
    ⟨2 ^ po - 1, by have := Nat.two_pow_pos po; omega⟩
  simp only [partSizes, List.sum_cons, sum_replicate, hk, Nat.add_sub_cancel] at hc hord ⊢
  rw [Nat.mul_succ] at hc
  rw [Nat.mul_comm k (bs / (k + 1))]
  omega

/-! ## The coded residual (L2 keystone) -/

/-- **Partitioned-residual round-trip** (`partitionsDecode_encode` of
    PLAN.md §4): for every valid encoder configuration, reading back a coded
    residual returns exactly the residual sequence. -/
theorem readResidual_writeResidual (bs ord : Nat) (cfg : ResidualCfg)
    (res : List Int) (hv : cfg.Valid bs ord res) (rest : BitStream) :
    readResidual bs ord (writeResidual bs ord cfg res ++ rest) = some (res, rest) := by
  obtain ⟨hpo, hdvd, hord, hlen, hclen, hpv⟩ := hv
  have hsum : (partSizes bs cfg.po ord).sum = res.length := by
    rw [partSizes_sum bs cfg.po ord hdvd hord, hlen]
  have hzip : cfg.choices.length
      = (chunkBySizes (partSizes bs cfg.po ord) res).length := by
    rw [chunkBySizes_length, partSizes_length, hclen]
  have hsnd : (cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res)).map
      Prod.snd = chunkBySizes (partSizes bs cfg.po ord) res :=
    map_snd_zip_eq _ _ hzip
  have hsizes : ((cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res)).map
      fun p => p.2.length) = partSizes bs cfg.po ord := by
    have hcomp : ((cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res)).map
        fun p => p.2.length)
        = ((cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res)).map
            Prod.snd).map List.length := by
      rw [List.map_map]; rfl
    rw [hcomp, hsnd, chunkBySizes_map_length _ _ hsum]
  have hcode : cfg.method.code < 2 ^ 2 := by cases cfg.method <;> decide
  have hofcode : Method.ofCode cfg.method.code = some cfg.method := by
    cases cfg.method <;> rfl
  have hmod : bs % 2 ^ cfg.po = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hparts := readParts_writeParts cfg.method
    (cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res)) hpv rest
  rw [hsizes, hsnd, chunkBySizes_flatten _ _ hsum] at hparts
  unfold writeResidual readResidual
  simp only [List.append_assoc, readBits_writeBits _ _ _ hcode, hofcode,
    readBits_writeBits _ _ _ (show cfg.po < 2 ^ 4 by omega)]
  rw [if_pos ⟨hmod, hord⟩]
  exact hparts

end Flac.Rice
