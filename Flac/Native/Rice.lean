import Flac.Native.Bits

/-!
# Rice coding and partitioned residuals (RFC 9639 §9.2.7)

Zigzag folding, Rice/RICE2 codes, escaped (unencoded) partitions, and the
partitioned coded-residual layer. Everything is defined over the bit model;
round-trip theorems live in `Flac.Spec.Rice`.

Heuristic choices — which partition order, which Rice parameter per
partition, whether to escape — are *inputs* here (`Partition`,
`ResidualCfg`), produced later by `Heuristics.lean` together with validity
certificates. The round-trip holds for every valid choice.
-/

namespace Flac.Rice

open Flac.Bits

/-! ## Zigzag folding (RFC 9639 §9.2.7.2) -/

/-- Fold a signed residual to unsigned: `x ≥ 0 ↦ 2x`, `x < 0 ↦ -2x - 1`. -/
def zigzag (x : Int) : Nat :=
  if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1

/-- Unfold: even `u ↦ u/2`, odd `u ↦ -(u/2) - 1`. -/
@[inline] def unzigzag (u : Nat) : Int :=
  if u % 2 = 0 then ((u / 2 : Nat) : Int) else -(((u / 2 : Nat) : Int) + 1)

/-! ## Rice code for a single residual -/

/-- Rice code of a folded value: quotient in unary, `k` remainder bits. -/
def writeRiceNat (k : Nat) (u : Nat) : BitStream :=
  writeUnary (u / 2 ^ k) ++ writeBits k (u % 2 ^ k)

def readRiceNat (k : Nat) (s : BitStream) : Option (Nat × BitStream) :=
  match readUnary s with
  | none => none
  | some (q, s) =>
    match readBits k s with
    | none => none
    | some (r, s) => some (q * 2 ^ k + r, s)

def writeRice (k : Nat) (x : Int) : BitStream :=
  writeRiceNat k (zigzag x)

def readRice (k : Nat) (s : BitStream) : Option (Int × BitStream) :=
  match readRiceNat k s with
  | none => none
  | some (u, s) => some (unzigzag u, s)

/-! ## Residual sequences -/

def writeRiceSeq (k : Nat) (xs : List Int) : BitStream :=
  xs.flatMap (writeRice k)

def readRiceSeq (k : Nat) : (count : Nat) → BitStream → Option (List Int × BitStream)
  | 0, s => some ([], s)
  | count+1, s =>
    match readRice k s with
    | none => none
    | some (x, s) =>
      match readRiceSeq k count s with
      | none => none
      | some (xs, s) => some (x :: xs, s)

/-- Unencoded residuals of an escaped partition (RFC 9639 §9.2.7.1):
    fixed-width two's complement, possibly 0 bits wide. -/
def writeSIntSeq (bits : Nat) (xs : List Int) : BitStream :=
  xs.flatMap (writeSInt bits)

def readSIntSeq (bits : Nat) : (count : Nat) → BitStream → Option (List Int × BitStream)
  | 0, s => some ([], s)
  | count+1, s =>
    match readSInt bits s with
    | none => none
    | some (x, s) =>
      match readSIntSeq bits count s with
      | none => none
      | some (xs, s) => some (x :: xs, s)

/-! ### Tail-recursive compiled twins for the residual readers

`readRiceSeq` / `readSIntSeq` build their list with a non-tail `x :: rec …`, one native
stack frame per residual sample. These readers are on the REFERENCE decoder path only:
`Rice.readResidual → readParts → readPart` is reached via `Subframe.read →
Frame.readChannels → Stream.readFrames → Stream.decodeReference` (the `List Bool` model,
the CLI `--decode` path). The SHIPPED array decoder (`decodeArrays`, hence `decodeBytes`
/ `decodePcm16A`) does NOT use them: its residual layer is `Flac.Decode.readRiceSeqScan`
/ `readSIntSeqGo` (`Native/Decode.lean`), which is already tail — verified in the
generated IR, where `Flac/Native/Decode.c` calls no `Flac.Rice.readRiceSeq*`.

The `*Acc` forms accumulate in reverse and are tail-recursive; the `@[csimp]` swaps make
the compiler emit them while the kernel checks value-equality, so every theorem over
`readRiceSeq` / `readSIntSeq` is untouched (they compute the same value). This is a sound
hardening of the reference decoder's two residual loops. It does not by itself make the
reference decoder stack-flat (it still has other non-tail `List Bool` loops, which is why
the fuzz rig bounds `decodeReference`'s input by its own cap), and it changes the shipped
array decoder not at all. -/

def readRiceSeqAcc (k : Nat) (acc : List Int) : (count : Nat) → BitStream → Option (List Int × BitStream)
  | 0, s => some (acc.reverse, s)
  | count+1, s =>
    match readRice k s with
    | none => none
    | some (x, s) => readRiceSeqAcc k (x :: acc) count s

def readRiceSeqTR (k : Nat) (count : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  readRiceSeqAcc k [] count s

theorem readRiceSeqAcc_eq (k : Nat) (acc : List Int) (count : Nat) (s : BitStream) :
    readRiceSeqAcc k acc count s
      = (readRiceSeq k count s).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction count generalizing acc s with
  | zero => simp [readRiceSeqAcc, readRiceSeq]
  | succ n ih =>
    simp only [readRiceSeqAcc, readRiceSeq]
    cases hr : readRice k s with
    | none => simp
    | some p =>
      obtain ⟨x, s'⟩ := p
      dsimp only
      rw [ih (x :: acc) s']
      cases readRiceSeq k n s' with
      | none => simp
      | some q => obtain ⟨xs, s''⟩ := q; simp [List.reverse_cons]

@[csimp] theorem readRiceSeq_eq_readRiceSeqTR : @readRiceSeq = @readRiceSeqTR := by
  funext k count s
  rw [readRiceSeqTR, readRiceSeqAcc_eq]; simp

def readSIntSeqAcc (bits : Nat) (acc : List Int) : (count : Nat) → BitStream → Option (List Int × BitStream)
  | 0, s => some (acc.reverse, s)
  | count+1, s =>
    match readSInt bits s with
    | none => none
    | some (x, s) => readSIntSeqAcc bits (x :: acc) count s

def readSIntSeqTR (bits : Nat) (count : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  readSIntSeqAcc bits [] count s

theorem readSIntSeqAcc_eq (bits : Nat) (acc : List Int) (count : Nat) (s : BitStream) :
    readSIntSeqAcc bits acc count s
      = (readSIntSeq bits count s).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction count generalizing acc s with
  | zero => simp [readSIntSeqAcc, readSIntSeq]
  | succ n ih =>
    simp only [readSIntSeqAcc, readSIntSeq]
    cases hr : readSInt bits s with
    | none => simp
    | some p =>
      obtain ⟨x, s'⟩ := p
      dsimp only
      rw [ih (x :: acc) s']
      cases readSIntSeq bits n s' with
      | none => simp
      | some q => obtain ⟨xs, s''⟩ := q; simp [List.reverse_cons]

@[csimp] theorem readSIntSeq_eq_readSIntSeqTR : @readSIntSeq = @readSIntSeqTR := by
  funext bits count s
  rw [readSIntSeqTR, readSIntSeqAcc_eq]; simp

/-! ## Partitions -/

/-- Coding method: 4-bit (RICE) or 5-bit (RICE2) parameters. -/
inductive Method where
  | rice4
  | rice5
deriving Repr, DecidableEq

def Method.code : Method → Nat
  | .rice4 => 0
  | .rice5 => 1

def Method.ofCode : Nat → Option Method
  | 0 => some .rice4
  | 1 => some .rice5
  | _ => none              -- 0b10, 0b11 reserved

def Method.paramBits : Method → Nat
  | .rice4 => 4
  | .rice5 => 5

/-- The all-ones escape code: 15 (4-bit) or 31 (5-bit). -/
def Method.escapeCode : Method → Nat
  | .rice4 => 15
  | .rice5 => 31

/-- Per-partition encoding choice (made by the heuristics layer). -/
inductive Partition where
  /-- Rice-code the partition with parameter `k`. -/
  | rice (k : Nat)
  /-- Escape: store residuals unencoded with `bits` bits each. -/
  | escape (bits : Nat)
deriving Repr, DecidableEq

/-- The certificate a partition choice must carry for the round-trip. -/
def Partition.Valid (m : Method) : Partition → List Int → Prop
  | .rice k, _ => k < m.escapeCode
  | .escape bits, xs => bits < 32 ∧ ∀ x ∈ xs, FitsSInt bits x

instance (m : Method) (p : Partition) (xs : List Int) :
    Decidable (Partition.Valid m p xs) := by
  unfold Partition.Valid
  rcases p with k | bits <;> exact inferInstance

def writePart (m : Method) (p : Partition) (xs : List Int) : BitStream :=
  match p with
  | .rice k => writeBits m.paramBits k ++ writeRiceSeq k xs
  | .escape bits =>
      writeBits m.paramBits m.escapeCode ++ writeBits 5 bits ++ writeSIntSeq bits xs

def readPart (m : Method) (count : Nat) (s : BitStream) :
    Option (List Int × BitStream) :=
  match readBits m.paramBits s with
  | none => none
  | some (k, s) =>
    if k = m.escapeCode then
      match readBits 5 s with
      | none => none
      | some (bits, s) => readSIntSeq bits count s
    else
      readRiceSeq k count s

def writeParts (m : Method) (parts : List (Partition × List Int)) : BitStream :=
  parts.flatMap fun p => writePart m p.1 p.2

def readParts (m : Method) : (sizes : List Nat) → BitStream → Option (List Int × BitStream)
  | [], s => some ([], s)
  | sz :: sizes, s =>
    match readPart m sz s with
    | none => none
    | some (p, s) =>
      match readParts m sizes s with
      | none => none
      | some (ps, s) => some (p ++ ps, s)

/-! ## The coded residual -/

/-- Partition sample counts for block size `bs`, partition order `po`,
    predictor order `ord`: the first partition is short by `ord` samples
    (RFC 9639 §9.2.7). -/
def partSizes (bs po ord : Nat) : List Nat :=
  (bs / 2 ^ po - ord) :: List.replicate (2 ^ po - 1) (bs / 2 ^ po)

/-- Split `xs` into consecutive chunks of the given sizes. -/
def chunkBySizes {α : Type} : (sizes : List Nat) → (xs : List α) → List (List α)
  | [], _ => []
  | sz :: sizes, xs => xs.take sz :: chunkBySizes sizes (xs.drop sz)

/-- Encoder-side residual configuration, produced by the heuristics layer. -/
structure ResidualCfg where
  method : Method
  /-- Partition order: the residual is split into `2^po` partitions. -/
  po : Nat
  /-- One choice per partition (`choices.length = 2^po`). -/
  choices : List Partition
deriving Repr

/-- Validity certificate tying a `ResidualCfg` to a concrete residual. -/
structure ResidualCfg.Valid (cfg : ResidualCfg) (bs ord : Nat)
    (res : List Int) : Prop where
  po_lt : cfg.po < 16
  dvd : 2 ^ cfg.po ∣ bs
  ord_lt : ord < bs / 2 ^ cfg.po
  len : res.length = bs - ord
  choices_len : cfg.choices.length = 2 ^ cfg.po
  parts_valid : ∀ p ∈ cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res),
    Partition.Valid cfg.method p.1 p.2

instance (cfg : ResidualCfg) (bs ord : Nat) (res : List Int) :
    Decidable (cfg.Valid bs ord res) :=
  decidable_of_iff
    (cfg.po < 16 ∧ 2 ^ cfg.po ∣ bs ∧ ord < bs / 2 ^ cfg.po ∧
      res.length = bs - ord ∧ cfg.choices.length = 2 ^ cfg.po ∧
      ∀ p ∈ cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res),
        Partition.Valid cfg.method p.1 p.2)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩,
     fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- Write a coded residual: 2-bit method, 4-bit partition order, partitions. -/
def writeResidual (bs ord : Nat) (cfg : ResidualCfg) (res : List Int) : BitStream :=
  writeBits 2 cfg.method.code ++ writeBits 4 cfg.po ++
    writeParts cfg.method (cfg.choices.zip (chunkBySizes (partSizes bs cfg.po ord) res))

/-- Read a coded residual, given block size and predictor order from the
    enclosing (sub)frame headers. Enforces the partition-order constraints
    of RFC 9639 §9.2.7. -/
def readResidual (bs ord : Nat) (s : BitStream) : Option (List Int × BitStream) :=
  match readBits 2 s with
  | none => none
  | some (mc, s) =>
    match Method.ofCode mc with
    | none => none
    | some m =>
      match readBits 4 s with
      | none => none
      | some (po, s) =>
        if bs % 2 ^ po = 0 ∧ ord < bs / 2 ^ po then
          readParts m (partSizes bs po ord) s
        else none

end Flac.Rice
