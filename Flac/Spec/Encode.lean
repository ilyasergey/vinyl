import Flac.Native.Codec
import Flac.Native.Encode
import Flac.Spec.Decode
import Flac.Spec.Emit
import Flac.Spec.PcmBytes

/-!
# The shipped writer simulates the verified one

`Flac.Encode.BitWriter` is the writer the shipped encoder runs: a
`ByteArray` plus a `UInt64` accumulator whose bits at or above the pending
count are deliberately stale (never masked, never read). `Flac.Emit.W` is
the writer every theorem in `Flac.Spec.Emit` is about: the same buffer plus
a `Nat` accumulator, masked at every step.

`Sim` relates the two, `Simulates` lifts it to writer transformers, and it
composes by `simulates_comp`. Together with `Flac.Emit.emitFast_eq_encode`
this is the road to identifying the shipped encoder's bytes with
`Flac.Stream.encode`'s — with no runtime certificate.
-/

namespace Flac.Encode

open Flac.Bits

/-! ## The relation -/

/-- The two writers hold the same bytes, the same pending count, and the
    same pending bits. Only the low `n` bits of the fast accumulator are
    related: the rest are stale by design. -/
def Sim (bw : BitWriter) (w : Emit.W) : Prop :=
  bw.buf = w.buf ∧ bw.n = w.n ∧ w.n < 8 ∧
    bw.acc.toNat % 2 ^ w.n = w.acc % 2 ^ w.n

/-- `F` (fast) simulates `f` (verified). -/
def Simulates (F : BitWriter → BitWriter) (f : Emit.W → Emit.W) : Prop :=
  ∀ bw w, Sim bw w → Sim (F bw) (f w)

theorem simulates_comp {F G : BitWriter → BitWriter} {f g : Emit.W → Emit.W}
    (hF : Simulates F f) (hG : Simulates G g) :
    Simulates (fun bw => G (F bw)) (fun w => g (f w)) :=
  fun _ _ h => hG _ _ (hF _ _ h)

theorem simulates_id : Simulates id id := fun _ _ h => h

/-- What a simulation is *for*: the fast buffer denotes the model
    bitstream the verified writer denotes. -/
theorem Sim.bits {bw : BitWriter} {w : Emit.W} (h : Sim bw w) :
    Emit.W.bits w = bytesToBits bw.buf ++ writeBits bw.n bw.acc.toNat := by
  obtain ⟨hbuf, hn, _, hacc⟩ := h
  unfold Emit.W.bits
  rw [hbuf, hn, Emit.writeBits_mod w.n w.acc, ← hacc, ← Emit.writeBits_mod]

/-! ## Arithmetic -/

/-- Bits `[d, d+8)` of two numbers agree as soon as their low `d + 8` bits
    do — the only fact the two flush loops need about each other. -/
private theorem byte_seg {x y d : Nat} (h : x % 2 ^ (d + 8) = y % 2 ^ (d + 8)) :
    x / 2 ^ d % 2 ^ 8 = y / 2 ^ d % 2 ^ 8 := by
  have hp : (2 : Nat) ^ (d + 8) = 2 ^ d * 2 ^ 8 := by rw [Nat.pow_add]
  rw [← Nat.mod_mul_right_div_self x (2 ^ d) (2 ^ 8),
    ← Nat.mod_mul_right_div_self y (2 ^ d) (2 ^ 8), ← hp, h]

/-- Small numbers are `UInt64` shift amounts unchanged. -/
private theorem toNat_ofNat_small {k : Nat} (h : k < 64) :
    (UInt64.ofNat k).toNat % 64 = k := by
  rw [UInt64.toNat_ofNat']
  have h64 : k < 2 ^ 64 := Nat.lt_trans h Nat.lt_two_pow_self
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h]

/-! ## The flush loops -/

/-- `flushBytes` peels exactly the bytes `flushGo` peels, and the pending
    bits still agree afterwards. `flushBytes` never masks its accumulator;
    it does not have to, because every byte it emits is `bits [n-8, n)` and
    nothing above `n` is ever read. -/
private theorem flush_sim (a : UInt64) : ∀ n : Nat, n < 64 →
    ∀ (buf : ByteArray) (acc : Nat), a.toNat % 2 ^ n = acc % 2 ^ n →
      BitWriter.flushBytes buf a n = (Emit.W.flushGo buf acc n).1 ∧
        a.toNat % 2 ^ (Emit.W.flushGo buf acc n).2.2
          = (Emit.W.flushGo buf acc n).2.1 % 2 ^ (Emit.W.flushGo buf acc n).2.2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn buf acc h
    unfold BitWriter.flushBytes Emit.W.flushGo
    by_cases h8 : n < 8
    · rw [dif_pos h8, dif_pos h8]
      exact ⟨rfl, h⟩
    · rw [dif_neg h8, dif_neg h8]
      have hbyte : (a >>> UInt64.ofNat (n - 8)).toUInt8
          = UInt8.ofNat (acc >>> (n - 8)) := by
        refine UInt8.toNat_inj.1 ?_
        rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_ofNat',
          toNat_ofNat_small (by omega), Nat.shiftRight_eq_div_pow,
          Nat.shiftRight_eq_div_pow]
        exact byte_seg (by rw [show n - 8 + 8 = n from by omega]; exact h)
      have hrec : a.toNat % 2 ^ (n - 8) = (acc &&& (p2 (n - 8) - 1)) % 2 ^ (n - 8) := by
        rw [p2_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
        rw [← Nat.mod_mod_of_dvd a.toNat (Nat.pow_dvd_pow 2 (show n - 8 ≤ n from by omega)),
          h, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show n - 8 ≤ n from by omega))]
      rw [hbyte]
      exact ih (n - 8) (by omega) (by omega) _ _ hrec

/-- `flushGo` leaves exactly `n % 8` bits pending. -/
private theorem flushGo_pending : ∀ n : Nat, ∀ (buf : ByteArray) (acc : Nat),
    (Emit.W.flushGo buf acc n).2.2 = n % 8 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro buf acc
    unfold Emit.W.flushGo
    by_cases h8 : n < 8
    · rw [dif_pos h8, Nat.mod_eq_of_lt h8]
    · rw [dif_neg h8, ih (n - 8) (by omega)]
      omega

/-! ## `push` -/

/-- The fast writer's field mask keeps the low `k` bits. -/
private theorem mask_toNat {k v : Nat} (hk : k ≤ 32) :
    (UInt64.ofNat v &&& ((1 <<< UInt64.ofNat k) - 1)).toNat = v % 2 ^ k := by
  have hkk : (UInt64.ofNat k).toNat % 64 = k := toNat_ofNat_small (by omega)
  have hlt : (2 : Nat) ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hsh : ((1 : UInt64) <<< UInt64.ofNat k).toNat = 2 ^ k := by
    rw [UInt64.toNat_shiftLeft, hkk]
    show 1 <<< k % 2 ^ 64 = 2 ^ k
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt hlt]
  have hone : (1 : UInt64) ≤ (1 : UInt64) <<< UInt64.ofNat k := by
    rw [UInt64.le_iff_toNat_le, hsh]
    exact Nat.one_le_two_pow
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ hone, hsh, UInt64.toNat_ofNat']
  show (v % 2 ^ 64) &&& (2 ^ k - 1) = v % 2 ^ k
  rw [Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show k ≤ 64 from by omega))]

/-- Splitting a `(high, low)` accumulator at the field boundary. -/
private theorem split_mod {A b m k : Nat} (hb : b < 2 ^ k) :
    (A * 2 ^ k + b) % 2 ^ (m + k) = A % 2 ^ m * 2 ^ k + b := by
  have hr : A % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have hsmall : A % 2 ^ m * 2 ^ k + b < 2 ^ m * 2 ^ k := by
    have h2 : (A % 2 ^ m + 1) * 2 ^ k ≤ 2 ^ m * 2 ^ k :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have hsplit : A * 2 ^ k + b
      = A / 2 ^ m * (2 ^ m * 2 ^ k) + (A % 2 ^ m * 2 ^ k + b) := by
    have h1 : A / 2 ^ m * (2 ^ m * 2 ^ k) + A % 2 ^ m * 2 ^ k
        = (A / 2 ^ m * 2 ^ m + A % 2 ^ m) * 2 ^ k := by
      rw [Nat.add_mul, Nat.mul_assoc]
    rw [Nat.div_add_mod'] at h1
    omega
  rw [Nat.pow_add, hsplit, Nat.mul_comm (A / 2 ^ m) (2 ^ m * 2 ^ k),
    Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]

/-- Both writers' `push` is a flush of an accumulator: agreeing on the low
    `n + k` bits before the flush is the whole content of the step. -/
private theorem sim_of_flush {bw : BitWriter} {w : Emit.W} {aF : UInt64}
    {aS mF mS : Nat} (hbuf : bw.buf = w.buf) (hmm : mF = mS) (hm : mS < 64)
    (hkey : aF.toNat % 2 ^ mS = aS % 2 ^ mS) :
    Sim ⟨BitWriter.flushBytes bw.buf aF mF, aF, mF % 8⟩
        ⟨(Emit.W.flushGo w.buf aS mS).1, (Emit.W.flushGo w.buf aS mS).2.1,
          (Emit.W.flushGo w.buf aS mS).2.2⟩ := by
  subst hmm
  obtain ⟨hb, ha⟩ := flush_sim aF mF hm w.buf aS hkey
  rw [flushGo_pending] at ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · show BitWriter.flushBytes bw.buf aF mF = _
    rw [hbuf]; exact hb
  · show mF % 8 = (Emit.W.flushGo w.buf aS mF).2.2
    rw [flushGo_pending]
  · show (Emit.W.flushGo w.buf aS mF).2.2 < 8
    rw [flushGo_pending]; omega
  · show aF.toNat % 2 ^ (Emit.W.flushGo w.buf aS mF).2.2
        = (Emit.W.flushGo w.buf aS mF).2.1 % 2 ^ (Emit.W.flushGo w.buf aS mF).2.2
    rw [flushGo_pending]; exact ha

/-- The two accumulators agree on the low `n + k` bits — the whole content
    of a `push`, and reusable by the hot loop, which inlines the flush. -/
private theorem push_key {bw : BitWriter} {w : Emit.W} (h : Sim bw w) (v : Nat)
    {k : Nat} (hk : k ≤ 32) :
    ((bw.acc <<< UInt64.ofNat k)
        ||| (UInt64.ofNat v &&& ((1 <<< UInt64.ofNat k) - 1))).toNat % 2 ^ (w.n + k)
      = (w.acc * p2 k + (v &&& (p2 k - 1))) % 2 ^ (w.n + k) := by
  obtain ⟨hbuf, hn, hn8, hacc⟩ := h
  have hkk : (UInt64.ofNat k).toNat % 64 = k := toNat_ofNat_small (by omega)
  have hfast : ((bw.acc <<< UInt64.ofNat k)
      ||| (UInt64.ofNat v &&& ((1 <<< UInt64.ofNat k) - 1))).toNat
      = bw.acc.toNat % 2 ^ (64 - k) * 2 ^ k + v % 2 ^ k := by
    have hmul : (bw.acc <<< UInt64.ofNat k).toNat
        = bw.acc.toNat % 2 ^ (64 - k) * 2 ^ k := by
      rw [UInt64.toNat_shiftLeft, hkk]
      show bw.acc.toNat <<< k % 2 ^ 64 = _
      rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k from by
        rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right]
    rw [UInt64.toNat_or, hmul, mask_toNat hk,
      ← Nat.shiftLeft_eq (bw.acc.toNat % 2 ^ (64 - k)) k,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k)) _,
      Nat.shiftLeft_eq]
  rw [hfast, p2_eq, Nat.and_two_pow_sub_one_eq_mod,
    split_mod (Nat.mod_lt _ (Nat.two_pow_pos k)),
    split_mod (Nat.mod_lt _ (Nat.two_pow_pos k)),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show w.n ≤ 64 - k from by omega)),
    hacc]

/-- The shipped `push` simulates the verified `push`, for every field width
    the encoder uses. -/
theorem sim_push {k v : Nat} (hk : k ≤ 32) :
    Simulates (fun bw => bw.push k v) (fun w => w.push k v) := by
  intro bw w h
  exact sim_of_flush h.1 (by rw [h.2.1]) (by have := h.2.2.1; omega)
    (push_key h v hk)

/-! ## Derived primitives

Each fast primitive is the same recursion as its `Emit.W` counterpart, so
each proof is the corresponding structural induction over `sim_push`. -/

theorem sim_pushBits (k v : Nat) :
    Simulates (fun bw => bw.pushBits k v) (fun w => w.pushBits k v) := by
  induction k using Nat.strongRecOn generalizing v with
  | ind k ih =>
    intro bw w h
    show Sim (bw.pushBits k v) (w.pushBits k v)
    unfold BitWriter.pushBits Emit.W.pushBits
    by_cases hk : k ≤ 32
    · rw [dif_pos hk, dif_pos hk]
      exact sim_push hk bw w h
    · rw [dif_neg hk, dif_neg hk]
      exact sim_push (by omega) _ _ (ih (k - 32) (by omega) (v >>> 32) bw w h)

theorem sim_pushUnary (q : Nat) :
    Simulates (fun bw => bw.pushUnary q) (fun w => w.pushUnary q) := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro bw w h
    show Sim (bw.pushUnary q) (w.pushUnary q)
    unfold BitWriter.pushUnary Emit.W.pushUnary
    by_cases hq : q < 32
    · rw [dif_pos hq, dif_pos hq]
      exact sim_push (by omega) bw w h
    · rw [dif_neg hq, dif_neg hq]
      exact ih (q - 32) (by omega) _ _ (sim_push (by omega) bw w h)

theorem sim_pushSInt (k : Nat) (x : Int) :
    Simulates (fun bw => bw.pushSInt k x) (fun w => w.pushSInt k x) :=
  sim_pushBits k _

/-- Byte alignment: the fast writer reads its own pending count, and the
    simulation is what says that count is the verified writer's. -/
theorem sim_align :
    Simulates BitWriter.align (fun w => w.push ((8 - w.n % 8) % 8) 0) := by
  intro bw w h
  show Sim (bw.push ((8 - bw.n % 8) % 8) 0) _
  rw [h.2.1]
  exact sim_push (by omega) bw w h

theorem sim_pushRice {k : Nat} (hk : k ≤ 32) (x : Int) :
    Simulates (fun bw => bw.pushRice k x) (fun w => w.pushRice k x) := by
  intro bw w h
  exact sim_push hk _ _ (sim_pushUnary _ _ _ h)

/-- The rare wide-quotient path of `pushRiceRange`: an already-folded
    magnitude, so there is no `zigzag` left to match. -/
theorem sim_pushRiceFolded {k : Nat} (hk : k ≤ 32) (u : Nat) :
    Simulates (fun bw => bw.pushRiceFolded k u)
      (fun w => (w.pushUnary (u >>> k)).push k (u &&& (p2 k - 1))) := by
  intro bw w h
  exact sim_push hk _ _ (sim_pushUnary _ _ _ h)

/-! ## Sequence writers -/

theorem sim_pushSIntSeg (b : Nat) (xs : Array Int) (start len : Nat) :
    Simulates (BitWriter.pushSIntSeg b xs start len)
      (Emit.W.pushSIntSeg b xs start len) := by
  induction len generalizing start with
  | zero => intro bw w h; exact h
  | succ len ih =>
    intro bw w h
    show Sim (BitWriter.pushSIntSeg b xs start (len + 1) bw)
      (Emit.W.pushSIntSeg b xs start (len + 1) w)
    unfold BitWriter.pushSIntSeg Emit.W.pushSIntSeg
    by_cases hs : start < xs.size
    · rw [if_pos hs, if_pos hs]
      exact ih (start + 1) _ _ (sim_pushSInt b _ _ _ h)
    · rw [if_neg hs, if_neg hs]
      exact h

theorem sim_pushSIntList (b : Nat) (cs : List Int) :
    Simulates (BitWriter.pushSIntList b cs) (Emit.W.pushSIntList b cs) := by
  induction cs with
  | nil => intro bw w h; exact h
  | cons c cs ih =>
    intro bw w h
    show Sim (BitWriter.pushSIntList b (c :: cs) bw)
      (Emit.W.pushSIntList b (c :: cs) w)
    unfold BitWriter.pushSIntList Emit.W.pushSIntList
    exact ih _ _ (sim_pushSInt b c _ _ h)

theorem sim_pushConts (v k : Nat) :
    Simulates (BitWriter.pushConts v k) (Emit.W.pushConts v k) := by
  induction k with
  | zero => intro bw w h; exact h
  | succ k ih =>
    intro bw w h
    show Sim (BitWriter.pushConts v (k + 1) bw) (Emit.W.pushConts v (k + 1) w)
    unfold BitWriter.pushConts Emit.W.pushConts
    exact ih _ _ (sim_push (by omega) _ _ h)

theorem sim_pushUtf8 (v : Nat) :
    Simulates (fun bw => bw.pushUtf8 v) (Emit.W.pushUtf8 v) := by
  intro bw w h
  show Sim (bw.pushUtf8 v) (Emit.W.pushUtf8 v w)
  unfold BitWriter.pushUtf8 Emit.W.pushUtf8
  split
  · exact sim_push (by omega) _ _ h
  · split
    · exact sim_pushConts v 1 _ _ (sim_push (by omega) _ _ h)
    · split
      · exact sim_pushConts v 2 _ _ (sim_push (by omega) _ _ h)
      · split
        · exact sim_pushConts v 3 _ _ (sim_push (by omega) _ _ h)
        · split
          · exact sim_pushConts v 4 _ _ (sim_push (by omega) _ _ h)
          · split
            · exact sim_pushConts v 5 _ _ (sim_push (by omega) _ _ h)
            · exact sim_pushConts v 6 _ _ (sim_push (by omega) _ _ h)

/-! ## The unpacked residual writer

`pushRiceRange` is the encoder's hot loop: it carries `buf`/`acc`/`n` as
three parameters rather than a `BitWriter`, so the per-sample path allocates
nothing. It stays provable because it goes through the same accumulator step
`push` does (`BitWriter.accPush`), which makes each of its two pushes
*definitionally* a `push` — there is no inlining left to discharge. -/

/-- The model writer masks the pushed value itself, so pre-masking is
    invisible. The hot loop hands it the unmasked magnitude. -/
private theorem W_push_mask (w : Emit.W) (k v : Nat) :
    Emit.W.push w k (v &&& (p2 k - 1)) = Emit.W.push w k v := by
  unfold Emit.W.push
  rw [p2_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod]

/-- The hot loop simulates `Emit.W.pushRiceSeg`. The partition never runs
    past the residual (`start + len ≤ res.size`), which is what lets the
    fast loop test only `i < stop` where the model also tests the array
    bound. -/
theorem sim_pushRiceRange {k : Nat} (hk : k ≤ 32) (res : Array Int) :
    ∀ (len start : Nat), start + len ≤ res.size →
      ∀ bw w, Sim bw w →
        Sim (pushRiceRange k (p2 k - 1) res start (start + len) bw.buf bw.acc bw.n)
          (Emit.W.pushRiceSeg k res start len w) := by
  intro len
  induction len with
  | zero =>
    intro start _ bw w h
    rw [pushRiceRange]
    simp only []
    rw [dif_neg (by omega)]
    exact h
  | succ len ih =>
    intro start hlen bw w h
    have hsize : start < res.size := by omega
    have hzz : (if 0 ≤ res.getD start 0 then 2 * (res.getD start 0).toNat
        else 2 * (-res.getD start 0).toNat - 1)
          = Rice.zigzag (res.getD start 0) := rfl
    rw [pushRiceRange]
    simp only []
    rw [dif_pos (show start < start + (len + 1) from by omega), hzz,
      show start + (len + 1) = start + 1 + len from by omega]
    simp only [Emit.W.pushRiceSeg]
    rw [if_pos hsize]
    by_cases hq : Rice.zigzag (res.getD start 0) >>> k < 32
    · rw [if_pos hq]
      have hw : Emit.W.pushRice w k (res.getD start 0)
          = (w.push (Rice.zigzag (res.getD start 0) >>> k + 1) 1).push k
              (Rice.zigzag (res.getD start 0)) := by
        rw [Emit.W.pushRice, W_push_mask, Emit.W.pushUnary, dif_pos hq]
      rw [hw]
      exact ih (start + 1) (by omega) _ _
        (sim_push hk _ _ (sim_push (show _ + 1 ≤ 32 from by omega) bw w h))
    · rw [if_neg hq]
      exact ih (start + 1) (by omega) _ _
        (sim_push hk _ _ (sim_pushUnary _ _ _ h))

/-! ## Partitions and residuals -/

private theorem paramBits_le (m : Rice.Method) : m.paramBits ≤ 32 := by
  cases m <;> decide

theorem sim_pushPartsR (m : Rice.Method) (res : Array Int) :
    ∀ (choices : List Rice.Partition) (sizes : List Nat) (start : Nat),
      (∀ k, Rice.Partition.rice k ∈ choices → k ≤ 32) →
      start + sizes.sum ≤ res.size →
      Simulates (pushPartsR m res choices sizes start)
        (Emit.W.pushParts m res choices sizes start) := by
  intro choices
  induction choices with
  | nil => intro sizes start _ _ bw w h; exact h
  | cons ch chs ih =>
    intro sizes start hk hb bw w h
    cases sizes with
    | nil => exact h
    | cons sz szs =>
      have hsum : (sz :: szs).sum = sz + szs.sum := by
        simp only [List.sum_cons]
      have hbnd : start + sz ≤ res.size := by omega
      have hb' : start + sz + szs.sum ≤ res.size := by omega
      have hk' : ∀ k, Rice.Partition.rice k ∈ chs → k ≤ 32 :=
        fun k hm => hk k (List.mem_cons_of_mem _ hm)
      simp only [pushPartsR, Emit.W.pushParts]
      cases ch with
      | rice k =>
        exact ih szs (start + sz) hk' hb' _ _
          (sim_pushRiceRange (hk k (List.mem_cons_self ..)) res sz start hbnd _ _
            (sim_push (paramBits_le m) bw w h))
      | escape bits =>
        exact ih szs (start + sz) hk' hb' _ _
          (sim_pushSIntSeg bits res start sz _ _
            (sim_push (by omega) _ _ (sim_push (paramBits_le m) bw w h)))

theorem sim_pushResidual (bs ord po : Nat) (ks : Array Nat) (res : Array Int)
    (hb : (Rice.partSizes bs po ord).sum ≤ res.size) :
    Simulates (fun bw => pushResidual bw bs ord po ks res)
      (Emit.W.pushResidual bs ord (riceCfgOf po ks) res) := by
  intro bw w h
  -- every parameter is clamped to 14 where the choice list is built
  have hk : ∀ k, Rice.Partition.rice k ∈ riceChoices po ks → k ≤ 32 := by
    intro k hm
    unfold riceChoices at hm
    obtain ⟨j, _, hj⟩ := List.mem_map.1 hm
    cases hj
    omega
  exact sim_pushPartsR .rice4 res (riceChoices po ks) (Rice.partSizes bs po ord) 0
    hk (by omega) _ _ (sim_push (by omega) _ _ (sim_push (by omega) bw w h))

/-! ## Subframes -/

/-- Subframe content: the fast plan's emission simulates
    `Emit.W.pushContent` at the plan's reference configuration. -/
theorem sim_pushContent (b : Nat) (pl : SubPlan) (xs : Array Int)
    (hok : pl.EmitOk xs) :
    Simulates (fun bw => pushContentOf bw b pl xs)
      (Emit.W.pushContent b (subCfgOf pl) xs) := by
  intro bw w h
  cases pl with
  | constant => exact sim_pushSInt b _ _ _ h
  | verbatim => exact sim_pushSIntSeg b xs 0 xs.size _ _ h
  | fixed ord po ks =>
    exact sim_pushResidual xs.size ord po ks _ hok _ _
      (sim_pushSIntSeg b xs 0 ord _ _ h)
  | lpc cs shift po ks =>
    exact sim_pushResidual xs.size cs.length po ks _ hok _ _
      (sim_pushSIntList 12 cs _ _
        (sim_pushSInt 5 _ _ _ (sim_push (by omega) _ _
          (sim_pushSIntSeg b xs 0 cs.length _ _ h))))

/-- One subframe, header bits included. Stated against `Emit.W.pushContent`
    so the wasted-bit *scaling* correspondence (`p.scaled` is the scaled
    block) stays with the chooser, where it belongs. -/
theorem sim_pushSubframeOf (p : SubPrep) (hok : p.plan.EmitOk p.scaled) :
    Simulates (fun bw => pushSubframeOf bw p)
      (fun w => Emit.W.pushContent (p.depth - p.wasted) (subCfgOf p.plan) p.scaled
        (if p.wasted = 0 then ((w.push 1 0).push 6 p.plan.typeCode).push 1 0
         else (((w.push 1 0).push 6 p.plan.typeCode).push 1 1).pushUnary
           (p.wasted - 1))) := by
  intro bw w h
  have hhdr : Sim
      (if p.wasted = 0 then ((bw.push 1 0).push 6 p.plan.typeCode).push 1 0
       else (((bw.push 1 0).push 6 p.plan.typeCode).push 1 1).pushUnary (p.wasted - 1))
      (if p.wasted = 0 then ((w.push 1 0).push 6 p.plan.typeCode).push 1 0
       else (((w.push 1 0).push 6 p.plan.typeCode).push 1 1).pushUnary
         (p.wasted - 1)) := by
    by_cases hw : p.wasted = 0
    · rw [if_pos hw, if_pos hw]
      exact sim_push (by omega) _ _ (sim_push (by omega) _ _
        (sim_push (by omega) bw w h))
    · rw [if_neg hw, if_neg hw]
      exact sim_pushUnary _ _ _ (sim_push (by omega) _ _
        (sim_push (by omega) _ _ (sim_push (by omega) bw w h)))
  exact sim_pushContent _ p.plan p.scaled hok _ _ hhdr

/-! ## Frames -/

private theorem typeCode_subCfgOf (pl : SubPlan) :
    (subCfgOf pl).typeCode = pl.typeCode := by
  cases pl <;> rfl

/-- One subframe against the reference writer, with the wasted-bit scaling
    supplied by the chooser (`SubPrep.Denotes`). -/
theorem sim_pushSubframe (p : SubPrep) (xs : Array Int) (hd : p.Denotes xs)
    (hok : p.plan.EmitOk p.scaled) :
    Simulates (fun bw => pushSubframeOf bw p)
      (Emit.W.pushSubframe p.depth ⟨p.wasted, subCfgOf p.plan⟩ xs) := by
  intro bw w h
  have he : Emit.W.pushSubframe p.depth ⟨p.wasted, subCfgOf p.plan⟩ xs w
      = Emit.W.pushContent (p.depth - p.wasted) (subCfgOf p.plan) p.scaled
        (if p.wasted = 0 then ((w.push 1 0).push 6 p.plan.typeCode).push 1 0
         else (((w.push 1 0).push 6 p.plan.typeCode).push 1 1).pushUnary
           (p.wasted - 1)) := by
    simp only [Emit.W.pushSubframe, typeCode_subCfgOf]
    rw [← hd]
  rw [he]
  exact sim_pushSubframeOf p hok bw w h

theorem sim_pushPlanOf : ∀ qs : List (SubPrep × Array Int),
    (∀ q ∈ qs, q.1.Denotes q.2 ∧ q.1.plan.EmitOk q.1.scaled) →
    Simulates (pushPlanOf qs) (Emit.W.pushPlan (planOf qs)) := by
  intro qs
  induction qs with
  | nil => intro _ bw w h; exact h
  | cons q qs ih =>
    intro hq bw w h
    obtain ⟨hd, hok⟩ := hq q (List.mem_cons_self ..)
    have hq' : ∀ r ∈ qs, r.1.Denotes r.2 ∧ r.1.plan.EmitOk r.1.scaled :=
      fun r hm => hq r (List.mem_cons_of_mem _ hm)
    simp only [pushPlanOf, planOf]
    exact ih hq' _ _ (sim_pushSubframe q.1 q.2 hd hok bw w h)

/-- A value read off the writer's own buffer — a CRC over the bytes emitted
    so far — is the same value on both sides, because the buffers are. -/
private theorem sim_push_buf {bw : BitWriter} {w : Emit.W} (h : Sim bw w)
    {k : Nat} (hk : k ≤ 32) (f : ByteArray → Nat) :
    Sim (bw.push k (f bw.buf)) (w.push k (f w.buf)) := by
  rw [h.1]
  exact sim_push hk bw w h

/-- One frame. The CRCs are computed over each writer's own buffer, and the
    simulation is exactly what makes those buffers equal. -/
theorem sim_pushFrameOf (b : Nat) (strat : Bool) (num : Nat) (fp : FramePrep)
    (asg : Frame.ChannelAsg) (chs : List (Array Int))
    (qs : List (SubPrep × Array Int))
    (hsubs : fp.subs = qs)
    (hplan : planOf qs = Emit.W.planA b asg chs)
    (hbs : fp.blockSize = (chs.headD #[]).size)
    (hcode : fp.code fp.subs.length = asg.code chs.length)
    (hq : ∀ q ∈ qs, q.1.Denotes q.2 ∧ q.1.plan.EmitOk q.1.scaled) :
    Simulates (fun bw => pushFrameOf bw b strat num fp)
      (Emit.W.pushFrame b strat num asg chs) := by
  intro bw w h
  have hstart : bw.buf.size = w.buf.size := by rw [h.1]
  -- the header, up to but not including the CRC-8
  have h1 : Sim
      ((((((((((bw.push 14 0x3FFE).push 1 0).push 1
        (if strat then 1 else 0)).push 4 7).push 4 0).push 4
        (fp.code fp.subs.length)).push 3
        (Frame.bpsCode b)).push 1 0).pushUtf8 num).push 16 (fp.blockSize - 1))
      (Emit.W.pushHeaderCore b strat num (chs.headD #[]).size
        (asg.code chs.length) w) := by
    rw [hcode, hbs]
    simp only [Emit.W.pushHeaderCore]
    have s1 := sim_push (k := 14) (v := 0x3FFE) (by omega) bw w h
    have s2 := sim_push (k := 1) (v := 0) (by omega) _ _ s1
    have s3 := sim_push (k := 1) (v := if strat then 1 else 0) (by omega) _ _ s2
    have s4 := sim_push (k := 4) (v := 7) (by omega) _ _ s3
    have s5 := sim_push (k := 4) (v := 0) (by omega) _ _ s4
    have s6 := sim_push (k := 4) (v := asg.code chs.length) (by omega) _ _ s5
    have s7 := sim_push (k := 3) (v := Frame.bpsCode b) (by omega) _ _ s6
    have s8 := sim_push (k := 1) (v := 0) (by omega) _ _ s7
    have s9 := sim_pushUtf8 num _ _ s8
    exact sim_push (k := 16) (v := (chs.headD #[]).size - 1) (by omega) _ _ s9
  rw [hsubs] at h1
  simp only [pushFrameOf, Emit.W.pushFrame, hsubs, hstart]
  refine sim_push_buf ?_ (by omega)
    (fun buf => (Crc.crc16Range buf w.buf.size buf.size).toNat)
  refine sim_align _ _ ?_
  rw [← hplan]
  refine sim_pushPlanOf qs hq _ _ ?_
  refine sim_push_buf ?_ (by omega)
    (fun buf => (Crc.crc8Range buf w.buf.size buf.size).toNat)
  exact h1

/-! ## The input bridge

The shipped encoder reads its samples straight out of the interleaved PCM
bytes, one window per frame worker (`frameChannels`). The reference reads
`deinterleave ch (pcm16OfByteList …)` and chunks it with
`Stream.chunkChannels`. These lemmas identify the two. -/

private theorem getD_toList (bytes : ByteArray) (j : Nat) :
    bytes.data.toList.getD j (0 : UInt8) = if h : j < bytes.size then bytes[j] else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < bytes.size
  · rw [dif_pos h, List.getElem?_eq_getElem (by simpa using h)]
    rfl
  · rw [dif_neg h, List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    rfl

/-- The fast per-sample read is the reference's byte pair. -/
private theorem sampleAt_eq (bytes : ByteArray) (j : Nat) :
    sampleAt bytes j
      = Flac.sInt16 (bytes.data.toList.getD j 0) (bytes.data.toList.getD (j + 1) 0) := by
  rw [getD_toList, getD_toList]
  rfl

/-- Indexing the parsed sample list, valid at every index because an even
    byte count leaves no trailing byte (`encodePcm16` rejects odd input). -/
private theorem getD_pcm16OfByteList : ∀ (n : Nat) (l : List UInt8), l.length = n →
    l.length % 2 = 0 → ∀ j, (Flac.pcm16OfByteList l).getD j 0
      = Flac.sInt16 (l.getD (2 * j) 0) (l.getD (2 * j + 1) 0) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hn hev j
    match l with
    | [] => simp [Flac.pcm16OfByteList, Flac.sInt16]
    | [_] => simp at hev
    | lo :: hi :: rest =>
      cases j with
      | zero => simp [Flac.pcm16OfByteList]
      | succ j =>
        have hrest : rest.length < n := by
          simp only [List.length_cons] at hn; omega
        have hev' : rest.length % 2 = 0 := by
          simp only [List.length_cons] at hev; omega
        show (Flac.pcm16OfByteList rest).getD j 0 = _
        rw [ih rest.length hrest rest rfl hev' j,
          show 2 * (j + 1) = 2 * j + 1 + 1 from by omega]
        simp only [List.getD_cons_succ]

/-- The sample at interleaved index `i` is the fast reader's byte pair. -/
private theorem getD_samples (bytes : ByteArray) (hev : bytes.size % 2 = 0) (i : Nat) :
    (Flac.pcm16OfByteList bytes.data.toList).getD i 0 = sampleAt bytes (2 * i) := by
  rw [getD_pcm16OfByteList bytes.data.toList.length bytes.data.toList rfl
    (by simpa using hev) i, sampleAt_eq]

private theorem getD_take {l : List Int} {m c : Nat} (h : c < m) :
    (l.take m).getD c 0 = l.getD c 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt h]

private theorem getD_drop : ∀ (m : Nat) (l : List Int) (i : Nat),
    (l.drop m).getD i 0 = l.getD (m + i) 0 := by
  intro m
  induction m with
  | zero => intro l i; simp
  | succ m ih =>
    intro l i
    match l with
    | [] => simp
    | x :: t =>
      simp only [List.drop_succ_cons]
      rw [ih t i, show m + 1 + i = m + i + 1 from by omega,
        List.getD_cons_succ]

private theorem getD_zipWith_cons {as : List Int} {bs : List (List Int)} {c : Nat}
    (ha : c < as.length) (hb : c < bs.length) :
    (List.zipWith (· :: ·) as bs).getD c [] = as.getD c 0 :: bs.getD c [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
  rfl

/-- Every deinterleaved channel has exactly `n` samples. -/
private theorem length_getD_deinterleaveN (ch : Nat) (_hch : 0 < ch) :
    ∀ (n : Nat) (l : List Int), n * ch ≤ l.length → ∀ c, c < ch →
      ((Flac.deinterleaveN ch n l).getD c []).length = n := by
  intro n
  induction n with
  | zero =>
    intro l _ c _
    simp only [Flac.deinterleaveN, List.getD_eq_getElem?_getD]
    cases h : (List.replicate ch ([] : List Int))[c]? with
    | none => rfl
    | some x =>
      have := List.getElem?_eq_some_iff.1 h
      obtain ⟨_, hx⟩ := this
      rw [Option.getD_some, ← hx, List.getElem_replicate]
      rfl
  | succ n ih =>
    intro l hl c hc
    have hstep : (n + 1) * ch = n * ch + ch := Nat.succ_mul ..
    have hbs : (Flac.deinterleaveN ch n (l.drop ch)).length = ch :=
      Flac.length_deinterleaveN ch n _ (by simp only [List.length_drop]; omega)
    have hta : (l.take ch).length = ch := by
      simp only [List.length_take]; omega
    simp only [Flac.deinterleaveN]
    rw [getD_zipWith_cons (by rw [hta]; exact hc) (by rw [hbs]; exact hc),
      List.length_cons,
      ih (l.drop ch) (by simp only [List.length_drop]; omega) c hc]

/-- Sample `t` of channel `c` is interleaved sample `t * ch + c`. -/
private theorem getD_deinterleaveN (ch : Nat) (_hch : 0 < ch) :
    ∀ (n : Nat) (l : List Int), n * ch ≤ l.length → ∀ c t, c < ch → t < n →
      ((Flac.deinterleaveN ch n l).getD c []).getD t 0 = l.getD (t * ch + c) 0 := by
  intro n
  induction n with
  | zero => intro _ _ _ t _ ht; omega
  | succ n ih =>
    intro l hl c t hc ht
    have hstep : (n + 1) * ch = n * ch + ch := Nat.succ_mul ..
    have hbs : (Flac.deinterleaveN ch n (l.drop ch)).length = ch :=
      Flac.length_deinterleaveN ch n _ (by simp only [List.length_drop]; omega)
    have hta : (l.take ch).length = ch := by
      simp only [List.length_take]; omega
    simp only [Flac.deinterleaveN]
    rw [getD_zipWith_cons (by rw [hta]; exact hc) (by rw [hbs]; exact hc)]
    cases t with
    | zero =>
      rw [List.getD_cons_zero, getD_take hc]
      congr 1
      omega
    | succ t =>
      have hts : (t + 1) * ch = t * ch + ch := Nat.succ_mul ..
      rw [List.getD_cons_succ,
        ih (l.drop ch) (by simp only [List.length_drop]; omega) c t hc (by omega),
        getD_drop]
      congr 1
      omega

private theorem drop_eq_getD_cons {α : Type} {l : List α} {i : Nat} (d : α)
    (h : i < l.length) : l.drop i = l.getD i d :: l.drop (i + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.drop_eq_getElem_cons h

private theorem length_getD_deinterleave {ch : Nat} (hch : 0 < ch) (l : List Int)
    {c : Nat} (hc : c < ch) :
    ((Flac.deinterleave ch l).getD c []).length = l.length / ch :=
  length_getD_deinterleaveN ch hch _ l (Nat.div_mul_le_self ..) c hc

private theorem getD_deinterleave {ch : Nat} (hch : 0 < ch) (l : List Int)
    {c t : Nat} (hc : c < ch) (ht : t < l.length / ch) :
    ((Flac.deinterleave ch l).getD c []).getD t 0 = l.getD (t * ch + c) 0 :=
  getD_deinterleaveN ch hch _ l (Nat.div_mul_le_self ..) c t hc ht

private theorem length_deinterleave {ch : Nat} (l : List Int) :
    (Flac.deinterleave ch l).length = ch :=
  Flac.length_deinterleaveN ch _ l (Nat.div_mul_le_self ..)

/-- One channel's window: what the frame worker reads out of the shared PCM
    bytes is the reference channel's `drop`-then-`take`. -/
private theorem channelSeg_eq (bytes : ByteArray) (hev : bytes.size % 2 = 0)
    {ch : Nat} (hch : 0 < ch) {c : Nat} (hc : c < ch) :
    ∀ (rem i : Nat) (out : Array Int),
      i + rem ≤ (Flac.pcm16OfByteList bytes.data.toList).length / ch →
      (channelSeg bytes ch c i rem out).toList
        = out.toList ++ ((((Flac.deinterleave ch
            (Flac.pcm16OfByteList bytes.data.toList)).getD c []).drop i).take rem) := by
  have hlen := length_getD_deinterleave hch (Flac.pcm16OfByteList bytes.data.toList) hc
  intro rem
  induction rem with
  | zero => intro i out _; simp [channelSeg]
  | succ rem ih =>
    intro i out hb
    have hi : i < ((Flac.deinterleave ch
        (Flac.pcm16OfByteList bytes.data.toList)).getD c []).length := by
      rw [hlen]; omega
    have hgi : ((Flac.deinterleave ch
        (Flac.pcm16OfByteList bytes.data.toList)).getD c []).getD i 0
        = sampleAt bytes (2 * (i * ch + c)) := by
      rw [getD_deinterleave hch (Flac.pcm16OfByteList bytes.data.toList) hc
        (by rw [hlen] at hi; omega), getD_samples bytes hev]
    simp only [channelSeg]
    rw [ih (i + 1) _ (by omega), Array.toList_push,
      drop_eq_getD_cons 0 hi, List.take_succ_cons, hgi, List.append_assoc]
    rfl

/-- All channels of one frame's window. -/
private theorem frameChannelsGo_eq (bytes : ByteArray) (hev : bytes.size % 2 = 0)
    {ch : Nat} (hch : 0 < ch) (lo len : Nat)
    (hfit : lo + len ≤ (Flac.pcm16OfByteList bytes.data.toList).length / ch) :
    ∀ (rem c : Nat) (out : Array (Array Int)), c + rem ≤ ch →
      (frameChannelsGo bytes ch lo len c rem out).toList
        = out.toList ++ (((Flac.deinterleave ch
            (Flac.pcm16OfByteList bytes.data.toList)).drop c).take rem).map
              (fun l => ((l.drop lo).take len).toArray) := by
  have hchs := length_deinterleave (ch := ch) (Flac.pcm16OfByteList bytes.data.toList)
  intro rem
  induction rem with
  | zero => intro c out _; simp [frameChannelsGo]
  | succ rem ih =>
    intro c out hb
    have hc : c < ch := by omega
    have hcl : c < (Flac.deinterleave ch
        (Flac.pcm16OfByteList bytes.data.toList)).length := by rw [hchs]; omega
    have hseg : channelSeg bytes ch c lo len (Array.emptyWithCapacity len)
        = ((((Flac.deinterleave ch
            (Flac.pcm16OfByteList bytes.data.toList)).getD c []).drop lo).take len).toArray := by
      have h := channelSeg_eq bytes hev hch hc len lo
        (Array.emptyWithCapacity len) (by omega)
      rw [show (Array.emptyWithCapacity len : Array Int).toList = [] from rfl,
        List.nil_append] at h
      rw [← h, Array.toArray_toList]
    simp only [frameChannelsGo]
    rw [ih (c + 1) _ (by omega), Array.toList_push, hseg,
      drop_eq_getD_cons [] hcl, List.take_succ_cons, List.map_cons,
      List.append_assoc]
    rfl

/-- **The input bridge.** The window each frame worker deinterleaves out of
    the shared PCM bytes is exactly the reference's frame: the channels of
    `deinterleave ∘ pcm16OfByteList`, dropped to `lo` and taken to `len` —
    which is what `Stream.chunkChannels` hands the verified emitter. -/
theorem frameChannels_eq (bytes : ByteArray) (hev : bytes.size % 2 = 0) {ch : Nat}
    (hch : 0 < ch) (lo len : Nat)
    (hfit : lo + len ≤ (Flac.pcm16OfByteList bytes.data.toList).length / ch) :
    (frameChannels bytes ch lo (lo + len)).toList
      = (Stream.takeAll len (Stream.dropAll lo (Flac.deinterleave ch
          (Flac.pcm16OfByteList bytes.data.toList)))).map List.toArray := by
  have hchs := length_deinterleave (ch := ch) (Flac.pcm16OfByteList bytes.data.toList)
  have h := frameChannelsGo_eq bytes hev hch lo len hfit ch 0
    (Array.emptyWithCapacity ch) (by omega)
  simp only [frameChannels, Nat.add_sub_cancel_left]
  rw [h, show (Array.emptyWithCapacity ch : Array (Array Int)).toList = [] from rfl,
    List.nil_append, List.drop_zero, List.take_of_length_le (Nat.le_of_eq hchs)]
  simp only [Stream.takeAll, Stream.dropAll, List.map_map]
  rfl

/-! ## The sanitised plan is valid

Every bound `Subframe.SubCfg.Valid` asks of the search's output is scalar, so
`SubPlan.sanitize`'s O(1) clamps establish all of them — nothing here reasons
about a `Float`. -/

private theorem fitsSInt_zero (n : Nat) : Flac.Bits.FitsSInt n 0 := by
  have h : (0 : Int) < ((2 ^ n : Nat) : Int) := Int.natCast_pos.2 (Nat.two_pow_pos n)
  unfold Flac.Bits.FitsSInt
  omega

theorem safePo_le (bs ord po : Nat) : safePo bs ord po ≤ 6 := by
  unfold safePo; split <;> omega

theorem safePo_dvd {bs ord po : Nat} (_h : ord < bs) :
    2 ^ safePo bs ord po ∣ bs := by
  unfold safePo
  split
  · rename_i hg
    exact (Nat.dvd_iff_mod_eq_zero ..).2 (by rw [← p2_eq]; exact hg.1)
  · simp

theorem safePo_ord {bs ord po : Nat} (h : ord < bs) :
    ord < bs / 2 ^ safePo bs ord po := by
  unfold safePo
  split
  · rename_i hg
    rw [← p2_eq]; exact hg.2.1
  · simpa using h

/-- A clamped Rice choice list is a valid residual configuration whenever the
    partition arithmetic works out — the `k < 15` half is the clamp in
    `riceChoices`. -/
theorem riceCfgOf_valid {bs ord po : Nat} (ks : Array Nat) {res : List Int}
    (hpo : po < 16) (hdvd : 2 ^ po ∣ bs) (hord : ord < bs / 2 ^ po)
    (hlen : res.length = bs - ord) :
    (riceCfgOf po ks).Valid bs ord res := by
  refine ⟨hpo, hdvd, hord, hlen, ?_, ?_⟩
  · show (riceChoices po ks).length = 2 ^ po
    unfold riceChoices
    rw [List.length_map, List.length_range, p2_eq]
  · intro p hp
    have h1 : p.1 ∈ riceChoices po ks := (List.of_mem_zip hp).1
    unfold riceChoices at h1
    obtain ⟨j, _, hj⟩ := List.mem_map.1 h1
    rw [← hj]
    show min (ks.getD j 10) 14 < 15
    omega

/-- The sanitised plan's reference configuration is valid on the block it was
    chosen for. `hc` is discharged by `choosePlanF`'s own constant-block
    guard; `hfit` comes from the input's bit depth. -/
theorem subCfgOf_sanitize_valid {b : Nat} (pl : SubPlan) {xs : List Int}
    (hfit : ∀ x ∈ xs, Flac.Bits.FitsSInt b x)
    (hc : pl = .constant → ∀ x ∈ xs, x = xs.headD 0) :
    (subCfgOf (pl.sanitize xs.length)).Valid b xs := by
  have hhead : Flac.Bits.FitsSInt b (xs.headD 0) := by
    match xs with
    | [] => exact fitsSInt_zero b
    | y :: t => exact hfit y (List.mem_cons_self ..)
  cases pl with
  | constant => exact ⟨hc rfl, hhead⟩
  | verbatim => exact hfit
  | fixed ord po ks =>
    show (subCfgOf (if min ord 4 < xs.length then _ else _)).Valid b xs
    split
    · rename_i hlt
      refine ⟨Nat.min_le_right .., fun x hx => hfit x (List.mem_of_mem_take hx), ?_⟩
      exact riceCfgOf_valid ks
        (by have := safePo_le xs.length (min ord 4) po; omega)
        (safePo_dvd hlt) (safePo_ord hlt)
        (by rw [Flac.Fixed.residual, Flac.Fixed.length_diffN])
    · exact hfit
  | lpc cs shift po ks =>
    show (subCfgOf (if 0 < ((cs.take 32).map clamp12).length ∧
      ((cs.take 32).map clamp12).length < xs.length then _ else _)).Valid b xs
    split
    · rename_i hg
      refine ⟨hg.1, ?_, ?_, ?_, ?_, ?_, Nat.min_le_right .., ?_⟩
      · rw [List.length_map, List.length_take]; omega
      · exact fun x hx => hfit x (List.mem_of_mem_take hx)
      · omega
      · omega
      · intro c hcm
        obtain ⟨d, _, hd⟩ := List.mem_map.1 hcm
        rw [← hd]
        unfold clamp12
        split
        · rename_i hf; exact hf
        · exact fitsSInt_zero 12
      · exact riceCfgOf_valid ks
          (by have := safePo_le xs.length ((cs.take 32).map clamp12).length po
              omega)
          (safePo_dvd hg.2) (safePo_ord hg.2)
          (by rw [Flac.Lpc.length_residual])
    · exact hfit

/-! ## Emission's own precondition is derivable too

`SubPlan.EmitOk` asks that the partitions cover no more than the residual
they code. Under the partition arithmetic `SubPlan.sanitize` already
guarantees, they cover it exactly, so nothing extra is checked at run time. -/

private theorem sum_replicate (n c : Nat) : (List.replicate n c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]
    omega

/-- The partitions of a legal configuration cover the residual exactly. -/
theorem partSizes_sum {bs po ord : Nat} (hdvd : 2 ^ po ∣ bs)
    (hord : ord < bs / 2 ^ po) : (Rice.partSizes bs po ord).sum = bs - ord := by
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < 2 ^ po := Nat.two_pow_pos po
  have hdiv : bs / 2 ^ po = c := by rw [hc, Nat.mul_div_cancel_left _ hpos]
  have hoc : ord < c := by rw [hdiv] at hord; exact hord
  have hle : c ≤ 2 ^ po * c := Nat.le_mul_of_pos_left c hpos
  have h2 : (2 ^ po - 1) * c = 2 ^ po * c - c := by rw [Nat.sub_mul, Nat.one_mul]
  unfold Rice.partSizes
  rw [List.sum_cons, sum_replicate, hdiv, hc]
  omega

theorem emitOk_sanitize (pl : SubPlan) (xs : Array Int) :
    (pl.sanitize xs.size).EmitOk xs := by
  cases pl with
  | constant => exact trivial
  | verbatim => exact trivial
  | fixed ord po ks =>
    show SubPlan.EmitOk (if min ord 4 < xs.size then _ else _) xs
    split
    · rename_i hlt
      show (Rice.partSizes xs.size (safePo xs.size (min ord 4) po) (min ord 4)).sum
        ≤ (Flac.Emit.fixedResA (min ord 4) xs).size
      have hsz : (Flac.Emit.fixedResA (min ord 4) xs).size = xs.size - min ord 4 := by
        rw [← Array.length_toList, Flac.Emit.fixedResA_toList, Flac.Fixed.residual,
          Flac.Fixed.length_diffN, Array.length_toList]
      rw [partSizes_sum (safePo_dvd hlt) (safePo_ord hlt), hsz]
      omega
    · exact trivial
  | lpc cs shift po ks =>
    show SubPlan.EmitOk (if 0 < ((cs.take 32).map clamp12).length ∧
      ((cs.take 32).map clamp12).length < xs.size then _ else _) xs
    split
    · rename_i hg
      show (Rice.partSizes xs.size
          (safePo xs.size ((cs.take 32).map clamp12).length po)
          ((cs.take 32).map clamp12).length).sum
        ≤ (Flac.Emit.lpcResA ((cs.take 32).map clamp12) (min shift 15) xs).size
      have hsz : (Flac.Emit.lpcResA ((cs.take 32).map clamp12) (min shift 15) xs).size
          = xs.size - ((cs.take 32).map clamp12).length := by
        rw [← Array.length_toList, Flac.Emit.lpcResA_toList,
          Flac.Lpc.length_residual, Array.length_toList]
      rw [partSizes_sum (safePo_dvd hg.2) (safePo_ord hg.2), hsz]
      omega
    · exact trivial

/-! ## Wasted bits are sound

The one part of `Subframe.SubCfg.Valid` that is not scalar: every sample must
be divisible by `2 ^ wasted`. `wastedDetectF` establishes it by construction —
it takes the minimum trailing-zero count over the block — so this is a proof,
not a runtime scan. -/

private theorem tzGo_dvd : ∀ (fuel n : Nat), 2 ^ tzGo fuel n ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n; simp [tzGo]
  | succ fuel ih =>
    intro n
    show 2 ^ (if n % 2 = 0 then 1 + tzGo fuel (n / 2) else 0) ∣ n
    split
    · rename_i he
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero he
      have h := ih (n / 2)
      rw [hm, Nat.mul_div_cancel_left _ (show 0 < 2 by omega)] at h
      rw [hm, Nat.mul_div_cancel_left _ (show 0 < 2 by omega), Nat.pow_add,
        Nat.pow_one]
      exact Nat.mul_dvd_mul_left 2 h
    · simp [Nat.one_dvd]

private theorem tzGo_dvd_int (fuel : Nat) (x : Int) :
    ((2 ^ tzGo fuel x.natAbs : Nat) : Int) ∣ x :=
  Int.ofNat_dvd_left.2 (tzGo_dvd fuel x.natAbs)

private theorem wastedGo_le (b : Nat) (blk : Array Int) :
    ∀ (fuel i best : Nat), blk.size - i ≤ fuel → wastedGo b blk i best ≤ best := by
  intro fuel
  induction fuel with
  | zero =>
    intro i best hf
    rw [wastedGo]
    rw [dif_neg (by omega)]
    omega
  | succ fuel ih =>
    intro i best hf
    rw [wastedGo]
    split
    · rename_i hlt
      split
      · omega
      · split
        · exact ih (i + 1) best (by omega)
        · exact Nat.le_trans (ih (i + 1) _ (by omega)) (Nat.min_le_left ..)
    · omega

private theorem wastedGo_dvd (b : Nat) (blk : Array Int) :
    ∀ (fuel i best j : Nat), blk.size - i ≤ fuel → i ≤ j →
      ((2 ^ wastedGo b blk i best : Nat) : Int) ∣ blk.getD j 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro i best j hf hij
    have : blk.getD j 0 = 0 := by
      unfold Array.getD
      rw [dif_neg (by omega)]
    rw [this]
    exact Int.dvd_zero _
  | succ fuel ih =>
    intro i best j hf hij
    rw [wastedGo]
    split
    · rename_i hlt
      split
      · rename_i h0
        simp
      · split
        · rename_i hz
          rcases Nat.eq_or_lt_of_le hij with he | hlt2
          · subst he
            have : blk.getD i 0 = 0 := by
              unfold Array.getD
              rw [dif_pos hlt]
              exact hz
            rw [this]
            exact Int.dvd_zero _
          · exact ih (i + 1) best j (by omega) (by omega)
        · rcases Nat.eq_or_lt_of_le hij with he | hlt2
          · have hle : wastedGo b blk (i + 1) (min best (tzGo b blk[i].natAbs))
                ≤ tzGo b blk[i].natAbs :=
              Nat.le_trans (wastedGo_le b blk fuel (i + 1) _ (by omega))
                (Nat.min_le_right ..)
            have hgi : blk.getD j 0 = blk[i] := by
              unfold Array.getD
              rw [dif_pos (by omega)]
              congr 1
              omega
            rw [hgi]
            exact Int.dvd_trans (Int.ofNat_dvd.2 (Nat.pow_dvd_pow 2 hle))
              (tzGo_dvd_int b blk[i])
          · exact ih (i + 1) _ j (by omega) (by omega)
    · have : blk.getD j 0 = 0 := by
        unfold Array.getD
        rw [dif_neg (by omega)]
      rw [this]
      exact Int.dvd_zero _

/-- The detected count is a legal wasted-bit count. -/
theorem wastedDetectF_lt {b : Nat} (hb : 0 < b) (blk : Array Int) :
    wastedDetectF b blk < b := by
  unfold wastedDetectF
  rw [if_neg (by omega)]
  have := wastedGo_le b blk (blk.size) 0 (b - 1) (by omega)
  omega

/-- **Every sample is divisible by `2 ^ wastedDetectF b blk`.** -/
theorem wastedDetectF_dvd (b : Nat) (blk : Array Int) (j : Nat) :
    ((2 ^ wastedDetectF b blk : Nat) : Int) ∣ blk.getD j 0 := by
  unfold wastedDetectF
  split
  · simp
  · exact wastedGo_dvd b blk blk.size 0 (b - 1) j (by omega) (by omega)

theorem wastedDetectF_dvd_mem (b : Nat) (blk : Array Int) :
    ∀ x ∈ blk.toList, ((2 ^ wastedDetectF b blk : Nat) : Int) ∣ x := by
  intro x hx
  obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.1 hx
  have hgi : blk.getD j 0 = x := by
    unfold Array.getD
    rw [dif_pos (by simpa using hj)]
    rw [← hval]
    rfl
  rw [← hgi]
  exact wastedDetectF_dvd b blk j

/-! ## The chooser correspondence

`chooseFrame` makes the decisions; `FramePrep.asg` names them as a
`Frame.ChannelAsg`. These lemmas say the two describe the same frame: same
channel code, same `(depth, config, samples)` plan, and each decision's
cached block really is the wasted-bit-scaled image of the block it was made
from. Nothing here reasons about a `Float` — the searches are only ever
*applied*, on both sides of every equation. -/

/-- The cached block is the scaled block: the fast code divides by
    `(p2 w : Int)` and `Flac.Bits.shiftDown w` *is* division by `2 ^ w`. -/
theorem chooseSub_denotes (b : Nat) (blk : Array Int) :
    (chooseSub b blk).Denotes blk := by
  simp only [chooseSub, SubPrep.Denotes]
  split
  · rfl
  · congr 1
    funext x
    simp only [Flac.Bits.shiftDown, p2_eq]

theorem chooseSub_emitOk (b : Nat) (blk : Array Int) :
    (chooseSub b blk).plan.EmitOk (chooseSub b blk).scaled :=
  emitOk_sanitize _ _

private theorem list_two {α : Type} (l : List α) (d : α) (h : l.length = 2) :
    l = [l.getD 0 d, l.getD 1 d] := by
  match l with
  | [_, _] => rfl
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: _ :: _ => simp at h

private theorem getD_eq {α : Type} (a : Array α) (i : Nat) (d : α) :
    a.getD i d = a.toList.getD i d := by
  unfold Array.getD
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h)]
    rfl
  · rename_i h
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    rfl

/-- Two channels, named the way both sides name them. -/
private theorem toList_two (a : Array (Array Int)) (h : a.size = 2) :
    a.toList = [a.getD 0 #[], a.getD 1 #[]] := by
  rw [getD_eq, getD_eq]
  exact list_two a.toList #[] (by simpa using h)

@[simp] private theorem chooseSub_depth (b : Nat) (blk : Array Int) :
    (chooseSub b blk).depth = b := rfl

private theorem planOf_map (b : Nat) : ∀ cs : List (Array Int),
    planOf (cs.map fun c => (chooseSub b c, c))
      = (((cs.map fun c => (chooseSub b c, c)).map fun q => q.1.cfg).map
          (fun c => (b, c))).zip cs := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, planOf, List.zip_cons_cons, ih, chooseSub_depth]

/-- The decisions denote exactly the reference's subframe plan. -/
theorem chooseFrame_planOf (b : Nat) (chs : Array (Array Int)) :
    planOf (chooseFrame b chs).subs
      = Emit.W.planA b (chooseFrame b chs).asg chs.toList := by
  rw [chooseFrame]
  simp only []
  split
  · rename_i h2
    rw [toList_two chs h2]
    split
    · simp only [FramePrep.asg, planOf, Emit.W.planA, List.map_cons,
        List.map_nil, List.zip_cons_cons, List.zip_nil_right, chooseSub_depth]
    · split
      · simp only [FramePrep.asg, planOf, Emit.W.planA, Flac.Stereo.sideA,
          chooseSub_depth]
      · split
        · simp only [FramePrep.asg, planOf, Emit.W.planA, Flac.Stereo.sideA,
            chooseSub_depth]
        · simp only [FramePrep.asg, planOf, Emit.W.planA, Flac.Stereo.sideA,
            Flac.Stereo.midA, chooseSub_depth]
  · simp only [FramePrep.asg, Array.toList_map, planOf_map, Emit.W.planA]

/-- The header code the fast encoder writes is the reference's. -/
theorem chooseFrame_code (b : Nat) (chs : Array (Array Int)) :
    (chooseFrame b chs).code (chooseFrame b chs).subs.length
      = (chooseFrame b chs).asg.code chs.size := by
  rw [chooseFrame]
  simp only []
  split
  · rename_i h2
    split
    · simp only [FramePrep.code, FramePrep.asg, Frame.ChannelAsg.code,
        List.length_cons, List.length_nil]
      omega
    · split
      · simp only [FramePrep.code, FramePrep.asg, Frame.ChannelAsg.code]
      · split
        · simp only [FramePrep.code, FramePrep.asg, Frame.ChannelAsg.code]
        · simp only [FramePrep.code, FramePrep.asg, Frame.ChannelAsg.code]
  · simp only [FramePrep.code, FramePrep.asg, Frame.ChannelAsg.code,
      Array.toList_map, List.length_map, Array.length_toList]

/-- Every decision is sound for emission. -/
theorem chooseFrame_subs_ok (b : Nat) (chs : Array (Array Int)) :
    ∀ q ∈ (chooseFrame b chs).subs,
      q.1.Denotes q.2 ∧ q.1.plan.EmitOk q.1.scaled := by
  have hpair : ∀ (d : Nat) (c : Array Int) (q : SubPrep × Array Int),
      q = (chooseSub d c, c) → q.1.Denotes q.2 ∧ q.1.plan.EmitOk q.1.scaled := by
    intro d c q hq
    subst hq
    exact ⟨chooseSub_denotes d c, chooseSub_emitOk d c⟩
  have hcons : ∀ (d0 d1 : Nat) (c0 c1 : Array Int) (q : SubPrep × Array Int),
      q ∈ [(chooseSub d0 c0, c0), (chooseSub d1 c1, c1)] →
      q.1.Denotes q.2 ∧ q.1.plan.EmitOk q.1.scaled := by
    intro d0 d1 c0 c1 q hq
    rcases List.mem_cons.1 hq with h | h
    · exact hpair _ _ q h
    · rcases List.mem_cons.1 h with h' | h'
      · exact hpair _ _ q h'
      · simp at h'
  rw [chooseFrame]
  simp only []
  split
  · split
    · exact hcons _ _ _ _
    · split
      · exact hcons _ _ _ _
      · split
        · exact hcons _ _ _ _
        · exact hcons _ _ _ _
  · intro q hq
    simp only [Array.toList_map, List.mem_map] at hq
    obtain ⟨c, _, hc⟩ := hq
    exact hpair b c q hc.symm

private theorem headD_eq_getD {α : Type} (l : List α) (d : α) :
    l.headD d = l.getD 0 d := by
  cases l <;> rfl

private theorem headD_toList (a : Array (Array Int)) :
    a.toList.headD #[] = a.getD 0 #[] := by
  rw [headD_eq_getD, getD_eq]

theorem chooseFrame_blockSize (b : Nat) (chs : Array (Array Int)) :
    (chooseFrame b chs).blockSize = (chs.toList.headD #[]).size := by
  rw [headD_toList, chooseFrame]
  simp only []
  split
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl

/-- **A whole frame.** The shipped encoder's frame — its own search, its own
    writers — emits exactly what the verified emitter emits for the channel
    assignment those decisions denote. -/
theorem sim_frame (b : Nat) (strat : Bool) (num : Nat) (chs : Array (Array Int)) :
    Simulates (fun bw => pushFrameOf bw b strat num (chooseFrame b chs))
      (Emit.W.pushFrame b strat num (chooseFrame b chs).asg chs.toList) :=
  sim_pushFrameOf b strat num (chooseFrame b chs) (chooseFrame b chs).asg
    chs.toList (chooseFrame b chs).subs rfl (chooseFrame_planOf b chs)
    (chooseFrame_blockSize b chs) (chooseFrame_code b chs)
    (chooseFrame_subs_ok b chs)

/-! ## The decisions carry the round-trip certificate

`Frame.ChannelAsg.orVerbatim` — what the reference encoder wraps every
chooser in — keeps a choice only if it is `Valid`. These lemmas show the
sanitised decisions always are, so `orVerbatim` is the identity on them and
the fast encoder needs no check of its own. -/

/-- `choosePlanF` answers `.constant` only behind its own all-equal guard. -/
theorem choosePlanF_constant {b : Nat} {blk : Array Int} {blkF : FloatArray}
    (h : choosePlanF b blk blkF = .constant) :
    ∀ x ∈ blk.toList, x = blk.getD 0 0 := by
  have hg : (blk.all fun x => x == blk.getD 0 0) = true := by
    rw [choosePlanF] at h
    split at h
    · rename_i hc
      exact hc
    · exfalso
      split at h
      all_goals try split at h
      all_goals try split at h
      all_goals simp at h
  intro x hx
  have hxa : x ∈ blk := by simpa using hx
  have := Array.all_eq_true_iff_forall_mem.1 hg x hxa
  simpa using this

/-- The cached block, as a list: the reference's scaled samples. -/
theorem chooseSub_scaled_toList (b : Nat) (blk : Array Int) :
    (chooseSub b blk).scaled.toList
      = blk.toList.map (Flac.Bits.shiftDown (chooseSub b blk).wasted) := by
  have hd := chooseSub_denotes b blk
  unfold SubPrep.Denotes at hd
  rw [hd]
  split
  · rename_i h
    rw [h, Flac.Bits.map_shiftDown_zero]
  · rw [Array.toList_map]

/-- **One decision carries its certificate.** -/
theorem chooseSub_cfg_valid {b : Nat} (hb : 0 < b) (blk : Array Int)
    (hfit : ∀ x ∈ blk.toList, Flac.Bits.FitsSInt b x) :
    (chooseSub b blk).cfg.Valid b blk.toList := by
  have hw : (chooseSub b blk).wasted = wastedDetectF b blk := rfl
  have hlt : (chooseSub b blk).wasted < b := by
    rw [hw]; exact wastedDetectF_lt hb blk
  have hdvd : ∀ x ∈ blk.toList,
      ((2 ^ (chooseSub b blk).wasted : Nat) : Int) ∣ x := by
    rw [hw]; exact wastedDetectF_dvd_mem b blk
  have hsc := chooseSub_scaled_toList b blk
  have hfit' : ∀ x ∈ blk.toList.map
      (Flac.Bits.shiftDown (chooseSub b blk).wasted),
      Flac.Bits.FitsSInt (b - (chooseSub b blk).wasted) x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hx
    rw [← hxy]
    exact Flac.Heuristics.fitsSInt_shiftDown b _ hlt y (hfit y hy) (hdvd y hy)
  have hlen : (chooseSub b blk).scaled.size
      = (blk.toList.map (Flac.Bits.shiftDown (chooseSub b blk).wasted)).length := by
    rw [← Array.length_toList, hsc]
  refine ⟨hlt, hdvd, ?_⟩
  show (subCfgOf (chooseSub b blk).plan).Valid (b - (chooseSub b blk).wasted)
    (blk.toList.map (Flac.Bits.shiftDown (chooseSub b blk).wasted))
  show (subCfgOf ((choosePlanF (b - (chooseSub b blk).wasted)
      (chooseSub b blk).scaled (chooseSub b blk).scaledF).sanitize
        (chooseSub b blk).scaled.size)).Valid _ _
  rw [hlen]
  refine subCfgOf_sanitize_valid _ hfit' ?_
  intro hconst x hx
  rw [← hsc] at hx
  have hval := choosePlanF_constant hconst x hx
  rw [← hsc, headD_eq_getD, ← getD_eq]
  exact hval

/-! ## The frame's decisions carry the certificate

`Frame.ChannelAsg.orVerbatim` — what the reference wraps every chooser in —
keeps a choice only when it is `Valid`. Showing the decisions always are is
what makes `orVerbatim` the identity on them, so the reference emits exactly
what the fast encoder chose. -/

private theorem mem_zipWith {α β γ : Type} {f : α → β → γ} :
    ∀ {l : List α} {r : List β} {x : γ}, x ∈ List.zipWith f l r →
      ∃ a ∈ l, ∃ b ∈ r, f a b = x := by
  intro l
  induction l with
  | nil => intro r x hx; simp at hx
  | cons a l ih =>
    intro r x hx
    match r with
    | [] => simp at hx
    | c :: r =>
      rw [List.zipWith_cons_cons] at hx
      rcases List.mem_cons.1 hx with h | h
      · exact ⟨a, List.mem_cons_self .., c, List.mem_cons_self .., h.symm⟩
      · obtain ⟨a', ha', b', hb', hfx⟩ := ih h
        exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', hfx⟩

private theorem mem_zip_map_self {α β γ : Type} {f : α → β} {g : α → γ} :
    ∀ {l : List α} {p : β × γ}, p ∈ (l.map f).zip (l.map g) →
      ∃ a ∈ l, (f a, g a) = p := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons a l ih =>
    intro p hp
    rw [List.map_cons, List.map_cons, List.zip_cons_cons] at hp
    rcases List.mem_cons.1 hp with h | h
    · exact ⟨a, List.mem_cons_self .., h.symm⟩
    · obtain ⟨a', ha', hfa⟩ := ih h
      exact ⟨a', List.mem_cons_of_mem _ ha', hfa⟩

private theorem getD_mem {α : Type} {l : List α} {i : Nat} (d : α)
    (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

private theorem side_fits_mem {b : Nat} {l r : Array Int}
    (hl : ∀ x ∈ l.toList, Flac.Bits.FitsSInt b x)
    (hr : ∀ x ∈ r.toList, Flac.Bits.FitsSInt b x) :
    ∀ x ∈ (Flac.Stereo.sideA l r).toList, Flac.Bits.FitsSInt (b + 1) x := by
  intro x hx
  rw [Flac.Stereo.sideA_toList, Flac.Stereo.side] at hx
  obtain ⟨u, hu, v, hv, huv⟩ := mem_zipWith hx
  rw [← huv]
  exact Flac.Stereo.side_fits b u v (hl u hu) (hr v hv)

private theorem mid_fits_mem {b : Nat} {l r : Array Int}
    (hl : ∀ x ∈ l.toList, Flac.Bits.FitsSInt b x)
    (hr : ∀ x ∈ r.toList, Flac.Bits.FitsSInt b x) :
    ∀ x ∈ (Flac.Stereo.midA l r).toList, Flac.Bits.FitsSInt b x := by
  intro x hx
  rw [Flac.Stereo.midA_toList, Flac.Stereo.mid] at hx
  obtain ⟨u, hu, v, hv, huv⟩ := mem_zipWith hx
  rw [← huv]
  exact Flac.Stereo.mid_fits b u v (hl u hu) (hr v hv)

/-- The four shapes `chooseFrame` can produce. Both independent branches —
    two channels coded independently, and more than two channels — share one
    description, which is what keeps this to four cases. -/
private theorem chooseFrame_shape (b : Nat) (chs : Array (Array Int)) :
    ((chooseFrame b chs).mode = .independent ∧
        (chooseFrame b chs).subs = chs.toList.map fun c => (chooseSub b c, c))
      ∨ (∃ l r, chs.toList = [l, r] ∧ (chooseFrame b chs).mode = .leftSide ∧
          (chooseFrame b chs).subs = [(chooseSub b l, l),
            (chooseSub (b + 1) (Flac.Stereo.sideA l r), Flac.Stereo.sideA l r)])
      ∨ (∃ l r, chs.toList = [l, r] ∧ (chooseFrame b chs).mode = .rightSide ∧
          (chooseFrame b chs).subs =
            [(chooseSub (b + 1) (Flac.Stereo.sideA l r), Flac.Stereo.sideA l r),
             (chooseSub b r, r)])
      ∨ (∃ l r, chs.toList = [l, r] ∧ (chooseFrame b chs).mode = .midSide ∧
          (chooseFrame b chs).subs =
            [(chooseSub b (Flac.Stereo.midA l r), Flac.Stereo.midA l r),
             (chooseSub (b + 1) (Flac.Stereo.sideA l r), Flac.Stereo.sideA l r)]) := by
  rw [chooseFrame]
  simp only []
  split
  · rename_i h2
    have ht := toList_two chs h2
    split
    · exact Or.inl ⟨rfl, by rw [ht]; rfl⟩
    · split
      · exact Or.inr (Or.inl ⟨_, _, ht, rfl, rfl⟩)
      · split
        · exact Or.inr (Or.inr (Or.inl ⟨_, _, ht, rfl, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨_, _, ht, rfl, rfl⟩))
  · exact Or.inl ⟨rfl, by rw [Array.toList_map]⟩

/-- **The frame's decisions are valid**, so `orVerbatim` keeps them. -/
theorem chooseFrame_asg_valid {b bs : Nat} (hb : 0 < b) (chs : Array (Array Int))
    (hlen : ∀ c ∈ chs.toList, c.toList.length = bs)
    (hfit : ∀ c ∈ chs.toList, ∀ x ∈ c.toList, Flac.Bits.FitsSInt b x)
    (hn1 : 1 ≤ chs.size) (hn8 : chs.size ≤ 8) :
    (chooseFrame b chs).asg.Valid b bs (chs.toList.map Array.toList) := by
  have hall : ∀ c ∈ chs.toList.map Array.toList, c.length = bs := by
    intro c hc
    obtain ⟨a, ha, hac⟩ := List.mem_map.1 hc
    rw [← hac]
    exact hlen a ha
  have hpair : ∀ (l r : Array Int), chs.toList = [l, r] →
      (∀ x ∈ l.toList, Flac.Bits.FitsSInt b x) ∧
        (∀ x ∈ r.toList, Flac.Bits.FitsSInt b x) := by
    intro l r ht
    exact ⟨hfit l (by rw [ht]; exact List.mem_cons_self ..),
      hfit r (by rw [ht]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  refine ⟨hall, ?_⟩
  rcases chooseFrame_shape b chs with ⟨hm, hs⟩ | ⟨l, r, ht, hm, hs⟩ |
    ⟨l, r, ht, hm, hs⟩ | ⟨l, r, ht, hm, hs⟩
  · rw [FramePrep.asg, hm, hs]
    refine ⟨by simpa using hn1, by simpa using hn8, ?_, ?_⟩
    · simp only [List.map_map, List.length_map]
    · intro p hp
      simp only [List.map_map] at hp
      obtain ⟨c, hc, hpc⟩ := mem_zip_map_self hp
      rw [← hpc]
      exact chooseSub_cfg_valid hb c (hfit c hc)
  · obtain ⟨hl, hr⟩ := hpair l r ht
    rw [FramePrep.asg, hm, hs, ht]
    refine ⟨chooseSub_cfg_valid hb _ hl, ?_⟩
    rw [← Flac.Stereo.sideA_toList]
    exact chooseSub_cfg_valid (by omega) _ (side_fits_mem hl hr)
  · obtain ⟨hl, hr⟩ := hpair l r ht
    rw [FramePrep.asg, hm, hs, ht]
    refine ⟨?_, chooseSub_cfg_valid hb _ hr⟩
    rw [← Flac.Stereo.sideA_toList]
    exact chooseSub_cfg_valid (by omega) _ (side_fits_mem hl hr)
  · obtain ⟨hl, hr⟩ := hpair l r ht
    rw [FramePrep.asg, hm, hs, ht]
    refine ⟨?_, ?_⟩
    · rw [← Flac.Stereo.midA_toList]
      exact chooseSub_cfg_valid hb _ (mid_fits_mem hl hr)
    · rw [← Flac.Stereo.sideA_toList]
      exact chooseSub_cfg_valid (by omega) _ (side_fits_mem hl hr)

/-! ## The reference, instantiated with our chooser, keeps our choice -/

theorem orVerbatim_of_valid {asg : Frame.ChannelAsg} {b bs : Nat}
    {chs : List (List Int)} (h : asg.Valid b bs chs) :
    asg.orVerbatim b bs chs = asg := by
  unfold Frame.ChannelAsg.orVerbatim
  rw [if_pos h]

private theorem map_toArray_toList (fr : List (List Int)) :
    (fr.map List.toArray).map Array.toList = fr := by
  induction fr with
  | nil => rfl
  | cons c fr ih => rw [List.map_cons, List.map_cons, ih, List.toList_toArray]

/-- **The sanitisation is enough.** `EncoderCfg.safeChooser` wraps every
    chooser in `orVerbatim`; on the fast encoder's decisions that wrapper is
    the identity, so the reference encoder emits exactly them. -/
theorem safeChooser_fastChooser {b : Nat} (hb : 0 < b) (blockSize : Nat)
    (varBlk : Bool) (fr : List (List Int))
    (hlen : ∀ c ∈ fr, c.length = (fr.headD []).length)
    (hfit : ∀ c ∈ fr, ∀ x ∈ c, Flac.Bits.FitsSInt b x)
    (hn1 : 1 ≤ fr.length) (hn8 : fr.length ≤ 8) :
    (Stream.EncoderCfg.mk blockSize varBlk (fastChooser b)).safeChooser b fr
      = fastChooser b fr := by
  have hct : ((fr.map List.toArray).toArray).toList = fr.map List.toArray :=
    List.toList_toArray
  have hsz : ((fr.map List.toArray).toArray).size = fr.length := by
    rw [← Array.length_toList, hct, List.length_map]
  have hmem : ∀ c ∈ ((fr.map List.toArray).toArray).toList,
      ∃ l ∈ fr, c.toList = l := by
    intro c hc
    rw [hct] at hc
    obtain ⟨l, hl, hlc⟩ := List.mem_map.1 hc
    exact ⟨l, hl, by rw [← hlc, List.toList_toArray]⟩
  have h1 : ∀ c ∈ ((fr.map List.toArray).toArray).toList,
      c.toList.length = (fr.headD []).length := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := hmem c hc
    rw [hcl]
    exact hlen l hl
  have h2 : ∀ c ∈ ((fr.map List.toArray).toArray).toList,
      ∀ x ∈ c.toList, Flac.Bits.FitsSInt b x := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := hmem c hc
    rw [hcl]
    exact hfit l hl
  have hv := chooseFrame_asg_valid (bs := (fr.headD []).length) hb
    ((fr.map List.toArray).toArray) h1 h2 (by rw [hsz]; omega) (by rw [hsz]; omega)
  rw [hct, map_toArray_toList] at hv
  exact orVerbatim_of_valid hv

/-! ## Streams

The reference folds one writer through every frame; the shipped encoder
builds each frame in its own worker, from an empty writer, and concatenates
the buffers. These lemmas join the two: emission only *appends*, which is the
same locality argument that licensed per-frame serialisation on the decode
side. -/

private theorem emptyWithCapacity_eq (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := by
  apply ByteArray.ext
  rfl

/-- Both writers start in simulation, whatever capacity they reserve. -/
theorem sim_empty (c₁ c₂ : Nat) : Sim (BitWriter.empty c₁) (Emit.W.empty c₂) := by
  refine ⟨?_, rfl, show (0 : Nat) < 8 by omega, rfl⟩
  show ByteArray.emptyWithCapacity c₁ = ByteArray.emptyWithCapacity c₂
  rw [emptyWithCapacity_eq, emptyWithCapacity_eq]

private theorem frame_write_dvd (b : Nat) (strat : Bool) (num : Nat)
    (asg : Frame.ChannelAsg) (chs : List (List Int)) :
    8 ∣ (Frame.write b strat num asg chs).length := by
  have h1 : 8 ∣ (Frame.body b strat num asg chs).length := alignToByte_dvd _
  simp only [Frame.write, List.length_append, length_writeBits]
  omega

/-- **Emission only appends.** A frame's bytes do not depend on what is
    already in the buffer, which is what lets each worker build its frame
    from an empty writer. -/
theorem pushFrame_buf_append (b : Nat) (strat : Bool) (num : Nat)
    (asg : Frame.ChannelAsg) (chs : List (Array Int)) (w : Emit.W) (hw : w.n = 0) :
    (Emit.W.pushFrame b strat num asg chs w).buf
      = w.buf ++ (Emit.W.pushFrame b strat num asg chs (Emit.W.empty 0)).buf := by
  obtain ⟨hb1, hn1⟩ := Emit.pushFrame_spec b strat num asg chs w hw
  obtain ⟨hb2, hn2⟩ := Emit.pushFrame_spec b strat num asg chs (Emit.W.empty 0) rfl
  have h1 := Emit.aligned_buf_of_bits hw hn1 hb1 (frame_write_dvd ..)
  have h2 := Emit.aligned_buf_of_bits (w := Emit.W.empty 0) rfl hn2 hb2
    (frame_write_dvd ..)
  rw [h1, h2]
  show _ = w.buf ++ (ByteArray.emptyWithCapacity 0 ++ _)
  rw [emptyWithCapacity_eq, ByteArray.empty_append]

/-- **The reference's frame fold is the shipped encoder's concatenation.**
    Each worker's payload carries the equation for its own frame, so this
    needs no fact about `Task` — a payload that records the wrong index just
    costs the work of rebuilding that frame. -/
theorem pushFrames_concat (b : Nat) (varBlk : Bool) (blockSize' : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg)
    (blockSize ch n : Nat) (bytes : ByteArray) :
    ∀ (frs : List (List (List Int)))
      (ts : List (Task (FrameStep blockSize ch n bytes)))
      (i : Nat) (w : Emit.W) (out : ByteArray),
      out = w.buf → w.n = 0 → frs.length = ts.length →
      (∀ k, k < frs.length →
        frameBytesPcm blockSize ch 16 false bytes n (i + k)
          = (Emit.W.pushFrame b varBlk
              (if varBlk then (i + k) * blockSize' else i + k)
              (chooser (frs.getD k [])) ((frs.getD k []).map List.toArray)
              (Emit.W.empty 0)).buf) →
      (Emit.W.pushFrames b varBlk blockSize' chooser i frs w).buf
        = concatFrames blockSize ch n bytes i ts out := by
  intro frs
  induction frs with
  | nil =>
    intro ts i w out hout _ hlen _
    match ts with
    | [] =>
      show w.buf = concatFrames blockSize ch n bytes i [] out
      rw [hout]
      rfl
    | _ :: _ => simp at hlen
  | cons fr frs ih =>
    intro ts i w out hout hw hlen hbody
    match ts with
    | [] => simp at hlen
    | t :: ts =>
      have hhead := hbody 0 (by simp)
      rw [Nat.add_zero] at hhead
      have happ := pushFrame_buf_append b varBlk
        (if varBlk then i * blockSize' else i) (chooser fr) (fr.map List.toArray) w hw
      have hn0 : (Emit.W.pushFrame b varBlk (if varBlk then i * blockSize' else i)
          (chooser fr) (fr.map List.toArray) w).n = 0 :=
        (Emit.pushFrame_spec b varBlk (if varBlk then i * blockSize' else i)
          (chooser fr) (fr.map List.toArray) w hw).2
      -- the payload's own equation, whichever branch the index check takes
      have hstep : (if t.get.idx = i then t.get.out
          else frameBytesPcm blockSize ch 16 false bytes n i)
          = frameBytesPcm blockSize ch 16 false bytes n i := by
        split
        · rename_i hi
          rw [t.get.ok, hi]
        · rfl
      show (Emit.W.pushFrames b varBlk blockSize' chooser (i + 1) frs
          (Emit.W.pushFrame b varBlk (if varBlk then i * blockSize' else i)
            (chooser fr) (fr.map List.toArray) w)).buf = _
      show _ = concatFrames blockSize ch n bytes (i + 1) ts
        (out ++ (if t.get.idx = i then t.get.out
                 else frameBytesPcm blockSize ch 16 false bytes n i))
      rw [hstep]
      refine ih ts (i + 1) _ (out ++ frameBytesPcm blockSize ch 16 false bytes n i)
        ?_ hn0 (by simpa using hlen) ?_
      · rw [hout, happ, hhead]
        rfl
      · intro k hk
        have hb := hbody (k + 1) (by simpa using hk)
        rw [show i + (k + 1) = i + 1 + k from by omega,
          List.getD_cons_succ] at hb
        exact hb

/-! ## The digest is a digest of the input

The shipped encoder takes the STREAMINFO digest over the input bytes; the
reference takes it over `Stream.pcmBytes` of the samples. Those are the same
bytes — which is the last thing needed for the two streams to be equal
byte for byte. -/

theorem pcmBytes_deinterleave {ch : Nat} (hch : 0 < ch) (bytes : ByteArray)
    (hsz : bytes.size % (2 * ch) = 0) :
    Stream.pcmBytes 16 (Flac.deinterleave ch
        (Flac.pcm16OfByteList bytes.data.toList)) = bytes := by
  have hmap : ((Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList)).map
      (fun x => x.toArray)).map Array.toList
      = Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList) :=
    map_toArray_toList _
  show Stream.pcmBytesRange 16 _ 0 _ = _
  rw [← Stream.pcm16FastA_eq_range, Flac.pcm16FastA_eq, hmap,
    Flac.pcm16Fast_deinterleave hch bytes hsz]

/-! ## Frames line up

The shipped encoder indexes frames by number; the reference walks a list of
chunks. These lemmas identify frame `f` on both sides. -/

private theorem dropAll_zero (chs : List (List Int)) :
    Stream.dropAll 0 chs = chs := by
  simp [Stream.dropAll]

private theorem dropAll_dropAll (k m : Nat) (chs : List (List Int)) :
    Stream.dropAll m (Stream.dropAll k chs) = Stream.dropAll (k + m) chs := by
  simp [Stream.dropAll, List.map_map, List.drop_drop]

private theorem take_min {α : Type} (l : List α) (m : Nat) :
    l.take m = l.take (min m l.length) := by
  rcases Nat.le_total m l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_length]

/-- Frame `f` of the reference's chunking is `take` after `drop`. -/
theorem chunkChannels_getD (nn : Nat) : ∀ (chs : List (List Int)) (f : Nat),
    f < (Stream.chunkChannels nn chs).length →
    (Stream.chunkChannels nn chs).getD f []
      = Stream.takeAll nn (Stream.dropAll (f * nn) chs) := by
  intro chs
  fun_induction Stream.chunkChannels nn chs with
  | case1 chs h =>
    intro f hf
    simp at hf
  | case2 chs h ih =>
    intro f hf
    cases f with
    | zero => rw [List.getD_cons_zero, Nat.zero_mul, dropAll_zero]
    | succ f =>
      rw [List.length_cons] at hf
      rw [List.getD_cons_succ, ih f (by omega), dropAll_dropAll,
        show nn + f * nn = (f + 1) * nn from by rw [Nat.succ_mul]; omega]

/-! ## The derived audio is well-formed

`encodePcm16Cfg` checks `Audio.WellFormed` at run time; on the audio the PCM
pipeline derives from its input, every clause is a *theorem*, so the shipped
encoder's O(1) guards suffice where the reference would scan. -/

private theorem sInt16_fits (lo hi : UInt8) :
    Flac.Bits.FitsSInt 16 (Flac.sInt16 lo hi) := by
  have hlo : lo.toNat < 256 := UInt8.toNat_lt_size lo
  have hhi : hi.toNat < 256 := UInt8.toNat_lt_size hi
  have h16 : ((2 ^ 16 : Nat) : Int) = 65536 := by rfl
  unfold Flac.sInt16 Flac.Bits.FitsSInt
  simp only []
  split <;> rename_i hv <;> rw [h16] <;> omega

private theorem pcm16OfByteList_fits : ∀ (m : Nat) (l : List UInt8), l.length = m →
    ∀ x ∈ Flac.pcm16OfByteList l, Flac.Bits.FitsSInt 16 x := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro l hm x hx
    match l with
    | [] => simp [Flac.pcm16OfByteList] at hx
    | [_] => simp [Flac.pcm16OfByteList] at hx
    | lo :: hi :: rest =>
      rw [show Flac.pcm16OfByteList (lo :: hi :: rest)
        = Flac.sInt16 lo hi :: Flac.pcm16OfByteList rest from rfl] at hx
      rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact sInt16_fits lo hi
      · exact ih rest.length (by simp only [List.length_cons] at hm; omega)
          rest rfl x h

private theorem getD_fits {L : List Int} (h : ∀ y ∈ L, Flac.Bits.FitsSInt 16 y)
    (i : Nat) : Flac.Bits.FitsSInt 16 (L.getD i 0) := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none]
    exact fitsSInt_zero 16

/-- Every deinterleaved sample fits 16 bits. -/
theorem deinterleave_fits {ch : Nat} (hch : 0 < ch) (bytes : ByteArray)
    (c : List Int)
    (hc : c ∈ Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList)) :
    ∀ x ∈ c, Flac.Bits.FitsSInt 16 x := by
  have hL : ∀ y ∈ Flac.pcm16OfByteList bytes.data.toList,
      Flac.Bits.FitsSInt 16 y :=
    pcm16OfByteList_fits _ bytes.data.toList rfl
  have hlen := length_deinterleave (ch := ch)
    (Flac.pcm16OfByteList bytes.data.toList)
  obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.1 hc
  intro x hx
  obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.1 hx
  have hjch : j < ch := by rw [hlen] at hj; exact hj
  have hgc : (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)).getD j [] = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hjc
  have hxg : c.getD t 0 = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact htx
  rw [← hxg, ← hgc]
  by_cases htn : t < (Flac.pcm16OfByteList bytes.data.toList).length / ch
  · rw [getD_deinterleave hch _ hjch htn]
    exact getD_fits hL _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ?_, Option.getD_none]
    · exact fitsSInt_zero 16
    · rw [length_getD_deinterleave hch _ hjch]
      omega

/-- Every deinterleaved channel has the same length: the sample count. -/
private theorem deinterleave_lengths {ch : Nat} (hch : 0 < ch) (L : List Int)
    (c : List Int) (hc : c ∈ Flac.deinterleave ch L) : c.length = L.length / ch := by
  have hlen := length_deinterleave (ch := ch) L
  obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.1 hc
  have hjch : j < ch := by rw [hlen] at hj; exact hj
  have hgc : (Flac.deinterleave ch L).getD j [] = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hjc
  rw [← hgc, length_getD_deinterleave hch L hjch]

/-- **The audio the PCM pipeline derives is well-formed** — every clause a
    theorem, so the shipped encoder's O(1) guards are enough where the
    reference would scan. -/
theorem audio_wellFormed {ch sr : Nat} (hch : 0 < ch) (hch8 : ch ≤ 8)
    (bytes : ByteArray) (hsr : sr < 2 ^ 20)
    (hn : bytes.size / (2 * ch) < 2 ^ 36) :
    (Stream.Audio.mk (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)) 16 sr).WellFormed := by
  have hlen := length_deinterleave (ch := ch)
    (Flac.pcm16OfByteList bytes.data.toList)
  have hL : (Flac.pcm16OfByteList bytes.data.toList).length = bytes.size / 2 := by
    rw [Flac.length_pcm16OfByteList, Array.length_toList]
    rfl
  have hns : (Stream.Audio.mk (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)) 16 sr).numSamples
      = bytes.size / (2 * ch) := by
    show ((Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)).headD []).length = _
    rw [headD_eq_getD, length_getD_deinterleave hch _ (by omega), hL,
      Nat.div_div_eq_div_mul]
  have hcl : (Stream.Audio.mk (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)) 16 sr).channels.length = ch := hlen
  have hbps : (Stream.Audio.mk (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)) 16 sr).bps = 16 := rfl
  refine ⟨by rw [hcl]; omega, by rw [hcl]; omega, by rw [hbps]; omega,
    by rw [hbps]; omega, ?_, ?_, hsr, by rw [hns]; exact hn⟩
  · intro c hc
    rw [deinterleave_lengths hch _ c hc, hns, hL, Nat.div_div_eq_div_mul]
  · intro c hc
    rw [hbps]
    exact deinterleave_fits hch bytes c hc

/-- The reference's chunk count is the shipped encoder's frame count. -/
theorem chunkChannels_length {nn : Nat} (hnn : 0 < nn) :
    ∀ chs : List (List Int), (Stream.chunkChannels nn chs).length
      = ((chs.headD []).length + nn - 1) / nn := by
  intro chs
  fun_induction Stream.chunkChannels nn chs with
  | case1 chs h =>
    rcases h with h | h
    · rw [h]
      simp only [List.length_nil]
      rw [Nat.div_eq_of_lt (by omega)]
    · omega
  | case2 chs h ih =>
    rw [not_or] at h
    have hm : 0 < (chs.headD []).length := by omega
    rw [List.length_cons, ih, Stream.headD_dropAll]
    rcases Nat.le_total nn (chs.headD []).length with hle | hle
    · rw [show (chs.headD []).length - nn + nn - 1
          = (chs.headD []).length - 1 from by omega,
        show (chs.headD []).length + nn - 1
          = (chs.headD []).length - 1 + nn from by omega,
        Nat.add_div_right _ hnn]
    · rw [show (chs.headD []).length - nn + nn - 1 = nn - 1 from by omega,
        Nat.div_eq_of_lt (by omega),
        show (chs.headD []).length + nn - 1
          = (chs.headD []).length - 1 + nn from by omega,
        Nat.add_div_right _ hnn, Nat.div_eq_of_lt (by omega)]

/-! ## Frame `k` is frame `k`

The shipped worker reads its window straight out of the PCM bytes; the
reference takes the `k`-th chunk of the deinterleaved channels. -/

private theorem takeAll_len_eq {chs : List (List Int)} {n lo m : Nat}
    (hlen : ∀ c ∈ chs, c.length = n) (hlo : lo ≤ n) :
    Stream.takeAll (min (lo + m) n - lo) (Stream.dropAll lo chs)
      = Stream.takeAll m (Stream.dropAll lo chs) := by
  simp only [Stream.takeAll, Stream.dropAll, List.map_map, Function.comp_def]
  refine List.map_congr_left ?_
  intro c hc
  rw [take_min (c.drop lo) m, take_min (c.drop lo) (min (lo + m) n - lo),
    List.length_drop, hlen c hc]
  congr 1
  omega

private theorem size_div_two (ch : Nat) (bytes : ByteArray) :
    (Flac.pcm16OfByteList bytes.data.toList).length / ch
      = bytes.size / (2 * ch) := by
  rw [Flac.length_pcm16OfByteList, Array.length_toList,
    show bytes.data.size = bytes.size from rfl, Nat.div_div_eq_div_mul]

/-- The window a frame worker reads is the reference's frame, as arrays. -/
theorem frameChannels_frame {ch blockSize : Nat} (hch : 0 < ch)
    (bytes : ByteArray) (hsz : bytes.size % (2 * ch) = 0) (k : Nat)
    (hk : k * blockSize ≤ bytes.size / (2 * ch)) :
    (frameChannels bytes ch (k * blockSize)
        (min (k * blockSize + blockSize) (bytes.size / (2 * ch)))).toList
      = (Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
          (Flac.deinterleave ch
            (Flac.pcm16OfByteList bytes.data.toList)))).map List.toArray := by
  have hev : bytes.size % 2 = 0 := by
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hsz
    rw [hq, Nat.mul_assoc]
    exact Nat.mul_mod_right 2 _
  have hdiv := size_div_two ch bytes
  have hsplit : min (k * blockSize + blockSize) (bytes.size / (2 * ch))
      = k * blockSize + (min (k * blockSize + blockSize)
          (bytes.size / (2 * ch)) - k * blockSize) := by omega
  rw [hsplit, frameChannels_eq bytes hev hch _ _ (by rw [hdiv]; omega)]
  congr 1
  refine takeAll_len_eq (n := bytes.size / (2 * ch)) ?_ hk
  intro c hc
  rw [deinterleave_lengths hch _ c hc, hdiv]

private theorem mem_takeAll_dropAll {chs : List (List Int)} {lo m : Nat}
    {c : List Int} (hc : c ∈ Stream.takeAll m (Stream.dropAll lo chs)) :
    ∃ d ∈ chs, c = (d.drop lo).take m := by
  simp only [Stream.takeAll, Stream.dropAll, List.map_map, Function.comp_def,
    List.mem_map] at hc
  obtain ⟨d, hd, hdc⟩ := hc
  exact ⟨d, hd, hdc.symm⟩

private theorem length_takeAll_dropAll {chs : List (List Int)} {n lo m : Nat}
    (hlen : ∀ c ∈ chs, c.length = n) :
    ∀ c ∈ Stream.takeAll m (Stream.dropAll lo chs), c.length = min m (n - lo) := by
  intro c hc
  obtain ⟨d, hd, hdc⟩ := mem_takeAll_dropAll hc
  rw [hdc, List.length_take, List.length_drop, hlen d hd]

private theorem count_takeAll_dropAll (chs : List (List Int)) (lo m : Nat) :
    (Stream.takeAll m (Stream.dropAll lo chs)).length = chs.length := by
  simp [Stream.takeAll, Stream.dropAll]

private theorem headD_mem {α : Type} {l : List α} (d : α) (h : 0 < l.length) :
    l.headD d ∈ l := by
  match l with
  | [] => simp at h
  | _ :: _ => exact List.mem_cons_self ..

/-- **Frame `k` is frame `k`.** The shipped worker's bytes are the bytes the
    verified emitter appends for the reference's `k`-th chunk. -/
theorem frameBytesPcm_eq {blockSize ch : Nat} (hch : 0 < ch) (hch8 : ch ≤ 8)
    (bytes : ByteArray) (hsz : bytes.size % (2 * ch) = 0) (k : Nat)
    (hk : k * blockSize ≤ bytes.size / (2 * ch)) :
    frameBytesPcm blockSize ch 16 false bytes (bytes.size / (2 * ch)) k
      = (Emit.W.pushFrame 16 false k
          ((Stream.EncoderCfg.mk blockSize false (fastChooser 16)).safeChooser 16
            (Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
              (Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList)))))
          ((Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
              (Flac.deinterleave ch
                (Flac.pcm16OfByteList bytes.data.toList)))).map List.toArray)
          (Emit.W.empty 0)).buf := by
  have hdiv := size_div_two ch bytes
  have hchlen : ∀ c ∈ Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList),
      c.length = bytes.size / (2 * ch) := by
    intro c hc
    rw [deinterleave_lengths hch _ c hc, hdiv]
  have hfc := frameChannels_frame hch bytes hsz k hk
  have harr : ((Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
      (Flac.deinterleave ch
        (Flac.pcm16OfByteList bytes.data.toList)))).map List.toArray).toArray
      = frameChannels bytes ch (k * blockSize)
          (min (k * blockSize + blockSize) (bytes.size / (2 * ch))) := by
    rw [← hfc, Array.toArray_toList]
  have hcount : (Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
      (Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList)))).length
      = ch := by
    rw [count_takeAll_dropAll,
      length_deinterleave (ch := ch) (Flac.pcm16OfByteList bytes.data.toList)]
  have hulen := length_takeAll_dropAll (m := blockSize) (lo := k * blockSize) hchlen
  have hhd := hulen _ (headD_mem [] (by rw [hcount]; omega))
  have hlen : ∀ c ∈ Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
      (Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList))),
      c.length = ((Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
        (Flac.deinterleave ch
          (Flac.pcm16OfByteList bytes.data.toList)))).headD []).length := by
    intro c hc
    rw [hulen c hc, hhd]
  have hfit : ∀ c ∈ Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
      (Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList))),
      ∀ x ∈ c, Flac.Bits.FitsSInt 16 x := by
    intro c hc x hx
    obtain ⟨d, hd, hdc⟩ := mem_takeAll_dropAll hc
    rw [hdc] at hx
    exact deinterleave_fits hch bytes d hd x
      (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hchooser : (Stream.EncoderCfg.mk blockSize false (fastChooser 16)).safeChooser
        16 (Stream.takeAll blockSize (Stream.dropAll (k * blockSize)
          (Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList))))
      = (chooseFrame 16 (frameChannels bytes ch (k * blockSize)
          (min (k * blockSize + blockSize) (bytes.size / (2 * ch))))).asg := by
    rw [safeChooser_fastChooser (by omega) blockSize false _ hlen hfit
      (by rw [hcount]; omega) (by rw [hcount]; omega)]
    show (chooseFrame 16 (_ : List (Array Int)).toArray).asg = _
    rw [harr]
  have hsim := sim_frame 16 false k (frameChannels bytes ch (k * blockSize)
      (min (k * blockSize + blockSize) (bytes.size / (2 * ch))))
    (BitWriter.empty ((min (k * blockSize + blockSize) (bytes.size / (2 * ch))
      - k * blockSize) * ch * 2 + 64)) (Emit.W.empty 0) (sim_empty _ 0)
  show (pushFrameOf (BitWriter.empty _) 16 false k (chooseFrame 16 _)).buf = _
  rw [hsim.1, hchooser, hfc]

/-! ## The whole stream -/

theorem numSamples_eq {ch : Nat} (hch : 0 < ch) (bytes : ByteArray) (sr : Nat) :
    (Stream.Audio.mk (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)) 16 sr).numSamples
      = bytes.size / (2 * ch) := by
  show ((Flac.deinterleave ch
    (Flac.pcm16OfByteList bytes.data.toList)).headD []).length = _
  rw [headD_eq_getD, length_getD_deinterleave hch _ (by omega),
    size_div_two ch bytes]

/-- The marker and STREAMINFO the shipped encoder writes are the reference's
    prefix. The digest matches by `pcmBytes_deinterleave`; every other field
    is the same push of the same number. -/
theorem sim_prefix {blockSize ch sr : Nat} (hch : 0 < ch) (bytes : ByteArray)
    (hsz : bytes.size % (2 * ch) = 0) (cap : Nat) :
    Sim ((((((((((((((BitWriter.empty 64).push 32 0x664C6143).push 1 1).push 7
              0).push 24 34).push 16 blockSize).push 16 blockSize).push 24
              0).push 24 0).push 20 sr).push 3 (ch - 1)).push 5 (16 - 1)).pushBits
              36 (bytes.size / (2 * ch))).pushBits 128
              (Stream.md5Nat (Md5.md5 bytes)))
      (Emit.W.pushStreamPrefix ⟨blockSize, false, fastChooser 16⟩
        ⟨Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList), 16, sr⟩
        (Emit.W.empty cap)) := by
  have hmd5 : Stream.md5Nat (Md5.md5 bytes)
      = Stream.md5Nat (Md5.md5 (Stream.pcmBytes 16 (Flac.deinterleave ch
          (Flac.pcm16OfByteList bytes.data.toList)))) := by
    rw [pcmBytes_deinterleave hch bytes hsz]
  have hns := numSamples_eq hch bytes sr
  have hcl : (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)).length = ch :=
    length_deinterleave _
  simp only [Emit.W.pushStreamPrefix, Emit.W.pushStreamInfo]
  rw [hmd5, hns, hcl]
  exact sim_pushBits 128 _ _ _ (sim_pushBits 36 _ _ _
    (sim_push (k := 5) (v := 16 - 1) (by omega) _ _
      (sim_push (k := 3) (v := ch - 1) (by omega) _ _
        (sim_push (k := 20) (v := sr) (by omega) _ _
          (sim_push (k := 24) (v := 0) (by omega) _ _
            (sim_push (k := 24) (v := 0) (by omega) _ _
              (sim_push (k := 16) (v := blockSize) (by omega) _ _
                (sim_push (k := 16) (v := blockSize) (by omega) _ _
                  (sim_push (k := 24) (v := 34) (by omega) _ _
                    (sim_push (k := 7) (v := 0) (by omega) _ _
                      (sim_push (k := 1) (v := 1) (by omega) _ _
                        (sim_push (k := 32) (v := 0x664C6143) (by omega) _ _
                          (sim_empty 64 cap)))))))))))))

/-- **The shipped encoder computes the reference encoder.** Its `Float`
    search, its `UInt64` writer, its per-frame workers — all of it produces
    exactly the bytes `Flac.Stream.encode` produces for the audio the PCM
    pipeline derives, with the search itself as the chooser. -/
theorem encodePcm16_eq {blockSize ch sr : Nat} (hch : 0 < ch) (hch8 : ch ≤ 8)
    (hbs : 0 < blockSize) (bytes : ByteArray)
    (hsz : bytes.size % (2 * ch) = 0) :
    encodePcm16 blockSize ch sr bytes
      = Stream.encode ⟨blockSize, false, fastChooser 16⟩
          ⟨Flac.deinterleave ch (Flac.pcm16OfByteList bytes.data.toList),
            16, sr⟩ := by
  have hns := numSamples_eq hch bytes sr
  have hsp := sim_prefix (blockSize := blockSize) (sr := sr) hch bytes hsz
    (64 + 2 * (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList)).length
      * (Stream.Audio.mk (Flac.deinterleave ch
          (Flac.pcm16OfByteList bytes.data.toList)) 16 sr).numSamples)
  have hcount : (Stream.chunkChannels blockSize (Flac.deinterleave ch
      (Flac.pcm16OfByteList bytes.data.toList))).length
      = (bytes.size / (2 * ch) + blockSize - 1) / blockSize := by
    rw [chunkChannels_length hbs,
      show ((Flac.deinterleave ch
        (Flac.pcm16OfByteList bytes.data.toList)).headD []).length
        = bytes.size / (2 * ch) from hns]
  rw [← Emit.encode_eq]
  show encodePcm16 blockSize ch sr bytes = (Emit.W.pushStream _ _ (Emit.W.empty _)).buf
  rw [encodePcm16]
  simp only []
  rw [if_neg (show ¬(ch = 0) from by omega),
    if_neg (show ¬(blockSize = 0) from by omega)]
  refine (pushFrames_concat 16 false blockSize
    ((Stream.EncoderCfg.mk blockSize false (fastChooser 16)).safeChooser 16)
    blockSize ch (bytes.size / (2 * ch)) bytes _ _ 0 _ _ hsp.1 ?_ ?_ ?_).symm
  · rw [Emit.emits_pending_mod (Emit.emits_pushStreamPrefix _ _) _ rfl]
    exact (Nat.dvd_iff_mod_eq_zero ..).1 (Emit.streamPrefixBits_length_dvd _ _)
  · rw [hcount, List.length_map, List.length_range]
  · intro k hk
    rw [hcount] at hk
    have hkb : k * blockSize ≤ bytes.size / (2 * ch) := by
      have h1 : (k + 1) * blockSize ≤ bytes.size / (2 * ch) + blockSize - 1 :=
        (Nat.le_div_iff_mul_le hbs).1 hk
      rw [Nat.succ_mul] at h1
      omega
    rw [Nat.zero_add, chunkChannels_getD blockSize _ k (by rw [hcount]; omega)]
    exact frameBytesPcm_eq hch hch8 bytes hsz k hkb

/-- The shipped encoder *is* the checked reference encoder at the fast
    chooser: every runtime check the reference performs is discharged by a
    theorem, so a `some` needs only the O(1) guards. -/
theorem encodePcm16Cfg_fast {blockSize ch sr : Nat} (hch : 0 < ch) (hch8 : ch ≤ 8)
    (bytes : ByteArray) (hsz : bytes.size % (2 * ch) = 0) (hsr : sr < 2 ^ 20)
    (hn : bytes.size / (2 * ch) < 2 ^ 36) (hbs16 : 16 ≤ blockSize)
    (hbs : blockSize ≤ 65535) :
    Flac.encodePcm16Cfg ⟨blockSize, false, fastChooser 16⟩ ch sr bytes
      = some (encodePcm16 blockSize ch sr bytes) := by
  unfold Flac.encodePcm16Cfg
  rw [if_pos ⟨hch, hsz⟩]
  unfold Flac.encodeCheckedCfg
  rw [if_pos ⟨audio_wellFormed hch hch8 bytes hsr hn, hbs16, hbs⟩,
    encodePcm16_eq hch hch8 (by omega) bytes hsz]

/-- **The byte-level guarantee for the shipped encoder, with no runtime
    certificate**: decoding what it produced returns exactly the input PCM. -/
theorem decodePcm16_encodePcm16_direct {blockSize ch sr : Nat} (hch : 0 < ch)
    (hch8 : ch ≤ 8) (bytes : ByteArray) (hsz : bytes.size % (2 * ch) = 0)
    (hsr : sr < 2 ^ 20) (hn : bytes.size / (2 * ch) < 2 ^ 36)
    (hbs16 : 16 ≤ blockSize) (hbs : blockSize ≤ 65535) :
    Flac.decodePcm16 (encodePcm16 blockSize ch sr bytes) = .ok bytes :=
  Flac.decodePcm16_encodePcm16Cfg
    (encodePcm16Cfg_fast hch hch8 bytes hsz hsr hn hbs16 hbs)

end Flac.Encode

namespace Flac.Stream

/-- **The shipped encoder's byte-level guarantee**: whenever
    `Flac.encodePcm16Fast` produces a FLAC file at all, decoding that file
    returns exactly the input PCM bytes. No hypotheses, no runtime
    certificate, and no trust in `Flac.Encode` — it is proven. -/
theorem decodePcm16_encodePcm16Fast {blockSize ch sr : Nat}
    {bytes flac : ByteArray}
    (h : Flac.encodePcm16Fast blockSize ch sr bytes = some flac) :
    Flac.decodePcm16 flac = .ok bytes := by
  unfold Flac.encodePcm16Fast at h
  split at h
  case isFalse => cases h
  case isTrue hg =>
    obtain ⟨hch, hch8, hsz, hsr, hn, hbs16, hbs⟩ := hg
    cases h
    exact Flac.Encode.decodePcm16_encodePcm16_direct hch hch8 bytes hsz hsr hn
      hbs16 hbs

end Flac.Stream
