import Flac.Native.Codec
import Flac.Native.Encode
import Flac.Spec.Decode
import Flac.Spec.Emit

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
  fun bw w h => hG _ _ (hF _ _ h)

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
    (hks : ∀ j, ks.getD j 10 ≤ 32)
    (hb : (Rice.partSizes bs po ord).sum ≤ res.size) :
    Simulates (fun bw => pushResidual bw bs ord po ks res)
      (Emit.W.pushResidual bs ord (riceCfgOf po ks) res) := by
  intro bw w h
  have hk : ∀ k, Rice.Partition.rice k ∈ riceChoices po ks → k ≤ 32 := by
    intro k hm
    unfold riceChoices at hm
    obtain ⟨j, _, hj⟩ := List.mem_map.1 hm
    cases hj
    exact hks j
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
    obtain ⟨hks, hb⟩ := hok
    exact sim_pushResidual xs.size ord po ks _ hks hb _ _
      (sim_pushSIntSeg b xs 0 ord _ _ h)
  | lpc cs shift po ks =>
    obtain ⟨hks, hb⟩ := hok
    exact sim_pushResidual xs.size cs.length po ks _ hks hb _ _
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
    Simulates (pushPlanOf (qs.map Prod.fst)) (Emit.W.pushPlan (planOf qs)) := by
  intro qs
  induction qs with
  | nil => intro _ bw w h; exact h
  | cons q qs ih =>
    intro hq bw w h
    obtain ⟨hd, hok⟩ := hq q (List.mem_cons_self ..)
    have hq' : ∀ r ∈ qs, r.1.Denotes r.2 ∧ r.1.plan.EmitOk r.1.scaled :=
      fun r hm => hq r (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, pushPlanOf, planOf]
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
    (hsubs : fp.subs = qs.map Prod.fst)
    (hplan : planOf qs = Emit.W.planA b asg chs)
    (hbs : fp.blockSize = (chs.headD #[]).size)
    (hcode : fp.chCode = asg.code chs.length)
    (hq : ∀ q ∈ qs, q.1.Denotes q.2 ∧ q.1.plan.EmitOk q.1.scaled) :
    Simulates (fun bw => pushFrameOf bw b strat num fp)
      (Emit.W.pushFrame b strat num asg chs) := by
  intro bw w h
  have hstart : bw.buf.size = w.buf.size := by rw [h.1]
  -- the header, up to but not including the CRC-8
  have h1 : Sim
      ((((((((((bw.push 14 0x3FFE).push 1 0).push 1
        (if strat then 1 else 0)).push 4 7).push 4 0).push 4 fp.chCode).push 3
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
private theorem length_getD_deinterleaveN (ch : Nat) (hch : 0 < ch) :
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
private theorem getD_deinterleaveN (ch : Nat) (hch : 0 < ch) :
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

end Flac.Encode
