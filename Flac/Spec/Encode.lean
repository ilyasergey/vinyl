import Flac.Native.Encode
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

/-- The shipped `push` simulates the verified `push`, for every field width
    the encoder uses. -/
theorem sim_push {k v : Nat} (hk : k ≤ 32) :
    Simulates (fun bw => bw.push k v) (fun w => w.push k v) := by
  intro bw w h
  obtain ⟨hbuf, hn, hn8, hacc⟩ := h
  have hkk : (UInt64.ofNat k).toNat % 64 = k := toNat_ofNat_small (by omega)
  -- the fast accumulator, as a `Nat`
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
  -- both accumulators agree on the low `n + k` bits
  have hkey : ((bw.acc <<< UInt64.ofNat k)
      ||| (UInt64.ofNat v &&& ((1 <<< UInt64.ofNat k) - 1))).toNat % 2 ^ (w.n + k)
      = (w.acc * p2 k + (v &&& (p2 k - 1))) % 2 ^ (w.n + k) := by
    rw [hfast, p2_eq, Nat.and_two_pow_sub_one_eq_mod,
      split_mod (Nat.mod_lt _ (Nat.two_pow_pos k)),
      split_mod (Nat.mod_lt _ (Nat.two_pow_pos k)),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show w.n ≤ 64 - k from by omega)),
      hacc]
  exact sim_of_flush hbuf (by rw [hn]) (by omega) hkey

end Flac.Encode
