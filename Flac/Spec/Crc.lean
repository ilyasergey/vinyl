import Flac.Native.Crc

/-!
# Correctness of allocation-free CRC ranges

The native range helpers fold directly over a bounded region of the source
`ByteArray`.  These lemmas connect that implementation to the existing CRCs on
`ByteArray.extract`, including the endpoint clamping performed by `extract`.
-/

namespace ByteArray

/-- Folding a byte-array range is the same as folding its extracted copy. -/
theorem foldlM_start_stop {m} [Monad m] {f : β → UInt8 → m β} {b}
    {xs : ByteArray} {start stop : Nat} :
    xs.foldlM f b start stop = (xs.extract start stop).foldlM f b := by
  unfold foldlM
  simp only [Nat.sub_zero, size_extract, Nat.le_refl, ↓reduceDIte]
  suffices foldlM.loop f xs (min stop xs.size) (by omega)
      (min stop xs.size - start) start b =
      foldlM.loop f (xs.extract start stop) (min stop xs.size - start) (by simp)
        (min stop xs.size - start) 0 b by
    split
    · have : min stop xs.size = stop := by omega
      simp_all
    · have : min stop xs.size = xs.size := by omega
      simp_all
  revert b
  suffices ∀ (b : β) (i k) (w : i + k = min stop xs.size - start),
      foldlM.loop f xs (min stop xs.size) (by omega) i (start + k) b =
      foldlM.loop f (xs.extract start stop) (min stop xs.size - start) (by simp) i k b by
    intro b
    simpa using this b (min stop xs.size - start) 0 (by omega)
  intro b i k w
  induction i generalizing b k with
  | zero =>
    simp only [Nat.zero_add] at w
    subst k
    simp [foldlM.loop]
  | succ i ih =>
    unfold foldlM.loop
    rw [dif_pos (by omega), dif_pos (by omega)]
    split <;> rename_i h
    · rfl
    · simp at h
      subst h
      simp only [getElem_extract]
      congr
      funext b
      specialize ih b (k + 1) (by omega)
      simp [← Nat.add_assoc] at ih
      rw [ih]

/-- Non-monadic specialization of `foldlM_start_stop`. -/
theorem foldl_start_stop {f : β → UInt8 → β} {b}
    {xs : ByteArray} {start stop : Nat} :
    xs.foldl f b start stop = (xs.extract start stop).foldl f b := by
  change Id.run (xs.foldlM _ b start stop) =
    Id.run ((xs.extract start stop).foldlM _ b)
  rw [foldlM_start_stop]

/-- Explicitly clamping the upper endpoint does not change an extraction. -/
theorem extract_min_stop (xs : ByteArray) (start stop : Nat) :
    xs.extract start (min stop xs.size) = xs.extract start stop := by
  apply ByteArray.ext_getElem
  · simp [Nat.min_assoc]
  · intro i hi hi'
    rw [ByteArray.getElem_extract, ByteArray.getElem_extract]

end ByteArray

namespace Flac.Crc

/-- The allocation-free CRC-8 range agrees with CRC-8 on an extracted copy. -/
theorem crc8Range_eq_extract (bs : ByteArray) (start stop : Nat) :
    crc8Range bs start stop = crc8 (bs.extract start stop) := by
  rw [crc8Range, ByteArray.foldl_start_stop, ByteArray.extract_min_stop]
  rfl

/-- The allocation-free CRC-16 range agrees with CRC-16 on an extracted copy. -/
theorem crc16Range_eq_extract (bs : ByteArray) (start stop : Nat) :
    crc16Range bs start stop = crc16 (bs.extract start stop) := by
  rw [crc16Range, ByteArray.foldl_start_stop, ByteArray.extract_min_stop]
  rfl

end Flac.Crc
