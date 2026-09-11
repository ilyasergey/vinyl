# The 32-bit scalar-`Int` cliff (a performance incident, not a bug)

*Recorded 2026-09-08 during optimization work; no theorem, no decoded byte and
no accepted stream changes.*

## What happened

Lean's `Int` is exact and unbounded, which is why the decoder can do its
sample arithmetic in ℤ and defend nothing against overflow. The runtime
represents small values as tagged scalars and everything else as GMP
bignums, and the scalar range is **32-bit** — not 63-bit. In the LPC restore
loop every tap is `acc + c * out[n]`, so on a 24-bit stream at order 12 the
partial sums leave the scalar range almost immediately and every tap
allocates.

Measured on an 8 M-sample mono tone encoded by libFLAC at `-8 -l 12`, in 24-bit
and 16-bit, before the machine-word kernels:

| | 16-bit, order 12 | 24-bit, order 12 |
|---|---|---|
| instructions / sample | 2,575 | **17,233** |
| GMP calls / sample | ~0 | **290** |
| `mi_malloc` / sample | ~0 | **14.5** |
| wall (same content) | 0.77 s | **5.31 s** |

Nothing was wrong: the decoder was correct, total, and within all its
budgets. It was seven times slower per sample on the bit depth the format is
usually *praised* for, and the cliff was invisible in every benchmark
because every probe in the corpus was 16-bit.

## Why it is worth a note

The cost model of an exact-arithmetic language is not uniform, and the
discontinuity is not where a reader expects it. "`Int` is exact, so the
proofs are simple" is true; "and the constant factor is flat" is not. The
performance story and the robustness story are the same story here: a
per-sample GMP allocation on attacker-chosen bit depth is also a denial of
service surface, and it sat one field of the STREAMINFO block away.

## What fixed it

The `Int64` restore kernel (`Lpc.restoreFast`, shipped behind
`restoreA_eq_restoreFast`): the taps and the history ride in machine words,
the sum is exact because the subframe grammar bounds it (order ≤ 32,
|c| < 2^15, |x| < 2^33 ⇒ |Σ| < 2^53), and values outside the guarded domain
fall back to the boxed loop. The 24-bit probe went 5.31 s → 0.157 s with zero
GMP calls, and the statement of every theorem about `restoreA` is unchanged.

## What to carry forward

- **Bit depth is a probe dimension.** A benchmark corpus that is entirely
  16-bit cannot see this class of cost at all.
- **Count GMP calls, not just cycles.** `lean_int_big_*` and `mi_malloc` per
  sample are the diagnostic; wall time only tells you afterwards.
- **The scalar boundary is 2^31, not 2^62.** Any per-sample `Int` value that
  can reach 2^31 on a *legal* stream is a cliff waiting for the input that
  crosses it.
