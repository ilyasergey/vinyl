/* rng.h -- ONE xorshift64 PRNG (Phase 4 dedup).
 *
 * The rig grew four separate xorshift64 implementations (vinyl_gen.c, mut_bench.c,
 * measure_encode.c, flac_struct.c), none cross-checked against the others. They
 * are the same algorithm; this is the single source. Header-only + `static inline`
 * so every translation unit gets its own copy with no link coupling, and the
 * UNSIGNED wrapping it relies on is well-defined (not UB -- this is exactly why the
 * scoped UBSan flavour excludes the `integer` group).
 *
 * Determinism is a REQUIREMENT here (reproducible seeds/corpora), so the constants
 * are fixed and documented; do not "improve" them.
 */
#ifndef RNG_H
#define RNG_H

#include <stdint.h>

/* Marsaglia xorshift64 (a=13, b=7, c=17). Period 2^64-1; never seed to 0. */
static inline uint64_t rng_next(uint64_t *s) {
  uint64_t x = *s ? *s : 0x9e3779b97f4a7c15ULL; /* avoid the fixed point at 0 */
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  *s = x;
  return x;
}

/* Top 32 bits (better-distributed than the low bits of an LCG-style step). */
static inline uint32_t rng_next32(uint64_t *s) { return (uint32_t)(rng_next(s) >> 32); }

/* SplitMix64 finalizer: turn a plain integer seed into a well-mixed state so two
 * nearby seeds do not produce correlated streams. */
static inline uint64_t rng_seed(uint64_t seed) {
  uint64_t z = seed + 0x9e3779b97f4a7c15ULL;
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  z = z ^ (z >> 31);
  return z ? z : 0x9e3779b97f4a7c15ULL;
}

#endif /* RNG_H */
