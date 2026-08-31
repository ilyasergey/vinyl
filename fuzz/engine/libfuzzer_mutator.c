/* LLVMFuzzerCustomMutator / LLVMFuzzerCustomCrossOver adapter over the CRC-aware
 * FLAC mutator (common/flac_struct.c). Linked into EVERY libFuzzer target;
 * fuzz_mutator_policy() decides at run time whether to run the structure-aware
 * mutator or delegate to libFuzzer's built-in one, so "mutator on/off" is a
 * runtime FUZZ_MUTATOR choice rather than a build-time relink.
 *
 * WHY THE CRC MUTATOR EXISTS
 * A FLAC frame carries a CRC-8 over the frame header (poly 0x07) and a CRC-16
 * over the whole frame (poly 0x8005). Flip one byte and the CRC-16 no longer
 * matches, so every plain mutant dies at the CRC gate before it can reach
 * Lpc.restoreA, readResidualA/readPartsA, the wasted-bits shiftUp path,
 * Fixed.restoreA warm-up, or Stereo.decode{LS,RS,MS} -- where the deep-decoder
 * defects live. Measured ~25-27x more libFLAC-accepted inputs than plain
 * mutation (tools/mut_bench rate).
 *
 * Delegating to LLVMFuzzerMutate and returning 0 from CrossOver reproduces
 * libFuzzer's own behaviour exactly, so FUZZ_MUTATOR=plain is behaviourally
 * identical to not linking a custom mutator at all. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_struct.h"
#include "mutator_policy.h"

/* Weakly referenced by flac_struct.c; in a libFuzzer link it always resolves. */
extern size_t LLVMFuzzerMutate(uint8_t *data, size_t size, size_t max);

size_t LLVMFuzzerCustomMutator(uint8_t *data, size_t size, size_t max, unsigned int seed) {
  if (fuzz_mutator_policy() == FUZZ_MUT_PLAIN)
    return LLVMFuzzerMutate ? LLVMFuzzerMutate(data, size, max) : size;
  static uint64_t rng;
  rng ^= 0x9E3779B97F4A7C15ULL * ((uint64_t)seed + 1);
  if (!rng)
    rng = 0x2545F4914F6CDD1DULL;
  size_t n = flac_mutate(data, size, max, &rng);
  return n ? n : (size ? size : 1);
}

size_t LLVMFuzzerCustomCrossOver(const uint8_t *a, size_t alen, const uint8_t *b, size_t blen,
                                 uint8_t *out, size_t max, unsigned int seed) {
  if (fuzz_mutator_policy() == FUZZ_MUT_PLAIN || alen == 0)
    return 0; /* 0 -> libFuzzer falls back to its own crossover */
  static uint64_t rng;
  rng ^= 0xD1B54A32D192ED03ULL * ((uint64_t)seed + 1);
  if (!rng)
    rng = 0x9E3779B97F4A7C15ULL;
  size_t n = alen < max ? alen : max;
  memcpy(out, a, n);
  return flac_crossover(out, n, b, blen, max, &rng);
}
