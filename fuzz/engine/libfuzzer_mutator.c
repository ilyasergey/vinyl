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

/* Sample-aware encode-side mutators (common/pcm_mutator.c). Declared here rather
 * than via a new header: they are the FUZZ_MUT_PCM policy's only two entry points. */
extern size_t pcm_mutate_packed(uint8_t *buf, size_t n, size_t cap, uint64_t *rng);
extern size_t pcm_mutate_g1_param(uint8_t *buf, size_t n, size_t cap, uint64_t *rng);

size_t LLVMFuzzerCustomMutator(uint8_t *data, size_t size, size_t max, unsigned int seed) {
  FuzzMutator pol = fuzz_mutator_policy();
  if (pol == FUZZ_MUT_PLAIN)
    return LLVMFuzzerMutate ? LLVMFuzzerMutate(data, size, max) : size;
  static uint64_t rng;
  rng ^= 0x9E3779B97F4A7C15ULL * ((uint64_t)seed + 1);
  if (!rng)
    rng = 0x2545F4914F6CDD1DULL;
  if (pol == FUZZ_MUT_PCM) {
    /* Dispatch by the running target's input format: packed s16le PCM gets the
     * header-preserving sample mutator; a small RAW block is a G1 gen_params
     * field walk. The sample-aware ops are SAME-LENGTH in-place transforms that
     * inject no new bytes, so on their own the corpus can never grow in length or
     * gain new sample entropy -- and on a too-short unit they are a strict no-op
     * that would spin. Mix in libFuzzer's own havoc 1-in-4 (and unconditionally for
     * short/other-kind units) to keep length growth and fresh entropy flowing. */
    const int kind = fuzz_target_info.input_kind;
    const int short_pcm = (kind == FUZZ_INPUT_PACKED_PCM && size < 6);
    if ((rng & 3u) == 0 || short_pcm ||
        (kind != FUZZ_INPUT_PACKED_PCM &&
         !(kind == FUZZ_INPUT_RAW && size >= 8 && size <= 32)))
      return LLVMFuzzerMutate ? LLVMFuzzerMutate(data, size, max) : size;
    size_t n = (kind == FUZZ_INPUT_PACKED_PCM) ? pcm_mutate_packed(data, size, max, &rng)
                                               : pcm_mutate_g1_param(data, size, max, &rng);
    return n ? n : (size ? size : 1);
  }
  size_t n = flac_mutate(data, size, max, &rng);
  return n ? n : (size ? size : 1);
}

size_t LLVMFuzzerCustomCrossOver(const uint8_t *a, size_t alen, const uint8_t *b, size_t blen,
                                 uint8_t *out, size_t max, unsigned int seed) {
  /* Only the CRC (FLAC-stream) mutator has a frame-granular crossover; PLAIN and
   * PCM return 0 so libFuzzer uses its own. */
  if (fuzz_mutator_policy() != FUZZ_MUT_CRC || alen == 0)
    return 0;
  static uint64_t rng;
  rng ^= 0xD1B54A32D192ED03ULL * ((uint64_t)seed + 1);
  if (!rng)
    rng = 0x9E3779B97F4A7C15ULL;
  size_t n = alen < max ? alen : max;
  memcpy(out, a, n);
  return flac_crossover(out, n, b, blen, max, &rng);
}
