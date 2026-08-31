/* AFL++ custom-mutator shim over the CRC-aware FLAC mutator.
 *
 * AFL++ has no notion of LLVMFuzzerCustomMutator, so the same flac_mutate() /
 * flac_crossover() used by the libFuzzer target is exposed here through
 * AFL++'s afl_custom_* API. Load with:
 *
 *   AFL_CUSTOM_MUTATOR_LIBRARY=build/lib/afl_mutator.so \
 *   AFL_CUSTOM_MUTATOR_ONLY=1 afl-fuzz ...
 *
 * Without AFL_CUSTOM_MUTATOR_ONLY, AFL++ interleaves its own havoc stages with
 * this one, which is usually what you want: havoc explores malformed headers
 * while this stage keeps producing streams that survive the CRC gate. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_struct.h"

#define CAP (1 << 20)

typedef struct {
  uint8_t *buf;
  uint64_t rng;
} Mut;

void *afl_custom_init(void *afl, unsigned int seed) {
  (void)afl;
  Mut *m = calloc(1, sizeof *m);
  if (!m)
    return NULL;
  m->buf = malloc(CAP);
  m->rng = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)seed * 0xD1B54A32D192ED03ULL);
  if (!m->rng)
    m->rng = 0x2545F4914F6CDD1DULL;
  if (!m->buf) {
    free(m);
    return NULL;
  }
  return m;
}

size_t afl_custom_fuzz(void *data, uint8_t *buf, size_t buf_size, uint8_t **out_buf,
                       uint8_t *add_buf, size_t add_buf_size, size_t max_size) {
  Mut *m = data;
  size_t cap = max_size && max_size < CAP ? max_size : CAP;
  size_t n = buf_size < cap ? buf_size : cap;
  memcpy(m->buf, buf, n);
  *out_buf = m->buf;
  /* add_buf is AFL++'s splice partner: use it for frame-granular crossover,
   * exactly like LLVMFuzzerCustomCrossOver does. */
  if (add_buf && add_buf_size > 0 && (m->rng >> 33) % 4 == 0) {
    size_t r = flac_crossover(m->buf, n, add_buf, add_buf_size, cap, &m->rng);
    if (r)
      return r;
  }
  size_t r = flac_mutate(m->buf, n, cap, &m->rng);
  return r ? r : (n ? n : 1);
}

void afl_custom_deinit(void *data) {
  Mut *m = data;
  if (!m)
    return;
  free(m->buf);
  free(m);
}
