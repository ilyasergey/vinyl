/* pcm_mutator (B4) -- a header-preserving, sample-aware mutator for the ENCODE
 * side (packed s16le PCM, common/pack.h) plus a positional G1-RAW-param mutator
 * for the gen_params block (common/vinyl_gen.c gen_build layout).
 *
 * WHY IT EXISTS
 * The CRC mutator (common/flac_struct.c) is a FLAC-*stream* mutator: it keeps a
 * decodable frame alive across the CRC gate. It does nothing useful on the encode
 * corpora, whose inputs are a 6-byte packed header + raw interleaved PCM: a byte
 * flip there is just noise, so libFuzzer's plain havoc rarely produces the
 * correlated, boundary-shaped signals that make the encoder pick FIXED/LPC and
 * emit real residuals. This mutator edits the sample region *as samples* --
 * repeating windows, copying/subtracting channels, clearing low bits, integrating
 * a residual into correlated audio, and splicing per-64 variance blocks -- while
 * preserving the 6-byte header (or re-rolling it only within pack_decode's
 * accepted envelope). The G1 variant walks the gen_params field boundaries.
 *
 * STATUS: DEFERRED / UNWIRED. These functions are complete and self-contained,
 * but NOT wired into the fuzz build or the FUZZ_MUTATOR / AFL_CUSTOM_MUTATOR
 * dispatch. Activating it is a follow-up: add a `build/lib/pcm_mutator.so` rule
 * (mirroring afl_mutator.so in mk/tools.mk), a `mutator="pcm"` variant in
 * fleet/config.py, and an AFL_CUSTOM_MUTATOR_LIBRARY branch in fleet/launch.py
 * for that kind (libFuzzer side additionally needs a FUZZ_MUT_PCM policy value in
 * engine/mutator_policy.{c,h} and a call in engine/libfuzzer_mutator.c, both of
 * which are outside the B4 file scope -- hence deferred rather than half-wired).
 *
 * The file exposes AFL++'s afl_custom_* API so that, once a `.so` rule exists, it
 * is a drop-in like engine/afl_mutator.c; it links nothing beyond libc and the
 * two header-only layers, so it never drags a fuzzer/Lean runtime into a run.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "pack.h" /* pack_decode, PackedInput, PACK_BS_MAX, k_sr_table */

/* xorshift64*, matching the rest of the rig's fixed-seed style. */
static uint64_t pm_next(uint64_t *s) {
  uint64_t x = *s ? *s : 0x9E3779B97F4A7C15ULL;
  x ^= x >> 12;
  x ^= x << 25;
  x ^= x >> 27;
  *s = x;
  return x * 0x2545F4914F6CDD1DULL;
}

static inline int16_t pm_get(const uint8_t *pcm, size_t i) {
  return (int16_t)((uint16_t)pcm[2 * i] | ((uint16_t)pcm[2 * i + 1] << 8));
}
static inline void pm_set(uint8_t *pcm, size_t i, int16_t v) {
  pcm[2 * i] = (uint8_t)((uint16_t)v & 0xff);
  pcm[2 * i + 1] = (uint8_t)(((uint16_t)v >> 8) & 0xff);
}

/* ===================================================================== PCM
 * Header-preserving, sample-aware mutation of a packed s16le input. Returns the
 * (unchanged) total length; edits happen in place within buf[6 .. 6+pcm_len).
 * `cap` bounds the buffer but this mutator never grows the input. */
size_t pcm_mutate_packed(uint8_t *buf, size_t n, size_t cap, uint64_t *rng) {
  (void)cap;
  PackedInput pi;
  if (!pack_decode(buf, n, &pi) || pi.pcm_len < 2 * (size_t)pi.ch)
    return n;
  uint8_t *pcm = buf + 6;
  int nch = pi.ch;
  size_t frames = pi.pcm_len / (2u * (size_t)nch);
  if (frames == 0)
    return n;

  switch (pm_next(rng) % 7u) {
  case 0: { /* repeat a window of frames elsewhere (self-similar structure) */
    size_t wlen = 1 + (size_t)(pm_next(rng) % frames);
    size_t src = (size_t)(pm_next(rng) % frames);
    size_t dst = (size_t)(pm_next(rng) % frames);
    for (size_t k = 0; k < wlen && src + k < frames && dst + k < frames; k++)
      for (int c = 0; c < nch; c++)
        pm_set(pcm, (dst + k) * nch + c, pm_get(pcm, (src + k) * nch + c));
    break;
  }
  case 1: { /* copy one channel over another (perfect inter-channel correlation) */
    if (nch >= 2) {
      int a = (int)(pm_next(rng) % (unsigned)nch), b = (int)(pm_next(rng) % (unsigned)nch);
      if (a != b)
        for (size_t f = 0; f < frames; f++)
          pm_set(pcm, f * nch + b, pm_get(pcm, f * nch + a));
    }
    break;
  }
  case 2: { /* replace ch b with (a - b): drives mid/side decorrelation choice */
    if (nch >= 2) {
      int a = (int)(pm_next(rng) % (unsigned)nch), b = (int)(pm_next(rng) % (unsigned)nch);
      if (a != b)
        for (size_t f = 0; f < frames; f++) {
          int32_t d = (int32_t)pm_get(pcm, f * nch + a) - (int32_t)pm_get(pcm, f * nch + b);
          pm_set(pcm, f * nch + b, (int16_t)d);
        }
    }
    break;
  }
  case 3: { /* clear the low k bits of every sample (wasted-bits path) */
    int k = 1 + (int)(pm_next(rng) % 8u);
    uint16_t mask = (uint16_t)(0xffffu << k);
    for (size_t i = 0; i < frames * (size_t)nch; i++)
      pm_set(pcm, i, (int16_t)((uint16_t)pm_get(pcm, i) & mask));
    break;
  }
  case 4: { /* integrate: turn a noisy region into a correlated random walk */
    for (int c = 0; c < nch; c++) {
      int32_t acc = 0;
      for (size_t f = 0; f < frames; f++) {
        acc += pm_get(pcm, f * nch + c);
        pm_set(pcm, f * nch + c, (int16_t)acc); /* wraps to 16 bits by design */
      }
    }
    break;
  }
  case 5: { /* per-64 variance splice: swap two 64-frame blocks */
    size_t blk = 64;
    if (frames >= 2 * blk) {
      size_t nb = frames / blk;
      size_t i = (size_t)(pm_next(rng) % nb), j = (size_t)(pm_next(rng) % nb);
      for (size_t k = 0; k < blk; k++)
        for (int c = 0; c < nch; c++) {
          size_t ia = (i * blk + k) * nch + c, ja = (j * blk + k) * nch + c;
          int16_t t = pm_get(pcm, ia);
          pm_set(pcm, ia, pm_get(pcm, ja));
          pm_set(pcm, ja, t);
        }
    }
    break;
  }
  default: { /* re-roll a header byte -- pack_decode reduces every byte modulo an
             * accepted range, so this stays within the checked envelope */
    buf[pm_next(rng) % 6u] = (uint8_t)pm_next(rng);
    break;
  }
  }
  return n;
}

/* ================================================================== G1 RAW
 * Positional boundary mutator for the gen_params block (vinyl_gen.c gen_build):
 *   [0]=bps-1  [1]=ch-1  [2]=adv|advkind|population  [3]=bs_idx|chooser_kind
 *   [4],[5]=nsamples/seed  [6]=sr_idx  [7]=seed  [8]=chooser arg (B3)
 * Snaps one field to a boundary value so field transitions (each bps, ch=2,
 * every chooser slot incl. the parameterized order-7 / partition / RICE2 arms)
 * are reached without waiting on random byte drift. Never shrinks below 9 bytes. */
size_t pcm_mutate_g1_param(uint8_t *buf, size_t n, size_t cap, uint64_t *rng) {
  static const uint8_t bps[] = {0, 7, 11, 15, 23, 31};       /* bps-1 for 1/8/12/16/24/32 */
  static const uint8_t chooser_arg[] = {6, 5, 8, 15, 15, 17, 18, 30, 64, 65, 66, 67, 128};
  if (n < 9) {
    if (cap < 9)
      return n;
    memset(buf + n, 0, 9 - n);
    n = 9;
  }
  switch (pm_next(rng) % 8u) {
  case 0:
    buf[0] = bps[pm_next(rng) % (sizeof bps / sizeof bps[0])];
    break;
  case 1:
    buf[1] = (uint8_t)(pm_next(rng) % 8u); /* ch-1: cover mono..8ch */
    break;
  case 2:
    buf[2] = (uint8_t)(pm_next(rng) & 0x1f); /* adversarial + advkind + population */
    break;
  case 3: { /* chooser_kind in bits 3-5, block-size index in bits 0-2 */
    unsigned kind = pm_next(rng) % 8u, bsidx = pm_next(rng) % 8u;
    buf[3] = (uint8_t)((kind << 3) | bsidx);
    break;
  }
  case 4: /* small nsamples (favor short blocks that stay under the output cap) */
    buf[4] = (uint8_t)pm_next(rng);
    buf[5] = (uint8_t)(pm_next(rng) & 3u);
    break;
  case 5:
    buf[6] = (uint8_t)(pm_next(rng) % 8u); /* sample-rate index */
    break;
  case 6:
    buf[8] = chooser_arg[pm_next(rng) % (sizeof chooser_arg / sizeof chooser_arg[0])];
    break;
  default:
    buf[7] = (uint8_t)pm_next(rng); /* seed churn */
    break;
  }
  return n;
}

/* ============================================================== AFL++ shim
 * Present so this becomes a drop-in custom mutator once a .so rule exists.
 * Heuristic split: a short input (<= 32 bytes) is a G1 RAW param block, anything
 * larger is packed PCM. Deliberately conservative -- unwired today. */
#define PM_CAP (1u << 20)

typedef struct {
  uint8_t *buf;
  uint64_t rng;
} PmState;

void *afl_custom_init(void *afl, unsigned int seed) {
  (void)afl;
  PmState *m = calloc(1, sizeof *m);
  if (!m)
    return NULL;
  m->buf = malloc(PM_CAP);
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
  (void)add_buf;
  (void)add_buf_size;
  PmState *m = data;
  size_t cap = max_size && max_size < PM_CAP ? max_size : PM_CAP;
  size_t n = buf_size < cap ? buf_size : cap;
  memcpy(m->buf, buf, n);
  *out_buf = m->buf;
  size_t r = (n <= 32) ? pcm_mutate_g1_param(m->buf, n, cap, &m->rng)
                       : pcm_mutate_packed(m->buf, n, cap, &m->rng);
  return r ? r : (n ? n : 1);
}

void afl_custom_deinit(void *data) {
  PmState *m = data;
  if (!m)
    return;
  free(m->buf);
  free(m);
}
