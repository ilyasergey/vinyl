#include "flac_residual.h"

#include <string.h>

#include "flac_bits.h"

/* The bit reader, the UTF-8-coded-number sizing and the subframe-offset
 * derivation all come from the shared common/flac_bits.h now -- this file
 * keeps only the residual-recomputation math, which is its own concern. */

/* channel/bps codes from the frame header (byte 3): channel assignment and depth. */
static int frame_is_mono(const uint8_t *b, size_t fs) {
  return flac_fh_channel_code(b, fs) == 0; /* 0 = single independent channel */
}

static int fixed_predict(const int64_t *x, long i, int order, int64_t *pred) {
  switch (order) {
    case 0: *pred = 0; return 1;
    case 1: *pred = x[i - 1]; return 1;
    case 2: *pred = 2 * x[i - 1] - x[i - 2]; return 1;
    case 3: *pred = 3 * x[i - 1] - 3 * x[i - 2] + x[i - 3]; return 1;
    case 4: *pred = 4 * x[i - 1] - 6 * x[i - 2] + 4 * x[i - 3] - x[i - 4]; return 1;
    default: return 0;
  }
}

int flac_residual_mono(const uint8_t *buf, size_t n, size_t frame_start, const int64_t *x, long nx,
                       int bps, ResidualInfo *ri) {
  memset(ri, 0, sizeof *ri);
  /* frame_is_mono reads buf[frame_start+3]; guard before it so a frame_start
   * near the end never reads past the buffer. */
  if (nx < 2 || bps < 1 || bps > 32 || frame_start + 4 > n)
    return 0;
  if (!frame_is_mono(buf, frame_start))
    return 0;
  size_t soff = flac_frame_body_offset(buf, n, frame_start);
  if (soff == 0)
    return 0;

  FlacBitReader r;
  fbr_init(&r, buf, n, soff * 8);
  if (fbr_read(&r, 1) != 0) /* mandatory 0 padding bit */
    return 0;
  int type = (int)fbr_read(&r, 6);
  int wasted_flag = (int)fbr_read(&r, 1);
  if (wasted_flag) /* skip wasted-bit subframes (residual is on x>>w) */
    return 0;

  int is_lpc, order;
  if (type == 0 || type == 1)
    return 0; /* CONSTANT / VERBATIM: no residual */
  else if (type >= 8 && type <= 12) {
    is_lpc = 0;
    order = type - 8;
  } else if (type >= 32) {
    is_lpc = 1;
    order = type - 31; /* 1..32 */
  } else
    return 0; /* reserved */

  if (order >= nx || order > 32)
    return 0;

  int64_t coef[32];
  int precision = 0, shift = 0;
  if (is_lpc) {
    /* Skip the `order` warmup samples (their VALUES we already have in x; we only
     * need to advance past them to precision/shift/coefs). Their bit width is the
     * sample depth `bps` -- Vinyl emits frame bit-depth code 0, so the caller
     * supplies the depth from the decode, not the frame header. */
    for (int k = 0; k < order; k++)
      (void)fbr_read_signed(&r, bps); /* skip warmup */
    precision = (int)fbr_read(&r, 4) + 1;
    if (precision > 32 || precision < 1)
      return 0;
    shift = (int)fbr_read_signed(&r, 5);
    if (shift < 0)
      return 0; /* negative shift is not produced by conformant encoders */
    for (int k = 0; k < order; k++)
      coef[k] = fbr_read_signed(&r, precision);
    if (r.err)
      return 0;
  }

  /* Recompute residuals from the reconstructed samples. */
  int64_t maxabs = 0, bad = 0;
  int viol = 0;
  const int64_t LIM = (int64_t)1 << 31; /* 2^31 */
  for (long i = order; i < nx; i++) {
    int64_t pred;
    if (is_lpc) {
      __int128 acc = 0;
      for (int j = 0; j < order; j++)
        acc += (__int128)coef[j] * (__int128)x[i - 1 - j];
      pred = (int64_t)(acc >> shift);
    } else if (!fixed_predict(x, i, order, &pred)) {
      return 0;
    }
    int64_t res = x[i] - pred;
    int64_t a = res < 0 ? -res : res;
    if (a > maxabs)
      maxabs = a;
    /* §9.2.7.3: |r| < 2^31 AND r != -2^31. */
    if (a >= LIM || res == -LIM) {
      if (!viol) {
        viol = 1;
        bad = res;
      }
    }
  }

  ri->analyzed = 1;
  ri->is_lpc = is_lpc;
  ri->order = order;
  ri->precision = precision;
  ri->shift = shift;
  ri->max_abs_residual = maxabs;
  ri->violation = viol;
  ri->bad_residual = bad;
  return 1;
}
