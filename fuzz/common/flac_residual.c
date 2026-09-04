#include "flac_residual.h"

#include <string.h>

#include "flac_bits.h"
#include "flac_struct.h"

/* The bit reader, the UTF-8-coded-number sizing and the subframe-offset
 * derivation all come from the shared common/flac_bits.h now -- this file
 * keeps only the residual-recomputation math, which is its own concern. */

/* Reconstruct one subframe's OWN sample domain from the decoder's reconstructed
 * OUTPUT channels. decodeArrays returns the final (left,right,...) planes, not the
 * decorrelated subframe values, so for a stereo-decorrelated frame subframe 0's
 * samples must be re-derived from the output: independent / left/side leave ch0 =
 * plane0; right/side makes ch0 the side (left-right); mid/side makes ch0 the mid
 * ((left+right)>>1). Output channel order is (left,right), so side = plane0-plane1
 * and mid = (plane0+plane1)>>1 exactly. Wasted bits shift every value right by w:
 * the decoder shifts left by w on output, so >>w recovers the coded value exactly
 * (the low w bits are known zero). */
enum { SV_PLANE0 = 0, SV_SIDE = 1, SV_MID = 2 };

typedef struct {
  const int64_t *p0, *p1;
  int mode;
  int wasted;
} SampleView;

static inline int64_t sv_at(const SampleView *v, long i) {
  int64_t raw;
  switch (v->mode) {
    case SV_SIDE:
      raw = v->p0[i] - v->p1[i];
      break;
    case SV_MID:
      raw = (v->p0[i] + v->p1[i]) >> 1;
      break;
    default:
      raw = v->p0[i];
  }
  return raw >> v->wasted;
}

static int fixed_predict(const SampleView *v, long i, int order, int64_t *pred) {
  switch (order) {
    case 0: *pred = 0; return 1;
    case 1: *pred = sv_at(v, i - 1); return 1;
    case 2: *pred = 2 * sv_at(v, i - 1) - sv_at(v, i - 2); return 1;
    case 3: *pred = 3 * sv_at(v, i - 1) - 3 * sv_at(v, i - 2) + sv_at(v, i - 3); return 1;
    case 4:
      *pred = 4 * sv_at(v, i - 1) - 6 * sv_at(v, i - 2) + 4 * sv_at(v, i - 3) - sv_at(v, i - 4);
      return 1;
    default: return 0;
  }
}

/* Analyze one subframe: seek to `start_bit`, parse the fixed-size subframe
 * header, and (for a FIXED/LPC subframe) check its recomputed residuals against
 * §9.2.7.3. `base` carries the plane derivation (mode + planes) for this
 * channel's own sample domain; `sub_bps` is its coded depth (base bps, +1 on the
 * expanded side channel). Fills *ri and returns 1 when a residual subframe was
 * analyzed; returns 0 for CONSTANT/VERBATIM/reserved/unparsable. */
static int analyze_subframe(const uint8_t *buf, size_t n, uint64_t start_bit,
                            const SampleView *base, int sub_bps, long nx, int channel,
                            ResidualInfo *ri) {
  FlacBitReader r;
  fbr_init(&r, buf, n, start_bit);
  if (fbr_read(&r, 1) != 0) /* mandatory 0 padding bit */
    return 0;
  int type = (int)fbr_read(&r, 6);
  int wasted = 0;
  if (fbr_read(&r, 1)) /* wasted-bits flag: wasted = unary(leading zeros) + 1 */
    wasted = (int)fbr_unary(&r) + 1;
  if (r.err || wasted < 0 || wasted >= sub_bps)
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

  SampleView v = *base;
  v.wasted = wasted;

  int64_t coef[32];
  int precision = 0, shift = 0;
  if (is_lpc) {
    /* Skip the `order` warmup samples (their VALUES we already recompute from the
     * planes; we only advance past them to precision/shift/coefs). Their coded bit
     * width is the subframe depth minus the wasted bits. */
    int warm = sub_bps - wasted;
    for (int k = 0; k < order; k++)
      (void)fbr_read_signed(&r, warm); /* skip warmup */
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
        acc += (__int128)coef[j] * (__int128)sv_at(&v, i - 1 - j);
      pred = (int64_t)(acc >> shift);
    } else if (!fixed_predict(&v, i, order, &pred)) {
      return 0;
    }
    int64_t res = sv_at(&v, i) - pred;
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
  ri->channel = channel;
  ri->sub_bps = sub_bps;
  ri->wasted = wasted;
  ri->max_abs_residual = maxabs;
  ri->violation = viol;
  ri->bad_residual = bad;
  return 1;
}

/* Build the SampleView + coded depth for channel `c` from the decoder's OUTPUT
 * planes, matching Frame.subframePlan / Decode.readChannels exactly:
 *   independent (side_mode 0): channel c = plane[c], depth bps.
 *   left/side  (1): ch0 = L = plane0 (bps); ch1 = side = plane0-plane1 (bps+1).
 *   right/side (2): ch0 = side = plane0-plane1 (bps+1); ch1 = R = plane1 (bps).
 *   mid/side   (3): ch0 = mid = (plane0+plane1)>>1 (bps); ch1 = side (bps+1).
 * Output channel order is (left,right), so side = plane0-plane1 and
 * mid = (plane0+plane1)>>1 exactly (Stereo.side / Stereo.mid). */
static void channel_view(const int64_t *const *planes, int side_mode, int c, int bps,
                         SampleView *v, int *sub_bps) {
  v->p1 = planes[1];
  v->wasted = 0;
  if (side_mode == 1) { /* left/side */
    if (c == 0) { v->p0 = planes[0]; v->p1 = NULL; v->mode = SV_PLANE0; *sub_bps = bps; }
    else        { v->p0 = planes[0]; v->mode = SV_SIDE; *sub_bps = bps + 1; }
  } else if (side_mode == 2) { /* right/side */
    if (c == 0) { v->p0 = planes[0]; v->mode = SV_SIDE; *sub_bps = bps + 1; }
    else        { v->p0 = planes[1]; v->p1 = NULL; v->mode = SV_PLANE0; *sub_bps = bps; }
  } else if (side_mode == 3) { /* mid/side */
    if (c == 0) { v->p0 = planes[0]; v->mode = SV_MID; *sub_bps = bps; }
    else        { v->p0 = planes[0]; v->mode = SV_SIDE; *sub_bps = bps + 1; }
  } else { /* independent */
    v->p0 = planes[c]; v->p1 = NULL; v->mode = SV_PLANE0; *sub_bps = bps;
  }
}

int flac_residual_frame(const uint8_t *buf, size_t n, size_t frame_start,
                        const int64_t *const *planes, int nch, long nx, int bps,
                        ResidualInfo *out) {
  /* flac_fh_channel_code reads buf[frame_start+3]; guard before it so a
   * frame_start near the end never reads past the buffer. */
  if (out == NULL || planes == NULL || nch < 1 || nch > FLAC_RESIDUAL_MAX_CH || nx < 2 ||
      bps < 1 || bps > 32 || frame_start + 4 > n || planes[0] == NULL)
    return 0;
  memset(out, 0, sizeof(ResidualInfo) * (size_t)nch);

  /* Decorrelation from the frame's channel-assignment code. The side channel
   * (depth bps+1) is the most §9.2.7.3-violation-prone spot. */
  unsigned chc = flac_fh_channel_code(buf, frame_start);
  int side_mode;
  if (chc <= 7)
    side_mode = 0;
  else if (chc == 8)
    side_mode = 1;
  else if (chc == 9)
    side_mode = 2;
  else if (chc == 10)
    side_mode = 3;
  else
    return 0; /* reserved channel assignment */

  if (side_mode == 0) { /* independent: nch subframes = nch output planes */
    if ((unsigned)nch != chc + 1)
      return 0;
  } else { /* stereo decorrelation: exactly two channels, both planes present */
    if (nch != 2 || planes[1] == NULL)
      return 0;
  }

  FlacFrameHeader fh;
  if (!flac_hdr_parse_permissive(buf, n, frame_start, (unsigned)bps, &fh))
    return 0;

  uint64_t starts[FLAC_RESIDUAL_MAX_CH];
  if (!flac_subframe_bit_offsets(buf, n, frame_start, (unsigned)fh.hlen, (unsigned)nch,
                                 (unsigned)bps, side_mode, starts))
    return 0;

  int count = 0;
  for (int c = 0; c < nch; c++) {
    SampleView v;
    int sub_bps;
    channel_view(planes, side_mode, c, bps, &v, &sub_bps);
    if (analyze_subframe(buf, n, starts[c], &v, sub_bps, nx, c, &out[count]))
      count++;
  }
  return count;
}

/* ---- stream-level exact reconstruction (decode-sample-divergence-highbps) ---- */

/* Read one Rice-coded (or escaped) residual partition of `count` values into r[],
 * returning 0 when the partition cannot be judged (reader overrun, a unary run so
 * long the value is pathological). Values are exact: no 32-bit container. */
static int read_residual_partition(FlacBitReader *br, int param_bits, long count, int64_t *r) {
  int esc = (1 << param_bits) - 1;
  int param = (int)fbr_read(br, param_bits);
  if (br->err)
    return 0;
  if (param == esc) {
    int width = (int)fbr_read(br, 5);
    for (long i = 0; i < count; i++)
      r[i] = width ? fbr_read_signed(br, width) : 0;
    return !br->err;
  }
  for (long i = 0; i < count; i++) {
    uint64_t q = fbr_unary(br);
    if (br->err || q > ((uint64_t)1 << 33))
      return 0; /* > 2^33 quotient: not a judgeable stream */
    uint64_t lsb = fbr_read(br, param);
    unsigned __int128 u = ((unsigned __int128)q << param) | lsb;
    __int128 v = (__int128)(u >> 1);
    if (u & 1)
      v = -v - 1;
    if (v > ((__int128)1 << 62) || v < -((__int128)1 << 62))
      return 0;
    r[i] = (int64_t)v;
  }
  return !br->err;
}

/* Exact reconstruction of one subframe; 1 = left its coded depth (o filled),
 * 0 = stayed in range or not judgeable. `bs` is the frame block size. */
static int reconstruct_subframe(const uint8_t *buf, size_t n, uint64_t start_bit, int sub_bps,
                                long bs, int channel, FlacOob *o) {
  FlacBitReader r;
  fbr_init(&r, buf, n, start_bit);
  if (fbr_read(&r, 1) != 0)
    return 0;
  int type = (int)fbr_read(&r, 6);
  int wasted = 0;
  if (fbr_read(&r, 1))
    wasted = (int)fbr_unary(&r) + 1;
  if (r.err || wasted < 0 || wasted >= sub_bps)
    return 0;
  int is_lpc, order;
  if (type >= 8 && type <= 12) {
    is_lpc = 0;
    order = type - 8;
  } else if (type >= 32) {
    is_lpc = 1;
    order = type - 31;
  } else
    return 0; /* CONSTANT / VERBATIM (read at coded width, cannot leave it) / reserved */
  int depth = sub_bps - wasted;
  if (order >= bs || order > 32 || depth < 1 || depth > 32 || bs > 65535)
    return 0;

  static int64_t x[65536];
  for (int k = 0; k < order; k++)
    x[k] = fbr_read_signed(&r, depth);
  int64_t coef[32];
  int shift = 0;
  if (is_lpc) {
    int precision = (int)fbr_read(&r, 4) + 1;
    shift = (int)fbr_read_signed(&r, 5);
    if (precision > 32 || shift < 0)
      return 0;
    for (int k = 0; k < order; k++)
      coef[k] = fbr_read_signed(&r, precision);
  }
  if (r.err)
    return 0;

  /* residual: method (2 bits), partition order (4 bits), 2^po partitions */
  int method = (int)fbr_read(&r, 2);
  int po = (int)fbr_read(&r, 4);
  if (r.err || method > 1)
    return 0;
  int param_bits = method == 0 ? 4 : 5;
  long npart = 1L << po;
  if (bs % npart != 0 || (bs >> po) < order)
    return 0;
  long idx = order;
  for (long p = 0; p < npart; p++) {
    long count = (bs >> po) - (p == 0 ? order : 0);
    if (!read_residual_partition(&r, param_bits, count, x + idx)) /* residuals parked in x[] */
      return 0;
    idx += count;
  }
  /* reconstruct in place: x[i] currently holds the residual for i >= order */
  const __int128 lo = -((__int128)1 << (depth - 1)), hi = (__int128)1 << (depth - 1);
  for (long i = order; i < bs; i++) {
    __int128 pred;
    if (is_lpc) {
      __int128 acc = 0;
      for (int j = 0; j < order; j++)
        acc += (__int128)coef[j] * (__int128)x[i - 1 - j];
      pred = acc >> shift;
    } else {
      switch (order) {
        case 0: pred = 0; break;
        case 1: pred = x[i - 1]; break;
        case 2: pred = 2 * (__int128)x[i - 1] - x[i - 2]; break;
        case 3: pred = 3 * (__int128)x[i - 1] - 3 * (__int128)x[i - 2] + x[i - 3]; break;
        default: pred = 4 * (__int128)x[i - 1] - 6 * (__int128)x[i - 2] + 4 * (__int128)x[i - 3] - x[i - 4];
      }
    }
    __int128 v = pred + x[i];
    if (v < lo || v >= hi) {
      o->index = i;
      o->channel = channel;
      o->depth = depth;
      o->value = (int64_t)(v > INT64_MAX ? INT64_MAX : v < INT64_MIN ? INT64_MIN : v);
      return 1;
    }
    x[i] = (int64_t)v; /* in range: exact, and safe in int64 */
  }
  return 0;
}

int flac_reconstruct_oob(const uint8_t *buf, size_t n, size_t frame_start, int nch, int bps,
                         FlacOob *o) {
  if (o == NULL || nch < 1 || nch > FLAC_RESIDUAL_MAX_CH || bps < 1 || bps > 32 || frame_start + 4 > n)
    return 0;
  unsigned chc = flac_fh_channel_code(buf, frame_start);
  int side_mode = chc <= 7 ? 0 : chc == 8 ? 1 : chc == 9 ? 2 : chc == 10 ? 3 : -1;
  if (side_mode < 0 || (side_mode == 0 && (unsigned)nch != chc + 1) || (side_mode && nch != 2))
    return 0;
  FlacFrameHeader fh;
  if (!flac_hdr_parse_permissive(buf, n, frame_start, (unsigned)bps, &fh) || fh.bs < 1 || fh.bps < 1)
    return 0;
  /* the frame's own resolved depth (its bps code, or the STREAMINFO fallback) */
  int fbps = (int)fh.bps;
  uint64_t starts[FLAC_RESIDUAL_MAX_CH];
  if (!flac_subframe_bit_offsets(buf, n, frame_start, (unsigned)fh.hlen, (unsigned)nch,
                                 (unsigned)fbps, side_mode, starts))
    return 0;
  for (int c = 0; c < nch; c++) {
    int side = (side_mode == 1 && c == 1) || (side_mode == 2 && c == 0) || (side_mode == 3 && c == 1);
    if (reconstruct_subframe(buf, n, starts[c], fbps + side, (long)fh.bs, c, o))
      return 1;
  }
  return 0;
}

int flac_reconstruct_oob_at(const uint8_t *buf, size_t n, int nch, int bps, long global_index,
                            FlacOob *o) {
  static FlacFrame fr[FLAC_MAX_FRAMES];
  size_t nf = flac_scan_frames(buf, n, fr, FLAC_MAX_FRAMES, 1);
  long acc = 0;
  for (size_t k = 0; k < nf; k++) {
    FlacFrameHeader fh;
    if (!flac_hdr_parse_permissive(buf, n, fr[k].start, (unsigned)bps, &fh) || fh.bs < 1)
      return 0; /* cannot map the index to a frame: not proven */
    if (global_index < acc + (long)fh.bs) {
      long local = global_index - acc;
      if (flac_reconstruct_oob(buf, n, fr[k].start, nch, bps, o) && o->index <= local) {
        o->frame = k;
        return 1;
      }
      return 0;
    }
    acc += (long)fh.bs;
  }
  return 0;
}
