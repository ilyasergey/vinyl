/* flac_residual.h (RFC 9639 §9.2.7.3) -- extract the RESIDUAL magnitudes a
 * mono single-frame FLAC subframe encodes, WITHOUT decoding the Rice bitstream.
 *
 * Trick that keeps this sound: for a lossless stream, sample x[i] = prediction +
 * residual EXACTLY, so residual[i] = x[i] - prediction(x). We therefore parse
 * only the fixed-size subframe HEADER (type/order/shift/coefficients) and
 * RECOMPUTE the residuals from the decoder's own reconstructed samples -- no
 * unary/Rice decoding, so no bit-miscount can invent a false residual. The RFC
 * bound (§9.2.7.3) is |r| < 2^31 AND r != -2^31 (a predicate trap: FitsSInt 32
 * INCLUDES -2^31, the RFC excludes it); Vinyl computes residuals in exact ℤ and
 * does not enforce it, reaching ~2^51 at bps 32 / order 32 / shift 0.
 *
 * Scope: mono, single frame, no wasted bits -- the corner the out-of-range witness lives
 * in and where residual = x[i] - prediction needs no cross-channel bit walking.
 * flac_struct.c stays verbatim; this is a NEW module beside it. */
#ifndef FLAC_RESIDUAL_H
#define FLAC_RESIDUAL_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
  int analyzed;   /* 1 = a mono LPC/FIXED subframe was parsed and checked */
  int is_lpc;     /* 1 LPC, 0 FIXED */
  int order;      /* predictor order */
  int precision;  /* LPC coefficient precision (bits), 0 for FIXED */
  int shift;      /* LPC quantization shift */
  int64_t max_abs_residual;
  int violation;       /* |r| >= 2^31 or r == -2^31 */
  int64_t bad_residual; /* the offending residual, if any */
} ResidualInfo;

/* Parse the single subframe of a mono frame at `frame_start` in buf/n, using the
 * decoder's reconstructed samples x[0..nx) to recompute residuals. `bps` is the
 * sample depth the decoder reported (Vinyl emits frame bit-depth code 0 =
 * "from STREAMINFO", so the depth cannot be read from the frame header -- the
 * caller supplies it). Returns 1 if a FIXED/LPC subframe was analyzed (fills *ri),
 * 0 if CONSTANT/VERBATIM, wasted bits, unparsable, or nx too small. */
int flac_residual_mono(const uint8_t *buf, size_t n, size_t frame_start, const int64_t *x, long nx,
                       int bps, ResidualInfo *ri);

#endif /* FLAC_RESIDUAL_H */
