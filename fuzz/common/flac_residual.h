/* flac_residual.h (RFC 9639 §9.2.7.3) -- extract the RESIDUAL magnitudes a FLAC
 * subframe encodes, WITHOUT decoding the Rice bitstream.
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
 * Scope: ALL channels/subframes of frame 0. Handles wasted bits (residual is on
 * x>>w) and every stereo decorrelation, re-deriving each subframe's own sample
 * domain from the decoder's output planes -- so both side channels (bps+1, the
 * most §9.2.7.3-violation-prone spot) are checked. Subframe c>=1 begins at a bit
 * offset that depends on the full Rice length of the earlier subframes; that
 * extent is located with flac_subframe_bit_offsets (a walker ADDED to
 * flac_struct.c reusing its frozen subframe_bits grammar), so no Rice length is
 * re-implemented here. flac_struct.c's mutator/generator output stays verbatim;
 * this is a NEW module beside it. */
#ifndef FLAC_RESIDUAL_H
#define FLAC_RESIDUAL_H

#include <stddef.h>
#include <stdint.h>

/* Max channels analyzed in one frame (matches the decoder's WIDE_MAX_CH). */
#define FLAC_RESIDUAL_MAX_CH 8

typedef struct {
  int analyzed;   /* 1 = an LPC/FIXED subframe was parsed and checked */
  int is_lpc;     /* 1 LPC, 0 FIXED */
  int order;      /* predictor order */
  int precision;  /* LPC coefficient precision (bits), 0 for FIXED */
  int shift;      /* LPC quantization shift */
  int channel;    /* subframe/channel index this record describes (0..nch-1) */
  int sub_bps;    /* effective subframe depth: base bps + 1 on the expanded side */
  int wasted;     /* wasted bits w applied (residual computed on x >> w) */
  int64_t max_abs_residual;
  int violation;        /* |r| >= 2^31 or r == -2^31 */
  int64_t bad_residual; /* the offending residual, if any */
} ResidualInfo;

/* Analyze EVERY channel of the frame at `frame_start` in buf/n, using the
 * decoder's reconstructed OUTPUT channels to recompute residuals. `planes` holds
 * the `nch` decoded channel planes (planes[c] for channel c; planes[0]/planes[1]
 * are left/right for a stereo-decorrelated frame). `nx` is frame 0's sample count
 * and `bps` the base sample depth the decoder reported (the caller supplies it;
 * the depth cannot always be read from the frame header). The channel-assignment
 * code selects how each subframe's own sample domain is derived from the output
 * planes: independent -> plane[c]; left/side -> ch0=plane0, ch1=side(plane0-
 * plane1, bps+1); right/side -> ch0=side (bps+1), ch1=plane1; mid/side ->
 * ch0=mid((plane0+plane1)>>1), ch1=side (bps+1). `out` must hold `nch` entries;
 * the analyzed subframes are written compactly into out[0..return), each carrying
 * its actual channel index in `.channel`. Returns the number of LPC/FIXED
 * subframes analyzed (0 if all CONSTANT/VERBATIM, the walk failed, the channel
 * assignment is reserved, or the inputs are out of range). */
int flac_residual_frame(const uint8_t *buf, size_t n, size_t frame_start,
                        const int64_t *const *planes, int nch, long nx, int bps,
                        ResidualInfo *out);

#endif /* FLAC_RESIDUAL_H */
