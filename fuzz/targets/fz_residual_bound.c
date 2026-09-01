/* fz_residual_bound (RFC 9639 §9.2.7.3) -- does Vinyl emit residuals outside
 * the RFC's signed-32-bit bound? Vinyl computes residuals in exact ℤ and never
 * checks |r| < 2^31 (and r != -2^31, the predicate trap FitsSInt 32 misses), so at
 * high depth / high LPC order the emitted residuals can reach ~2^51. decode_encode
 * still holds (Vinyl decodes in exact ℤ), so this is an EMIT-set conformance
 * finding, not a round-trip break -- invisible to any decoder-tolerance oracle.
 *
 * Method: G1 emits a stream at the fuzzer's depth; we analyze ALL channels of
 * frame 0 (any frame count, mono or stereo), recomputing residuals from Vinyl's
 * own reconstructed samples (flac_residual_frame -- no Rice decoding, so no false
 * residual). Every side channel (bps+1, the most §9.2.7.3-violation-prone spot) is
 * reached via flac_subframe_bit_offsets. The graded reachability: 16-bit is safe by
 * arithmetic (so a violation there would be a detector bug -> we assert 16-bit
 * NEVER violates), and the default chooser at depths 17-32 is the fuzzer's target.
 *
 * Catalogues + counts by default; aborts under FUZZ_STRICT>=ACCEPT. Input: RAW
 * (G1 parameters). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_bits.h"
#include "../common/flac_residual.h"
#include "../common/flac_struct.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_gen.h"
#include "../common/wide_diff.h"

static unsigned long g_execs, g_gen_ok, g_analyzed, g_lpc, g_fixed, g_side, g_violations, g_viol16;
static int64_t g_max_residual;

static void report(FILE *o) {
  fprintf(o,
          "[resid] execs=%lu gen_ok=%lu analyzed(frame0 all subframes)=%lu (lpc=%lu fixed=%lu "
          "side_ch=%lu) | bound_violations(|r|>=2^31)=%lu max|r|=%lld | 16bit_violations=%lu "
          "(MUST be 0)\n",
          g_execs, g_gen_ok, g_analyzed, g_lpc, g_fixed, g_side, g_violations,
          (long long)g_max_residual, g_viol16);
}

FUZZ_TARGET(.name = "fz_residual_bound",
            .summary = "emit-set: residual magnitude bound |r|<2^31 on Vinyl's output",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .needs_flac = 1, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  /* A3a: drive BOTH the reference writer and Emit.emitFast (byte-equal by
   * emitFast_eq_encode) and analyze the `fast` bytes, so this target actually
   * executes Emit.emitFast. The residual oracle is unchanged (the buffers are
   * byte-identical); the unchecked buffer is emitted only to exercise the pair. */
  uint8_t *unchecked, *flac;
  size_t ulen, flen;
  GenParams gp;
  if (!vinyl_gen_encode_pair(data, size, &unchecked, &ulen, &flac, &flen, &gp))
    return 0;
  (void)unchecked;
  (void)ulen;
  g_gen_ok++;

  /* Analyze frame 0 only: its samples are x[0..blocksize). Any frame count is
   * fine -- we clamp the sample window to frame 0's block size below. */
  static FlacFrame frames[4];
  size_t nf = flac_scan_frames(flac, flen, frames, 4, 1);
  if (nf < 1)
    return 0;

  static Wide w;
  wide_reset(&w, "vinyl");
  vinyl_wide_decode(flac, flen, &w);
  if (w.rc != DEC_OK || w.nch < 1 || w.nsamples < 2 || w.overflow)
    return 0;

  /* Frame 0's block size bounds the sample window (multi-frame streams carry more
   * samples than the first frame). Depth is decoder-reported (frame code 0). */
  FlacFrameHeader fh;
  if (!flac_hdr_parse_permissive(flac, flen, frames[0].start, (unsigned)w.bps, &fh))
    return 0;
  long nx = w.nsamples < (long)fh.bs ? w.nsamples : (long)fh.bs;

  ResidualInfo ri[FLAC_RESIDUAL_MAX_CH];
  int na = flac_residual_frame(flac, flen, frames[0].start, (const int64_t *const *)w.plane, w.nch,
                               nx, w.bps, ri);
  if (na <= 0)
    return 0;

  /* Accumulate per-channel stats, and record the first real bound violation.
   * The detector-bug self-check must fire per violating channel (it aborts on
   * the spot); the out-of-range / strict handling is a per-stream decision made
   * once after the scan. */
  int viol_idx = -1;
  for (int i = 0; i < na; i++) {
    const ResidualInfo *r = &ri[i];
    g_analyzed++;
    if (r->is_lpc)
      g_lpc++;
    else
      g_fixed++;
    if (r->sub_bps > w.bps) /* this channel was an expanded side channel */
      g_side++;
    if (r->max_abs_residual > g_max_residual)
      g_max_residual = r->max_abs_residual;

    if (!r->violation)
      continue;
    /* Soundness self-check: at 16-bit, residuals of a GENUINE in-range signal are
     * bounded by arithmetic and CANNOT exceed 2^31 -- a violation there (in ANY
     * channel, side included) means the extractor miscounted. This is gated on
     * gp.in_range: on out-of-range provenance (advkind 1/2/3) the codec's wrapSInt
     * fires in the stereo/subframe recurrence, so the recomputed side
     * (plane0-plane1) and residual (x[i]-pred) are FABRICATED and can exceed 2^31
     * even at bps<=16 -- that is not a detector bug, it is the out-of-range
     * catalogue case below, so it must NOT abort here. */
    if (gp.in_range && w.bps <= 16) {
      g_viol16++;
      fprintf(stderr,
              "\n[DETECTOR BUG] residual bound 'violation' at bps=%d, where it is arithmetically\n"
              "  impossible (sub_bps=%d ch=%d order=%d shift=%d wasted=%d bad_r=%lld) --\n"
              "  flac_residual_frame miscounted (bad plane derivation or bit walk)\n",
              w.bps, r->sub_bps, r->channel, r->order, r->shift, r->wasted,
              (long long)r->bad_residual);
      oracle_dump_write("resid_detector_bug", flac, flen);
      FUZZ_ABORT(); /* a false finding is worse than a missed one */
    }
    if (viol_idx < 0)
      viol_idx = i;
  }

  if (viol_idx >= 0) {
    const ResidualInfo *r = &ri[viol_idx];
    /* 8B: on OUT-OF-RANGE G1 provenance the recompute x[i]-pred assumes no wrap, so
     * the reconstructed samples being out of the bit-depth envelope can FABRICATE a
     * residual >2^31 that Vinyl never emitted. Catalogue that separately; only an
     * IN-RANGE input (the genuine hostile_fixed_bps32 case, advkind 0) is a real
     * emit-set finding. */
    if (!gp.in_range) {
      oracle_dump_write("resid_out_of_range_provenance", flac, flen);
      fuzz_tick();
      return 0;
    }
    g_violations++;
    oracle_dump_write("resid_bound_violation", flac, flen);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[EMIT-SET] residual escapes signed-32-bit bound (RFC 9639 §9.2.7.3)\n"
              "  bps=%d sub_bps=%d ch=%d %s order=%d shift=%d wasted=%d: |r|=%lld >= 2^31 (or\n"
              "  r=-2^31) -- Vinyl emits residuals in exact ℤ with no bound check; a strict RFC\n"
              "  decoder rejects this stream\n",
              w.bps, r->sub_bps, r->channel, r->is_lpc ? "LPC" : "FIXED", r->order, r->shift,
              r->wasted, (long long)(r->bad_residual < 0 ? -r->bad_residual : r->bad_residual));
      FUZZ_ABORT();
    }
  }
  fuzz_tick();
  return 0;
}
