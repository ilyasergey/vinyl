/* fz_residual_bound (RFC 9639 §9.2.7.3) -- does Vinyl emit residuals outside
 * the RFC's signed-32-bit bound? Vinyl computes residuals in exact ℤ and never
 * checks |r| < 2^31 (and r != -2^31, the predicate trap FitsSInt 32 misses), so at
 * high depth / high LPC order the emitted residuals can reach ~2^51. decode_encode
 * still holds (Vinyl decodes in exact ℤ), so this is an EMIT-set conformance
 * finding, not a round-trip break -- invisible to any decoder-tolerance oracle.
 *
 * Method: G1 emits a stream at the fuzzer's depth; we analyze only MONO
 * SINGLE-FRAME LPC/FIXED subframes, recomputing residuals from Vinyl's own
 * reconstructed samples (flac_residual_mono -- no Rice decoding, so no false
 * residual). The graded reachability: 16-bit is safe by
 * arithmetic (so a violation there would be a detector bug -> we assert 16-bit
 * NEVER violates), and the default chooser at depths 17-32 is the fuzzer's target.
 *
 * Catalogues + counts by default; aborts under FUZZ_STRICT>=ACCEPT. Input: RAW
 * (G1 parameters). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_residual.h"
#include "../common/flac_struct.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_gen.h"
#include "../common/wide_diff.h"

static unsigned long g_execs, g_gen_ok, g_analyzed, g_lpc, g_fixed, g_violations, g_viol16;
static int64_t g_max_residual;

static void report(FILE *o) {
  fprintf(o,
          "[resid] execs=%lu gen_ok=%lu analyzed(mono 1-frame)=%lu (lpc=%lu fixed=%lu) | "
          "bound_violations(|r|>=2^31)=%lu max|r|=%lld | 16bit_violations=%lu (MUST be 0)\n",
          g_execs, g_gen_ok, g_analyzed, g_lpc, g_fixed, g_violations, (long long)g_max_residual,
          g_viol16);
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

  /* single frame only, so decoded samples map 1:1 to the frame. */
  static FlacFrame frames[4];
  size_t nf = flac_scan_frames(flac, flen, frames, 4, 1);
  if (nf != 1)
    return 0;

  static Wide w;
  wide_reset(&w, "vinyl");
  vinyl_wide_decode(flac, flen, &w);
  if (w.rc != DEC_OK || w.nch != 1 || w.nsamples < 2 || w.overflow)
    return 0;

  ResidualInfo ri;
  if (!flac_residual_mono(flac, flen, frames[0].start, w.plane[0], w.nsamples, w.bps, &ri))
    return 0;
  g_analyzed++;
  if (ri.is_lpc)
    g_lpc++;
  else
    g_fixed++;
  if (ri.max_abs_residual > g_max_residual)
    g_max_residual = ri.max_abs_residual;

  if (ri.violation) {
    /* Soundness self-check: at 16-bit, residuals are bounded by arithmetic and
     * CANNOT exceed 2^31 -- a violation there means the extractor miscounted, so
     * surface it separately and loudly (it invalidates the search). This holds
     * regardless of provenance, so it is checked BEFORE the in-range gate. */
    if (w.bps <= 16) {
      g_viol16++;
      fprintf(stderr,
              "\n[DETECTOR BUG] residual bound 'violation' at bps=%d, where it is arithmetically\n"
              "  impossible (order=%d shift=%d bad_r=%lld) -- flac_residual_mono miscounted\n",
              w.bps, ri.order, ri.shift, (long long)ri.bad_residual);
      oracle_dump_write("resid_detector_bug", flac, flen);
      FUZZ_ABORT(); /* a false finding is worse than a missed one */
    }
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
              "  bps=%d %s order=%d shift=%d: |r|=%lld >= 2^31 (or r=-2^31) -- Vinyl emits residuals\n"
              "  in exact ℤ with no bound check; a strict RFC decoder rejects this stream\n",
              w.bps, ri.is_lpc ? "LPC" : "FIXED", ri.order, ri.shift,
              (long long)(ri.bad_residual < 0 ? -ri.bad_residual : ri.bad_residual));
      FUZZ_ABORT();
    }
  }
  fuzz_tick();
  return 0;
}
