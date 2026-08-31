/* fz_samples_diff -- the ANY-DEPTH THREE-WAY sample differential. The
 * rest of the decode rig compares s16le bytes and gates to 16-bit; this one
 * compares decoded int SAMPLES (Vinyl decodeArrays vs libFLAC AND ffmpeg native
 * planes) at every bit depth (4-32), closing the codec's 16-bit-only test blind
 * spot via referee triangulation.
 * Two independent references let the oracle separate "Vinyl is the outlier"
 * (a spec-reading bug -> abort) from "the two references disagree and Vinyl
 * picked a side" (referee laxness -> catalogue). Accept/reject rows require BOTH
 * references to agree against Vinyl before escalating (FUZZ_STRICT), and a Vinyl
 * bignum sample is catalogued not aborted (garbage-in).
 * Input kind: flac_stream (CRC mutator). Severity: V (a decode divergence). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h" /* oracle_dump_write */
#include "../common/vinyl_api.h"
#include "../common/wide_diff.h"

static unsigned long g_execs, g_all_ok, g_both_rej, g_vinyl_only, g_ref_only, g_skip, g_geom,
    g_ref_disagree, g_bignum, g_ffmpeg_ok, g_flac_ok, g_hdr_clash, g_out_of_contract, g_resource;

static void report(FILE *o) {
  double clash_pct = g_execs ? 100.0 * (double)g_hdr_clash / (double)g_execs : 0.0;
  fprintf(o,
          "[wide3] execs=%lu all_ok=%lu both_rej=%lu vinyl_only=%lu ref_only=%lu skip=%lu "
          "geom=%lu ref_disagree=%lu bignum=%lu out_of_contract=%lu resource=%lu | flac_ok=%lu "
          "ffmpeg_ok=%lu | hdr_clash=%lu (%.1f%% suppressed, F5)\n",
          g_execs, g_all_ok, g_both_rej, g_vinyl_only, g_ref_only, g_skip, g_geom, g_ref_disagree,
          g_bignum, g_out_of_contract, g_resource, g_flac_ok, g_ffmpeg_ok, g_hdr_clash, clash_pct);
}

FUZZ_TARGET(.name = "fz_samples_diff",
            .summary = "any-depth 3-way sample differential: Vinyl vs libFLAC vs ffmpeg planes",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .needs_flac = 1, .report = report)

/* Resource attribution is done OFFLINE now (Phase 5B), not in this hot loop. The
 * old in-band instrument read /proc/self/statm field 2 = CURRENT RSS, which is
 * monotone under Lean's retaining allocator, so a per-exec `rss1-rss0` delta was
 * dominated by unreturned earlier allocations -- it "fired once then never". The
 * honest per-input resource signal is `tools/measure_decode` (getrusage
 * ru_maxrss = PEAK, one input per process) swept over the grown corpus; the
 * out-of-band rss_limit_mb / cgroup / watchdog bound the live run. */

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  static Wide vin, flc, ffm;
  g_execs++;
  wide_reset(&vin, "vinyl");
  wide_reset(&flc, "libflac");
  wide_reset(&ffm, "ffmpeg");
  vinyl_wide_decode(data, size, &vin);
  flac_wide_decode(data, size, &flc);
  ffmpeg_wide_decode(data, size, &ffm);
  if (vin.overflow)
    g_bignum++;
  if (flc.rc == DEC_OK)
    g_flac_ok++;
  if (ffm.rc == DEC_OK)
    g_ffmpeg_ok++;
  switch (wide_diff_oracle(data, size, &vin, &flc, &ffm)) {
    case WD_BOTH_REJECT: g_both_rej++; break;
    case WD_ALL_OK: g_all_ok++; break;
    case WD_VINYL_ONLY: g_vinyl_only++; break;
    case WD_REF_ONLY: g_ref_only++; break;
    case WD_SKIP: g_skip++; break;
    case WD_GEOM: g_geom++; break;
    case WD_REF_DISAGREE: g_ref_disagree++; break;
    case WD_HDR_CLASH: g_hdr_clash++; break;
    case WD_OUT_OF_CONTRACT: g_out_of_contract++; break;
  }
  fuzz_tick();
  return 0;
}
