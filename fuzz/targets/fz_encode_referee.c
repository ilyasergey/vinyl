/* fz_encode_referee -- the ffmpeg (+ libFLAC) EMIT-SIDE referee on Vinyl's
 * PRODUCTION encoders. fz_roundtrip validates encodePcm16Fast / encodePcm16Cfg only
 * through VINYL's own decoders (self round-trip); fz_gen_roundtrip runs the 3-way
 * decode consensus but on Stream.Unchecked.encode (the generator writer). Nothing
 * ran the two SHIPPED public encoders' emitted bytes through an INDEPENDENT referee.
 * This does: encode real PCM with Vinyl (fast, then checked), then decode those bytes
 * three ways -- Vinyl, libFLAC (every exec), ffmpeg (the lazy 1-in-N census gate, which
 * also forces ffmpeg whenever Vinyl and libFLAC already disagree) -- and run the
 * established wide_diff oracle. Because the input is Vinyl's OWN valid encoder output,
 * all three MUST decode to the same samples; a libFLAC/ffmpeg contradiction (or a
 * Vinyl-only accept) is an ENCODER conformance bug, caught by the same triangulation the
 * decode side uses. (ffmpeg's per-call codec open/teardown is heavy, so forcing it on
 * every exec starves throughput; the lazy gate keeps libFLAC refereeing every stream and
 * samples ffmpeg, which is the same discipline the decode-side targets use.)
 *
 * Why not a byte-level comparison to ffmpeg's ENCODER (as one might first read the
 * task): it is infeasible. Two FLAC encoders make independent LPC-order / Rice-param /
 * partition-order / apodization choices, and Vinyl's cost model uses a Float.log2 that
 * is not correctly-rounded, so the emitted BYTES legitimately differ across encoders
 * and platforms. There is no host-portable byte oracle. The DECODE consensus on the
 * emitted stream is the sound, tolerance-free oracle: both references and Vinyl must
 * agree on the PCM a valid FLAC stream decodes to, whatever bytes produced it.
 *
 * Escalation. A genuine libFLAC/ffmpeg SAMPLE contradiction on Vinyl's own output aborts
 * unconditionally inside wide_diff_oracle (a valid FLAC stream must decode identically).
 * The softer "Vinyl accepts its own emitted stream, both references reject" class
 * (`vinyl_only`) is catalogue-only unless FUZZ_STRICT >= FUZZ_STRICT_ACCEPT, so in the
 * catalogue-by-default campaigns watch the `vinyl_only` counter, not just for an abort.
 *
 * Input kind: RAW, unpacked by common/pack.h (bs <= 4608, the checked-encode domain),
 * sharing the encode/gen + encode/shapes corpora with fz_roundtrip / fz_encode_diff.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/pack.h"
#include "../common/vinyl_api.h"   /* DEC_* */
#include "../common/vinyl_modes.h" /* vm_encode_fast, vm_encode_slow */
#include "../common/wide_diff.h"

static unsigned long g_execs, g_fast_ok, g_slow_ok, g_refereed;
static unsigned long g_all_ok, g_ref_disagree, g_vinyl_only, g_ref_only, g_geom, g_out_of_contract,
    g_skip, g_other;

static void report(FILE *o) {
  fprintf(o,
          "[enc_referee] execs=%lu fast_ok=%lu slow_ok=%lu refereed=%lu | all_agree=%lu "
          "ref_disagree=%lu vinyl_only=%lu ref_only=%lu geom=%lu out_of_contract=%lu skip=%lu "
          "other=%lu\n",
          g_execs, g_fast_ok, g_slow_ok, g_refereed, g_all_ok, g_ref_disagree, g_vinyl_only,
          g_ref_only, g_geom, g_out_of_contract, g_skip, g_other);
}

FUZZ_TARGET(.name = "fz_encode_referee",
            .summary = "ffmpeg+libFLAC emit-side referee: Vinyl's production-encoder bytes, 3-way decode consensus",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .report = report)

/* Decode Vinyl's emitted `flac` three ways and run the wide oracle. On valid encoder
 * output all three agree; a genuine libFLAC/ffmpeg sample contradiction aborts inside
 * wide_diff_oracle (its established policy). ffmpeg goes through the lazy gate: libFLAC
 * referees every stream, ffmpeg samples (and is forced when Vinyl and libFLAC disagree). */
static void run_referee(const uint8_t *flac, size_t flen) {
  static Wide vin, flc, ffm;
  wide_reset(&vin, "vinyl");
  wide_reset(&flc, "libflac");
  wide_reset(&ffm, "ffmpeg");
  vinyl_wide_decode(flac, flen, &vin);
  flac_wide_decode(flac, flen, &flc);
  ffmpeg_wide_decode(flac, flen, &ffm);
  g_refereed++;
  /* Pass the EMITTED stream (not the packed-PCM fuzzer input) as the oracle's data:
   * wide_diff_oracle -> flac_hdr_consistent scans it for a STREAMINFO/frame clash, and
   * the divergence dump should hold the FLAC bytes that diverged. Feeding the raw PCM
   * input here would let a mutant PCM prefix that happens to spell "fLaC" trip a
   * spurious WD_HDR_CLASH and silently discard a real referee verdict. */
  switch (wide_diff_oracle(flac, flen, &vin, &flc, &ffm)) {
  case WD_ALL_OK: g_all_ok++; break;
  case WD_REF_DISAGREE: g_ref_disagree++; break;
  case WD_VINYL_ONLY: g_vinyl_only++; break;
  case WD_REF_ONLY: g_ref_only++; break;
  case WD_GEOM: g_geom++; break;
  case WD_OUT_OF_CONTRACT: g_out_of_contract++; break;
  case WD_SKIP: case WD_BOTH_REJECT: case WD_HDR_CLASH: g_skip++; break;
  default: g_other++; break;
  }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  PackedInput pk;
  if (!pack_decode(data, size, &pk) || pk.pcm_len < 2u * (size_t)pk.ch)
    return 0; /* need at least one whole frame of PCM */

  /* vm_encode_fast/slow return a pointer into their own reused internal buffer (a
   * vm_buf grown by fuzz_grow), NOT a caller-owned allocation -- so it must NOT be
   * freed (fz_roundtrip uses the same convention). Each function owns a distinct
   * buffer, so the fast result stays valid across the checked call below. */
  uint8_t *flac;
  size_t flen;
  /* Fast production encoder (Flac.encodePcm16Fast, the CLI `--encode`). */
  if (vm_encode_fast(pk.pcm, pk.pcm_len, pk.bs, (size_t)pk.ch, pk.sr, &flac, &flen)) {
    g_fast_ok++;
    run_referee(flac, flen);
  }
  /* Checked encoder (Flac.encodePcm16Cfg). Same PCM, independent chooser -- its bytes
   * differ from the fast encoder's, but its decode consensus must hold identically. */
  if (vm_encode_slow(pk.pcm, pk.pcm_len, pk.bs, (size_t)pk.ch, pk.sr, &flac, &flen)) {
    g_slow_ok++;
    run_referee(flac, flen);
  }

  fuzz_tick();
  return 0;
}
