/* fz_gen_roundtrip (G1 driver) -- the any-depth encode->decode round-trip on
 * Vinyl's OWN proven writer. vinyl_gen (Stream.Unchecked.encode) emits
 * correct-by-construction FLAC at arbitrary bit depth (1-32), channel count
 * (1-8) and sample content; this decodes it three ways (Vinyl decodeArrays vs
 * libFLAC vs ffmpeg) and runs the 3-way oracle. It is the force-multiplier the
 * encode side lacked: every OTHER encode path is 16-bit-only, so the depths this
 * reaches (17-32, LPC/stereo/wasted selected by the default chooser on real
 * content) were untestable.
 *
 * Two things it catches, via the SHARED oracle (no new abort logic):
 *   - a Vinyl decode that contradicts a libFLAC+ffmpeg consensus on Vinyl's own
 *     emitted bytes -> abort (encoder/decoder/compiler defect);
 *   - the output-contract witness: the ADVERSARIAL population crafts a
 *     stereo stream whose left/side reconstruction escapes FitsSInt bps; if the
 *     default chooser picks the decorrelating mode, wide_diff's clause fires
 *     (wide_output_contract). If it never fires across a long run, that itself is
 *     the P9 signal (the default chooser avoids the mode; force it with a custom
 *     chooser).
 *
 * Input kind: RAW (the bytes are generator PARAMETERS -- bps/ch/sr/blockSize/
 * population/samples -- not a FLAC stream; the plain mutator explores that
 * parameter space). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_gen.h"
#include "../common/wide_diff.h"

static unsigned long g_execs, g_gen_ok, g_valid, g_adv, g_all_ok, g_vinyl_only, g_ref_only, g_geom,
    g_ref_disagree, g_skip, g_both_rej, g_hdr_clash, g_contract_candidates, g_out_of_contract,
    g_self_decode_fail, g_md5_checked, g_md5_mismatch, g_ground_checked, g_ground_mismatch;

static void report(FILE *o) {
  fprintf(o,
          "[gen-rt] execs=%lu gen_ok=%lu (valid=%lu adversarial=%lu) | all_ok=%lu vinyl_only=%lu "
          "ref_only=%lu geom=%lu ref_disagree=%lu skip=%lu both_rej=%lu hdr_clash=%lu | "
          "outofrange_candidates=%lu out_of_contract=%lu self_decode_fail=%lu | md5_checked=%lu "
          "md5_mismatch=%lu | ground_checked=%lu ground_mismatch=%lu\n",
          g_execs, g_gen_ok, g_valid, g_adv, g_all_ok, g_vinyl_only, g_ref_only, g_geom,
          g_ref_disagree, g_skip, g_both_rej, g_hdr_clash, g_contract_candidates, g_out_of_contract,
          g_self_decode_fail, g_md5_checked, g_md5_mismatch, g_ground_checked, g_ground_mismatch);
}

FUZZ_TARGET(.name = "fz_gen_roundtrip",
            .summary = "any-depth round-trip on Vinyl's own writer (G1): Unchecked.encode -> 3-way "
                       "decode oracle",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .needs_flac = 1, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  uint8_t *flac;
  size_t flen;
  GenParams gp;
  if (!vinyl_gen_encode(data, size, &flac, &flen, &gp))
    return 0;
  g_gen_ok++;
  if (gp.adversarial)
    g_adv++;
  else
    g_valid++;
  if (gp.expect_contract)
    g_contract_candidates++;

  static Wide vin, flc, ffm;
  wide_reset(&vin, "vinyl");
  wide_reset(&flc, "libflac");
  wide_reset(&ffm, "ffmpeg");
  vinyl_wide_decode(flac, flen, &vin);
  flac_wide_decode(flac, flen, &flc);
  ffmpeg_wide_decode(flac, flen, &ffm);

  /* Unchecked.encode self-decode boundary. G1 drives Stream.Unchecked.encode,
   * NOT the checked public encoder, so the hypothesis-free round-trip capstone
   * does NOT cover this output: the round-trip of the UNCHECKED encoder is not an
   * established theorem (it may be false for out-of-envelope configs). A
   * self-decode failure here is therefore a CANDIDATE finding -- Vinyl's own
   * writer emitted a stream its decoder rejects -- to catalogue for review, NOT a
   * proven theorem violation to abort on unconditionally. We restrict to the
   * IN-RANGE population (gp.in_range: non-adversarial, or the in-envelope
   * adversarial advkind 0 whose alternating +/- half-scale samples still fit
   * FitsSInt bps) AND assert it is inside the checked encoder's domain (bps 4-32,
   * ch 1-8, sr>0, blockSize <= 4608, in-range audio -- vinyl_gen guarantees all of
   * these), so the finding is sound: on that domain the checked encoder round-trips
   * by decode_encode, and Unchecked diverging from it is exactly the §2.5 class.
   * Abort only under a validated must-agree run (FUZZ_STRICT).
   *
   * The lower bound tracks `Audio.WellFormed`, which is RFC 9639 Table 3's 4-32.
   * It read `>= 1` while WellFormed did; a bps<4 audio has no conforming encoding,
   * so the unchecked writer emits a stream the decoder is right to reject and
   * `decode_encode` says nothing about it -- counting that as a self-decode
   * failure is an oracle error, not a codec one. */
  const int in_checked_domain =
      gp.bps >= 4 && gp.bps <= 32 && gp.ch >= 1 && gp.ch <= 8 && gp.sr > 0 && gp.bs <= 4608;
  if (gp.in_range && in_checked_domain && vin.rc != DEC_OK) {
    g_self_decode_fail++;
    oracle_dump_write("gen_self_decode_fail", flac, flen);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[UNCHECKED SELF-DECODE — §2.5 candidate] Vinyl's Unchecked.encode emitted a stream\n"
              "  Vinyl will not decode, on in-domain valid audio bps=%d ch=%d bs=%zu nsamples=%zu\n"
              "  -> %zuB FLAC, decodeArrays=none (the checked encoder round-trips on this domain)\n",
              gp.bps, gp.ch, gp.bs, gp.nsamples, flen);
      FUZZ_ABORT();
    }
  }

  /* Ground truth (no referee): on the IN-RANGE in-domain population (gp.in_range:
   * non-adversarial, or the in-envelope adversarial advkind 0),
   * decode(Unchecked.encode A) = A is theorem-backed (round-trip over the
   * encoder's image), so Vinyl's decoded samples must equal the ones G1
   * generated. This catches a common-mode encoder error all three decoders would
   * agree on (invisible to the 3-way oracle) AND doubles as the FFI-layout
   * selftest -- a wrong Audio/EncoderCfg ctor layout shows here as a systematic
   * mismatch. Catalogue; abort under strict. */
  if (gp.in_range && in_checked_domain && vin.rc == DEC_OK && !vin.overflow &&
      vin.nch == gp.ch && vin.nsamples == (long)gp.nsamples) {
    g_ground_checked++;
    int bad_c = -1;
    long bad_i = -1;
    for (int c = 0; c < gp.ch && bad_c < 0; c++) {
      const int64_t *exp = vinyl_gen_expected(c);
      if (!exp)
        continue;
      for (long i = 0; i < vin.nsamples; i++)
        if (vin.plane[c][i] != exp[i]) {
          bad_c = c;
          bad_i = i;
          break;
        }
    }
    if (bad_c >= 0) {
      g_ground_mismatch++;
      oracle_dump_write("gen_ground_truth", flac, flen);
      if (fuzz_env_strict() >= FUZZ_STRICT_LEN) {
        fprintf(stderr,
                "\n[GROUND TRUTH — round-trip on the binary] Vinyl decoded G1's own valid stream to\n"
                "  DIFFERENT samples than were encoded: ch %d idx %ld vinyl=%lld expected=%lld\n"
                "  (bps=%d ch=%d nsamples=%zu) -- decode(Unchecked.encode A) != A on the encoder's image\n",
                bad_c, bad_i, (long long)vin.plane[bad_c][bad_i],
                (long long)vinyl_gen_expected(bad_c)[bad_i], gp.bps, gp.ch, gp.nsamples);
        FUZZ_ABORT();
      }
    }
  }

  /* MD5 convention check: decode G1's own output with libFLAC MD5 checking on.
   * Vinyl writes a STREAMINFO MD5 (RFC 9639 §9.2.2); its convention has never been
   * validated above 16-bit. ONLY on the IN-RANGE population (gp.in_range):
   * out-of-range adversarial audio (advkind 1-3) is out of FitsSInt(bps), so
   * Vinyl's MD5 (over the original samples) and libFLAC's (over the wrapped-decoded
   * samples) legitimately differ -- that is not an MD5-convention bug. On in-range
   * audio (including the in-envelope adversarial advkind 0) a mismatch IS a sound
   * finding. Catalogue; abort under strict. */
  int md5 = (gp.in_range && in_checked_domain) ? flac_md5_verify(flac, flen) : MD5_UNCHECKED;
  if (md5 != MD5_UNCHECKED)
    g_md5_checked++;
  if (md5 == MD5_MISMATCH) {
    g_md5_mismatch++;
    oracle_dump_write("gen_md5_mismatch", flac, flen);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[MD5 CONVENTION] Vinyl's STREAMINFO MD5 does not match libFLAC's MD5 of the\n"
              "  decoded audio -- bps=%d ch=%d nsamples=%zu (RFC 9639 §9.2.2; unvalidated >16-bit)\n",
              gp.bps, gp.ch, gp.nsamples);
      FUZZ_ABORT();
    }
  }

  switch (wide_diff_oracle(flac, flen, &vin, &flc, &ffm)) {
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
