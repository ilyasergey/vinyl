/* fz_self_consistent -- the decoder output-CONTRACT oracle. No referee,
 * no Lean shim, ANY bit depth. Every stream the PRODUCTION decoder accepts is
 * split against the two halves of Audio.WellFormed (Stream.lean:502):
 *
 *   ABORT (robust, garbage-INDEPENDENT decoder guarantees):
 *     - structurally-invalid output: channel count outside [1,8], bps outside
 *       [1,32], RAGGED planes (channels of unequal length), sampleRate >= 2^20,
 *       or numSamples >= 2^36. A decoder that accepts a stream must still
 *       produce rectangular, in-range-shaped output -- true even for corrupt
 *       input.
 *     - encoder contradiction: output is structurally valid AND every sample
 *       fits bps (so Audio.WellFormed holds) yet Flac.encode returns none. The
 *       encoder rejected audio the decoder produced and the theorem says is
 *       representable.
 *
 *   MEASURE (garbage-TOLERATED, Bits.lean:178 -- NOT a bug on corrupt input):
 *     - a decoded sample outside [-2^(bps-1), 2^(bps-1)) or arriving as a GMP
 *       bignum. Counted and DUMPED for offline triage: the §1.1 stereo-overflow
 *       construction lives here, but so does ordinary garbage-in, so it is not
 *       an abort until fed a valid (encoder-image) stream.
 *     - channel-count incoherence (clause 3a): the decoded Audio's channel count
 *       differs from the STREAMINFO the decoder just parsed -- recombine's zipWith
 *       truncation returning fewer channels than declared. A real
 *       output-contract finding, but the CRC mutator manufactures channel/bps
 *       contradictions constantly, so it is catalogued + counted (selfcon_
 *       channel_incoherent) and escalates to abort only under FUZZ_STRICT>=ACCEPT.
 *
 * A 16-bit corpus stream is structurally valid and re-encodes, so the clean
 * corpus never aborts. Input kind: flac_stream (CRC mutator). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_checks.h"

static unsigned long g_execs, g_decoded, g_unfit, g_bignum, g_channel_incoherent, g_mode_disagree;

static void report(FILE *o) {
  unsigned long capped = vinyl_encode_capped_count();
  double cap_pct = g_decoded ? 100.0 * (double)capped / (double)g_decoded : 0.0;
  fprintf(o,
          "[selfcon] execs=%lu decoded=%lu | measured: unfit=%lu bignum=%lu "
          "(garbage-in tolerated) | channel_incoherent=%lu (output-contract) | "
          "mode_disagree=%lu (reference/byte lane) | "
          "encode_capped=%lu (%.1f%% of decoded -- re-encode assertion suppressed, D7)\n",
          g_execs, g_decoded, g_unfit, g_bignum, g_channel_incoherent, g_mode_disagree, capped,
          cap_pct);
}

FUZZ_TARGET(.name = "fz_self_consistent",
            .summary = "decoder output contract: structural validity + re-encode (any depth)",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (fuzz_over_sample_cap(data, size)) /* 6E: skip declared-bomb inputs */
    return 0;
  SelfConsistency sc;
  vinyl_self_consistency(data, size, &sc);
  if (!sc.decoded)
    return 0;
  g_decoded++;

  /* Cross-decoder agreement (A1): the reference decoder (decodeOption_eq_reference)
   * and the byte decoder (decodeBytes_spec + pcmBytesA_eq, checked at any depth)
   * must accept exactly when production does and yield the same audio/bytes. A
   * disagreement is a compiler/runtime/csimp defect on the binary, catalogued by
   * default and escalated to abort under FUZZ_STRICT>=LEN for regression pinning. */
  if (sc.reference_disagreed || sc.byte_disagreed) {
    g_mode_disagree++;
    oracle_dump_write("selfcon_mode_disagree", data, size);
    if (fuzz_env_strict() >= FUZZ_STRICT_LEN) {
      fprintf(stderr,
              "\n[MODE DISAGREEMENT — THEOREM ON THE BINARY] production decoder disagrees with a\n"
              "  sibling decoder (input=%zuB): reference_disagreed=%d byte_disagreed=%d "
              "(ch=%d bps=%d sr=%d samples=%lu bad_ch=%d bad_idx=%d)\n"
              "  contradicts decodeOption_eq_reference / decodeBytes_spec + pcmBytesA_eq\n",
              size, sc.reference_disagreed, sc.byte_disagreed, sc.ch, sc.bps, sc.sr, sc.samples,
              sc.bad_ch, sc.bad_idx);
      FUZZ_ABORT();
    }
  }

  /* Clause 3a (output-contract): the decoder accepted a stream, parsed its
   * STREAMINFO, then returned an Audio with a different channel count than
   * STREAMINFO declared -- recombine's zipWith truncation returning fewer
   * channels than declared, silent data loss. This IS an output-contract
   * finding, but the CRC mutator MANUFACTURES channel/bps contradictions
   * constantly (header_field_op rewrites channel codes, then repairs the CRC), so
   * on this differential rig the pattern is common, not rare. Catalogue + count
   * by default (like the accept-set observations); abort only under
   * FUZZ_STRICT>=ACCEPT, for regression-pinning a specific witness once filed. */
  if (sc.channel_incoherent) {
    g_channel_incoherent++;
    oracle_dump_write("selfcon_channel_incoherent", data, size);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[OUTPUT-CONTRACT VIOLATION] decoded channel count disagrees with the stream\n"
              "  STREAMINFO channels=%d frame channels=%d but decoded Audio has ch=%d "
              "(bps=%d sr=%d samples=%lu)\n"
              "  a stream the decoder accepted returned fewer/more channels than it declared\n"
              "  (recombine truncation: success with silent channel data loss)\n",
              sc.si_ch, sc.frame_ch, sc.ch, sc.bps, sc.sr, sc.samples);
      FUZZ_ABORT();
    }
  }

  if (!sc.structural_ok) {
    fprintf(stderr,
            "\n[OUTPUT-CONTRACT VIOLATION] decoder produced structurally-invalid audio\n"
            "  ch=%d bps=%d sr=%d samples=%lu | bad_channels=%d bad_bps=%d ragged=%d "
            "bad_rate=%d bad_count=%d\n"
            "  a lossless decoder must emit rectangular, in-shape output even for corrupt input\n",
            sc.ch, sc.bps, sc.sr, sc.samples, sc.bad_channels, sc.bad_bps, sc.ragged, sc.bad_rate,
            sc.bad_count);
    oracle_dump_write("selfcon_structural", data, size);
    FUZZ_ABORT();
  }

  /* P1.2 budget assertion -- runtime-checks Flac.Stream.decode_size_le on the
   * shipped binary. The decoder's decompression-bomb bound guarantees
   * 2*Σ|channel| ≤ decodeBudget(input), with decodeBudget(bytes) = 4096*size +
   * 65536 (decodeAmpl=4096, decodeFloor=65536, Flac/Native/Stream.lean:471-479).
   * structural_ok held above, so the output is rectangular and Σ|channel| equals
   * ch*samples exactly. A violation means the binary decoded more output than the
   * budget the decoder is proven to enforce. NOTE: the two constants MIRROR the
   * Lean decodeAmpl/decodeFloor -- there is no stable vinyl_ decodeBudget export
   * to source them from (see rig report); keep in sync if the codec budget moves. */
  unsigned long long budget_total = (unsigned long long)sc.ch * (unsigned long long)sc.samples;
  unsigned long long decode_budget = 4096ULL * (unsigned long long)size + 65536ULL;
  if (2ULL * budget_total > decode_budget) {
    fprintf(stderr,
            "\n[BUDGET VIOLATION — decode_size_le ON THE BINARY] decoder output exceeds the\n"
            "  decompression-bomb budget (input=%zuB ch=%d samples=%lu): 2*%llu > "
            "decodeBudget=%llu\n"
            "  contradicts Flac.Stream.decode_size_le (2*Σ|channel| ≤ 4096*size + 65536)\n",
            size, sc.ch, sc.samples, budget_total, decode_budget);
    oracle_dump_write("selfcon_budget_violation", data, size);
    FUZZ_ABORT();
  }

  /* Garbage-tolerated observables: dump for triage, do NOT abort. */
  if (sc.saw_bignum) {
    g_bignum++;
    oracle_dump_write("selfcon_bignum", data, size);
  } else if (!sc.fit_ok) {
    g_unfit++;
    oracle_dump_write("selfcon_unfit", data, size);
  }

  /* Encoder contradiction: WellFormed holds (structural && fit) but encode said
   * none. This is the only fit-related ABORT, and it is robust. */
  if (sc.structural_ok && sc.fit_ok && sc.reencodes == 0) {
    fprintf(stderr,
            "\n[ENCODER CONTRADICTION] Flac.encode returned none on WellFormed decoded audio\n"
            "  ch=%d bps=%d sr=%d samples=%lu (structural_ok && fit_ok but encode==none)\n",
            sc.ch, sc.bps, sc.sr, sc.samples);
    oracle_dump_write("selfcon_encode_contradiction", data, size);
    FUZZ_ABORT();
  }
  fuzz_tick();
  return 0;
}
