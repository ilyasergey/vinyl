/* fz_streaminfo_contradict -- the SUPPRESSED class made a target. The
 * differential oracles DISCARD frame-vs-STREAMINFO clashes (flac_hdr_consistent
 * skips them: libFLAC follows the frame, Vinyl follows STREAMINFO, so a diff is
 * not a defect). This target throws away the referee entirely and asks the only
 * interesting question: what does Vinyl PRODUCE on such a stream?
 *
 * It takes a valid base stream and rewrites STREAMINFO fields -- which carry NO
 * CRC, so no repair is needed and the frames stay byte-for-byte valid -- to
 * contradict the frames, then decodes with Vinyl only and checks the output
 * contract:
 *
 *   (c) sample-rate 0 with audio  (§9.1.7 MUST NOT): STREAMINFO sampleRate := 0.
 *       fz_self_consistent's bad_rate check (sr >= 2^20) MISSES sr==0, and no
 *       other target sees it -- this is the uniquely-uncaught sample-rate sub-case.
 *   (a) channel count: STREAMINFO channels := a different legal
 *       value; the decoded Audio's channel count should track it.
 *   (b) bit depth: STREAMINFO bps := a different legal value;
 *       the decoded bps LABEL vs the samples' actual depth.
 *
 * Referee-free. The CRC mutator manufactures these constantly, so like clause-3a
 * this CATALOGUES + counts by default and aborts only under FUZZ_STRICT>=ACCEPT
 * (regression-pinning a filed witness). Input kind: flac_stream. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../common/ffi_util.h"
#include "../common/flac_bits.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_api.h"
#include "../common/wide_diff.h"

/* STREAMINFO field bit offsets come from common/flac_bits.h (the single source):
 * FLAC_SI_SAMPLERATE_BIT / FLAC_SI_CHANNELS_BIT / FLAC_SI_BPS_BIT. */

static unsigned long g_execs, g_base_ok, g_sr0_audio, g_ch_incoherent, g_bps_incoherent;

static void report(FILE *o) {
  fprintf(o,
          "[si-contra] execs=%lu base_ok=%lu | sr0_with_audio=%lu (§9.1.7) "
          "channel_incoherent=%lu bps_incoherent=%lu\n",
          g_execs, g_base_ok, g_sr0_audio, g_ch_incoherent, g_bps_incoherent);
}

FUZZ_TARGET(.name = "fz_streaminfo_contradict",
            .summary = "deliberate STREAMINFO/frame contradictions; Vinyl output contract",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .report = report)

static uint8_t *g_buf;
static size_t g_cap;
static uint8_t *dup_base(const uint8_t *d, size_t n) {
  fuzz_grow(&g_buf, &g_cap, n ? n : 1);
  memcpy(g_buf, d, n);
  return g_buf;
}

/* Decode a candidate with Vinyl only; return 1 if it produced audio. */
static int vinyl_decode(const uint8_t *d, size_t n, Wide *w) {
  wide_reset(w, "vinyl");
  vinyl_wide_decode(d, n, w);
  return w->rc == DEC_OK && w->nsamples > 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  /* Require a base that starts with STREAMINFO (block type 0) of length 34, and
   * that Vinyl decodes to audio -- otherwise there is no coherent contract to
   * contradict. */
  if (size < 42 || memcmp(data, "fLaC", 4) != 0 || (data[4] & 0x7f) != 0)
    return 0;
  if (((data[5] << 16) | (data[6] << 8) | data[7]) != 34)
    return 0;

  static Wide base;
  if (!vinyl_decode(data, size, &base)) {
    fuzz_tick();
    return 0;
  }
  int base_ch = base.nch, base_bps = base.bps;
  g_base_ok++;

  static Wide w;

  /* (c) sample-rate 0 with audio (§9.1.7). */
  {
    uint8_t *b = dup_base(data, size);
    flac_put_bits(b, FLAC_SI_SAMPLERATE_BIT, 20, 0);
    if (vinyl_decode(b, size, &w)) {
      /* Vinyl accepted a stream whose STREAMINFO declares sample rate 0 and still
       * produced audio -- RFC 9.1.7 says the rate MUST NOT be 0 with audio. */
      g_sr0_audio++;
      oracle_dump_write("streaminfo_sr0_audio", b, size);
      if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
        fprintf(stderr,
                "\n[OUTPUT-CONTRACT VIOLATION] sample rate 0 accepted with audio (§9.1.7)\n"
                "  STREAMINFO sampleRate:=0 but Vinyl decoded %ld samples x %d ch at reported sr=%d\n",
                w.nsamples, w.nch, w.sr);
        FUZZ_ABORT();
      }
    }
  }

  /* (a) channel count contradiction: STREAMINFO channels := a different legal
   * value (1..8, != frame-derived). Vinyl's decoded channel count should equal
   * the STREAMINFO it parsed. */
  {
    uint8_t *b = dup_base(data, size);
    int newch = (base_ch % 8) + 1;
    if (newch == base_ch)
      newch = (newch % 8) + 1;
    flac_put_bits(b, FLAC_SI_CHANNELS_BIT, 3, (uint32_t)(newch - 1));
    if (vinyl_decode(b, size, &w) && w.nch != newch) {
      g_ch_incoherent++;
      oracle_dump_write("streaminfo_channel_incoherent", b, size);
      if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
        fprintf(stderr,
                "\n[OUTPUT-CONTRACT VIOLATION] decoded channel count != STREAMINFO\n"
                "  STREAMINFO channels:=%d but Vinyl returned %d channels\n",
                newch, w.nch);
        FUZZ_ABORT();
      }
    }
  }

  /* (b) bit depth contradiction: STREAMINFO bps := a SMALLER legal depth than the
   * frames carry. Whatever depth Vinyl then reports (w.bps), the output contract
   * is that the reported depth must BOUND the reconstructed samples. If a sample
   * escapes FitsSInt(w.bps), the label does not describe the data
   * (reconstructed at frame depth, labelled the STREAMINFO one). This is robust to
   * which field Vinyl uses for the label. */
  /* Rewrite STREAMINFO bps to a SMALLER legal depth than the base carries, so a
   * sample reconstructed at the frame depth cannot fit the reported label. The
   * old code added 1 (a LARGER depth) when base_bps <= 8, contradicting its own
   * comment and never firing (bug 13). Below 5 bits there is no smaller legal
   * depth, so skip. NOTE: a VINYL-emitted base carries frame bit-depth code 0
   * ("depth from STREAMINFO"), so rewriting STREAMINFO bps changes the
   * reconstruction depth coherently and this cannot fire on it; it fires on bases
   * whose FRAMES carry an explicit depth (libFLAC/ffmpeg output in the corpus). */
  if (base_bps > 4) {
    uint8_t *b = dup_base(data, size);
    int newbps = base_bps > 8 ? 8 : base_bps - 1; /* always < base_bps */
    flac_put_bits(b, FLAC_SI_BPS_BIT, 5, (uint32_t)(newbps - 1));
    if (vinyl_decode(b, size, &w) && w.bps >= 1 && w.bps <= 32) {
      long long hi = 1LL << (w.bps - 1), lo = -hi;
      int bad = 0;
      for (int c = 0; c < w.nch && !bad; c++)
        for (long i = 0; i < w.nsamples; i++)
          if (w.plane[c][i] < lo || w.plane[c][i] >= hi) {
            bad = 1;
            break;
          }
      if (bad) {
        g_bps_incoherent++;
        oracle_dump_write("streaminfo_bps_incoherent", b, size);
        if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
          fprintf(stderr,
                  "\n[OUTPUT-CONTRACT VIOLATION] reported bps does not bound samples\n"
                  "  STREAMINFO bps:=%d, Vinyl reports bps=%d but a sample escapes FitsSInt(%d)\n",
                  newbps, w.bps, w.bps);
          FUZZ_ABORT();
        }
      }
    }
  }

  fuzz_tick();
  return 0;
}
