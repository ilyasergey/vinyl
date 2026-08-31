/* fz_roundtrip — encode-side capstones tested on the compiled binary. Input
 * packing: common/pack.h (blockSize <= 4608, the checked-encode domain).
 *
 *  1. vinyl_encode_fast(pcm) -> flac; decode_fast, decode_pcm16 and decode_ref
 *     of that flac must EACH return exactly the original PCM -> abort() on
 *     failure. Only the decode_pcm16 lane is the bare capstone
 *     `decodePcm16_encodePcm16Fast`; decode_fast and decode_ref are that capstone
 *     COMPOSED with the decode-mode-equivalence lemmas (see demand_roundtrip),
 *     so each lane's abort cites its own composition rather than the capstone
 *     alone -- the capstone never mentions decodeBytes or decodeReference.
 *  2. vinyl_encode_slow(pcm) likewise, rooted at `decodePcm16_encodePcm16Cfg`.
 *  3. fast vs slow BYTE IDENTITY: NOT a theorem (different choosers), an
 *     ARCHITECTURE claim -> counted + printed, no abort.
 *  4. accept/reject agreement for the same parameters (counted; audio_wellFormed
 *     backs the fast-accept => slow-accept direction). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/pack.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_modes.h"

#define VM_REF_MAX_FLAC 8192

static unsigned long g_execs, g_enc_ok, g_enc_rej, g_rt_checked, g_ref_skipped;
static unsigned long g_fastslow_mismatch, g_accept_mismatch;

static void report(FILE *o) {
  fprintf(o,
          "[rt] execs=%lu enc_ok=%lu enc_rej=%lu rt_pairs=%lu fastslow_mm=%lu accept_mm=%lu "
          "ref_skipped=%lu\n",
          g_execs, g_enc_ok, g_enc_rej, g_rt_checked, g_fastslow_mismatch, g_accept_mismatch,
          g_ref_skipped);
}

FUZZ_TARGET(.name = "fz_roundtrip",
            .summary = "encode->decode round-trip capstones on the binary (fast + slow)",
            .input_kind = FUZZ_INPUT_PACKED_PCM, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 1, .report = report)

static void dump_params(size_t bs, size_t ch, size_t sr, size_t pcm_len) {
  fprintf(stderr, "  params: blockSize=%zu ch=%zu sampleRate=%zu pcm_len=%zu\n", bs, ch, sr,
          pcm_len);
}

/* `theorems` names the exact composition backing THIS (encoder, decoder) lane.
 * Only the decode_pcm16 lane is a single named capstone
 * (decodePcm16_encodePcm16Fast / …Cfg: `encode… = some flac → decodePcm16 flac =
 * ok bytes`). The decode_fast and decode_ref lanes are that capstone COMPOSED
 * with the decode-mode-equivalence lemmas -- decodePcm16 → decodeBytes bytes via
 * decodeBytes_spec + decodePcm16A_eq + pcm16FastA_eq_range, and decodePcm16 →
 * decodeReference∘pcmBytes via decodeOption_eq_reference + pcmBytesA_eq. Naming
 * `decodePcm16_encodePcm16Fast` alone for the ref lane (as this rig once did)
 * over-claims: that theorem never mentions decodeReference. */
static void demand_roundtrip(const char *enc, const char *mode, const char *theorems,
                             int (*dec)(const uint8_t *, size_t, uint8_t **, size_t *, int *, int *,
                                        int *),
                             const uint8_t *flac, size_t flen, const uint8_t *pcm, size_t plen,
                             size_t bs, size_t ch, size_t sr) {
  uint8_t *dp;
  size_t dl;
  int db, dc, ds;
  int rc = dec(flac, flen, &dp, &dl, &db, &dc, &ds);
  const char *what = NULL;
  size_t off = 0;
  if (rc != DEC_OK)
    what = "decoder did not accept the encoder's output";
  else if (dl != plen)
    what = "decoded PCM length differs from input";
  else if (memcmp(dp, pcm, plen) != 0)
    what = "decoded PCM bytes differ from input";
  else if (db != 16 || dc != (int)ch || ds != (int)sr)
    what = "decoded (bps,ch,sr) differs from encode parameters";
  if (!what)
    return;
  if (rc == DEC_OK) {
    size_t m = dl < plen ? dl : plen;
    while (off < m && dp[off] == pcm[off])
      off++;
  }
  fprintf(stderr,
          "\n[ROUND-TRIP FAILURE — THEOREM VIOLATION ON THE BINARY] %s via %s: %s\n"
          "  flac=%zuB  pcm_in=%zuB  pcm_out=%zuB  first_diff_off=%zu\n"
          "  decoded: rc=%d bps=%d ch=%d sr=%d\n",
          enc, mode, what, flen, plen, rc == DEC_OK ? dl : 0, off, rc, db, dc, ds);
  dump_params(bs, ch, sr, plen);
  if (rc == DEC_OK && off < plen && off < dl)
    fprintf(stderr, "  in[%zu]=%02x out[%zu]=%02x\n", off, pcm[off], off, dp[off]);
  fprintf(stderr, "  contradicts %s\n", theorems);
  abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  PackedInput in;
  if (!pack_decode(data, size, &in))
    return 0;
  g_execs++;
  size_t ch = (size_t)in.ch, bs = in.bs, sr = in.sr;
  const uint8_t *pcm = in.pcm;
  size_t plen = in.pcm_len;

  uint8_t *ffast, *fslow;
  size_t lfast, lslow;
  int okf = vm_encode_fast(pcm, plen, bs, ch, sr, &ffast, &lfast);
  int oks = vm_encode_slow(pcm, plen, bs, ch, sr, &fslow, &lslow);

  if (okf != oks) {
    /* pack.h's domain is bs in [16,4608], sr in the table (<2^20), whole-frame
     * PCM -- exactly where encodePcm16Fast's extra preconditions (sr<2^20,
     * size/(2ch)<2^36, 16<=bs<=4608) all hold, so its accept set coincides with
     * encodePcm16Cfg's (Pcm16ShapeOk alone, Codec.lean). A disagreement here is
     * therefore a real claim violation, not a domain artifact. */
    g_accept_mismatch++;
    fprintf(stderr,
            "\n[CLAIM VIOLATION] encoder accept/reject disagrees within the shared checked domain: "
            "fast=%s slow=%s\n",
            okf ? "accept" : "reject", oks ? "accept" : "reject");
    dump_params(bs, ch, sr, plen);
    abort();
  }

  if (okf) {
    demand_roundtrip("encode_fast", "decode_fast",
                     "decodePcm16_encodePcm16Fast + decodeBytes_spec + decodePcm16A_eq + "
                     "pcm16FastA_eq_range (16-bit)",
                     vinyl_decode_fast, ffast, lfast, pcm, plen, bs, ch, sr);
    demand_roundtrip("encode_fast", "decode_pcm16", "decodePcm16_encodePcm16Fast", vm_decode_pcm16,
                     ffast, lfast, pcm, plen, bs, ch, sr);
    if (lfast <= VM_REF_MAX_FLAC)
      demand_roundtrip("encode_fast", "decode_ref",
                       "decodePcm16_encodePcm16Fast + decodeOption_eq_reference + pcmBytesA_eq "
                       "(16-bit)",
                       vm_decode_ref, ffast, lfast, pcm, plen, bs, ch, sr);
    else
      g_ref_skipped++;
  }
  if (oks) {
    demand_roundtrip("encode_slow", "decode_fast",
                     "decodePcm16_encodePcm16Cfg + decodeBytes_spec + decodePcm16A_eq + "
                     "pcm16FastA_eq_range (16-bit)",
                     vinyl_decode_fast, fslow, lslow, pcm, plen, bs, ch, sr);
    demand_roundtrip("encode_slow", "decode_pcm16", "decodePcm16_encodePcm16Cfg", vm_decode_pcm16,
                     fslow, lslow, pcm, plen, bs, ch, sr);
    if (lslow <= VM_REF_MAX_FLAC)
      demand_roundtrip("encode_slow", "decode_ref",
                       "decodePcm16_encodePcm16Cfg + decodeOption_eq_reference + pcmBytesA_eq "
                       "(16-bit)",
                       vm_decode_ref, fslow, lslow, pcm, plen, bs, ch, sr);
    else
      g_ref_skipped++;
  }

  if (okf && oks) {
    g_rt_checked++;
    if (lfast != lslow || memcmp(ffast, fslow, lfast) != 0) {
      g_fastslow_mismatch++;
      size_t m = lfast < lslow ? lfast : lslow, off = 0;
      while (off < m && ffast[off] == fslow[off])
        off++;
      fprintf(stderr,
              "\n[CLAIM VIOLATION] encode_fast vs encode_slow bytes differ (NOT a theorem —\n"
              "  fastChooser vs defaultAsgChooser; ARCHITECTURE.md documents identity)\n"
              "  fast=%zuB slow=%zuB first_diff_off=%zu\n",
              lfast, lslow, off);
      dump_params(bs, ch, sr, plen);
    }
    g_enc_ok++;
  } else if (!okf && !oks) {
    g_enc_rej++;
  }
  fuzz_tick();
  return 0;
}
