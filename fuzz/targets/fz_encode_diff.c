/* fz_encode_diff — coverage-guided differential encode. Input packing:
 * common/pack.h (checked-encode domain, blockSize <= 4608). Oracles:
 *  1. flac_decode(vinyl_encode_fast(pcm)) == pcm  — Vinyl must emit FLAC the
 *     reference reads back losslessly. Violation -> abort().
 *  2. vinyl_decode_fast(flac_encode(pcm)) == pcm  — clean Vinyl REJECT of
 *     genuine libFLAC output is catalogued; DEC_OK with wrong bytes -> abort().
 *  3. Parameter agreement classified (both-ok / vinyl-only / libflac-only /
 *     both-reject). "Both rejected" is agreement, never a finding.
 *  4. Metrics only (byte-compat is a documented non-goal). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_api.h"
#include "../common/fuzz_target.h"
#include "../common/pack.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_modes.h"

static unsigned long g_execs, g_short;
static unsigned long g_both_ok, g_vinyl_only, g_flac_only, g_both_rej;
static unsigned long g_xdec_a_ok, g_xdec_b_ok, g_xdec_b_rej;
static unsigned long g_bytes_identical;
static double g_rsum, g_rmin = 1e300, g_rmax;

static void report(FILE *f) {
  fprintf(f,
          "[enc] execs=%lu short=%lu | params both_ok=%lu vinyl_only=%lu flac_only=%lu both_rej=%lu "
          "| xdecA_ok=%lu xdecB_ok=%lu xdecB_rej=%lu | ident=%lu (%.2f%%) "
          "ratio mean=%.4f min=%.4f max=%.4f\n",
          g_execs, g_short, g_both_ok, g_vinyl_only, g_flac_only, g_both_rej, g_xdec_a_ok,
          g_xdec_b_ok, g_xdec_b_rej, g_bytes_identical,
          g_both_ok ? 100.0 * (double)g_bytes_identical / (double)g_both_ok : 0.0,
          g_both_ok ? g_rsum / (double)g_both_ok : 0.0, g_both_ok ? g_rmin : 0.0, g_rmax);
}

FUZZ_TARGET(.name = "fz_encode_diff",
            .summary = "Vinyl encode vs libFLAC, round-trip through the reference",
            .input_kind = FUZZ_INPUT_PACKED_PCM, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 1, .needs_flac = 1, .report = report)

static void die(const char *what, int ch, unsigned bs, uint32_t sr, int level, size_t pn,
                const uint8_t *pcm, const uint8_t *got, size_t got_len, int rb, int rc, int rs) {
  size_t off = 0, m = got && got_len < pn ? got_len : pn;
  if (got)
    while (off < m && pcm[off] == got[off])
      off++;
  fprintf(stderr,
          "\n[ENCODE-DIVERGENCE] %s\n"
          "  params : ch=%d blockSize=%u sampleRate=%u level=%d pcm=%zuB (%zu frames)\n"
          "  decode : bps=%d ch=%d sr=%d len=%zu (expected len=%zu) first_diff_off=%zu\n",
          what, ch, bs, sr, level, pn, ch ? pn / (2 * (size_t)ch) : 0, rb, rc, rs, got_len, pn, off);
  if (got && off < m)
    fprintf(stderr, "  pcm[%zu..]=%02x %02x  got[%zu..]=%02x %02x\n", off, pcm[off],
            off + 1 < pn ? pcm[off + 1] : 0, off, got[off], off + 1 < got_len ? got[off + 1] : 0);
  report(stderr);
  abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  PackedInput in;
  if (!pack_decode(data, size, &in)) {
    g_short++;
    return 0;
  }
  int ch = in.ch;
  unsigned bs = in.bs;
  uint32_t sr = in.sr;
  int level = in.level;
  const uint8_t *pcm = in.pcm;
  size_t pn = in.pcm_len;

  uint8_t *vout, *fout;
  size_t vlen, flen;
  int ve = vm_encode_fast(pcm, pn, bs, ch, (size_t)sr, &vout, &vlen);
  int fe = flac_encode(pcm, pn, (int)bs, ch, (int)sr, level, &fout, &flen);

  if (ve == ENC_OK && fe == ENC_OK)
    g_both_ok++;
  else if (ve == ENC_OK)
    g_vinyl_only++;
  else if (fe == ENC_OK)
    g_flac_only++;
  else
    g_both_rej++;

  if (ve == ENC_OK) {
    uint8_t *fp;
    size_t fl;
    int fb, fc, fs;
    int r = flac_decode(vout, vlen, &fp, &fl, &fb, &fc, &fs);
    /* Vinyl's fast encoder claims to emit valid 16-bit FLAC; if the reference
     * cannot read it back, that is the corrupted-output class (b) -- unconditio-
     * nally, NOT only when libFLAC's own ENCODER would have accepted these
     * params. The old `if (fe == ENC_OK)` guard suppressed exactly the case the
     * client cares about: Vinyl accepting geometry libFLAC's encoder refuses and
     * emitting a stream libFLAC's decoder then rejects. */
    if (r != DEC_OK)
      die(r == DEC_SKIP ? "libFLAC saw non-16-bit in Vinyl's stream"
                        : "libFLAC cannot decode Vinyl's stream",
          ch, bs, sr, level, pn, pcm, NULL, 0, fb, fc, fs);
    if (fc != ch || fs != (int)sr || fb != 16)
      die("libFLAC reads different params from Vinyl's stream", ch, bs, sr, level, pn, pcm, fp, fl,
          fb, fc, fs);
    if (fl != pn || (pn && memcmp(fp, pcm, pn) != 0))
      die("libFLAC decode of Vinyl's stream is not the input PCM", ch, bs, sr, level, pn, pcm, fp,
          fl, fb, fc, fs);
    g_xdec_a_ok++;
  }

  if (fe == ENC_OK) {
    uint8_t *vp;
    size_t vl;
    int vb, vc, vs;
    int r = vinyl_decode_fast(fout, flen, &vp, &vl, &vb, &vc, &vs);
    if (r == DEC_OK) {
      if (vc != ch || vs != (int)sr || vb != 16)
        die("Vinyl reads different params from libFLAC's stream", ch, bs, sr, level, pn, pcm, vp,
            vl, vb, vc, vs);
      if (vl != pn || (pn && memcmp(vp, pcm, pn) != 0))
        die("Vinyl decode of libFLAC's stream is not the input PCM", ch, bs, sr, level, pn, pcm, vp,
            vl, vb, vc, vs);
      g_xdec_b_ok++;
    } else {
      g_xdec_b_rej++;
    }
  }

  if (ve == ENC_OK && fe == ENC_OK) {
    if (vlen == flen && memcmp(vout, fout, vlen) == 0)
      g_bytes_identical++;
    double ratio = (double)vlen / (double)flen;
    g_rsum += ratio;
    if (ratio < g_rmin)
      g_rmin = ratio;
    if (ratio > g_rmax)
      g_rmax = ratio;
  }
  fuzz_tick();
  return 0;
}
