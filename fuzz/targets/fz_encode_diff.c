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
#include <unistd.h>

#include "FLAC/stream_encoder.h"

#include "../common/flac_api.h"
#include "../common/fuzz_target.h"
#include "../common/pack.h"
#include "../common/rng.h"
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
  FUZZ_ABORT();
}

/* P2.9 — drive libFLAC's encoder with its FULL knob set. The shared
 * flac_encode() wrapper (common/flac_api.c) only exposes set_compression_level;
 * even level 8 caps max_lpc_order=12 and max_residual_partition_order=6, so no
 * externally-generated stream in the whole rig ever carried LPC order 13..32 or
 * partition order 7..15 -- Vinyl's decode of those regions had only self-
 * referential corroboration. We cannot edit the shared wrapper, so we run our own
 * libFLAC encoder here: it keeps the compression level as a BASE (it presets every
 * search knob) and then overrides the individual knobs explicitly, all BEFORE
 * init_stream, so the level's defaults give way to the fuzzed geometry. The base
 * geometry (subset off, verify off, 16-bit, ch/sr/blockSize/total) is identical to
 * flac_encode(), and any setter/init failure is the ordinary encoder-setup-failure
 * path -> ENC_REJECT (never a new abort), exactly as flac_encode() treats it. Its
 * output buffer is wrapper-local, so it never aliases Vinyl's stream. */
static uint8_t *fe_out;
static size_t fe_cap, fe_len;
static FLAC__int32 *fe_i32;
static size_t fe_i32cap;
static FLAC__StreamEncoder *fe_enc;

/* A few valid libFLAC apodization specs selected by a fuzzed byte. */
static const char *const fe_apod[] = {
    "tukey(0.5)", "hann", "welch", "flattop", "partial_tukey(2)", "punchout_tukey(3)", "rectangle",
};

static void fe_out_ensure(size_t need) {
  if (need > fe_cap) {
    size_t cap = fe_cap ? fe_cap : (1u << 16);
    while (cap < need)
      cap *= 2;
    uint8_t *p = realloc(fe_out, cap);
    if (!p)
      _exit(1);
    fe_out = p;
    fe_cap = cap;
  }
}

static FLAC__StreamEncoderWriteStatus fe_write_cb(const FLAC__StreamEncoder *enc,
                                                  const FLAC__byte buffer[], size_t bytes,
                                                  uint32_t samples, uint32_t current_frame,
                                                  void *client) {
  (void)enc;
  (void)samples;
  (void)current_frame;
  (void)client;
  fe_out_ensure(fe_len + bytes);
  memcpy(fe_out + fe_len, buffer, bytes);
  fe_len += bytes;
  return FLAC__STREAM_ENCODER_WRITE_STATUS_OK;
}

/* Encode `pcm`/`n` through libFLAC with knobs derived from `knob_seed` (the
 * residual entropy pack_decode discards -- the whole 6-byte header + input size,
 * mixed through the shared xorshift, so mutating any header byte re-explores the
 * knob space). Modulo keeps each knob in a libFLAC-legal range; combinations
 * libFLAC still refuses at init (e.g. max_lpc_order vs blockSize, or a partition
 * order that does not divide the block) come back as ENC_REJECT and are classified
 * by the caller like any other libFLAC refusal. */
static int flac_encode_knobs(const uint8_t *pcm, size_t n, int bs, int ch, int sr, int level,
                             uint64_t knob_seed, uint8_t **out, size_t *len) {
  *out = NULL;
  *len = 0;
  if (ch <= 0 || n % (2 * (size_t)ch) != 0)
    return ENC_REJECT;
  if (!fe_enc) {
    fe_enc = FLAC__stream_encoder_new();
    if (!fe_enc)
      return ENC_REJECT;
  }
  size_t frames = n / (2 * (size_t)ch);
  fe_len = 0;

  uint64_t ks = knob_seed;
  uint32_t max_lpc = rng_next32(&ks) % 33u;      /* 0 disables LPC; 1..32 incl. 13..32 */
  uint32_t qlp = rng_next32(&ks) % 12u;          /* 0 (encoder-chosen) or 5..15 */
  if (qlp)
    qlp += 4u;
  uint32_t pmax = rng_next32(&ks) % 16u;         /* max residual partition order 0..15 */
  uint32_t pmin = rng_next32(&ks) % (pmax + 1u); /* 0 <= min <= max <= 15 */
  uint32_t rflags = rng_next32(&ks);
  FLAC__bool exhaustive = (rflags & 1u) ? true : false;
  FLAC__bool midside = (rflags & 2u) ? true : false;
  FLAC__bool loose = (rflags & 4u) ? true : false;
  const char *apod = fe_apod[(rflags >> 3) % (sizeof fe_apod / sizeof fe_apod[0])];

  int ok = FLAC__stream_encoder_set_compression_level(fe_enc, (uint32_t)level) &&
           FLAC__stream_encoder_set_streamable_subset(fe_enc, false) &&
           FLAC__stream_encoder_set_verify(fe_enc, false) &&
           FLAC__stream_encoder_set_channels(fe_enc, (uint32_t)ch) &&
           FLAC__stream_encoder_set_bits_per_sample(fe_enc, 16) &&
           FLAC__stream_encoder_set_sample_rate(fe_enc, (uint32_t)sr) &&
           FLAC__stream_encoder_set_blocksize(fe_enc, (uint32_t)bs) &&
           FLAC__stream_encoder_set_total_samples_estimate(fe_enc, (FLAC__uint64)frames) &&
           /* Explicit knobs override the level's presets (P2.9). */
           FLAC__stream_encoder_set_max_lpc_order(fe_enc, max_lpc) &&
           FLAC__stream_encoder_set_qlp_coeff_precision(fe_enc, qlp) &&
           FLAC__stream_encoder_set_min_residual_partition_order(fe_enc, pmin) &&
           FLAC__stream_encoder_set_max_residual_partition_order(fe_enc, pmax) &&
           FLAC__stream_encoder_set_do_exhaustive_model_search(fe_enc, exhaustive) &&
           FLAC__stream_encoder_set_apodization(fe_enc, apod);
  /* Mid/side is only valid for stereo; libFLAC clears it for other channel counts
   * at init, so guard here and leave the level's (non-stereo-safe) default in place
   * otherwise. loose is only meaningful with do_mid_side, so gate it on midside. */
  if (ok && ch == 2)
    ok = FLAC__stream_encoder_set_do_mid_side_stereo(fe_enc, midside) &&
         FLAC__stream_encoder_set_loose_mid_side_stereo(fe_enc, midside && loose);
  if (!ok) {
    FLAC__stream_encoder_finish(fe_enc); /* restore UNINITIALIZED for reuse */
    return ENC_REJECT;
  }
  if (FLAC__stream_encoder_init_stream(fe_enc, fe_write_cb, NULL, NULL, NULL, NULL) !=
      FLAC__STREAM_ENCODER_INIT_STATUS_OK) {
    FLAC__stream_encoder_finish(fe_enc);
    return ENC_REJECT;
  }

  if (frames) {
    size_t samples = frames * (size_t)ch;
    if (samples > fe_i32cap) {
      free(fe_i32);
      fe_i32cap = samples * 2;
      fe_i32 = malloc(fe_i32cap * sizeof(FLAC__int32));
      if (!fe_i32)
        _exit(1);
    }
    for (size_t i = 0; i < samples; i++)
      fe_i32[i] = (FLAC__int32)(int16_t)(pcm[2 * i] | (pcm[2 * i + 1] << 8));
    if (!FLAC__stream_encoder_process_interleaved(fe_enc, fe_i32, (uint32_t)frames)) {
      FLAC__stream_encoder_finish(fe_enc);
      return ENC_REJECT;
    }
  }
  if (!FLAC__stream_encoder_finish(fe_enc))
    return ENC_REJECT;

  *out = fe_out;
  *len = fe_len;
  return ENC_OK;
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

  /* Knob seed = the residual entropy pack_decode discards (the whole 6-byte
   * header + input size). pack_decode succeeded, so data[0..5] are valid. */
  uint64_t kseed = rng_seed(((uint64_t)data[0]) | ((uint64_t)data[1] << 8) |
                            ((uint64_t)data[2] << 16) | ((uint64_t)data[3] << 24) |
                            ((uint64_t)data[4] << 32) | ((uint64_t)data[5] << 40) |
                            ((uint64_t)size << 48));

  uint8_t *vout, *fout;
  size_t vlen, flen;
  int ve = vm_encode_fast(pcm, pn, bs, ch, (size_t)sr, &vout, &vlen);
  int fe = flac_encode_knobs(pcm, pn, (int)bs, ch, (int)sr, level, kseed, &fout, &flen);

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
