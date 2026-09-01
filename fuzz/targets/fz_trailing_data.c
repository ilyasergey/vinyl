/* fz_trailing_data -- the "reject where a referee still recovers the audio"
 * target, on ORDINARY files. Two policies, reported as SEPARATE findings:
 *
 *   TRAILING: a valid stream with appended bytes. The overwhelmingly common case
 *     is a 128-byte ID3v1 tag ("TAG" + 125), which countless real FLAC files
 *     carry. Empirically (verified with flac 1.4.2 + ffmpeg): ffmpeg decodes the
 *     base audio and ignores the tail (exit 0, full sample count), while libFLAC
 *     reports LOST_SYNC on the tail -- so the reference that RECOVERS the audio is
 *     ffmpeg, and the probe fires when EITHER reference recovers the full base
 *     sample count (flc_full || ffm_full). Vinyl's decode returns none, discarding
 *     audio a tolerant decoder keeps. This is the only accept-set finding that
 *     fires on a file a user ALREADY HAS -- `cat a.flac tag.bin` -- not a
 *     crafted/`--lax` stream.
 *   TRUNCATION: the same stream cut at a frame boundary. libFLAC/ffmpeg return the
 *     intact prefix; Vinyl returns nothing. The two policies contradict the
 *     decoder's silent frame truncation: Vinyl truncates when frames disagree with
 *     STREAMINFO but refuses entirely when bytes are missing -- neither documented.
 *
 * NOT a bug abort by default: all-or-nothing decode is arguably a legitimate
 * policy, and this fires across the whole valid corpus. Divergences are catalogued
 * (trailing_reject / truncation_reject dumps) and counted. Under FUZZ_STRICT>=2 the
 * ID3v1 trailing case escalates to abort, for regression-pinning once filed.
 *
 * Input kind: flac_stream (CRC mutator gives diverse still-valid bases). The
 * target self-gates: it only probes a base Vinyl accepts and at least one
 * reference decodes to the same sample count. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../common/ffi_util.h"
#include "../common/flac_struct.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_api.h"
#include "../common/wide_diff.h"

/* Truncation boundaries probed per input; the rest are skipped and counted so a
 * bounded sweep never reads as full coverage. */
#define TRUNC_CAP 8

static unsigned long g_execs, g_base_ok, g_trailing_reject, g_trailing_id3, g_truncation_reject,
    g_trunc_capped, g_prefix_id3v2;

static void report(FILE *o) {
  fprintf(o,
          "[trailing] execs=%lu base_ok=%lu | trailing_reject=%lu (id3v1=%lu) "
          "truncation_reject=%lu trunc_capped=%lu | id3v2_prefix=%lu\n",
          g_execs, g_base_ok, g_trailing_reject, g_trailing_id3, g_truncation_reject, g_trunc_capped,
          g_prefix_id3v2);
}

FUZZ_TARGET(.name = "fz_trailing_data",
            .summary = "reject-where-referees-accept: trailing bytes (ID3v1) + frame-boundary "
                       "truncation",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .needs_flac = 1, .report = report)

/* Growable scratch for the base ++ suffix stream. */
static uint8_t *g_buf;
static size_t g_cap;

/* force_ffm bypasses the lazy ffmpeg gate. The base-establishment decode uses it
 * so ffm_base is reliably determined instead of being gated out (and forced
 * false) whenever Vinyl and libFLAC already agree on the clean base -- which is
 * the overwhelmingly common case and silently disabled the ffmpeg-corroborated
 * findings. The per-probe decodes keep the gated variant: after appending trailing
 * garbage Vinyl and libFLAC both reject, and that both-reject case now consults
 * ffmpeg through the ordinary gate, so forcing there buys no signal, only cost. */
static void decode3(const uint8_t *d, size_t n, Wide *v, Wide *f, Wide *g, int force_ffm) {
  wide_reset(v, "vinyl");
  wide_reset(f, "libflac");
  wide_reset(g, "ffmpeg");
  vinyl_wide_decode(d, n, v);
  flac_wide_decode(d, n, f);
  if (force_ffm)
    ffmpeg_wide_decode_forced(d, n, g);
  else
    ffmpeg_wide_decode(d, n, g);
}

/* base ++ suffix: Vinyl loses the whole file where a reference still recovers
 * the base's full audio. */
static void probe_trailing(const uint8_t *base, size_t bn, long base_ns, int flc_base, int ffm_base,
                           const uint8_t *suf, size_t suflen, int is_id3) {
  size_t n = bn + suflen;
  uint8_t *b = fuzz_grow(&g_buf, &g_cap, n ? n : 1);
  memcpy(b, base, bn);
  memcpy(b + bn, suf, suflen);
  static Wide dv, df, dg;
  decode3(b, n, &dv, &df, &dg, 0);
  int vin_lost = (dv.rc != DEC_OK || dv.nsamples < base_ns);
  int flc_full = flc_base && df.rc == DEC_OK && df.nsamples == base_ns;
  int ffm_full = ffm_base && dg.rc == DEC_OK && dg.nsamples == base_ns;
  if (vin_lost && (flc_full || ffm_full)) {
    g_trailing_reject++;
    if (is_id3)
      g_trailing_id3++;
    oracle_dump_write("trailing_reject", b, n);
    if (is_id3 && fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[ACCEPT-SET: TRAILING DATA] Vinyl rejects a valid stream + 128-byte ID3v1 tag\n"
              "  base=%zuB (samples=%ld) + tag=128B: Vinyl rc=%d samples=%ld; "
              "libFLAC=%s ffmpeg=%s recover the full audio\n"
              "  ordinary real-world files carry ID3v1 tags; `cat a.flac tag.bin` reproduces\n",
              bn, base_ns, dv.rc, dv.nsamples, flc_full ? "OK" : "-", ffm_full ? "OK" : "-");
      FUZZ_ABORT();
    }
  }
}

/* prefix ++ base: an ID3v2 tag placed BEFORE `fLaC` (C6). Vinyl requires the
 * marker at byte 0 and rejects the whole file; libFLAC/ffmpeg skip a leading
 * ID3v2 and recover the full base audio -- an accept-set divergence on a file
 * ordinary taggers produce (they write ID3v2 at the front). Symmetric to the
 * ID3v1 TRAILING case: catalogued + counted, escalates under FUZZ_STRICT>=ACCEPT. */
static void probe_prefix(const uint8_t *base, size_t bn, long base_ns, int flc_base, int ffm_base,
                         const uint8_t *pre, size_t prelen) {
  size_t n = prelen + bn;
  uint8_t *b = fuzz_grow(&g_buf, &g_cap, n ? n : 1);
  memcpy(b, pre, prelen);
  memcpy(b + prelen, base, bn);
  static Wide dv, df, dg;
  decode3(b, n, &dv, &df, &dg, 0);
  int vin_lost = (dv.rc != DEC_OK || dv.nsamples < base_ns);
  int flc_full = flc_base && df.rc == DEC_OK && df.nsamples == base_ns;
  int ffm_full = ffm_base && dg.rc == DEC_OK && dg.nsamples == base_ns;
  if (vin_lost && (flc_full || ffm_full)) {
    g_prefix_id3v2++;
    oracle_dump_write("trailing_id3v2_prefix", b, n);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[ACCEPT-SET: ID3v2 PREFIX] Vinyl rejects a stream carrying a leading ID3v2 tag\n"
              "  tag=%zuB + base=%zuB (samples=%ld): Vinyl rc=%d samples=%ld; libFLAC=%s ffmpeg=%s "
              "recover the full audio\n"
              "  Vinyl requires `fLaC` at byte 0; ID3v2 taggers write the tag BEFORE the stream\n",
              prelen, bn, base_ns, dv.rc, dv.nsamples, flc_full ? "OK" : "-", ffm_full ? "OK" : "-");
      FUZZ_ABORT();
    }
  }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (fuzz_over_sample_cap(data, size)) /* 6E: skip declared-bomb inputs */
    return 0;
  if (size < 8)
    return 0;

  /* Establish a base Vinyl accepts, corroborated by >=1 reference on sample count. */
  static Wide bv, bf, bg;
  decode3(data, size, &bv, &bf, &bg, 1);
  if (bv.rc != DEC_OK || bv.nsamples <= 0) {
    fuzz_tick();
    return 0;
  }
  long base_ns = bv.nsamples;
  int flc_base = (bf.rc == DEC_OK && bf.nsamples == base_ns);
  int ffm_base = (bg.rc == DEC_OK && bg.nsamples == base_ns);
  if (!flc_base && !ffm_base) {
    fuzz_tick();
    return 0;
  }
  g_base_ok++;

  /* Frame boundaries of the base, for the truncation half (non-strict: a mutated
   * base may carry stale header CRCs even though flac_mutate repairs them). */
  static FlacFrame frames[FLAC_MAX_FRAMES];
  size_t nf = flac_scan_frames(data, size, frames, FLAC_MAX_FRAMES, 0);

  /* ---- TRAILING ---- */
  static uint8_t id3[128];
  id3[0] = 'T';
  id3[1] = 'A';
  id3[2] = 'G'; /* rest already zero after first init; re-zero defensively */
  memset(id3 + 3, 0, sizeof id3 - 3);
  static const uint8_t one[1] = {0};
  static const uint8_t four[4] = {0, 0, 0, 0};
  probe_trailing(data, size, base_ns, flc_base, ffm_base, id3, sizeof id3, 1);
  probe_trailing(data, size, base_ns, flc_base, ffm_base, one, sizeof one, 0);
  probe_trailing(data, size, base_ns, flc_base, ffm_base, four, sizeof four, 0);
  if (nf >= 1) {
    /* a whole extra frame with a broken CRC, and a partial (half) frame. */
    size_t f0 = frames[0].start, f0e = frames[0].end;
    if (f0e > f0 && f0e <= size) {
      size_t flen = f0e - f0;
      uint8_t *extra = malloc(flen);
      if (extra) {
        memcpy(extra, data + f0, flen);
        extra[flen - 1] ^= 0xFF; /* corrupt the CRC-16 tail */
        probe_trailing(data, size, base_ns, flc_base, ffm_base, extra, flen, 0);
        probe_trailing(data, size, base_ns, flc_base, ffm_base, extra, flen / 2, 0);
        free(extra);
      }
    }
  }

  /* ---- ID3v2 PREFIX (C6) ---- : a minimal 10-byte ID3v2 header (version 2.3,
   * syncsafe size 0, no payload) placed BEFORE `fLaC`. libFLAC/ffmpeg skip it. */
  static const uint8_t id3v2[10] = {'I', 'D', '3', 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  probe_prefix(data, size, base_ns, flc_base, ffm_base, id3v2, sizeof id3v2);

  /* ---- TRUNCATION ---- : cut before frame k, keeping frames 0..k-1. */
  size_t lim = nf >= 2 ? nf - 1 : 0;
  if (lim > TRUNC_CAP) {
    g_trunc_capped++;
    lim = TRUNC_CAP;
  }
  for (size_t k = 1; k <= lim; k++) {
    size_t cut = frames[k].start;
    if (cut == 0 || cut >= size)
      continue;
    static Wide dv, df, dg;
    decode3(data, cut, &dv, &df, &dg, 0);
    int vin_none = (dv.rc != DEC_OK || dv.nsamples <= 0);
    int flc_prefix = flc_base && df.rc == DEC_OK && df.nsamples > 0 && df.nsamples < base_ns;
    int ffm_prefix = ffm_base && dg.rc == DEC_OK && dg.nsamples > 0 && dg.nsamples < base_ns;
    if (vin_none && (flc_prefix || ffm_prefix)) {
      g_truncation_reject++;
      oracle_dump_write("truncation_reject", data, cut);
      break; /* one catalogued truncation per input is enough */
    }
  }

  fuzz_tick();
  return 0;
}
