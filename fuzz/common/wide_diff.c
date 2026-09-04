#include "wide_diff.h"

#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>
#include <libavutil/samplefmt.h>

#include "FLAC/stream_decoder.h"
#include "ffi_util.h"
#include "flac_residual.h" /* flac_reconstruct_oob_at: RFC-invalid reconstruction witness */
#include "flac_struct.h" /* flac_hdr_consistent */
#include "fuzz_target.h"
#include "oracle.h"
#include "vinyl_api.h" /* DEC_OK / DEC_REJECT */

extern lean_object *vinyl_decode_arrays(lean_object *bytes);

/* ---- Wide buffer management ------------------------------------------- */
void wide_reset(Wide *w, const char *name) {
  w->name = name;
  w->rc = DEC_REJECT;
  w->nch = w->bps = w->sr = 0;
  w->nsamples = 0;
  w->overflow = 0;
}

static void wide_ensure(Wide *w, int c, size_t need) {
  if (need > w->cap[c]) {
    size_t cap = w->cap[c] ? w->cap[c] : 4096;
    while (cap < need)
      cap *= 2;
    int64_t *p = realloc(w->plane[c], cap * sizeof(int64_t));
    if (!p)
      _exit(1);
    w->plane[c] = p;
    w->cap[c] = cap;
  }
}

/* ---- libFLAC native-plane decoder ------------------------------------ */
typedef struct {
  const uint8_t *in;
  size_t n, pos;
  Wide *w;
  int err, mixed, toomany;
  int si_sr;        /* STREAMINFO sample rate, captured in fw_meta (0 = not seen) */
  int sr_mismatch;  /* a frame sample rate contradicted STREAMINFO -- malformed */
} FlacWideCtx;

static FlacWideCtx fw;
static FLAC__StreamDecoder *fw_dec;

static FLAC__StreamDecoderReadStatus fw_read(const FLAC__StreamDecoder *d, FLAC__byte b[],
                                             size_t *bytes, void *c) {
  (void)d;
  (void)c;
  if (fw.pos >= fw.n) {
    *bytes = 0;
    return FLAC__STREAM_DECODER_READ_STATUS_END_OF_STREAM;
  }
  size_t k = fw.n - fw.pos;
  if (k > *bytes)
    k = *bytes;
  memcpy(b, fw.in + fw.pos, k);
  fw.pos += k;
  *bytes = k;
  return FLAC__STREAM_DECODER_READ_STATUS_CONTINUE;
}
static FLAC__bool fw_eof(const FLAC__StreamDecoder *d, void *c) {
  (void)d;
  (void)c;
  return fw.pos >= fw.n;
}
static FLAC__StreamDecoderWriteStatus fw_write(const FLAC__StreamDecoder *d, const FLAC__Frame *f,
                                               const FLAC__int32 *const b[], void *c) {
  (void)d;
  (void)c;
  unsigned bps = f->header.bits_per_sample, ch = f->header.channels, bs = f->header.blocksize;
  if (ch > WIDE_MAX_CH) {
    fw.toomany = 1;
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }
  /* RFC 9639 §9.1: a frame whose sample rate contradicts STREAMINFO is malformed.
   * The strict libFLAC CLI aborts on it ("sample rate is X in frame but Y in
   * STREAMINFO"); libFLAC-the-library does not, so without this the wide referee is
   * MORE lenient than the CLI and would form a false libFLAC+ffmpeg "consensus"
   * against Vinyl on a malformed stream (see findings/decode-sample-divergence-highbps
   * repro-min-215B). Match the CLI so a contradiction is a reject, not a consensus. */
  if (fw.si_sr && (int)f->header.sample_rate != fw.si_sr) {
    fw.sr_mismatch = 1;
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }
  if (fw.w->nsamples == 0) {
    fw.w->bps = (int)bps;
    fw.w->nch = (int)ch;
    fw.w->sr = (int)f->header.sample_rate;
  } else if ((int)ch != fw.w->nch || (int)bps != fw.w->bps) {
    fw.mixed = 1;
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }
  for (unsigned cc = 0; cc < ch; cc++)
    wide_ensure(fw.w, (int)cc, (size_t)fw.w->nsamples + bs);
  for (unsigned i = 0; i < bs; i++)
    for (unsigned cc = 0; cc < ch; cc++)
      fw.w->plane[cc][fw.w->nsamples + i] = (int64_t)b[cc][i];
  fw.w->nsamples += (long)bs;
  return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}
static void fw_meta(const FLAC__StreamDecoder *d, const FLAC__StreamMetadata *m, void *c) {
  (void)d;
  (void)c;
  if (m->type == FLAC__METADATA_TYPE_STREAMINFO && fw.w->nsamples == 0) {
    fw.w->bps = (int)m->data.stream_info.bits_per_sample;
    fw.w->nch = (int)m->data.stream_info.channels;
    fw.w->sr = (int)m->data.stream_info.sample_rate;
    fw.si_sr = (int)m->data.stream_info.sample_rate;
  }
}
static void fw_err(const FLAC__StreamDecoder *d, FLAC__StreamDecoderErrorStatus s, void *c) {
  (void)d;
  (void)s;
  (void)c;
  fw.err = 1;
}

/* Phase 6D: the most recent Vinyl and libFLAC decode results, captured so the
 * ffmpeg adjudication gate can decide whether the SECOND referee is needed at
 * all. Every caller decodes vinyl, then libFLAC, then ffmpeg on the same bytes,
 * so these two pointers name the correct siblings when ffmpeg_wide_decode runs.
 * g_ff_skipped records that ffmpeg gated itself out (vinyl==libFLAC already), so
 * wide_diff_oracle can tell an intentional skip from a genuine ffmpeg reject. */
static const Wide *g_last_vin;
static const Wide *g_last_flc;
static int g_ff_skipped;
static unsigned long g_ff_skip_total; /* cumulative gate skips, for the campaign census */
#define FF_CENSUS_EVERY 64 /* 1-in-N forced ffmpeg run to keep the referee-split census honest */

int flac_wide_decode(const uint8_t *in, size_t n, Wide *w) {
  g_last_flc = w;
  if (!fw_dec) {
    fw_dec = FLAC__stream_decoder_new();
    if (!fw_dec)
      return DEC_REJECT;
  }
  memset(&fw, 0, sizeof fw);
  fw.in = in;
  fw.n = n;
  fw.w = w;
  FLAC__stream_decoder_set_md5_checking(fw_dec, false);
  if (FLAC__stream_decoder_init_stream(fw_dec, fw_read, NULL, NULL, NULL, fw_eof, fw_write, fw_meta,
                                       fw_err, NULL) != FLAC__STREAM_DECODER_INIT_STATUS_OK) {
    FLAC__stream_decoder_finish(fw_dec);
    return DEC_REJECT;
  }
  FLAC__bool ok = FLAC__stream_decoder_process_until_end_of_stream(fw_dec);
  FLAC__StreamDecoderState st = FLAC__stream_decoder_get_state(fw_dec);
  FLAC__stream_decoder_finish(fw_dec);
  /* nsamples==0 is NOT a rejection here: a metadata-only stream is legal FLAC
   * (the oracle skips the empty comparison). Rejecting it would make a
   * metadata-only stream Vinyl accepts read as an accept-divergence. */
  if (!ok || fw.err || fw.mixed || fw.toomany || fw.sr_mismatch ||
      st != FLAC__STREAM_DECODER_END_OF_STREAM)
    return (w->rc = DEC_REJECT);
  return (w->rc = DEC_OK);
}

/* ---- libFLAC MD5 verification ---------------------------------------- */
/* Decode `in` with libFLAC's MD5 CHECKING ON and report whether the STREAMINFO
 * MD5 Vinyl wrote matches libFLAC's MD5 of the decoded audio. FLAC__..._finish()
 * returns false iff md5_checking was on AND the MD5 mismatched; an all-zero
 * STREAMINFO MD5 ("unknown") makes libFLAC skip the check and finish() succeed.
 * So a return of MD5_MISMATCH is unambiguous: a NON-zero MD5 that did not match,
 * i.e. Vinyl's MD5 convention (RFC 9639 §9.2.2) diverges from libFLAC's -- a
 * broken security-relevant primitive that no round-trip theorem covers, and that
 * has never been validated above 16-bit. Own context/decoder so it never
 * disturbs flac_wide_decode's md5-off singleton. */
typedef struct {
  const uint8_t *in;
  size_t n, pos;
  int err, got;
} Md5Ctx;
static Md5Ctx m5;
static FLAC__StreamDecoder *m5_dec;

static FLAC__StreamDecoderReadStatus m5_read(const FLAC__StreamDecoder *d, FLAC__byte b[],
                                             size_t *bytes, void *c) {
  (void)d;
  (void)c;
  if (m5.pos >= m5.n) {
    *bytes = 0;
    return FLAC__STREAM_DECODER_READ_STATUS_END_OF_STREAM;
  }
  size_t k = m5.n - m5.pos;
  if (k > *bytes)
    k = *bytes;
  memcpy(b, m5.in + m5.pos, k);
  m5.pos += k;
  *bytes = k;
  return FLAC__STREAM_DECODER_READ_STATUS_CONTINUE;
}
static FLAC__StreamDecoderWriteStatus m5_write(const FLAC__StreamDecoder *d, const FLAC__Frame *f,
                                               const FLAC__int32 *const b[], void *c) {
  (void)d;
  (void)f;
  (void)b;
  (void)c;
  m5.got = 1; /* libFLAC accumulates the MD5 internally regardless of this cb */
  return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}
static void m5_err(const FLAC__StreamDecoder *d, FLAC__StreamDecoderErrorStatus s, void *c) {
  (void)d;
  (void)s;
  (void)c;
  m5.err = 1;
}

int flac_md5_verify(const uint8_t *in, size_t n) {
  if (!m5_dec) {
    m5_dec = FLAC__stream_decoder_new();
    if (!m5_dec)
      return MD5_UNCHECKED;
  }
  memset(&m5, 0, sizeof m5);
  m5.in = in;
  m5.n = n;
  FLAC__stream_decoder_set_md5_checking(m5_dec, true);
  if (FLAC__stream_decoder_init_stream(m5_dec, m5_read, NULL, NULL, NULL, NULL, m5_write, NULL,
                                       m5_err, NULL) != FLAC__STREAM_DECODER_INIT_STATUS_OK) {
    FLAC__stream_decoder_finish(m5_dec);
    return MD5_UNCHECKED;
  }
  FLAC__bool ok = FLAC__stream_decoder_process_until_end_of_stream(m5_dec);
  FLAC__StreamDecoderState st = FLAC__stream_decoder_get_state(m5_dec);
  int got = m5.got, err = m5.err;
  /* finish() runs the MD5 comparison; false => md5_checking on AND mismatch. */
  FLAC__bool fin = FLAC__stream_decoder_finish(m5_dec);
  if (!ok || err || !got || st != FLAC__STREAM_DECODER_END_OF_STREAM)
    return MD5_UNCHECKED; /* decode itself did not cleanly complete */
  return fin ? MD5_MATCH : MD5_MISMATCH;
}

/* ---- libavcodec (ffmpeg) native-plane decoder ------------------------ */
/* A second, independent reference decoder (RFC references libFLAC AND ffmpeg).
 * FLAC in ffmpeg decodes to S16 planes for bps<=16 (right-aligned, as-is) and
 * to S32 planes for bps>16 LEFT-JUSTIFIED into 32 bits; we shift back by
 * (32 - bits_per_raw_sample) so the values match libFLAC/Vinyl (verified
 * bit-exact at 8/12/16/24-bit, mono and stereo). Reads from memory via a custom
 * AVIOContext; robust to malformed input (returns reject, does not crash). */
typedef struct {
  const uint8_t *in;
  size_t n, pos;
} FfMem;

static int ff_read(void *opaque, uint8_t *buf, int size) {
  FfMem *m = opaque;
  size_t k = m->n - m->pos;
  if (k == 0)
    return AVERROR_EOF;
  if ((size_t)size < k)
    k = (size_t)size;
  memcpy(buf, m->in + m->pos, k);
  m->pos += k;
  return (int)k;
}

/* Phase 6D adjudication predicate: ffmpeg is only a SECOND referee, but it can
 * only be skipped when it genuinely cannot change the verdict: Vinyl and libFLAC
 * both accepted with identical geometry AND identical samples. In that case
 * ffmpeg would at most catalogue a ref_disagree, so the ~700us
 * avformat_open_input/find_stream_info/decode/teardown is pure overhead. The
 * both-reject case is NOT skippable: that is exactly where the ffmpeg-only-accept
 * / accept-set signal lives (libFLAC and Vinyl both reject a stream ffmpeg
 * recovers), so the referee must be consulted. A Vinyl bignum overflow makes the
 * sample comparison untrustworthy, so force the referee in that case too. */
static int ffm_adjudication_skippable(const Wide *vin, const Wide *flc) {
  if (vin->overflow)
    return 0;
  if (vin->rc != DEC_OK || flc->rc != DEC_OK)
    return 0;
  if (vin->nch != flc->nch || vin->nsamples != flc->nsamples)
    return 0;
  for (int c = 0; c < vin->nch; c++)
    for (long i = 0; i < vin->nsamples; i++)
      if (vin->plane[c][i] != flc->plane[c][i])
        return 0;
  return 1;
}

/* The actual ffmpeg open/decode/teardown. Shared verbatim by the gated
 * ffmpeg_wide_decode and the unconditional ffmpeg_wide_decode_forced so both
 * entry points run identical decode logic; only the lazy gate differs. */
static int ffmpeg_wide_decode_body(const uint8_t *in, size_t n, Wide *w) {
  static int quieted;
  if (!quieted) {
    av_log_set_level(AV_LOG_QUIET);
    quieted = 1;
  }
  const size_t IOBUF = 4096;
  unsigned char *iob = av_malloc(IOBUF);
  if (!iob)
    return (w->rc = DEC_REJECT);
  FfMem mem = {in, n, 0};
  AVIOContext *avio = avio_alloc_context(iob, (int)IOBUF, 0, &mem, ff_read, NULL, NULL);
  AVFormatContext *fmt = avformat_alloc_context();
  AVCodecContext *ctx = NULL;
  AVPacket *pkt = NULL;
  AVFrame *fr = NULL;
  int rc = DEC_REJECT, si = -1, mixed = 0, toomany = 0, unsupported = 0;
  if (!avio || !fmt)
    goto done;
  fmt->pb = avio;
  const AVInputFormat *iff = av_find_input_format("flac");
  if (avformat_open_input(&fmt, NULL, iff, NULL) < 0) {
    fmt = NULL; /* freed by open_input on failure */
    goto done;
  }
  if (avformat_find_stream_info(fmt, NULL) < 0)
    goto done;
  for (unsigned i = 0; i < fmt->nb_streams; i++)
    if (fmt->streams[i]->codecpar->codec_type == AVMEDIA_TYPE_AUDIO) {
      si = (int)i;
      break;
    }
  if (si < 0)
    goto done;
  AVCodecParameters *par = fmt->streams[si]->codecpar;
  const AVCodec *cod = avcodec_find_decoder(par->codec_id);
  if (!cod)
    goto done;
  ctx = avcodec_alloc_context3(cod);
  if (!ctx || avcodec_parameters_to_context(ctx, par) < 0 || avcodec_open2(ctx, cod, NULL) < 0)
    goto done;
  pkt = av_packet_alloc();
  fr = av_frame_alloc();
  if (!pkt || !fr)
    goto done;

  while (av_read_frame(fmt, pkt) >= 0) {
    if (pkt->stream_index == si && avcodec_send_packet(ctx, pkt) == 0) {
      while (avcodec_receive_frame(ctx, fr) == 0) {
        int ch = fr->ch_layout.nb_channels, bs = fr->nb_samples;
        if (ch > WIDE_MAX_CH) {
          toomany = 1;
          break;
        }
        if (w->nsamples == 0) {
          w->nch = ch;
          w->bps = ctx->bits_per_raw_sample ? ctx->bits_per_raw_sample : par->bits_per_raw_sample;
          w->sr = ctx->sample_rate;
        } else if (ch != w->nch) {
          mixed = 1;
          break;
        }
        int bpr = w->bps;
        int shift = (bpr > 0 && bpr < 32) ? (32 - bpr) : 0;
        enum AVSampleFormat sf = fr->format;
        /* FLAC decodes to exactly these four planar/packed int formats. An
         * unrecognized format (a future/planar-float libavcodec layout) must NOT
         * be silently read as an all-zero plane and still returned DEC_OK -- that
         * fabricates a zero reference that forms false consensus or false
         * divergence. Reject the stream instead. */
        if (sf != AV_SAMPLE_FMT_S16P && sf != AV_SAMPLE_FMT_S32P &&
            sf != AV_SAMPLE_FMT_S16 && sf != AV_SAMPLE_FMT_S32) {
          unsupported = 1;
          break;
        }
        for (int c = 0; c < ch; c++) {
          wide_ensure(w, c, (size_t)w->nsamples + bs);
          for (int i = 0; i < bs; i++) {
            int64_t v;
            if (sf == AV_SAMPLE_FMT_S16P)
              v = ((int16_t *)fr->extended_data[c])[i];
            else if (sf == AV_SAMPLE_FMT_S32P)
              v = (int64_t)((int32_t *)fr->extended_data[c])[i] >> shift;
            else if (sf == AV_SAMPLE_FMT_S16)
              v = ((int16_t *)fr->extended_data[0])[i * ch + c];
            else
              v = (int64_t)((int32_t *)fr->extended_data[0])[i * ch + c] >> shift;
            w->plane[c][w->nsamples + i] = v;
          }
        }
        w->nsamples += bs;
      }
    }
    av_packet_unref(pkt);
    if (mixed || toomany || unsupported)
      break;
  }
  /* Require actually-decoded audio for DEC_OK. avformat_open_input +
   * find_stream_info succeed on a container that yields ZERO audio frames
   * (metadata-only, or a header ffmpeg parses but cannot decode); counting that
   * as an accepting reference inflates nref_ok and MASKS the WD_VINYL_ONLY /
   * WD_REF_ONLY accept-set rows (bug 8). A zero-audio open is not corroboration. */
  rc = (!mixed && !toomany && !unsupported && w->nsamples > 0) ? DEC_OK : DEC_REJECT;

done:
  if (fr)
    av_frame_free(&fr);
  if (pkt)
    av_packet_free(&pkt);
  if (ctx)
    avcodec_free_context(&ctx);
  if (fmt)
    avformat_close_input(&fmt);
  /* close_input does not free a caller-supplied pb; the demuxer may have
   * realloc'd its buffer, so free the CURRENT one, then the context. */
  if (avio) {
    av_freep(&avio->buffer);
    avio_context_free(&avio);
  }
  return (w->rc = rc);
}

int ffmpeg_wide_decode(const uint8_t *in, size_t n, Wide *w) {
  /* Phase 6D lazy ffmpeg -- the primary throughput lever. Run the second referee
   * ONLY when it can matter, i.e. when Vinyl and libFLAC DISAGREE (acceptance,
   * geometry, or a sample value), plus a cheap 1-in-N census sample so the
   * referee-split statistics are not silently zeroed. On the overwhelming
   * majority of inputs the two lead decoders already agree, so this drops the
   * full open/decode/teardown entirely.
   * TODO persistent ctx: a file-static AVCodecContext reset with
   * avcodec_flush_buffers would trim the residual per-call cost when ffmpeg IS
   * run, but the FLAC demuxer plus per-stream STREAMINFO extradata make a
   * persistent context invasive to do safely here, so only the dominant gating
   * win is taken. */
  static unsigned long gate_counter;
  const int forced = (++gate_counter % FF_CENSUS_EVERY) == 0;
  g_ff_skipped = 0;
  if (!forced && g_last_vin && g_last_flc &&
      ffm_adjudication_skippable(g_last_vin, g_last_flc)) {
    g_ff_skipped = 1;
    g_ff_skip_total++;
    return (w->rc = DEC_REJECT);
  }
  return ffmpeg_wide_decode_body(in, n, w);
}

/* Unconditional ffmpeg decode -- bypasses the lazy gate entirely. For callers
 * (e.g. base-establishment in fz_trailing_data) that need ffmpeg's verdict
 * reliably rather than 1-in-FF_CENSUS_EVERY of the time. */
int ffmpeg_wide_decode_forced(const uint8_t *in, size_t n, Wide *w) {
  g_ff_skipped = 0;
  return ffmpeg_wide_decode_body(in, n, w);
}

/* Cumulative count of executions on which the lazy gate skipped ffmpeg. */
unsigned long wide_ff_skip_total(void) {
  return g_ff_skip_total;
}

/* ---- Vinyl decodeArrays -> planes ------------------------------------ */
int vinyl_wide_decode(const uint8_t *in, size_t n, Wide *w) {
  g_last_vin = w;
  lean_object *r = vinyl_decode_arrays(mk_ba(in, n)); /* consumes ba */
  if (lean_obj_tag(r) == 0) {
    lean_dec(r);
    return (w->rc = DEC_REJECT);
  }
  lean_object *p = lean_ctor_get(r, 0);   /* List (Array Int) × Nat × Nat */
  lean_object *chs = lean_ctor_get(p, 0); /* borrowed */
  lean_object *q = lean_ctor_get(p, 1);
  w->bps = nat_small(lean_ctor_get(q, 0));
  w->sr = nat_small(lean_ctor_get(q, 1));

  int c = 0;
  long ns = -1;
  for (lean_object *node = chs; !lean_is_scalar(node); node = lean_ctor_get(node, 1)) {
    if (c >= WIDE_MAX_CH) {
      c = WIDE_MAX_CH + 1; /* too many channels: flag by overshoot */
      break;
    }
    lean_object *arr = lean_ctor_get(node, 0); /* Array Int */
    size_t sz = lean_array_size(arr);
    wide_ensure(w, c, sz ? sz : 1);
    for (size_t i = 0; i < sz; i++) {
      lean_object *x = lean_array_get_core(arr, i);
      if (lean_is_scalar(x))
        w->plane[c][i] = lean_scalar_to_int64(x);
      else {
        w->overflow = 1; /* bignum sample: does not fit int64 */
        w->plane[c][i] = 0;
      }
    }
    if (ns < 0)
      ns = (long)sz;
    else if ((long)sz != ns)
      ns = -2; /* ragged (should not happen) */
    c++;
  }
  w->nch = c;
  w->nsamples = (ns >= 0) ? ns : 0;
  lean_dec(r);
  return (w->rc = DEC_OK);
}

/* ---- the three-way oracle -------------------------------------------- */
/* WD_* tally codes live in wide_diff.h so the targets can name them. */
enum { CMP_EQUAL, CMP_DIFF, CMP_GEOM };

/* Compare decoded SAMPLES (not the bps label -- ffmpeg's bps reporting is the
 * least reliable of the three, and identical values under a different label are
 * a labelling artefact, not a codec divergence). */
static int wide_cmp(const Wide *a, const Wide *b, int *diff_c, long *diff_i) {
  if (a->nch != b->nch || a->nsamples != b->nsamples)
    return CMP_GEOM;
  for (int c = 0; c < a->nch; c++)
    for (long i = 0; i < a->nsamples; i++)
      if (a->plane[c][i] != b->plane[c][i]) {
        if (diff_c)
          *diff_c = c;
        if (diff_i)
          *diff_i = i;
        return CMP_DIFF;
      }
  return CMP_EQUAL;
}

/* output-contract: the decoder's codomain is FitsSInt bps -- every returned
 * sample must lie in [-2^(bps-1), 2^(bps-1)) for the declared output depth. But
 * stereo un-decorrelation can reconstruct e.g. right = left - side with
 * left = -2^(b-1), side = 2^b-1 giving right ≈ -1.5·2^b, which escapes that
 * range. Returns 1 (with the offending cell) if any sample is out of contract. */
static int wide_out_of_contract(const Wide *w, int *bad_c, long *bad_i, long long *bad_v) {
  int bps = w->bps;
  if (bps < 1 || bps > 32)
    return 0;
  long long hi = 1LL << (bps - 1), lo = -hi;
  for (int c = 0; c < w->nch; c++)
    for (long i = 0; i < w->nsamples; i++) {
      long long v = (long long)w->plane[c][i];
      if (v < lo || v >= hi) {
        if (bad_c)
          *bad_c = c;
        if (bad_i)
          *bad_i = i;
        if (bad_v)
          *bad_v = v;
        return 1;
      }
    }
  return 0;
}

/* Contract test for a single value. */
static int val_out_of_contract(long long v, int bps) {
  if (bps < 1 || bps > 32)
    return 0;
  long long hi = 1LL << (bps - 1);
  return v < -hi || v >= hi;
}

/* When Vinyl and a reference DIFFER at a cell whose Vinyl value is itself out of
 * FitsSInt(bps), that is the output-contract finding -- Vinyl's codomain escaped
 * its declared depth -- reached through a DIFF path, NOT a decode divergence to
 * abort on. The references store the reconstructed value in a fixed-width int
 * container (libFLAC int32; ffmpeg int16 at bps<=16, or a bps-wide value after
 * the S32 >>shift) and so WRAP it: at bps 24/32 both wrap identically, forming a
 * false consensus Vinyl (exact ℤ) differs from, and at bps 17-31 the ffmpeg
 * >>shift makes the wrap non-clean -- so the sound test is on Vinyl's value
 * alone, not on the exact difference. This is the s41_bps24/32 false-consensus /
 * single-reference false-abort guard. */

static void report(const char *what, size_t insz, const Wide *v, const Wide *f, const Wide *g) {
  fprintf(stderr,
          "\n[WIDE DIVERGENCE] %s input=%zuB\n"
          "  %-7s: rc=%d bps=%d ch=%d sr=%d samples=%ld overflow=%d\n"
          "  %-7s: rc=%d bps=%d ch=%d sr=%d samples=%ld\n"
          "  %-7s: rc=%d bps=%d ch=%d sr=%d samples=%ld\n",
          what, insz, v->name, v->rc, v->bps, v->nch, v->sr, v->nsamples, v->overflow, f->name,
          f->rc, f->bps, f->nch, f->sr, f->nsamples, g->name, g->rc, g->bps, g->nch, g->sr,
          g->nsamples);
}

int wide_diff_oracle(const uint8_t *data, size_t size, const Wide *vin, const Wide *flc,
                     const Wide *ffm) {
  const int strict = fuzz_env_strict();
  const int nref_ok = (flc->rc == DEC_OK) + (ffm->rc == DEC_OK);

  if (vin->rc != DEC_OK && nref_ok == 0)
    return WD_BOTH_REJECT;

  /* frame-vs-STREAMINFO clash: the references follow the frame header, Vinyl
   * follows STREAMINFO -- neither is a defect. Check BEFORE any accept/reject
   * escalation so a strict run never aborts on it. */
  if (!flac_hdr_consistent(data, size))
    return WD_HDR_CLASH;

  /* Accept-set rows, decided on rc alone. Requiring BOTH references to agree
   * against Vinyl is what the second referee buys: a lone libFLAC reject is
   * often a libFLAC quirk, but libFLAC AND ffmpeg both rejecting a stream Vinyl
   * accepts is the P5 accept-set-too-wide class. */
  if (vin->rc == DEC_OK && nref_ok == 0) {
    oracle_dump_write("wide_vinyl_only", data, size);
    if (strict >= FUZZ_STRICT_ACCEPT) {
      report("VINYL_ONLY: Vinyl accepts, both references reject (strict)", size, vin, flc, ffm);
      FUZZ_ABORT();
    }
    return WD_VINYL_ONLY;
  }
  if (vin->rc != DEC_OK && nref_ok == 2) {
    oracle_dump_write("wide_ref_only", data, size);
    if (strict >= FUZZ_STRICT_ACCEPT) {
      report("REF_ONLY: both references accept, Vinyl rejects (strict)", size, vin, flc, ffm);
      FUZZ_ABORT();
    }
    return WD_REF_ONLY;
  }
  if (vin->rc != DEC_OK) {
    /* nref_ok == 1: the references disagree on acceptance; Vinyl siding with the
     * rejecting one is defensible referee laxness, not a Vinyl defect. */
    oracle_dump_write("wide_ref_disagree", data, size);
    return WD_REF_DISAGREE;
  }

  /* Vinyl accepted and at least one reference accepted. Garbage-in guards. */
  if (vin->overflow) {
    oracle_dump_write("wide_vinyl_bignum", data, size);
    return WD_SKIP;
  }
  if (vin->nsamples == 0)
    return WD_SKIP; /* metadata-only Vinyl output: nothing to compare */

  /* Sample/geometry comparison. The abort case is the highest-confidence one:
   * Vinyl contradicts a REFERENCE CONSENSUS -- both independent decoders agree
   * with each other and Vinyl differs. Requiring the two references to
   * corroborate each other is exactly what the second referee buys: it separates
   * "Vinyl is the outlier" (a spec-reading bug) from "the two references
   * disagree and Vinyl picked a side" (referee laxness / garbage-in framing on a
   * corrupt stream -- a predictor-wrap class), which must NOT abort. */
  const int flc_audio = (flc->rc == DEC_OK && flc->nsamples > 0);
  const int ffm_audio = (ffm->rc == DEC_OK && ffm->nsamples > 0);

  /* Output-contract, checked BEFORE the flc-vs-ffm consensus gate and
   * corroborated by libFLAC ALONE. Vinyl's decoder codomain must be
   * FitsSInt(bps), but P1 wraps only inside the subframe recurrence, so a stereo
   * un-decorrelation (right = left - side, both at their legal extremes) can
   * still return a sample outside [-2^(bps-1), 2^(bps-1)). That is EXACTLY the
   * case where ffmpeg legitimately disagrees with libFLAC -- at bps<=16 ffmpeg
   * decodes to int16 planes and WRAPS the out-of-range value -- so a
   * consensus-first path files this finding as a referee split and the contract
   * check never runs (bug 1). libFLAC keeps full int32, so it is the reliable
   * corroborator: if Vinyl returns an out-of-contract sample and libFLAC
   * reconstructs the SAME value, that value is the correct per-spec
   * reconstruction and the finding is real -- the decoder has no output
   * contract, not a decode divergence. Catalogue by default; abort only in a
   * must-agree / regression run (bug 5). */
  if (flc_audio && !vin->overflow) {
    int oc = 0;
    long oi = 0;
    long long ov = 0;
    if (wide_out_of_contract(vin, &oc, &oi, &ov) && flc->nch == vin->nch &&
        flc->nsamples == vin->nsamples && oc < flc->nch && oi < flc->nsamples &&
        (long long)flc->plane[oc][oi] == ov) {
      report("output-contract: reconstructed sample escapes FitsSInt(bps), corroborated by libFLAC",
             size, vin, flc, ffm);
      fprintf(stderr,
              "  channel %d index %ld: value=%lld outside [-2^%d, 2^%d) (bps=%d, libFLAC-"
              "corroborated -- the correct per-spec reconstruction is out of range)\n",
              oc, oi, ov, vin->bps - 1, vin->bps - 1, vin->bps);
      oracle_dump_write("wide_output_contract", data, size);
      if (strict >= FUZZ_STRICT_ACCEPT)
        FUZZ_ABORT();
      return WD_OUT_OF_CONTRACT;
    }
  }

  if (flc_audio && ffm_audio) {
    if (wide_cmp(flc, ffm, NULL, NULL) != CMP_EQUAL) {
      /* the two references disagree with each other: no consensus to hold Vinyl
       * to. Catalogue; never abort on a referee split. */
      oracle_dump_write("wide_ref_disagree", data, size);
      return WD_REF_DISAGREE;
    }
    /* reference CONSENSUS: compare Vinyl to it. */
    int c = 0;
    long i = 0;
    switch (wide_cmp(vin, flc, &c, &i)) {
      case CMP_EQUAL:
        /* Vinyl matches the two-reference consensus and (checked above) is in
         * contract -- a clean pass. */
        return WD_ALL_OK;
      case CMP_DIFF:
        /* An out-of-contract Vinyl sample that both references merely WRAPPED is
         * the output-contract finding, not a consensus divergence: at bps 24/32
         * libFLAC (int32) and ffmpeg wrap identically, forming a false consensus
         * Vinyl (exact ℤ) differs from. Route to the output-contract class. */
        if (val_out_of_contract(vin->plane[c][i], vin->bps)) {
          report("output-contract: reconstruction escapes FitsSInt(bps); both references wrapped it",
                 size, vin, flc, ffm);
          fprintf(stderr, "  channel %d index %ld: vinyl=%lld ref=%lld (bps=%d, container-wrap)\n", c,
                  i, (long long)vin->plane[c][i], (long long)flc->plane[c][i], vin->bps);
          oracle_dump_write("wide_output_contract", data, size);
          if (strict >= FUZZ_STRICT_ACCEPT)
            FUZZ_ABORT();
          return WD_OUT_OF_CONTRACT;
        }
        /* Phase 8A wrap-congruence (defensive): Vinyl and the two-reference
         * consensus differ at this sample, but are CONGRUENT mod 2^bps -- a
         * fixed-width container wrap, not a decode divergence. Unsigned mask
         * arithmetic only (never signed %), guarded 0 < bps < 32. Congruence is
         * exact for the stereo-decorrelation class at EVERY index and for the LPC
         * class at the FIRST divergent index (which is exactly the index wide_cmp
         * reports here) -- so nobody should "improve" this to require congruence
         * at all indices. Catalogue to its own bucket, never abort. */
        if (vin->bps > 0 && vin->bps < 32) {
          uint64_t m = ((uint64_t)1 << vin->bps) - 1;
          if ((((uint64_t)(vin->plane[c][i] - flc->plane[c][i])) & m) == 0) {
            oracle_dump_write("wide_wrap_divergence", data, size);
            return WD_REF_DISAGREE;
          }
        }
        /* Stream-level RFC-invalidity witness (the decode-sample-divergence-highbps
         * class, findings/): if the frame containing sample i reconstructs a subframe
         * OUT OF ITS CODED DEPTH at or before i -- computed exactly from the bitstream,
         * no decoder involved -- then RFC 9639 §5 leaves its decoding unspecified.
         * Vinyl folds to the coded depth (P1 `Lpc.restoreA` wrap), the references keep
         * container width with non-clean arithmetic at bps 17-31 (the mod-2^bps test
         * above cannot see it), so a consensus here is two implementations agreeing on
         * unspecified behaviour, not a Vinyl defect. Catalogue with the witness; the
         * check cannot fire on a valid stream, so it can never mask a real divergence. */
        {
          FlacOob oob;
          if (flac_reconstruct_oob_at(data, size, vin->nch, vin->bps, i, &oob)) {
            fprintf(stderr,
                    "[wide] sample divergence at ch%d[%ld] on an RFC-INVALID stream: frame %zu "
                    "subframe %d reconstructs %lld at local sample %ld, outside its %d-bit coded "
                    "depth (RFC 9639 §5: unspecified) -- decode-sample-divergence-highbps class, "
                    "catalogued\n",
                    c, i, oob.frame, oob.channel, (long long)oob.value, oob.index, oob.depth);
            oracle_dump_write("wide_sample_diff_oob_coded", data, size);
            return WD_REF_DISAGREE;
          }
        }
        report("decoded SAMPLE differs -- Vinyl vs a libFLAC+ffmpeg consensus", size, vin, flc,
               ffm);
        fprintf(stderr, "  channel %d index %ld: vinyl=%lld consensus=%lld (bps=%d)\n", c, i,
                (long long)vin->plane[c][i], (long long)flc->plane[c][i], vin->bps);
        oracle_dump_write("wide_sample_diff", data, size);
        FUZZ_ABORT(); /* two independent decoders agree; Vinyl is the outlier */
      default:   /* geometry: Vinyl's sample count/channels differ from consensus */
        report("geometry differs -- Vinyl vs a libFLAC+ffmpeg consensus", size, vin, flc, ffm);
        oracle_dump_write("wide_geom_diff", data, size);
        if (strict >= FUZZ_STRICT_LEN)
          FUZZ_ABORT();
        return WD_GEOM;
    }
  }

  /* Only one reference produced audio: an UNCORROBORATED 2-way comparison. On a
   * mutated stream a lone disagreement is frequently a predictor-wrap
   * class, so catalogue + dump by default and escalate to abort
   * only under FUZZ_STRICT (must-agree / regression runs). */
  const Wide *R = flc_audio ? flc : (ffm_audio ? ffm : NULL);
  if (!R)
    return WD_SKIP; /* no reference produced comparable audio */
  int c = 0;
  long i = 0;
  switch (wide_cmp(vin, R, &c, &i)) {
    case CMP_EQUAL:
      /* Exactly ONE reference produced audio and Vinyl matched it: the OTHER
       * reference rejected/produced nothing, so this is a referee SPLIT, not a
       * corroborated pass. Reporting WD_ALL_OK here hides exactly the "one
       * referee accepts, one rejects" case the second referee was added to
       * surface. Tally as a disagreement and dump so the split rate is visible. */
      /* Phase 6D: if ffmpeg was gated out precisely BECAUSE Vinyl and libFLAC
       * already agreed bit-for-bit (g_ff_skipped), this is that same clean
       * consensus, not a referee split -- ffmpeg could only have catalogued a
       * ref_disagree, never flipped a verdict. Report the pass. */
      if (g_ff_skipped)
        return WD_ALL_OK;
      oracle_dump_write("wide_ref_split", data, size);
      return WD_REF_DISAGREE;
    case CMP_DIFF:
      /* Out-of-contract Vinyl sample the lone reference merely wrapped -> the
       * output-contract finding, not a decode divergence (the s41 single-ref
       * false-abort). */
      if (val_out_of_contract(vin->plane[c][i], vin->bps)) {
        report("output-contract: reconstruction escapes FitsSInt(bps); the reference wrapped it",
               size, vin, flc, ffm);
        fprintf(stderr, "  channel %d index %ld: vinyl=%lld %s=%lld (bps=%d, container-wrap)\n", c, i,
                (long long)vin->plane[c][i], R->name, (long long)R->plane[c][i], vin->bps);
        oracle_dump_write("wide_output_contract", data, size);
        if (strict >= FUZZ_STRICT_ACCEPT)
          FUZZ_ABORT();
        return WD_OUT_OF_CONTRACT;
      }
      report("decoded SAMPLE differs -- Vinyl vs a single reference (uncorroborated)", size, vin,
             flc, ffm);
      fprintf(stderr, "  channel %d index %ld: vinyl=%lld %s=%lld (bps=%d)\n", c, i,
              (long long)vin->plane[c][i], R->name, (long long)R->plane[c][i], vin->bps);
      oracle_dump_write("wide_sample_diff_1ref", data, size);
      if (strict >= FUZZ_STRICT_LEN)
        FUZZ_ABORT();
      return WD_REF_DISAGREE;
    default:
      oracle_dump_write("wide_geom_diff_1ref", data, size);
      if (strict >= FUZZ_STRICT_LEN)
        FUZZ_ABORT();
      return WD_GEOM;
  }
}
