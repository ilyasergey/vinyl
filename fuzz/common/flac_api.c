#include "flac_api.h"

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "FLAC/stream_decoder.h"

typedef struct {
  const uint8_t *in;
  size_t n, pos;
  uint8_t *out; /* wrapper-owned, reused, geometric growth */
  size_t cap, len;
  int err, skip, saw_meta, got_frame;
  int bps, ch, sr;          /* from the first decoded frame */
  int m_bps, m_ch, m_sr;    /* from STREAMINFO */
} Ctx;

static Ctx g;
static FLAC__StreamDecoder *g_dec;

static void out_ensure(size_t need) {
  if (need > g.cap) {
    size_t cap = g.cap ? g.cap : (1u << 16);
    while (cap < need)
      cap *= 2;
    uint8_t *p = realloc(g.out, cap);
    if (!p)
      _exit(1);
    g.out = p;
    g.cap = cap;
  }
}

static FLAC__StreamDecoderReadStatus read_cb(const FLAC__StreamDecoder *dec, FLAC__byte buffer[],
                                             size_t *bytes, void *client) {
  (void)dec;
  (void)client;
  if (g.pos >= g.n) {
    *bytes = 0;
    return FLAC__STREAM_DECODER_READ_STATUS_END_OF_STREAM;
  }
  size_t k = g.n - g.pos;
  if (k > *bytes)
    k = *bytes;
  memcpy(buffer, g.in + g.pos, k);
  g.pos += k;
  *bytes = k;
  return FLAC__STREAM_DECODER_READ_STATUS_CONTINUE;
}

static FLAC__bool eof_cb(const FLAC__StreamDecoder *dec, void *client) {
  (void)dec;
  (void)client;
  return g.pos >= g.n;
}

static FLAC__StreamDecoderWriteStatus write_cb(const FLAC__StreamDecoder *dec,
                                               const FLAC__Frame *frame,
                                               const FLAC__int32 *const buffer[], void *client) {
  (void)dec;
  (void)client;
  unsigned bps = frame->header.bits_per_sample;
  unsigned ch = frame->header.channels;
  unsigned bs = frame->header.blocksize;
  if (g.skip || bps != 16) {
    g.skip = 1;
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }
  if (!g.got_frame) {
    g.got_frame = 1;
    g.bps = (int)bps;
    g.ch = (int)ch;
    g.sr = (int)frame->header.sample_rate;
  } else if ((int)ch != g.ch || (int)bps != g.bps) {
    /* Mid-stream channel/bps change: a single interleaved s16 buffer cannot
     * represent it. Refuse, like the flac CLI does -> the decoder ends
     * FLAC__STREAM_DECODER_ABORTED and flac_decode reports DEC_REJECT. */
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }
  out_ensure(g.len + (size_t)bs * ch * 2);
  uint8_t *o = g.out + g.len;
  for (unsigned i = 0; i < bs; i++)
    for (unsigned c = 0; c < ch; c++) {
      FLAC__int32 v = buffer[c][i];
      *o++ = (uint8_t)(v & 0xff);
      *o++ = (uint8_t)((v >> 8) & 0xff);
    }
  g.len = (size_t)(o - g.out);
  return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}

static void meta_cb(const FLAC__StreamDecoder *dec, const FLAC__StreamMetadata *m, void *client) {
  (void)dec;
  (void)client;
  if (m->type == FLAC__METADATA_TYPE_STREAMINFO) {
    g.saw_meta = 1;
    g.m_bps = (int)m->data.stream_info.bits_per_sample;
    g.m_ch = (int)m->data.stream_info.channels;
    g.m_sr = (int)m->data.stream_info.sample_rate;
    if (g.m_bps != 16)
      g.skip = 1; /* mirror Vinyl's 16-bit-only gate */
  }
}

static void err_cb(const FLAC__StreamDecoder *dec, FLAC__StreamDecoderErrorStatus status,
                   void *client) {
  (void)dec;
  (void)status;
  (void)client;
  g.err = 1;
}

int flac_decode(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len, int *bps, int *ch,
                int *sr) {
  *pcm = NULL;
  *len = 0;
  *bps = *ch = *sr = 0;
  if (!g_dec) {
    g_dec = FLAC__stream_decoder_new();
    if (!g_dec)
      return DEC_REJECT;
  }
  g.in = in;
  g.n = n;
  g.pos = 0;
  g.len = 0;
  g.err = g.skip = g.saw_meta = g.got_frame = 0;
  g.bps = g.ch = g.sr = g.m_bps = g.m_ch = g.m_sr = 0;

  FLAC__stream_decoder_set_md5_checking(g_dec, false);
  if (FLAC__stream_decoder_init_stream(g_dec, read_cb, /*seek=*/NULL, /*tell=*/NULL,
                                       /*length=*/NULL, eof_cb, write_cb, meta_cb, err_cb,
                                       NULL) != FLAC__STREAM_DECODER_INIT_STATUS_OK) {
    FLAC__stream_decoder_finish(g_dec);
    return DEC_REJECT;
  }
  FLAC__bool ok = FLAC__stream_decoder_process_until_end_of_stream(g_dec);
  FLAC__StreamDecoderState st = FLAC__stream_decoder_get_state(g_dec);
  FLAC__stream_decoder_finish(g_dec);

  if (g.skip)
    return DEC_SKIP;
  /* success = clean end of stream, no error callback, and actual FLAC content
   * was seen (bare EOF on garbage also ends in END_OF_STREAM). */
  if (!ok || g.err || st != FLAC__STREAM_DECODER_END_OF_STREAM)
    return DEC_REJECT;
  if (!g.saw_meta && !g.got_frame)
    return DEC_REJECT;

  *pcm = g.out;
  *len = g.len;
  /* Prefer STREAMINFO values: that is where Vinyl reports its params from, so
   * the (bps,ch,sr) oracle compares like with like. Frame-derived values are
   * only used for headerless streams (which Vinyl rejects anyway). */
  if (g.saw_meta) {
    *bps = g.m_bps;
    *ch = g.m_ch;
    *sr = g.m_sr;
  } else {
    *bps = g.bps;
    *ch = g.ch;
    *sr = g.sr;
  }
  return DEC_OK;
}

/* ============ encoder wrappers (folded in from flac_encode_api.c) ============ */
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "FLAC/stream_encoder.h"

/* Wrapper-owned output + int32 conversion buffers, reused across calls. */
static uint8_t *e_out;
static size_t e_cap, e_len;
static FLAC__int32 *e_i32;
static size_t e_i32cap; /* in samples */
static FLAC__StreamEncoder *g_enc;

static void enc_out_ensure(size_t need) {
  if (need > e_cap) {
    size_t cap = e_cap ? e_cap : (1u << 16);
    while (cap < need)
      cap *= 2;
    uint8_t *p = realloc(e_out, cap);
    if (!p)
      _exit(1);
    e_out = p;
    e_cap = cap;
  }
}

static FLAC__StreamEncoderWriteStatus enc_write_cb(const FLAC__StreamEncoder *enc,
                                               const FLAC__byte buffer[], size_t bytes,
                                               uint32_t samples, uint32_t current_frame,
                                               void *client) {
  (void)enc;
  (void)samples;
  (void)current_frame;
  (void)client;
  enc_out_ensure(e_len + bytes);
  memcpy(e_out + e_len, buffer, bytes);
  e_len += bytes;
  return FLAC__STREAM_ENCODER_WRITE_STATUS_OK;
}

int flac_encode(const uint8_t *pcm, size_t n, int bs, int ch, int sr, int level, uint8_t **out,
                size_t *len) {
  *out = NULL;
  *len = 0;
  if (ch <= 0 || n % (2 * (size_t)ch) != 0)
    return ENC_REJECT;
  if (!g_enc) {
    g_enc = FLAC__stream_encoder_new();
    if (!g_enc)
      return ENC_REJECT;
  }
  size_t frames = n / (2 * (size_t)ch);
  e_len = 0;

  /* set_compression_level first: it presets the search knobs; blocksize is
   * not part of a level, we pin it afterwards. Subset off so parameter combos
   * Vinyl accepts (e.g. bs=65535 @ 44.1kHz) still produce genuine libFLAC
   * streams for the cross-decode oracle; sampleRate/blocksize hard limits
   * still apply and rejects are classified by the target. */
  int ok = FLAC__stream_encoder_set_compression_level(g_enc, (uint32_t)level) &&
           FLAC__stream_encoder_set_streamable_subset(g_enc, false) &&
           FLAC__stream_encoder_set_verify(g_enc, false) &&
           FLAC__stream_encoder_set_channels(g_enc, (uint32_t)ch) &&
           FLAC__stream_encoder_set_bits_per_sample(g_enc, 16) &&
           FLAC__stream_encoder_set_sample_rate(g_enc, (uint32_t)sr) &&
           FLAC__stream_encoder_set_blocksize(g_enc, (uint32_t)bs) &&
           FLAC__stream_encoder_set_total_samples_estimate(g_enc, (FLAC__uint64)frames);
  if (!ok) {
    FLAC__stream_encoder_finish(g_enc); /* restore UNINITIALIZED for reuse */
    return ENC_REJECT;
  }
  if (FLAC__stream_encoder_init_stream(g_enc, enc_write_cb, NULL, NULL, NULL, NULL) !=
      FLAC__STREAM_ENCODER_INIT_STATUS_OK) {
    FLAC__stream_encoder_finish(g_enc);
    return ENC_REJECT;
  }

  if (frames) {
    size_t samples = frames * (size_t)ch;
    if (samples > e_i32cap) {
      free(e_i32);
      e_i32cap = samples * 2;
      e_i32 = malloc(e_i32cap * sizeof(FLAC__int32));
      if (!e_i32)
        _exit(1);
    }
    for (size_t i = 0; i < samples; i++)
      e_i32[i] = (FLAC__int32)(int16_t)(pcm[2 * i] | (pcm[2 * i + 1] << 8));
    if (!FLAC__stream_encoder_process_interleaved(g_enc, e_i32, (uint32_t)frames)) {
      FLAC__stream_encoder_finish(g_enc);
      return ENC_REJECT;
    }
  }
  if (!FLAC__stream_encoder_finish(g_enc))
    return ENC_REJECT;

  *out = e_out;
  *len = e_len;
  return ENC_OK;
}

/* ============ strict flac -t validator (folded in from flac_validate.c) ============ */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "FLAC/stream_decoder.h"

/* Distinct from flac_api.c: MD5 checking is ON here, so FLAC__stream_decoder_
 * finish() returns false when the decoded audio's MD5 does not match STREAMINFO
 * -- exactly the check `flac -t` makes and the decode-diff oracle cannot. On top
 * of MD5, this wrapper implements the STREAMINFO-vs-frame consistency checks the
 * old no-op meta callback advertised but never performed (RFC 9639 §9.1). */
typedef struct {
  const uint8_t *in;
  size_t n, pos;
  uint8_t *out;
  size_t cap, len;
  int err, got_frame, bps, ch, sr, mixed;
  /* STREAMINFO (from the meta callback). */
  int si_seen, si_min_bs, si_max_bs, si_ch, si_bps, si_sr;
  unsigned long si_total;
  /* Framing observed so far. `prev_bs` is the block size of the most recent
   * frame; it is not known to be interior (and thus bound by minBlock) until a
   * further frame arrives, so the min-block check is applied one frame behind. */
  unsigned long frames, samples, frame_min_bs, frame_max_bs;
  unsigned prev_bs;
  int have_prev;
  const char *si_why; /* first STREAMINFO inconsistency, if any */
} VCtx;

static VCtx vg;
static FLAC__StreamDecoder *vg_dec;

static void si_fail(const char *why) {
  if (!vg.si_why)
    vg.si_why = why;
}

static void venc_out_ensure(size_t need) {
  if (need > vg.cap) {
    size_t cap = vg.cap ? vg.cap : (1u << 16);
    while (cap < need)
      cap *= 2;
    uint8_t *p = realloc(vg.out, cap);
    if (!p)
      _exit(1);
    vg.out = p;
    vg.cap = cap;
  }
}

static FLAC__StreamDecoderReadStatus vrd(const FLAC__StreamDecoder *d, FLAC__byte b[], size_t *bytes,
                                         void *c) {
  (void)d;
  (void)c;
  if (vg.pos >= vg.n) {
    *bytes = 0;
    return FLAC__STREAM_DECODER_READ_STATUS_END_OF_STREAM;
  }
  size_t k = vg.n - vg.pos;
  if (k > *bytes)
    k = *bytes;
  memcpy(b, vg.in + vg.pos, k);
  vg.pos += k;
  *bytes = k;
  return FLAC__STREAM_DECODER_READ_STATUS_CONTINUE;
}
static FLAC__bool veof(const FLAC__StreamDecoder *d, void *c) {
  (void)d;
  (void)c;
  return vg.pos >= vg.n;
}
static FLAC__StreamDecoderWriteStatus vwr(const FLAC__StreamDecoder *d, const FLAC__Frame *f,
                                          const FLAC__int32 *const b[], void *c) {
  (void)d;
  (void)c;
  unsigned bps = f->header.bits_per_sample, ch = f->header.channels, bs = f->header.blocksize;
  if (!vg.got_frame) {
    vg.got_frame = 1;
    vg.bps = (int)bps;
    vg.ch = (int)ch;
    vg.sr = (int)f->header.sample_rate;
  } else if ((int)ch != vg.ch || (int)bps != vg.bps) {
    vg.mixed = 1;
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }

  /* STREAMINFO-vs-frame consistency (RFC 9639 §9.1). */
  if (vg.si_seen) {
    if ((int)ch != vg.si_ch || (int)bps != vg.si_bps)
      si_fail("frame channels/bps disagree with STREAMINFO");
    if (vg.si_sr && (int)f->header.sample_rate != vg.si_sr)
      si_fail("frame sample rate disagrees with STREAMINFO");
    if ((int)bs > vg.si_max_bs)
      si_fail("frame block size exceeds STREAMINFO maximum");
    /* The previous frame is now known to be non-last -> it must meet minBlock. */
    if (vg.have_prev && (int)vg.prev_bs < vg.si_min_bs)
      si_fail("interior frame block size below STREAMINFO minimum");
  }
  vg.prev_bs = bs;
  vg.have_prev = 1;
  vg.frames++;
  vg.samples += bs;
  if (!vg.frame_min_bs || bs < vg.frame_min_bs)
    vg.frame_min_bs = bs;
  if (bs > vg.frame_max_bs)
    vg.frame_max_bs = bs;

  if (bps != 16)
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  venc_out_ensure(vg.len + (size_t)bs * ch * 2);
  uint8_t *o = vg.out + vg.len;
  for (unsigned i = 0; i < bs; i++)
    for (unsigned cc = 0; cc < ch; cc++) {
      FLAC__int32 v = b[cc][i];
      *o++ = (uint8_t)(v & 0xff);
      *o++ = (uint8_t)((v >> 8) & 0xff);
    }
  vg.len = (size_t)(o - vg.out);
  return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}
static void vmt(const FLAC__StreamDecoder *d, const FLAC__StreamMetadata *m, void *c) {
  (void)d;
  (void)c;
  if (m->type != FLAC__METADATA_TYPE_STREAMINFO)
    return;
  const FLAC__StreamMetadata_StreamInfo *si = &m->data.stream_info;
  vg.si_seen = 1;
  vg.si_min_bs = (int)si->min_blocksize;
  vg.si_max_bs = (int)si->max_blocksize;
  vg.si_ch = (int)si->channels;
  vg.si_bps = (int)si->bits_per_sample;
  vg.si_sr = (int)si->sample_rate;
  vg.si_total = (unsigned long)si->total_samples;
  if (si->min_blocksize < 16 || si->max_blocksize < 16 ||
      si->min_blocksize > si->max_blocksize)
    si_fail("STREAMINFO min/max block size out of range or inverted");
}
static void ver(const FLAC__StreamDecoder *d, FLAC__StreamDecoderErrorStatus s, void *c) {
  (void)d;
  (void)s;
  (void)c;
  vg.err = 1;
}

int flac_validate_strict(const uint8_t *flac, size_t flen, const uint8_t *pcm, size_t plen,
                         FlacValidation *v) {
  memset(v, 0, sizeof *v);
  if (!vg_dec) {
    vg_dec = FLAC__stream_decoder_new();
    if (!vg_dec) {
      v->why = "decoder alloc failed";
      return 0;
    }
  }
  memset(&vg, 0, sizeof vg);
  vg.in = flac;
  vg.n = flen;

  FLAC__stream_decoder_set_md5_checking(vg_dec, true); /* the whole point */
  if (FLAC__stream_decoder_init_stream(vg_dec, vrd, NULL, NULL, NULL, veof, vwr, vmt, ver, NULL) !=
      FLAC__STREAM_DECODER_INIT_STATUS_OK) {
    FLAC__stream_decoder_finish(vg_dec);
    v->why = "init failed";
    return 0;
  }
  /* libFLAC delivers STREAMINFO to the metadata callback by default (as
   * flac_api.c's meta_cb relies on); no set_metadata_respond needed. */
  FLAC__bool ok = FLAC__stream_decoder_process_until_end_of_stream(vg_dec);
  FLAC__StreamDecoderState st = FLAC__stream_decoder_get_state(vg_dec);
  /* finish() returns false when md5 checking is on and the MD5 mismatched. */
  FLAC__bool md5 = FLAC__stream_decoder_finish(vg_dec);

  /* totalSamples consistency (0 == "unknown", skip). */
  if (vg.si_seen && vg.si_total && vg.si_total != vg.samples)
    si_fail("STREAMINFO totalSamples != decoded sample count");

  v->decoded_len = vg.len;
  v->bps = vg.bps;
  v->ch = vg.ch;
  v->sr = vg.sr;
  v->si_min_bs = vg.si_min_bs;
  v->si_max_bs = vg.si_max_bs;
  v->si_ch = vg.si_ch;
  v->si_bps = vg.si_bps;
  v->si_sr = vg.si_sr;
  v->si_total = vg.si_total;
  v->frames = vg.frames;
  v->samples = vg.samples;
  v->frame_min_bs = vg.frame_min_bs;
  v->frame_max_bs = vg.frame_max_bs;
  /* C1: a metadata-only stream (0 frames, plen==0) is a legal FLAC file -- the
   * STREAMINFO is present, no error fired, and there is simply no audio. Do not
   * require a frame. */
  v->decoded_ok =
      ok && !vg.err && st == FLAC__STREAM_DECODER_END_OF_STREAM && (vg.got_frame || vg.si_seen);
  v->md5_ok = md5;
  v->streaminfo_ok = (vg.si_why == NULL);

  if (vg.mixed) {
    v->why = "mid-stream channel/bps change";
    return 0;
  }
  if (!v->decoded_ok) {
    v->why = "libFLAC did not cleanly decode Vinyl's stream";
    return 0;
  }
  if (!v->md5_ok) {
    v->why = "STREAMINFO MD5 does not match the decoded audio";
    return 0;
  }
  if (!v->streaminfo_ok) {
    v->why = vg.si_why;
    return 0;
  }
  if (v->decoded_len != plen || (plen && memcmp(vg.out, pcm, plen) != 0)) {
    v->why = "decoded audio is not the input PCM";
    return 0;
  }
  return 1;
}

void flac_validate_report(FILE *o, const FlacValidation *v, const uint8_t *flac, size_t flen) {
  (void)flac;
  fprintf(o,
          "\n[INVALID OUTPUT] %s\n"
          "  stream=%zuB decoded_ok=%d md5_ok=%d streaminfo_ok=%d decoded_len=%zu bps=%d ch=%d "
          "sr=%d\n"
          "  STREAMINFO: minBlk=%d maxBlk=%d ch=%d bps=%d sr=%d total=%lu\n"
          "  frames=%lu samples=%lu observed blockSize=[%lu,%lu]\n",
          v->why ? v->why : "(unknown)", flen, v->decoded_ok, v->md5_ok, v->streaminfo_ok,
          v->decoded_len, v->bps, v->ch, v->sr, v->si_min_bs, v->si_max_bs, v->si_ch, v->si_bps,
          v->si_sr, v->si_total, v->frames, v->samples, v->frame_min_bs, v->frame_max_bs);
}
