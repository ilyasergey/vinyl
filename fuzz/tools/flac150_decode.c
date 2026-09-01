/* flac150_decode -- decode a FLAC file with libFLAC 1.5.0 and print an accept/reject
 * verdict plus the decoded geometry. Linked against build/lib/libflac.plain150.a (the
 * SEPARATE 1.5.0 referee, built by scripts/build_flac150.sh), it is the cross-version
 * counterpart to the fleet's 1.4.2 decode: run both on the same stream and a differing
 * verdict is an accept-set shift between libFLAC versions (e.g. 1.5.0 rejects block size
 * 65536, which 1.4.2 accepts). Prints one line to stdout and exits 0 on accept, 1 on
 * reject, 2 on usage error -- so a script can diff verdicts across versions.
 *
 *   flac150_decode <file.flac>
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "FLAC/stream_decoder.h"

typedef struct {
  const uint8_t *in;
  size_t n, pos;
  int err, got, bps, ch, sr;
  int si_sr, sr_mismatch;
  unsigned long samples;
} Ctx;
static Ctx c;

static FLAC__StreamDecoderReadStatus rd(const FLAC__StreamDecoder *d, FLAC__byte b[], size_t *bytes,
                                        void *u) {
  (void)d;
  (void)u;
  if (c.pos >= c.n) {
    *bytes = 0;
    return FLAC__STREAM_DECODER_READ_STATUS_END_OF_STREAM;
  }
  size_t k = c.n - c.pos;
  if (k > *bytes)
    k = *bytes;
  memcpy(b, c.in + c.pos, k);
  c.pos += k;
  *bytes = k;
  return FLAC__STREAM_DECODER_READ_STATUS_CONTINUE;
}
static FLAC__bool eof(const FLAC__StreamDecoder *d, void *u) {
  (void)d;
  (void)u;
  return c.pos >= c.n;
}
static FLAC__StreamDecoderWriteStatus wr(const FLAC__StreamDecoder *d, const FLAC__Frame *f,
                                         const FLAC__int32 *const b[], void *u) {
  (void)d;
  (void)b;
  (void)u;
  if (c.si_sr && (int)f->header.sample_rate != c.si_sr) {
    c.sr_mismatch = 1;
    return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
  }
  if (!c.got) {
    c.got = 1;
    c.bps = (int)f->header.bits_per_sample;
    c.ch = (int)f->header.channels;
    c.sr = (int)f->header.sample_rate;
  }
  c.samples += f->header.blocksize;
  return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}
static void meta(const FLAC__StreamDecoder *d, const FLAC__StreamMetadata *m, void *u) {
  (void)d;
  (void)u;
  if (m->type == FLAC__METADATA_TYPE_STREAMINFO)
    c.si_sr = (int)m->data.stream_info.sample_rate;
}
static void err(const FLAC__StreamDecoder *d, FLAC__StreamDecoderErrorStatus s, void *u) {
  (void)d;
  (void)s;
  (void)u;
  c.err = 1;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <file.flac>\n", argv[0]);
    return 2;
  }
  FILE *fp = fopen(argv[1], "rb");
  if (!fp) {
    fprintf(stderr, "flac150_decode: cannot open %s\n", argv[1]);
    return 2;
  }
  /* Read the WHOLE file -- a fixed prefix buffer would judge any stream longer than
   * the cap on a truncated prefix, manufacturing bogus accept/reject verdicts (and thus
   * false cross-version "shifts") on the large-input corpora. */
  if (fseek(fp, 0, SEEK_END) != 0) {
    fprintf(stderr, "flac150_decode: cannot seek %s\n", argv[1]);
    fclose(fp);
    return 2;
  }
  long fsz = ftell(fp);
  rewind(fp);
  if (fsz < 0) {
    fclose(fp);
    return 2;
  }
  uint8_t *buf = malloc((size_t)fsz ? (size_t)fsz : 1);
  if (!buf) {
    fclose(fp);
    return 2;
  }
  size_t n = fread(buf, 1, (size_t)fsz, fp);
  fclose(fp);
  if (n != (size_t)fsz) {
    fprintf(stderr, "flac150_decode: short read %s (%zu of %ld)\n", argv[1], n, fsz);
    free(buf);
    return 2;
  }

  memset(&c, 0, sizeof c);
  c.in = buf;
  c.n = n;
  FLAC__StreamDecoder *dec = FLAC__stream_decoder_new();
  if (!dec) {
    printf("reject reason=decoder_new_failed\n");
    return 1;
  }
  FLAC__stream_decoder_set_md5_checking(dec, false);
  int ok = FLAC__stream_decoder_init_stream(dec, rd, NULL, NULL, NULL, eof, wr, meta, err, NULL) ==
           FLAC__STREAM_DECODER_INIT_STATUS_OK;
  if (ok)
    ok = FLAC__stream_decoder_process_until_end_of_stream(dec);
  FLAC__StreamDecoderState st = FLAC__stream_decoder_get_state(dec);
  FLAC__stream_decoder_finish(dec);
  FLAC__stream_decoder_delete(dec);

  int accept = ok && !c.err && !c.sr_mismatch && c.got &&
               st == FLAC__STREAM_DECODER_END_OF_STREAM;
  free(buf);
  if (accept) {
    printf("accept flac=%s bps=%d ch=%d sr=%d samples=%lu\n", FLAC__VERSION_STRING, c.bps, c.ch,
           c.sr, c.samples);
    return 0;
  }
  printf("reject flac=%s err=%d sr_mismatch=%d got=%d state=%s\n", FLAC__VERSION_STRING, c.err,
         c.sr_mismatch, c.got, FLAC__StreamDecoderStateString[st]);
  return 1;
}
