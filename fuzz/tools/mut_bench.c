/* mut_bench -- measures what the CRC-aware mutator actually buys.
 *
 *   mut_bench selftest              CRC vectors + generator/repair round trip
 *   mut_bench gen DIR N [SEED]      write N generated CRC-correct seeds
 *   mut_bench rate DIR N [SEED]     libFLAC acceptance rate, plain vs CRC-aware
 *
 * "Acceptance" is measured against libFLAC 1.4.2 directly (not through
 * common/flac_api.c) so the *reason* for rejection is visible: this build owns
 * the error callback and tallies LOST_SYNC / BAD_HEADER / FRAME_CRC_MISMATCH /
 * UNPARSEABLE, which is exactly the gate the CRC repair is supposed to open.
 *
 * Links libFLAC only -- no Lean, no libFuzzer. The mutator's LLVMFuzzerMutate
 * reference is weak, so here it stays NULL and every mutation is ours. */
#include <dirent.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#include "../common/flac_bits.h"
#include "../common/flac_struct.h"
#include "../common/rng.h"
#include "FLAC/stream_decoder.h"

#define MAXBUF (1 << 20)

/* ------------------------------------------------- minimal libFLAC harness */
typedef struct {
  const uint8_t *in;
  size_t n, pos;
  unsigned long frames;
  int err_lost_sync, err_bad_header, err_crc, err_unparseable, err_other;
} Dec;

static Dec d;

static FLAC__StreamDecoderReadStatus rd(const FLAC__StreamDecoder *x, FLAC__byte b[], size_t *cnt,
                                        void *c) {
  (void)x;
  (void)c;
  if (d.pos >= d.n) {
    *cnt = 0;
    return FLAC__STREAM_DECODER_READ_STATUS_END_OF_STREAM;
  }
  size_t k = d.n - d.pos;
  if (k > *cnt)
    k = *cnt;
  memcpy(b, d.in + d.pos, k);
  d.pos += k;
  *cnt = k;
  return FLAC__STREAM_DECODER_READ_STATUS_CONTINUE;
}
static FLAC__bool eof(const FLAC__StreamDecoder *x, void *c) {
  (void)x;
  (void)c;
  return d.pos >= d.n;
}
static FLAC__StreamDecoderWriteStatus wr(const FLAC__StreamDecoder *x, const FLAC__Frame *f,
                                         const FLAC__int32 *const b[], void *c) {
  (void)x;
  (void)f;
  (void)b;
  (void)c;
  d.frames++;
  return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}
static void mt(const FLAC__StreamDecoder *x, const FLAC__StreamMetadata *m, void *c) {
  (void)x;
  (void)m;
  (void)c;
}
static void er(const FLAC__StreamDecoder *x, FLAC__StreamDecoderErrorStatus s, void *c) {
  (void)x;
  (void)c;
  switch (s) {
  case FLAC__STREAM_DECODER_ERROR_STATUS_LOST_SYNC:
    d.err_lost_sync++;
    break;
  case FLAC__STREAM_DECODER_ERROR_STATUS_BAD_HEADER:
    d.err_bad_header++;
    break;
  case FLAC__STREAM_DECODER_ERROR_STATUS_FRAME_CRC_MISMATCH:
    d.err_crc++;
    break;
  case FLAC__STREAM_DECODER_ERROR_STATUS_UNPARSEABLE_STREAM:
    d.err_unparseable++;
    break;
  default:
    d.err_other++;
    break;
  }
}

static FLAC__StreamDecoder *g_dec;

/* Returns the number of frames libFLAC decoded; error counters live in `d`. */
static unsigned long try_decode(const uint8_t *in, size_t n, int *clean) {
  if (!g_dec)
    g_dec = FLAC__stream_decoder_new();
  d.in = in;
  d.n = n;
  d.pos = 0;
  d.frames = 0;
  d.err_lost_sync = d.err_bad_header = d.err_crc = d.err_unparseable = d.err_other = 0;
  FLAC__stream_decoder_set_md5_checking(g_dec, false);
  if (FLAC__stream_decoder_init_stream(g_dec, rd, NULL, NULL, NULL, eof, wr, mt, er, NULL) !=
      FLAC__STREAM_DECODER_INIT_STATUS_OK) {
    FLAC__stream_decoder_finish(g_dec);
    *clean = 0;
    return 0;
  }
  FLAC__bool ok = FLAC__stream_decoder_process_until_end_of_stream(g_dec);
  FLAC__StreamDecoderState st = FLAC__stream_decoder_get_state(g_dec);
  FLAC__stream_decoder_finish(g_dec);
  int nerr = d.err_lost_sync + d.err_bad_header + d.err_crc + d.err_unparseable + d.err_other;
  *clean = ok && !nerr && st == FLAC__STREAM_DECODER_END_OF_STREAM && d.frames > 0;
  return d.frames;
}

/* ------------------------------------------------------------ corpus load */
typedef struct {
  uint8_t *p;
  size_t n;
} Blob;

static size_t load_dir(const char *dir, Blob *out, size_t max, size_t cap_bytes) {
  DIR *h = opendir(dir);
  if (!h) {
    fprintf(stderr, "cannot open %s\n", dir);
    exit(1);
  }
  struct dirent *e;
  size_t k = 0;
  while (k < max && (e = readdir(h))) {
    if (e->d_name[0] == '.')
      continue;
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", dir, e->d_name);
    struct stat sb;
    if (stat(path, &sb) || !S_ISREG(sb.st_mode) || sb.st_size == 0 ||
        (size_t)sb.st_size > cap_bytes)
      continue;
    FILE *f = fopen(path, "rb");
    if (!f)
      continue;
    out[k].p = malloc((size_t)sb.st_size);
    out[k].n = fread(out[k].p, 1, (size_t)sb.st_size, f);
    fclose(f);
    if (out[k].n)
      k++;
    else
      free(out[k].p);
  }
  closedir(h);
  return k;
}

/* ----------------------------------------------------------- plain mutator
 * A stand-in for libFuzzer's built-in byte mutator: same op mix (bit flip,
 * byte set, arithmetic, interesting value, chunk copy, insert/erase), no
 * awareness of FLAC structure. This is the baseline the CRC-aware mutator is
 * measured against. */
/* PRNG is the shared rng.h (same xorshift64 constants); r32 kept as a local
 * alias so the plain-mutator op mix below reads unchanged. */
static uint32_t r32(uint64_t *s) { return rng_next32(s); }

static size_t plain_mutate(uint8_t *b, size_t n, size_t max, uint64_t *rng) {
  static const uint8_t interesting[8] = {0x00, 0x01, 0x0F, 0x10, 0x7F, 0x80, 0xFE, 0xFF};
  unsigned ops = 1 + r32(rng) % 8;
  for (unsigned i = 0; i < ops && n; i++) {
    size_t p = r32(rng) % n;
    switch (r32(rng) % 8) {
    case 0:
      b[p] ^= (uint8_t)(1u << (r32(rng) & 7));
      break;
    case 1:
      b[p] = (uint8_t)r32(rng);
      break;
    case 2:
      b[p] += (uint8_t)(1 + r32(rng) % 15) * ((r32(rng) & 1) ? 1 : -1);
      break;
    case 3:
      b[p] = interesting[r32(rng) & 7];
      break;
    case 4: {
      size_t len = 1 + r32(rng) % 16, src = r32(rng) % n;
      if (src + len > n)
        len = n - src;
      if (p + len > n)
        len = n - p;
      memmove(b + p, b + src, len);
      break;
    }
    case 5: {
      size_t len = 1 + r32(rng) % 16;
      if (p + len > n)
        len = n - p;
      memset(b + p, (uint8_t)r32(rng), len);
      break;
    }
    case 6: { /* erase */
      size_t len = 1 + r32(rng) % 16;
      if (p + len > n)
        len = n - p;
      memmove(b + p, b + p + len, n - p - len);
      n -= len;
      break;
    }
    default: { /* insert */
      size_t len = 1 + r32(rng) % 16;
      if (n + len > max)
        break;
      memmove(b + p + len, b + p, n - p);
      memset(b + p, (uint8_t)r32(rng), len);
      n += len;
      break;
    }
    }
  }
  return n;
}

/* ------------------------------------------------------------------ modes */
static int selftest(void) {
  int bad = 0;
  bad += flac_bits_selftest(); /* shared bit/CRC layer known-answer vectors */
  uint8_t v[] = "123456789";
  uint8_t c8 = flac_crc8(v, 9);
  uint16_t c16 = flac_crc16(v, 9);
  printf("crc8(\"123456789\")  = 0x%02x (want 0xf4)   %s\n", c8, c8 == 0xF4 ? "OK" : "FAIL");
  printf("crc16(\"123456789\") = 0x%04x (want 0xfee8) %s\n", c16, c16 == 0xFEE8 ? "OK" : "FAIL");
  bad += (c8 != 0xF4) + (c16 != 0xFEE8);

  uint8_t *b = malloc(MAXBUF);
  uint64_t rng = 0xC0FFEE1234567ULL;
  unsigned ok = 0, tried = 0, repaired_same = 0;
  for (int i = 0; i < 400; i++) {
    size_t n = flac_generate(b, MAXBUF, &rng, 1);
    if (!n)
      continue;
    tried++;
    int clean;
    try_decode(b, n, &clean);
    ok += clean != 0;
    /* the structural walk must agree with the generator: repairing a freshly
     * generated stream must not change a single byte */
    uint8_t *cp = malloc(n);
    memcpy(cp, b, n);
    flac_rescan_repair(cp, n);
    repaired_same += memcmp(cp, b, n) == 0;
    free(cp);
  }
  printf("generator: %u/%u streams accepted by libFLAC, %u/%u byte-identical after repair\n", ok,
         tried, repaired_same, tried);
  bad += (ok != tried) + (repaired_same != tried);
  free(b);
  return bad;
}

static int gen_corpus(const char *dir, int count, uint64_t seed) {
  if (mkdir(dir, 0755) != 0 && errno != EEXIST) {
    fprintf(stderr, "cannot create %s: %s\n", dir, strerror(errno));
    return 1;
  }
  uint8_t *b = malloc(MAXBUF);
  uint64_t rng = seed;
  int written = 0;
  for (int i = 0; i < count * 8 && written < count; i++) {
    size_t n = flac_generate(b, MAXBUF, &rng, 1);
    if (!n || n > 200000)
      continue;
    char path[4096];
    snprintf(path, sizeof path, "%s/gen_%05d_%zu", dir, written, n);
    FILE *f = fopen(path, "wb");
    if (!f) {
      fprintf(stderr, "cannot open %s: %s\n", path, strerror(errno));
      continue;
    }
    fwrite(b, 1, n, f);
    fclose(f);
    written++;
  }
  free(b);
  printf("wrote %d generated seeds to %s\n", written, dir);
  return 0;
}

typedef struct {
  unsigned long tot, clean, any_frame;
  unsigned long lost_sync, bad_header, crc_mismatch, unparseable;
} Tally;

static void tally(Tally *t, const uint8_t *b, size_t n) {
  int clean;
  unsigned long fr = try_decode(b, n, &clean);
  t->tot++;
  t->clean += clean != 0;
  t->any_frame += fr > 0;
  t->lost_sync += d.err_lost_sync > 0;
  t->bad_header += d.err_bad_header > 0;
  t->crc_mismatch += d.err_crc > 0;
  t->unparseable += d.err_unparseable > 0;
}

static void show(const char *name, const Tally *t) {
  printf("%-18s n=%-7lu accepted=%-7lu (%5.2f%%)  produced>=1 frame=%-7lu (%5.2f%%)\n", name,
         t->tot, t->clean, t->tot ? 100.0 * t->clean / t->tot : 0.0, t->any_frame,
         t->tot ? 100.0 * t->any_frame / t->tot : 0.0);
  printf("%-18s   inputs hitting: LOST_SYNC=%lu BAD_HEADER=%lu FRAME_CRC_MISMATCH=%lu "
         "UNPARSEABLE=%lu\n",
         "", t->lost_sync, t->bad_header, t->crc_mismatch, t->unparseable);
}

static int rate(const char *dir, int iters, uint64_t seed, size_t maxlen) {
  static Blob seeds[4096];
  size_t ns = load_dir(dir, seeds, 4096, maxlen);
  if (!ns) {
    fprintf(stderr, "no usable seeds in %s\n", dir);
    return 1;
  }
  printf("seeds: %zu from %s (<= %zu bytes)\n", ns, dir, maxlen);

  Tally base = {0}, plain = {0}, crc = {0};
  uint8_t *b = malloc(maxlen + 64);
  uint64_t rng = seed;
  for (size_t i = 0; i < ns; i++)
    tally(&base, seeds[i].p, seeds[i].n);

  uint64_t r1 = seed, r2 = seed; /* same stream of seed choices for both arms */
  for (int i = 0; i < iters; i++) {
    size_t k = r32(&rng) % ns;
    memcpy(b, seeds[k].p, seeds[k].n);
    tally(&plain, b, plain_mutate(b, seeds[k].n, maxlen, &r1));
    memcpy(b, seeds[k].p, seeds[k].n);
    tally(&crc, b, flac_mutate(b, seeds[k].n, maxlen, &r2));
  }
  show("seed corpus", &base);
  show("plain mutation", &plain);
  show("CRC-aware mutation", &crc);
  printf("\nacceptance ratio (CRC-aware / plain) = %.1fx\n",
         plain.clean ? (double)crc.clean / plain.clean : 0.0);
  free(b);
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s selftest | gen DIR N [SEED] | rate DIR N [SEED] [MAXLEN]\n",
            argv[0]);
    return 2;
  }
  if (!strcmp(argv[1], "selftest"))
    return selftest();
  if (!strcmp(argv[1], "gen") && argc >= 4)
    return gen_corpus(argv[2], atoi(argv[3]), argc > 4 ? strtoull(argv[4], 0, 0) : 0x9E3779B97F4A7C15ULL);
  if (!strcmp(argv[1], "rate") && argc >= 4)
    return rate(argv[2], atoi(argv[3]), argc > 4 ? strtoull(argv[4], 0, 0) : 0x123456789ABCDEFULL,
                argc > 5 ? (size_t)strtoull(argv[5], 0, 0) : 16384);
  fprintf(stderr, "bad arguments\n");
  return 2;
}
