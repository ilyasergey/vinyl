#include "buckets.h"

#include <dirent.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "fuzz_target.h" /* fuzz_target_info.input_kind -> reproducer extension (5C) */

/* ---- SHA-256 (compact, public-domain style) -- content-addressed reproducer
 * names, so O_EXCL never silently drops a DISTINCT second witness the way a
 * 64-bit FNV collision could. Not perf-critical: a reproducer dir, not the hot
 * loop. -------------------------------------------------------------------- */
typedef struct {
  uint32_t h[8];
  uint64_t len;
  uint8_t buf[64];
  size_t n;
} Sha256;

static uint32_t ror(uint32_t x, int r) { return (x >> r) | (x << (32 - r)); }

static void sha256_block(Sha256 *s, const uint8_t *p) {
  static const uint32_t K[64] = {
      0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
      0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
      0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
      0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
      0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
      0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
      0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
      0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
  uint32_t w[64];
  for (int i = 0; i < 16; i++)
    w[i] = (uint32_t)p[i * 4] << 24 | (uint32_t)p[i * 4 + 1] << 16 | (uint32_t)p[i * 4 + 2] << 8 |
           (uint32_t)p[i * 4 + 3];
  for (int i = 16; i < 64; i++) {
    uint32_t s0 = ror(w[i - 15], 7) ^ ror(w[i - 15], 18) ^ (w[i - 15] >> 3);
    uint32_t s1 = ror(w[i - 2], 17) ^ ror(w[i - 2], 19) ^ (w[i - 2] >> 10);
    w[i] = w[i - 16] + s0 + w[i - 7] + s1;
  }
  uint32_t a = s->h[0], b = s->h[1], c = s->h[2], d = s->h[3];
  uint32_t e = s->h[4], f = s->h[5], g = s->h[6], h = s->h[7];
  for (int i = 0; i < 64; i++) {
    uint32_t S1 = ror(e, 6) ^ ror(e, 11) ^ ror(e, 25);
    uint32_t ch = (e & f) ^ (~e & g);
    uint32_t t1 = h + S1 + ch + K[i] + w[i];
    uint32_t S0 = ror(a, 2) ^ ror(a, 13) ^ ror(a, 22);
    uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
    uint32_t t2 = S0 + maj;
    h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
  }
  s->h[0] += a; s->h[1] += b; s->h[2] += c; s->h[3] += d;
  s->h[4] += e; s->h[5] += f; s->h[6] += g; s->h[7] += h;
}

static void sha256(const uint8_t *data, size_t n, char out[65]) {
  Sha256 s = {{0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
               0x5be0cd19}, 0, {0}, 0};
  s.len = (uint64_t)n * 8;
  size_t i = 0;
  for (; i + 64 <= n; i += 64)
    sha256_block(&s, data + i);
  uint8_t tail[128];
  size_t t = n - i;
  memcpy(tail, data + i, t);
  tail[t++] = 0x80;
  size_t pad = (t <= 56) ? 56 - t : 120 - t;
  memset(tail + t, 0, pad);
  t += pad;
  for (int k = 0; k < 8; k++)
    tail[t + k] = (uint8_t)(s.len >> (56 - 8 * k));
  t += 8;
  for (size_t j = 0; j < t; j += 64)
    sha256_block(&s, tail + j);
  for (int k = 0; k < 8; k++)
    snprintf(out + k * 8, 9, "%08x", s.h[k]);
}

/* ---- dynamic bucket registry ------------------------------------------- */
/* One entry per witness-config class. occ is UNCAPPED (a plain counter);
 * `files` (distinct reproducers written) is capped separately at FILE_CAP; and
 * `min_size` tracks the smallest witness seen so the minimal reproducer is kept. */
#define FILE_CAP 512
typedef struct {
  char cls[48];
  unsigned long occ;   /* occurrences (uncapped)                     */
  unsigned files;      /* distinct witness files written (<= FILE_CAP)*/
  int capped;          /* files hit FILE_CAP                          */
  size_t min_size;     /* smallest witness seen (0 = none yet)        */
} Bucket;

static Bucket *g_b;
static size_t g_n, g_cap;

static Bucket *find_bucket(const char *cls, int *is_new) {
  for (size_t i = 0; i < g_n; i++)
    if (strncmp(g_b[i].cls, cls, sizeof g_b[i].cls) == 0) {
      *is_new = 0;
      return &g_b[i];
    }
  if (g_n == g_cap) {
    size_t nc = g_cap ? g_cap * 2 : 32;
    Bucket *nb = realloc(g_b, nc * sizeof *nb);
    if (!nb)
      return NULL; /* out of memory: drop the record rather than crash */
    g_b = nb;
    g_cap = nc;
  }
  Bucket *e = &g_b[g_n++];
  memset(e, 0, sizeof *e);
  snprintf(e->cls, sizeof e->cls, "%s", cls);
  *is_new = 1;
  return e;
}

/* The bucket table is per PROCESS, but the fleet runs libFuzzer `-fork=1`, which
 * restarts the worker child continuously (150+ jobs in a long campaign). Each fresh
 * child starts at files=0 and writes another FILE_CAP reproducers per class, so a
 * catalogue class dumped 100k+ near-duplicate files (GBs) over a 6 h run and filled
 * the disk. Seed the counters from what is ALREADY on disk the first time this
 * process touches a class, so FILE_CAP is a global bound: count entries (stop at
 * FILE_CAP, so a full dir costs one bounded readdir) and take min.* as the standing
 * minimum so a larger witness never overwrites a smaller one from a prior child. */
static void seed_from_dir(Bucket *b, const char *dir, const char *ext) {
  DIR *d = opendir(dir);
  if (!d)
    return;
  unsigned n = 0;
  struct dirent *e;
  while (n < FILE_CAP && (e = readdir(d)) != NULL) {
    if (e->d_name[0] == '.' || strncmp(e->d_name, "min.", 4) == 0)
      continue;
    n++;
  }
  closedir(d);
  b->files = n;
  b->capped = (n >= FILE_CAP);
  char mpath[640];
  snprintf(mpath, sizeof mpath, "%s/min.%s", dir, ext);
  struct stat st;
  if (stat(mpath, &st) == 0 && st.st_size > 0)
    b->min_size = (size_t)st.st_size;
}

static const char *repro_ext(void) {
  /* 5C: name reproducers by the target's input_kind, not always .flac. */
  switch (fuzz_target_info.input_kind) {
  case FUZZ_INPUT_PACKED_PCM: return "pcm";
  case FUZZ_INPUT_RAW: return "bin";
  default: return "flac";
  }
}

static const char *dump_dir(void) {
  const char *base = getenv("FUZZ_DUMP_DIR");
  return base ? base : "./divergences";
}

static void write_file(const char *path, const uint8_t *data, size_t size, int excl) {
  int flags = O_WRONLY | O_CREAT | (excl ? O_EXCL : O_TRUNC);
  int fd = open(path, flags, 0644);
  if (fd < 0)
    return;
  size_t off = 0;
  while (off < size) {
    ssize_t w = write(fd, data + off, size - off);
    if (w <= 0)
      break;
    off += (size_t)w;
  }
  close(fd);
}

void bucket_record(const char *cls, const uint8_t *data, size_t size) {
  int is_new = 0;
  Bucket *b = find_bucket(cls, &is_new);
  if (!b)
    return;
  b->occ++;
  if (is_new)
    /* new-bucket-loud: the "don't miss a new class" signal, free, never aborts. */
    fprintf(stderr, "[bucket] NEW witness-config class '%s' (first occurrence, %zuB)\n", cls, size);

  /* Persist counters periodically (and on every new bucket) so a timeout/SIGKILL
   * -- which skips atexit AND FUZZ_ABORT -- still leaves an up-to-date counters
   * file for the fleet to sum. Cheap: the file is small and rename() is atomic. */
  static unsigned long since_write;
  if (is_new || (++since_write & 0x0fff) == 0)
    bucket_write_counters();

  const char *base = dump_dir();
  mkdir(base, 0755);
  char dir[512];
  snprintf(dir, sizeof dir, "%s/%s", base, cls);
  mkdir(dir, 0755);
  const char *ext = repro_ext();
  if (is_new)
    seed_from_dir(b, dir, ext); /* global FILE_CAP across -fork children */

  /* (1) the minimal witness per bucket, overwritten when a smaller input arrives. */
  if (b->min_size == 0 || size < b->min_size) {
    b->min_size = size;
    char mpath[640];
    snprintf(mpath, sizeof mpath, "%s/min.%s", dir, ext);
    write_file(mpath, data, size, 0 /* overwrite */);
  }
  /* (2) a content-hashed diversity sample, O_EXCL-deduped, capped independently. */
  if (b->files < FILE_CAP) {
    char hex[65];
    sha256(data, size, hex);
    char path[720];
    snprintf(path, sizeof path, "%s/%.16s_%zu.%s", dir, hex, size, ext);
    /* count a genuine NEW file only (O_EXCL): re-seeing the same content is an
     * occurrence, already counted above, and must not burn a file slot. */
    if (access(path, F_OK) != 0) {
      write_file(path, data, size, 1 /* excl */);
      if (access(path, F_OK) == 0)
        b->files++;
    }
  } else {
    b->capped = 1;
  }
}

void bucket_report(FILE *f) {
  if (!g_n)
    return;
  fprintf(f, "[buckets] %zu witness-config class(es) "
             "(occurrences; NOT bug counts -- root-cause counting is triage over "
             "bucket representatives):\n",
          g_n);
  for (size_t i = 0; i < g_n; i++)
    fprintf(f, "  %-32s occ=%lu files=%u%s min=%zuB\n", g_b[i].cls, g_b[i].occ, g_b[i].files,
            g_b[i].capped ? " (capped)" : "", g_b[i].min_size);
}

void bucket_write_counters(void) {
  if (!g_n)
    return;
  char path[640];
  const char *env = getenv("FUZZ_COUNTERS");
  if (env)
    snprintf(path, sizeof path, "%s", env);
  else
    snprintf(path, sizeof path, "%s/counters-%ld.json", dump_dir(), (long)getpid());
  mkdir(dump_dir(), 0755);
  /* Write to a temp then rename so a concurrent reader never sees a half file. */
  char tmp[672];
  snprintf(tmp, sizeof tmp, "%s.tmp", path);
  FILE *f = fopen(tmp, "w");
  if (!f)
    return;
  fprintf(f, "{\n  \"pid\": %ld,\n  \"buckets\": {\n", (long)getpid());
  for (size_t i = 0; i < g_n; i++)
    fprintf(f, "    \"%s\": {\"occurrences\": %lu, \"files\": %u, \"capped\": %s, \"min_size\": %zu}%s\n",
            g_b[i].cls, g_b[i].occ, g_b[i].files, g_b[i].capped ? "true" : "false", g_b[i].min_size,
            i + 1 < g_n ? "," : "");
  fprintf(f, "  }\n}\n");
  fclose(f);
  rename(tmp, path);
}
