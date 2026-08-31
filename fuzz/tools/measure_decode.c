/* measure_decode -- the resource-MEASUREMENT harness. Not a fuzzer: it
 * replays a corpus through the production decoder and reports, per input and in
 * aggregate, the numbers `cost-semantics.md` argues about, MEASURED rather than
 * restated:
 *   - input bytes -> decoded samples -> decoded bytes at the declared depth;
 *   - the amplification ratio decoded_bytes / input_bytes (the "how big a bomb"
 *     figure) and the sample-count/byte ratio;
 *   - the unit mismatch: Stream.decodeBudget charges 2 units/sample regardless
 *     of depth while pcmBytesRange writes ceil(bps/8) bytes/sample, so at 24/32
 *     bits the real output is 1.5-2x the 16-bit accounting;
 *   - peak process RSS (getrusage) -- the only honest way to set every fuzz
 *     target's rss_limit_mb.
 *
 *   measure_decode <file-or-dir> [...]
 */
#include <dirent.h>
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/stat.h>

#include "vinyl_api.h" /* vinyl_init, DEC_* */

extern lean_object *lp_vinyl_Flac_Decode_decodeArrays(lean_object *bytes);

static double g_max_ratio;
static char g_max_path[512];
static unsigned long g_files, g_decoded;

static long list_len(lean_object *l) {
  long k = 0;
  for (; !lean_is_scalar(l); l = lean_ctor_get(l, 1))
    k++;
  return k;
}

static void measure(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f)
    return;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (sz <= 0 || sz > (1 << 24)) {
    fclose(f);
    return;
  }
  uint8_t *buf = malloc((size_t)sz);
  if (!buf || fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
    free(buf);
    fclose(f);
    return;
  }
  fclose(f);
  g_files++;

  lean_object *ba = lean_alloc_sarray(1, (size_t)sz, (size_t)sz);
  memcpy(lean_sarray_cptr(ba), buf, (size_t)sz);
  lean_object *r = lp_vinyl_Flac_Decode_decodeArrays(ba);
  if (lean_obj_tag(r) == 1) {
    g_decoded++;
    lean_object *p = lean_ctor_get(r, 0);
    lean_object *chs = lean_ctor_get(p, 0);
    lean_object *q = lean_ctor_get(p, 1);
    int bps = lean_is_scalar(lean_ctor_get(q, 0)) ? (int)lean_unbox(lean_ctor_get(q, 0)) : 0;
    long nch = list_len(chs);
    long nsamp = (nch && !lean_is_scalar(chs)) ? (long)lean_array_size(lean_ctor_get(chs, 0)) : 0;
    long total_samples = nch * nsamp;
    long decoded_bytes = total_samples * ((bps + 7) / 8);
    double ratio = (double)decoded_bytes / (double)sz;
    if (ratio > g_max_ratio) {
      g_max_ratio = ratio;
      snprintf(g_max_path, sizeof g_max_path, "%s", path);
    }
    printf("%-48s in=%ldB ch=%ld bps=%d samples=%ld out=%ldB ratio=%.1fx\n", path, sz, nch, bps,
           total_samples, decoded_bytes, ratio);
  }
  lean_dec(r);
  free(buf);
}

static void walk(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0)
    return;
  if (S_ISDIR(st.st_mode)) {
    DIR *d = opendir(path);
    if (!d)
      return;
    struct dirent *e;
    char child[1024];
    while ((e = readdir(d))) {
      if (e->d_name[0] == '.')
        continue;
      snprintf(child, sizeof child, "%s/%s", path, e->d_name);
      walk(child);
    }
    closedir(d);
  } else {
    measure(path);
  }
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <file-or-dir> [...]\n", argv[0]);
    return 2;
  }
  if (vinyl_init())
    return 1;
  for (int i = 1; i < argc; i++)
    walk(argv[i]);
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  printf("\n--- summary ---\n");
  printf("files=%lu decoded=%lu  peak RSS=%ld MB\n", g_files, g_decoded, ru.ru_maxrss / 1024);
  printf("max amplification=%.1fx at %s\n", g_max_ratio, g_max_path[0] ? g_max_path : "(none)");
  printf("note: decodeBudget charges 2 units/sample regardless of depth; real output is\n");
  printf("      ceil(bps/8) bytes/sample, so 24/32-bit streams beat the 16-bit accounting.\n");
  return 0;
}
