/* Verification helper: run both wrappers on files, print their verdicts, and
 * optionally dump the decoded PCM for cross-checking against `flac -d`.
 * Usage: pcm_check [-dump prefix] file... */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_api.h"
#include "../common/vinyl_api.h"

static const char *codename(int c) {
  return c == DEC_OK ? "OK" : c == DEC_SKIP ? "SKIP" : "REJECT";
}

static void dump(const char *prefix, const char *which, int idx, const uint8_t *p, size_t n) {
  char path[4096];
  snprintf(path, sizeof path, "%s.%d.%s.raw", prefix, idx, which);
  FILE *f = fopen(path, "wb");
  if (f) {
    fwrite(p, 1, n, f);
    fclose(f);
  }
}

int main(int argc, char **argv) {
  const char *prefix = NULL;
  int argi = 1;
  if (argc > 2 && strcmp(argv[1], "-dump") == 0) {
    prefix = argv[2];
    argi = 3;
  }
  if (vinyl_init() != 0)
    return 2;
  int bad = 0;
  for (int i = argi; i < argc; i++) {
    FILE *f = fopen(argv[i], "rb");
    if (!f) {
      fprintf(stderr, "cannot open %s\n", argv[i]);
      return 2;
    }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *buf = malloc((size_t)n);
    if (fread(buf, 1, (size_t)n, f) != (size_t)n)
      return 2;
    fclose(f);

    uint8_t *vp, *fp;
    size_t vl, fl;
    int vb, vc, vs, fb, fc, fs;
    int v = vinyl_decode_fast(buf, (size_t)n, &vp, &vl, &vb, &vc, &vs);
    int r = flac_decode(buf, (size_t)n, &fp, &fl, &fb, &fc, &fs);
    int same = (v == DEC_OK && r == DEC_OK && vl == fl && memcmp(vp, fp, vl) == 0 && vb == fb &&
                vc == fc && vs == fs);
    printf("%-60s vinyl=%s(len=%zu bps=%d ch=%d sr=%d) libflac=%s(len=%zu bps=%d ch=%d sr=%d) %s\n",
           argv[i], codename(v), vl, vb, vc, vs, codename(r), fl, fb, fc, fs,
           v == DEC_OK && r == DEC_OK ? (same ? "PCM_IDENTICAL" : "PCM_DIFFERS") : "-");
    if (v == DEC_OK && r == DEC_OK && !same)
      bad = 1;
    if (prefix) {
      if (v == DEC_OK)
        dump(prefix, "vinyl", i - argi, vp, vl);
      if (r == DEC_OK)
        dump(prefix, "libflac", i - argi, fp, fl);
    }
    free(buf);
  }
  return bad;
}
