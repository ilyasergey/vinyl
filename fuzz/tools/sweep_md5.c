/* sweep_md5 -- the deterministic CI sibling of fz_md5. fz_md5's coverage
 * saturates within the first inputs (MD5 padding is a function of length, not
 * content), so running it as a campaign burns executions on a flat surface. This
 * tool replaces that campaign with a fixed, exhaustive-at-the-edges sweep that a
 * regression run can assert on:
 *
 *   1. the RFC 1321 / NIST known-answer vectors (also cross-checks md5_ref itself
 *      against the published digests, so the differential's reference is pinned);
 *   2. a padding-boundary sweep over EVERY length 0..130 -- covers the 55/56 and
 *      119/120 one-extra-block transitions (rem<56 vs rem>=56) exhaustively;
 *   3. a few thousand fixed-seed (xorshift, seed constant in-source) random-length
 *      vectors, so a content-dependent defect that slips past the boundaries still
 *      has a deterministic chance to surface.
 *
 * Every vector differentials Flac.Md5.md5 (Vinyl's hand-written 64-round MD5, via
 * the same vinyl_md5 extern fz_md5.c uses) against common/md5_ref.c. A mismatch is
 * a broken STREAMINFO/frame digest in a verified codec -- flac -t would reject
 * Vinyl's output while every round-trip theorem still holds. Prints
 * `sweep_md5: N vectors, 0 mismatches` and exits non-zero on any mismatch.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "md5_ref.h"
#include "vinyl_api.h"   /* vinyl_init */
#include "vinyl_modes.h" /* vinyl_md5 (the same extern fz_md5.c uses) */

#define RAND_VECTORS 4000
#define RAND_MAX_LEN 2048
#define PAD_MAX_LEN 130
#define XORSHIFT_SEED 0x9E3779B97F4A7C15ULL /* fixed in-source seed */

static unsigned long g_vectors, g_mismatch;

static uint64_t xs_state = XORSHIFT_SEED;

static uint64_t xs_next(void) {
  uint64_t x = xs_state;
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  xs_state = x;
  return x;
}

static void hexcat(char *dst, const uint8_t *d) {
  for (int i = 0; i < 16; i++)
    sprintf(dst + i * 2, "%02x", d[i]);
}

/* Differential one message. `expect_hex` (33 chars) is the published KAT digest
 * or NULL; when present, md5_ref itself is pinned to the KAT so the reference of
 * the differential cannot silently rot. */
static void check(const uint8_t *msg, size_t n, const char *expect_hex) {
  uint8_t va[16], vb[16];
  char a[33], b[33];
  size_t dn = vinyl_md5(msg, n, va);
  md5_ref(msg, n, vb);
  g_vectors++;
  hexcat(a, va);
  hexcat(b, vb);

  int bad = (dn != 16) || memcmp(va, vb, 16) != 0;
  if (expect_hex && (strcmp(b, expect_hex) != 0 || strcmp(a, expect_hex) != 0))
    bad = 1;
  if (bad) {
    g_mismatch++;
    fprintf(stderr,
            "[MD5 MISMATCH] len=%zu vinyl_digest_len=%zu\n"
            "  vinyl=%s\n  ref  =%s\n",
            n, dn, a, b);
    if (expect_hex)
      fprintf(stderr, "  kat  =%s\n", expect_hex);
  }
}

/* RFC 1321 appendix / NIST known-answer test suite. */
static void kat(void) {
  static const char alpha[] = "abcdefghijklmnopqrstuvwxyz";
  static const char alnum[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  static const char eights[] = "1234567890123456789012345678901234567890"
                               "1234567890123456789012345678901234567890";
  struct {
    const char *msg;
    const char *hex;
  } v[] = {
      {"", "d41d8cd98f00b204e9800998ecf8427e"},
      {"a", "0cc175b9c0f1b6a831c399e269772661"},
      {"abc", "900150983cd24fb0d6963f7d28e17f72"},
      {"message digest", "f96b697d7cb7938d525a2f31aaf161d0"},
      {alpha, "c3fcd3d76192e4007dfb496cca67e13b"},
      {alnum, "d174ab98d277d9f5a5611c2c9f419d9f"},
      {eights, "57edf4a22be3c955ac49da2e2107b67a"},
  };
  for (size_t i = 0; i < sizeof v / sizeof v[0]; i++)
    check((const uint8_t *)v[i].msg, strlen(v[i].msg), v[i].hex);
}

/* Every length 0..PAD_MAX_LEN, content = a fixed byte ramp. Covers the 55/56 and
 * 119/120 one-extra-block padding transitions exhaustively. */
static void padding_sweep(void) {
  uint8_t buf[PAD_MAX_LEN + 1];
  for (size_t j = 0; j <= PAD_MAX_LEN; j++)
    buf[j] = (uint8_t)(j * 31 + 7);
  for (size_t n = 0; n <= PAD_MAX_LEN; n++)
    check(buf, n, NULL);
}

/* Fixed-seed random-length vectors: deterministic content and lengths. */
static void random_sweep(void) {
  static uint8_t buf[RAND_MAX_LEN];
  for (int v = 0; v < RAND_VECTORS; v++) {
    size_t n = (size_t)(xs_next() % (RAND_MAX_LEN + 1));
    for (size_t i = 0; i < n; i++)
      buf[i] = (uint8_t)xs_next();
    check(buf, n, NULL);
  }
}

int main(void) {
  if (vinyl_init())
    return 1;
  kat();
  padding_sweep();
  random_sweep();
  printf("sweep_md5: %lu vectors, %lu mismatches\n", g_vectors, g_mismatch);
  return g_mismatch ? 1 : 0;
}
