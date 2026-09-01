/* fz_md5 -- differential the codec's hand-written Flac.Md5.md5 against an
 * independent RFC 1321 reference (common/md5_ref.c). Vinyl's MD5 is 64 unrolled
 * rounds with proof-indexed reads, tested only against RFC 1321's 7 vectors and
 * real audio; the classic defect zone is the length-dependent padding at
 * lengths == 54..63 mod 64 (one extra block). Those exact boundary lengths are
 * swept ONCE in init (their coverage saturates immediately and is
 * content-independent -- padding is a function of length); every exec then hashes
 * only the raw input, so the target is not paying an ~18x per-exec tax.
 *
 * A divergence is a broken STREAMINFO/frame MD5 in a verified codec: `flac -t`
 * would reject Vinyl's output while every round-trip theorem still holds -- the
 * cleanest illustration that the proof does not cover this primitive. Severity:
 * corrupted-output (class b). Input kind: raw. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../common/fuzz_target.h"
#include "../common/md5_ref.h"
#include "../common/vinyl_modes.h"

static unsigned long g_execs, g_hashes;

static void report(FILE *o) {
  fprintf(o, "[md5] execs=%lu hashes=%lu\n", g_execs, g_hashes);
}

/* Lengths straddling every multiple of 64 near the one-extra-block boundary. */
static const size_t k_bounds[] = {0,   1,   55,  56,  57,  63,  64,  65,  111, 112,
                                  119, 120, 127, 128, 191, 192, 255, 256};

static void hexcat(char *dst, const uint8_t *d) {
  for (int i = 0; i < 16; i++)
    sprintf(dst + i * 2, "%02x", d[i]);
}

static void demand_equal(const uint8_t *msg, size_t n) {
  uint8_t va[16], vb[16];
  size_t dn = vinyl_md5(msg, n, va);
  md5_ref(msg, n, vb);
  g_hashes++;
  if (dn != 16 || memcmp(va, vb, 16) != 0) {
    char a[33], b[33];
    hexcat(a, va);
    hexcat(b, vb);
    fprintf(stderr,
            "\n[MD5 DIVERGENCE] len=%zu vinyl_digest_len=%zu\n"
            "  vinyl=%s\n  ref  =%s\n"
            "  a broken MD5 in a verified codec: flac -t rejects Vinyl's output, no theorem "
            "violated\n",
            n, dn, a, b);
    FUZZ_ABORT();
  }
  /* Hex path: drives Flac.Md5.md5Hex + its flatMapTR nibble->hex helper (cold
   * when only the raw digest is copied). Oracle = the reference digest, lowercase
   * hex-encoded; a mismatch is the same broken-primitive finding as above. */
  char vh[33], rh[33];
  size_t hn = vinyl_md5_hex(msg, n, vh);
  hexcat(rh, vb);
  if (hn != 32 || memcmp(vh, rh, 32) != 0) {
    fprintf(stderr,
            "\n[MD5 HEX DIVERGENCE] len=%zu vinyl_hex_len=%zu\n"
            "  vinyl=%s\n  ref  =%s\n"
            "  Flac.Md5.md5Hex disagrees with the reference digest's hex encoding\n",
            n, hn, vh, rh);
    FUZZ_ABORT();
  }
}

/* Sweep the padding-boundary lengths ONCE at startup (after vinyl_init). Padding
 * behaviour is a function of length, not content, so a single deterministic pass
 * covers the edge; doing it per exec was an ~18x throughput tax on a target whose
 * coverage otherwise saturates within the first inputs. */
static void md5_init(void) {
  size_t maxL = k_bounds[sizeof k_bounds / sizeof k_bounds[0] - 1];
  uint8_t *scratch = malloc(maxL ? maxL : 1);
  if (!scratch)
    _exit(1);
  for (size_t j = 0; j < maxL; j++)
    scratch[j] = (uint8_t)j;
  for (size_t i = 0; i < sizeof k_bounds / sizeof k_bounds[0]; i++)
    demand_equal(scratch, k_bounds[i]);
  free(scratch);
}

FUZZ_TARGET(.name = "fz_md5",
            .summary = "Flac.Md5.md5 vs an independent RFC 1321 reference (padding boundaries)",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .init = md5_init, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  demand_equal(data, size); /* boundary lengths already swept in md5_init */
  fuzz_tick();
  return 0;
}
