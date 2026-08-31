#include "oracle.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "buckets.h"
#include "flac_struct.h"
#include "fuzz_target.h"
#include "vinyl_api.h" /* DEC_REJECT / DEC_OK / DEC_SKIP */

static void report(const char *what, size_t insz, size_t voff, const OracleResult *a,
                   const OracleResult *b) {
  fprintf(stderr,
          "\n[DIVERGENCE] %s input=%zuB first_diff_off=%zu\n"
          "  %-7s: len=%zu bps=%d ch=%d sr=%d\n"
          "  %-7s: len=%zu bps=%d ch=%d sr=%d\n",
          what, insz, voff, a->name, a->len, a->bps, a->ch, a->sr, b->name, b->len, b->bps, b->ch,
          b->sr);
}

int oracle_decode_diff(const uint8_t *data, size_t size, const OracleResult *a,
                       const OracleResult *b) {
  if (a->rc == DEC_SKIP || b->rc == DEC_SKIP)
    return ORACLE_SKIP;

  if (a->rc != DEC_OK && b->rc != DEC_OK)
    return ORACLE_BOTH_REJECT;

  /* A frame header contradicting STREAMINFO (channels/bit depth) makes libFLAC
   * follow the frame while Vinyl follows STREAMINFO -- neither is a defect. This
   * MUST be checked before the accept/reject escalation below: the same clash
   * often makes one side reject rather than differ, and escalating that to an
   * abort under FUZZ_STRICT would fire on a non-defect. */
  if (!flac_hdr_consistent(data, size)) {
    /* This fires on a large share of mutated streams; printing per call floods
     * stderr with millions of identical lines (bug 10). Note the first few, then
     * stay silent -- the ORACLE_INCONSISTENT return already carries the signal. */
    static unsigned noted;
    if (noted < 8)
      fprintf(stderr, "[note] frame header contradicts STREAMINFO (%zuB) -- comparison skipped%s\n",
              size, ++noted == 8 ? " (further notes suppressed)" : "");
    return ORACLE_INCONSISTENT;
  }

  /* Accept/reject divergences: the client's wanted bug class ("Vinyl accepts,
   * libFLAC rejects" and vice versa). Not a proof violation on their own (no
   * completeness theorem either direction), so catalogued + dumped by default;
   * FUZZ_STRICT>=2 (must-reject / regression runs) turns them into aborts. */
  if (a->rc == DEC_OK && b->rc != DEC_OK) {
    oracle_dump_write("a_only", data, size);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      report("A_ONLY: a accepts, b rejects (strict)", size, 0, a, b);
      FUZZ_ABORT();
    }
    return ORACLE_A_ONLY;
  }
  if (a->rc != DEC_OK && b->rc == DEC_OK) {
    oracle_dump_write("b_only", data, size);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      report("B_ONLY: b accepts, a rejects (strict)", size, 0, a, b);
      FUZZ_ABORT();
    }
    return ORACLE_B_ONLY;
  }

  /* both DEC_OK from here on (frame-vs-STREAMINFO clash already handled above). */

  if (a->len != b->len) {
    size_t m = a->len < b->len ? a->len : b->len;
    size_t off = 0;
    while (off < m && a->pcm[off] == b->pcm[off])
      off++;
    /* Attribute the mismatch: the structural walk knows how many samples the
     * frames hold. When `a` (Vinyl) matches that and `b` (libFLAC) does not,
     * libFLAC is the outlier -- catalogue that as its own narrower class. */
    uint64_t exp = flac_expected_samples(data, size);
    size_t want = (size_t)exp * (size_t)a->ch * 2;
    if (exp && a->len == want && b->len != want) {
      fprintf(stderr,
              "[note] %s PCM length %zu != frame structure %zu (%s matches); input=%zuB -- "
              "catalogued\n",
              b->name, b->len, want, a->name, size);
      return ORACLE_OVERRUN;
    }
    /* Any other length mismatch is high-signal but not a proven defect on its
     * own: dump + count; abort only if FUZZ_STRICT>=1. */
    report("PCM length differs", size, off, a, b);
    oracle_dump_write("len_diff", data, size);
    if (fuzz_env_strict() >= FUZZ_STRICT_LEN)
      FUZZ_ABORT();
    return ORACLE_LEN_DIFF;
  }

  if (memcmp(a->pcm, b->pcm, a->len) != 0) {
    size_t off = 0;
    while (off < a->len && a->pcm[off] == b->pcm[off])
      off++;
    report("PCM bytes differ", size, off, a, b);
    fprintf(stderr, "  %s[%zu..]=%02x %02x  %s[%zu..]=%02x %02x\n", a->name, off, a->pcm[off],
            off + 1 < a->len ? a->pcm[off + 1] : 0, b->name, off, b->pcm[off],
            off + 1 < b->len ? b->pcm[off + 1] : 0);
    oracle_dump_write("byte_diff", data, size);
    FUZZ_ABORT();
  }

  /* Params-only difference on byte-identical PCM is a harness artefact (the two
   * wrappers take the values from different places), not a codec divergence.
   * Never abort. */
  if (a->bps != b->bps || a->ch != b->ch || a->sr != b->sr) {
    report("stream params differ (PCM identical) -- catalogued, not a defect", size, 0, a, b);
    return ORACLE_PARAM_ONLY;
  }

  return ORACLE_BOTH_OK;
}

/* ---- reproducer dump ----------------------------------------------------
 * Delegates to the shared witness-config bucket registry (common/buckets.c):
 * an UNCAPPED occurrence counter per class, a content-addressed (SHA-256)
 * diversity sample capped independently, the minimal witness per class, and a
 * reproducer extension chosen from the target's input_kind (5C: no more `.flac`
 * on RAW/PCM targets). This replaces the old FNV-1a input-hash scheme, whose
 * g_tbl[16] silently stopped counting past 16 classes and whose 64-bit hash
 * could collide and drop a distinct witness. */
void oracle_dump_write(const char *cls, const uint8_t *data, size_t size) {
  bucket_record(cls, data, size);
}
