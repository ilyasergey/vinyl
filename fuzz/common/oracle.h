/* oracle.h — the shared Vinyl-vs-libFLAC decode-diff oracle used by both
 * fz_decode_diff (AFL-havoc arm, malformed-header space) and
 * fz_decode_structured (CRC-aware mutator, deep-decoder space). Splitting
 * this out is what keeps the two targets from silently drifting apart the
 * way fz_decode_diff and fz_crc_structured did in the old cfuzz rig (see
 * DESIGN.md §7.3): fz_decode_diff used to abort() on a params-only
 * difference that its own successor deliberately catalogued instead. */
#ifndef ORACLE_H
#define ORACLE_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
  const char *name;
  int rc; /* DEC_REJECT / DEC_OK / DEC_SKIP */
  uint8_t *pcm;
  size_t len;
  int bps, ch, sr;
} OracleResult;

enum {
  ORACLE_SKIP = 0,     /* non-16-bit on either side; out of scope        */
  ORACLE_BOTH_REJECT,  /* agreement                                      */
  ORACLE_BOTH_OK,      /* agreement, PCM + params identical              */
  ORACLE_A_ONLY,       /* a (Vinyl) accepts, b (libFLAC) rejects; dumped */
  ORACLE_B_ONLY,       /* b (libFLAC) accepts, a (Vinyl) rejects; dumped */
  ORACLE_INCONSISTENT, /* frame header vs STREAMINFO clash; skipped      */
  ORACLE_PARAM_ONLY,   /* (bps,ch,sr) differ, PCM identical; harness art.*/
  ORACLE_OVERRUN,      /* b's PCM longer than the frame structure holds  */
  ORACLE_LEN_DIFF,     /* both DEC_OK, PCM length differs; dumped        */
};

/* Compares two decodes of the same FLAC bytes `data`/`size`. `a` MUST be the
 * Vinyl-family result (the one flac_expected_samples/flac_hdr_consistent are
 * used to corroborate) and `b` the libFLAC result. On a genuine PCM *byte*
 * divergence (equal length, differing bytes) this prints full triage detail
 * and abort()s -- it never returns in that case. A PCM *length* mismatch is
 * high-signal but not proof of a defect on its own (see ORACLE_LEN_DIFF), so
 * it is dumped + counted and only aborts if ORACLE_ABORT_ON_LEN is set in the
 * environment. ORACLE_A_ONLY/ORACLE_B_ONLY (accept/reject divergences) are
 * always dumped too, deduplicated and capped, under FUZZ_DUMP_DIR (default
 * ./divergences/{a_only,b_only,len_diff}/). Otherwise it returns one of the
 * ORACLE_* codes above for the caller to tally. */
int oracle_decode_diff(const uint8_t *data, size_t size, const OracleResult *a,
                       const OracleResult *b);

/* Write a divergence reproducer to $FUZZ_DUMP_DIR/<cls>/, O_EXCL-deduped and
 * capped per class (folded in from oracle_dump). */
void oracle_dump_write(const char *cls, const uint8_t *data, size_t size);

#endif /* ORACLE_H */
