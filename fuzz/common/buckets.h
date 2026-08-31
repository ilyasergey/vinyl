/* buckets.h -- witness-config bucketing + fork-safe counters (Phase 2C/2D).
 *
 * Replaces the old FNV-1a INPUT-HASH dedup in oracle_dump_write, which conflated
 * three different things and mis-reported them as if they were bug counts:
 *   - a class counter (e.g. 246,209) is an OCCURRENCE count, not a bug count;
 *   - the ~512-file dir was a hash-DIVERSITY sample, not a bug count;
 *   - one defect legitimately spans many buckets (under-alloc x bps x ch x clamp).
 * and had three concrete defects: g_tbl[16] silently stopped counting past 16
 * classes (a run had ~20); FNV can collide so O_EXCL silently drops a real second
 * witness; and every reproducer was named `.flac` even for RAW/PCM targets.
 *
 * A "bucket" here is a witness-CONFIG class (the `cls` string the oracle/target
 * chooses from codec state -- a_only, len_diff, selcon_unfit, ...). For each we
 * keep: an UNCAPPED occurrence counter; a content-hashed diversity sample of
 * witness files (SHA-256 names, O_EXCL, capped -- a SECOND independent cap); and
 * the single MINIMAL witness seen (overwritten when a smaller input arrives).
 * Report the field as `witness_configs`, never "N bugs".
 */
#ifndef BUCKETS_H
#define BUCKETS_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

/* One occurrence of bucket `cls` on input `data`/`size`. Increments the (uncapped)
 * occurrence counter, updates the minimal witness, and -- under the per-class file
 * cap -- writes a content-hashed diversity reproducer. Loud on a NEW bucket. */
void bucket_record(const char *cls, const uint8_t *data, size_t size);

/* Human summary: each bucket's occurrences, distinct witness files, capped?. */
void bucket_report(FILE *f);

/* Write per-process counters JSON to $FUZZ_COUNTERS if set, else
 * $FUZZ_DUMP_DIR/counters-<pid>.json. Called from fuzz_main's report (periodic +
 * atexit) AND from FUZZ_FAIL before abort() (atexit does NOT run on abort). The
 * per-pid path lets the fleet SUM across -fork children. Idempotent. */
void bucket_write_counters(void);

#endif /* BUCKETS_H */
