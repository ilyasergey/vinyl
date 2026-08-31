/* fuzz_target.h — THE contract between a target and the common layer. A target
 * is exactly: this struct (via the FUZZ_TARGET macro), plus a
 * LLVMFuzzerTestOneInput. There is no per-target LLVMFuzzerInitialize to
 * copy-paste; the macro emits a standard one that calls fuzz_common_init. */
#ifndef FUZZ_TARGET_H
#define FUZZ_TARGET_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "buckets.h"

/* Uniform abort at a genuine-violation site (2D). The witness dump + bucket
 * increment happen at the call site (oracle_dump_write / bucket_record) BEFORE
 * this; FUZZ_ABORT flushes stderr and PERSISTS the per-process counters -- atexit
 * does NOT run on abort(), so without this every bucket count is lost on the very
 * runs that matter (a strict abort). Then abort() so libFuzzer captures the crash. */
#define FUZZ_ABORT()                                                                                 \
  do {                                                                                               \
    fflush(stderr);                                                                                  \
    bucket_write_counters();                                                                         \
    abort();                                                                                         \
  } while (0)

typedef enum {
  FUZZ_INPUT_FLAC_STREAM = 0, /* raw FLAC bytes; the CRC mutator applies      */
  FUZZ_INPUT_PACKED_PCM = 1,  /* common/pack.h header + s16le payload         */
  FUZZ_INPUT_RAW = 2,         /* opaque; never structure-mutate               */
} FuzzInputKind;

typedef enum { FUZZ_MUT_PLAIN = 0, FUZZ_MUT_CRC = 1 } FuzzMutator;

typedef struct {
  const char *name;          /* MUST equal the source file's basename         */
  const char *summary;       /* one line; printed in the startup banner       */
  FuzzInputKind input_kind;
  FuzzMutator default_mutator; /* env FUZZ_MUTATOR overrides at run time       */
  unsigned needs_vinyl : 1;    /* run vinyl_init() before the first exec       */
  unsigned needs_flac : 1;     /* documentation + `make validate` only         */
  void (*init)(void);          /* optional, after vinyl_init; may be NULL      */
  void (*report)(FILE *);      /* periodic + atexit stats;    may be NULL      */
} FuzzTargetInfo;

extern const FuzzTargetInfo fuzz_target_info;

/* common/fuzz_main.c, inside libfuzzcommon.a. Runs vinyl_init() when
 * needs_vinyl (which calls lean_init_task_manager() -- fix C1, the single most
 * important line in the rig), parses fuzz_env once, prints the banner,
 * atexit(report). Returns 0. */
int fuzz_common_init(int *argc, char ***argv);
void fuzz_tick(void); /* call once per exec; drives the periodic report */

#define FUZZ_TARGET(...)                                                                            \
  const FuzzTargetInfo fuzz_target_info = {__VA_ARGS__};                                            \
  int LLVMFuzzerInitialize(int *argc, char ***argv) { return fuzz_common_init(argc, argv); }


/* --- run-time knobs, folded in from fuzz_target.h --- */
/* fuzz_target.h — run-time knobs parsed ONCE at init, out of the oracle hot path.
 * The reference rig called getenv() per mismatch inside oracle.c; here every
 * knob is read a single time in fuzz_env_init() and consulted through these
 * accessors. */

/* 3-level abort strictness, from $FUZZ_STRICT (default 0):
 *   0  catalogue + dump everything; abort only on a genuine PCM BYTE divergence
 *   1  + abort on a PCM LENGTH difference (ORACLE_LEN_DIFF)
 *   2  + abort on an ACCEPT/REJECT divergence (A_ONLY / B_ONLY) -- for
 *        must-reject and regression-corpus runs where any divergence is a bug */
enum { FUZZ_STRICT_BYTES = 0, FUZZ_STRICT_LEN = 1, FUZZ_STRICT_ACCEPT = 2 };

void fuzz_env_init(void); /* idempotent; called by fuzz_common_init */
int fuzz_env_strict(void);

/* Current process resident set in KiB (/proc/self/statm field 2 x page size),
 * 0 if unavailable. An in-band resource instrument: sampled around a decode it
 * gives a per-exec RSS delta, so a decompression bomb is attributable to its
 * input rather than only tripping the out-of-band rss_limit/watchdog. */
size_t fuzz_rss_kb(void);

/* Deterministic-repeat count for the mode/parallel targets, from $VM_REPEAT
 * (default 1). Re-decoding the same input N times under a live task pool is
 * how a nondeterministic parallel defect is caught. */
int fuzz_env_repeat(void);

/* Force the parallel decode path even below Decode.parThreshold, from
 * $VM_FORCE_PAR (default 0). */
int fuzz_env_force_par(void);

/* Phase 6E: harness-side sample cap. The P2 budget permits ~2048 samples per
 * input byte, so a small CONSTANT-heavy seed decodes to tens of MB and the corpus
 * self-selects for bombs (fz_decode_modes.serial fell to 9/s). A decode target
 * calls this at the top and DEC_SKIPs when the STREAMINFO's DECLARED totalSamples
 * exceeds $FUZZ_MAX_SAMPLES (default 1<<20; 0 disables). It reads the field through
 * the shared flac_bits accessor -- NOT a per-target STREAMINFO parser. NOT applied
 * to fz_samples_diff (keeps bomb exploration) or fz_decode_capacity (whose finding
 * IS the large-declared case). */
size_t fuzz_max_samples(void);
int fuzz_over_sample_cap(const uint8_t *data, size_t size);

#endif /* FUZZ_TARGET_H */
