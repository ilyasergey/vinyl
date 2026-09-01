/* fuzz_main.c — the shared init/report driver that FUZZ_TARGET's generated
 * LLVMFuzzerInitialize calls. This is the single home for what used to be
 * copy-pasted into every target's LLVMFuzzerInitialize. */
#include "fuzz_target.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "flac_bits.h" /* flac_si_total_samples -- the shared STREAMINFO accessor (6E) */
#include "flac_struct.h" /* flac_expected_samples -- honest sample count when total=0 */


int vinyl_init(void); /* common/vinyl_api.c */

/* Persist the target's report() line to $FUZZ_DUMP_DIR/report-<pid>.txt, mirroring
 * buckets.c's per-pid temp+rename mechanism (same env var, same pid-in-the-name,
 * same SIGKILL-proof atomic write). Under libFuzzer -fork the atexit report runs in
 * the fork PARENT, which never executes an input, so its stderr line reads execs=0;
 * the CHILDREN's real counters otherwise vanish with the /tmp/libFuzzerTemp.*.dir
 * logs libFuzzer deletes on clean exit. Writing each process's own file here makes
 * every child's counters durable for the fleet to pick the busiest one. No-op when
 * FUZZ_DUMP_DIR is unset (i.e. outside the fleet) or the target has no report(). */
static void write_report_file(void) {
  const char *dir = getenv("FUZZ_DUMP_DIR");
  if (!dir || !*dir || !fuzz_target_info.report)
    return;
  mkdir(dir, 0755);
  char path[640];
  snprintf(path, sizeof path, "%s/report-%ld.txt", dir, (long)getpid());
  char tmp[672];
  snprintf(tmp, sizeof tmp, "%s.tmp", path);
  FILE *f = fopen(tmp, "w");
  if (!f)
    return;
  fuzz_target_info.report(f); /* the SAME text rendered to stderr below -- unchanged */
  fclose(f);
  rename(tmp, path);
}

static void run_report(void) {
  if (fuzz_target_info.report)
    fuzz_target_info.report(stderr);
  /* Witness-config buckets are shared plumbing every target feeds via the oracle,
   * so they are reported + persisted here regardless of whether the target has its
   * own report(). counters.json is what the fleet SUMS across -fork children (the
   * stderr scrape kept only the last line). */
  bucket_report(stderr);
  bucket_write_counters();
  write_report_file();
}

int fuzz_common_init(int *argc, char ***argv) {
  (void)argc;
  (void)argv;
  fuzz_env_init();
  if (fuzz_target_info.needs_vinyl && vinyl_init() != 0) {
    fprintf(stderr, "[%s] vinyl_init failed\n", fuzz_target_info.name);
    exit(1);
  }
  if (fuzz_target_info.init)
    fuzz_target_info.init();
  /* Report the RESOLVED mutator ($FUZZ_MUTATOR wins over the target default),
   * not just the default -- a plain-mutator run used to still print "crc". */
  const char *mut = getenv("FUZZ_MUTATOR");
  if (!mut || !*mut)
    mut = fuzz_target_info.default_mutator == FUZZ_MUT_CRC ? "crc" : "plain";
  fprintf(stderr, "[%s] %s | input_kind=%d mutator=%s strict=%d\n", fuzz_target_info.name,
          fuzz_target_info.summary ? fuzz_target_info.summary : "", (int)fuzz_target_info.input_kind,
          mut, fuzz_env_strict());
  /* Always register: even a target with no report() has bucket counters to flush
   * at exit (a clean campaign exit -- not an abort, which uses FUZZ_ABORT). */
  atexit(run_report);
  return 0;
}

/* Called once per exec by targets that want the shared periodic-report cadence
 * (every 16384 execs). Targets keeping their own cadence simply do not call it. */
void fuzz_tick(void) {
  static unsigned long n;
  if (((++n) & 0x3fff) == 0)
    run_report();
}

/* ============ run-time knobs (folded in from fuzz_env.c) ============ */
/* Static defaults are the pre-init values (repeat=1), so the accessors are safe
 * even before fuzz_common_init runs -- which it always does before any exec. */
static int g_strict, g_repeat = 1, g_force_par;
static size_t g_max_samples = 1u << 20; /* 6E: FUZZ_MAX_SAMPLES, 0 disables */

static int env_int(const char *name, int dflt, int lo, int hi) {
  const char *v = getenv(name);
  if (!v || !*v)
    return dflt;
  int n = atoi(v);
  return n < lo ? lo : n > hi ? hi : n;
}

void fuzz_env_init(void) {
  g_strict = env_int("FUZZ_STRICT", FUZZ_STRICT_BYTES, FUZZ_STRICT_BYTES, FUZZ_STRICT_ACCEPT);
  g_repeat = env_int("VM_REPEAT", 1, 1, 64);
  g_force_par = env_int("VM_FORCE_PAR", 0, 0, 1);
  const char *ms = getenv("FUZZ_MAX_SAMPLES");
  if (ms && *ms) {
    long long v = atoll(ms);
    g_max_samples = v < 0 ? 0 : (size_t)v; /* 0 disables the cap */
  }
}

int fuzz_env_strict(void) { return g_strict; }
int fuzz_env_repeat(void) { return g_repeat; }
int fuzz_env_force_par(void) { return g_force_par; }
size_t fuzz_max_samples(void) { return g_max_samples; }

int fuzz_over_sample_cap(const uint8_t *data, size_t size) {
  /* Only meaningful for a STREAMINFO-led FLAC stream (marker + metadata header +
   * 34-byte STREAMINFO payload). The first metadata block must be STREAMINFO
   * (type 0) for the offsets to be valid. */
  if (!g_max_samples || size < 42 || memcmp(data, "fLaC", 4) != 0)
    return 0;
  if ((data[4] & 0x7f) != 0)
    return 0; /* first block is not STREAMINFO -- offsets would be wrong */
  /* The declared STREAMINFO total is untrusted (CRC-mutable) and 0 means
   * "unknown" (RFC 9639 §9.1.3), so keying off it alone leaks two ways: total=0
   * reads as "0 samples" and bypasses the cap on an arbitrarily large stream,
   * and a tiny file can declare a huge total and be dropped even though it can
   * only decode to a handful of samples. Cap on min(declared, budget) instead,
   * and when the declared total is the "unknown" sentinel 0, use the frames'
   * actual summed block sizes (flac_expected_samples) rather than 0. The budget
   * is the decoder's own decompression-bomb bound: decode_size_le guarantees
   * 2*Σ|channel| ≤ decodeBudget = 4096*size + 65536 (Flac/Native/Stream.lean:
   * 471-479), so no stream can yield more than decodeBudget/2 = 2048*size + 32768
   * inter-channel samples regardless of what STREAMINFO claims (K = decodeAmpl/2
   * = 2048, floor = decodeFloor/2 = 32768). FUZZ_MAX_SAMPLES=0 still fully
   * disables the cap via the g_max_samples guard above. */
  uint64_t budget = (uint64_t)2048 * (uint64_t)size + 32768; /* = decodeBudget/2 */
  uint64_t declared = flac_si_total_samples(data);
  uint64_t effective = declared == 0 ? flac_expected_samples(data, size)
                                     : (declared < budget ? declared : budget);
  return effective > (uint64_t)g_max_samples;
}

size_t fuzz_rss_kb(void) {
  FILE *f = fopen("/proc/self/statm", "r");
  if (!f)
    return 0;
  unsigned long total = 0, resident = 0;
  int got = fscanf(f, "%lu %lu", &total, &resident);
  fclose(f);
  if (got < 2)
    return 0;
  return (size_t)resident * (size_t)(sysconf(_SC_PAGESIZE) / 1024);
}
