/* fz_decode_stack -- the DECODE-side mirror of fz_encode_stack: a bounded-stack
 * child that catalogues the ok->crash frontier of the decoder's non-tail interior
 * recursion.
 *
 * The class. Lean does no TCO-modulo-cons, so an `f x :: rec ...` shape keeps one
 * native frame per element. The child drives the PRODUCTION decoder
 * (Flac.decodePcm16A, the CLI `--decode-pcm16` path), whose per-frame interior loops
 * are the tail ARRAY forms -- Flac.Decode.readRiceSeqScan / readSIntSeqGo / readPartsA
 * (up to 2^15 partitions) / restoreA / the tail undiff -- so it is EXPECTED to survive
 * at every stack size. NOTE this decoder does NOT use Flac.Rice.readRiceSeq/readSIntSeq
 * at all (verified in the IR: Flac/Native/Decode.c calls no Flac.Rice.readRiceSeq*);
 * those readers live only on the reference path (Stream.decodeReference), which
 * overflows on deep input by construction and is deliberately NOT probed here.
 *
 * STATUS: this is the decode-side analogue of fz_encode_stack -- a forward REGRESSION
 * PIN expected green. The shipped array decoder was verified stack-flat in its residual
 * layer (it survives here at every stack size); a witness means a future change
 * introduced a NON-TAIL loop into the shipped decode path -- exactly the
 * enumerative-guarantee gap the @[csimp] gate cannot see (a MISSING swap is
 * invisible to a gate that pins the swaps that exist). Catalogue-by-default;
 * FUZZ_STRICT>=1 escalates it to a hard abort so a strict / regression campaign pins
 * "the shipped decoder overflows" as a finding.
 *
 * EMITTER: the child builds the deep stream with libFLAC (flac_encode, subset off), so
 * it reaches a LEGAL block size up to 65535 -- the maximum a frame header can express,
 * which the checked Lean encoder (capped at 4608) cannot emit -- and the emitter is
 * entirely outside the Lean codec, so a decode signal is unambiguously the decoder. The
 * checked-encoder path remains available (`vinyl_decode_probe <...> checked`) for a
 * Vinyl-encoded round-trip variant.
 *
 * Why a dedicated child process. It runs the decoder in an ISOLATED child whose
 * stack is bounded small (RLIMIT_STACK, set before an execv -- the exact mechanism
 * tools/stack_probe.sh uses via `ulimit -s`), reads the child's SIGABRT/SIGSEGV as
 * the witness, and records the (blockSize, channels, frames, stackKB) ok->crash
 * relationship WITHOUT aborting the fuzzer. The child builds its own deep stream
 * (encode of correlated PCM, then decode) -- see tools/vinyl_decode_probe.c.
 *
 * Input kind: RAW. The four bytes select the probe geometry; libFuzzer/AFL explore
 * the frontier by mutating them. The heavy lifting is in the forked child, so this
 * target's own coverage is intentionally shallow -- it is a resource prober, not a
 * codepath differential.
 */
#include <libgen.h>
#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../common/fuzz_target.h"

/* Geometry lattice. Decode recursion depth = residual length ~= block size (per
 * frame's interior), so LARGE block sizes drive the depth up; small stacks make
 * the overflow reachable early. The sweep over BOTH axes is the class relationship:
 * the crossover MOVES with block size and stack size, it is not one magic number.
 * 65535 is the largest block size a frame header can express; the libFLAC emitter
 * reaches it (the checked encoder could not), so every entry is a distinct reachable
 * block size across the full legal range. */
static const size_t k_bs[] = {512, 4096, 16384, 32768, 65535};
/* 256 KB is the floor: below it even a shallow decode overflows (uninformative).
 * 8192 KB anchors the survivor side (a real deployment's main stack). The crossover
 * moving across this span IS the decode-side non-tail-recursion class. */
static const long k_stack_kb[] = {256, 512, 1024, 2048, 4096, 8192};
/* Full frames the stream carries: a handful is plenty -- the per-frame INTERIOR
 * depth (not the frame count, which is tail-swapped) is what overflows, so one full
 * block-size frame already reaches the depth; a few add margin without cost. */
enum { FRAMES_MIN = 1, FRAMES_MAX = 3 };

static char g_probe[PATH_MAX];
static unsigned long g_execs, g_short, g_overflow, g_survived, g_reject, g_slow, g_other;

/* Locate build/bin/vinyl_decode_probe once: $VINYL_DECODE_PROBE overrides, else it
 * sits beside this binary (/proc/self/exe's dir), which is CWD-independent and
 * correct for every build flavour (fuzz/covfuzz/afl all live in build/bin). */
static void init_probe(void) {
  const char *env = getenv("VINYL_DECODE_PROBE");
  if (env && *env) {
    snprintf(g_probe, sizeof g_probe, "%s", env);
    return;
  }
  char self[PATH_MAX];
  ssize_t n = readlink("/proc/self/exe", self, sizeof self - 1);
  if (n <= 0) {
    fprintf(stderr, "fz_decode_stack: cannot resolve /proc/self/exe; "
                    "set VINYL_DECODE_PROBE to build/bin/vinyl_decode_probe\n");
    _exit(1);
  }
  self[n] = '\0';
  snprintf(g_probe, sizeof g_probe, "%s/vinyl_decode_probe", dirname(self));
}

static void report(FILE *o) {
  fprintf(o,
          "[decode_stack] execs=%lu short=%lu overflow=%lu survived=%lu reject=%lu "
          "slow=%lu other_sig=%lu\n",
          g_execs, g_short, g_overflow, g_survived, g_reject, g_slow, g_other);
  bucket_report(o);
}

FUZZ_TARGET(.name = "fz_decode_stack",
            .summary = "decode non-tail interior recursion: bounded-stack child catalogues the ok->crash frontier",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 0, .init = init_probe, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size < 4) {
    g_short++;
    return 0;
  }
  int ch = 1 + (data[0] % 2); /* 1-2 channels: channels add breadth, not depth
                               * (subframes decode sequentially, one at a time) */
  size_t bs = k_bs[data[1] % (sizeof k_bs / sizeof k_bs[0])];
  size_t frames = FRAMES_MIN + (size_t)(data[2] % (FRAMES_MAX - FRAMES_MIN + 1));
  long stack_kb = k_stack_kb[data[3] % (sizeof k_stack_kb / sizeof k_stack_kb[0])];
  /* samples per channel = full frames of the chosen block size, so at least one
   * frame carries a residual of ~blockSize samples -- the deep interior recursion. */
  size_t samples = bs * frames;

  char a_samples[24], a_ch[8], a_bs[24];
  snprintf(a_samples, sizeof a_samples, "%zu", samples);
  snprintf(a_ch, sizeof a_ch, "%d", ch);
  snprintf(a_bs, sizeof a_bs, "%zu", bs);

  pid_t pid = fork();
  if (pid < 0) {
    fprintf(stderr, "fz_decode_stack: fork failed\n");
    _exit(1);
  }
  if (pid == 0) {
    /* Child: bound the stack BEFORE exec so the probe's fresh main-thread stack is
     * the small one, then hand off. A bounded main stack is what makes the per-
     * frame interior recursion overflow at a shallow, fast depth. */
    struct rlimit rl = {.rlim_cur = (rlim_t)stack_kb * 1024, .rlim_max = (rlim_t)stack_kb * 1024};
    setrlimit(RLIMIT_STACK, &rl);
    char *argv[] = {g_probe, a_samples, a_ch, a_bs, (char *)"flac", NULL};
    execv(g_probe, argv);
    _exit(127); /* exec failed -- parent sees 127 and flags it */
  }

  int status;
  while (waitpid(pid, &status, 0) < 0)
    ;

  if (WIFSIGNALED(status)) {
    int sig = WTERMSIG(status);
    if (sig == SIGSEGV || sig == SIGABRT || sig == SIGBUS) {
      /* The decoder overflowed at this (blockSize, ch, frames, stackKB): a non-tail
       * interior shipped-decode loop (readPartsA / readRiceSeqScan / readSIntSeqGo /
       * restoreA / the tail undiff) that regressed to non-tail. */
      g_overflow++;
      bucket_record("decode_stack_overflow", data, size);
      if (fuzz_env_strict() >= FUZZ_STRICT_LEN) {
        fprintf(stderr,
                "\n[DECODE STACK OVERFLOW REGRESSION] Flac.decodePcm16A overflowed the stack\n"
                "  channels=%d blockSize=%zu frames=%zu samples/ch=%zu RLIMIT_STACK=%ldKB sig=%d\n"
                "  (a per-frame INTERIOR shipped-decode loop regressed to non-tail: expected the\n"
                "   tail array forms readRiceSeqScan / readSIntSeqGo / readPartsA / restoreA -- depth ~ bs)\n",
                ch, bs, frames, samples, stack_kb, sig);
        FUZZ_ABORT();
      }
    } else {
      g_other++; /* SIGKILL (watchdog) or similar -- not attributable to the class */
    }
  } else if (WIFEXITED(status)) {
    switch (WEXITSTATUS(status)) {
    case 0: g_survived++; break;
    case 3: g_reject++; break;  /* stream unbuildable or decoder rejected the geometry */
    case 4: g_slow++; break;    /* child alarm -- healthy but slow, not a crash */
    case 127:
      fprintf(stderr, "fz_decode_stack: could not exec %s\n", g_probe);
      _exit(1);
    default: g_other++; break;
    }
  }

  fuzz_tick();
  return 0;
}
