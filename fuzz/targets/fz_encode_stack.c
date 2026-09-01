/* fz_encode_stack -- autonomous rediscovery of C04, the encoder's non-tail
 * recursion stack overflow (findings/encoder-stack-overflow-CONFIRMED).
 *
 * The class: Lean does no TCO-modulo-cons, so an `f x :: rec ...` shape keeps one
 * native frame per element. The per-SAMPLE loops (bitsToByteList, pcm16OfByteList,
 * deinterleaveN) got @[csimp] tail swaps on 2026-08-30, and the per-FRAME loops
 * Stream.writeFrames / Stream.chunkChannels PLUS the residual/search loops
 * (Fixed.diff1, Lpc.residualAux, Heuristics.partitionSearch's List.sum->foldl) got
 * theirs on 2026-08-31. A re-baseline (tools/vinyl_encode_probe, 12500 frames at
 * bs=16) now shows NO overflow down to a 128 KB stack -- C04 is FIXED at source.
 *
 * STATUS: this target is now a REGRESSION PIN, expected green. It should catalogue
 * zero overflows; a witness means a NEW un-swapped non-tail loop was introduced
 * (e.g. in concatFrames, Emit.pushFrames, or a future heuristic), which the
 * enumerative stack guarantee cannot otherwise see. The stack guarantee is
 * ENUMERATIVE -- a MISSING swap is invisible to the gate that pins existing swaps
 * -- so a fuzzer that catalogues the ok->crash frontier remains the only route to
 * finding the next un-swapped loop on its own.
 *
 * Why a dedicated child process. It runs the encoder in an ISOLATED child whose
 * stack is bounded small (RLIMIT_STACK, set before an execv -- the exact mechanism
 * tools/stack_probe.sh uses via `ulimit -s`), reads the child's SIGABRT/SIGSEGV as
 * the witness, and records the (samples, channels, blockSize, stackKB) ok->crash
 * relationship WITHOUT aborting the fuzzer. A bounded stack would make any
 * regression reachable at a few thousand frames, so each probe stays fast.
 *
 * This is a CLASS catalogue by default (like every other detector): a child that
 * overflows is bucketed, not fatal. FUZZ_STRICT>=1 escalates it to a hard abort so
 * a regression/strict campaign pins "the encoder overflows again" as a finding.
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

/* Geometry lattice. Small blockSizes drive the FLAC-frame count (recursion depth)
 * up; small stacks make the overflow reachable early. The sweep over BOTH axes is
 * the class relationship the finding demands -- the crossover MOVES with input
 * size and stack size, it is not one magic number. */
static const size_t k_bs[] = {16, 64, 256, 1024, 4096};
/* 256 KB is the floor: below it even a trivial encode overflows (uninformative).
 * The per-frame recursion overflow band sits at 256-1024 KB for the frame counts
 * a <=200k-sample probe reaches; 2048-8192 KB anchor the survivor side (8 MB is a
 * real deployment's main stack). The crossover moving across this span IS C04. */
static const long k_stack_kb[] = {256, 512, 1024, 2048, 4096, 8192};
/* Samples/channel cap: the largest input a single probe builds. ceil(200000/16) =
 * 12500 frames is deep enough to overflow every bounded stack in the lattice, and
 * a survivor (large stack, no overflow) encodes 200k samples in well under the
 * child's alarm. PCM is at most 200000*8*2 = 3.2 MB of heap. */
enum { SAMPLES_MAX = 200000, SAMPLES_MIN = 64 };

static char g_probe[PATH_MAX];
static unsigned long g_execs, g_short, g_overflow, g_survived, g_reject, g_slow, g_other;

/* Locate build/bin/vinyl_encode_probe once: $VINYL_ENCODE_PROBE overrides, else it
 * sits beside this binary (/proc/self/exe's dir), which is CWD-independent and
 * correct for every build flavour (fuzz/covfuzz/afl all live in build/bin). */
static void init_probe(void) {
  const char *env = getenv("VINYL_ENCODE_PROBE");
  if (env && *env) {
    snprintf(g_probe, sizeof g_probe, "%s", env);
    return;
  }
  char self[PATH_MAX];
  ssize_t n = readlink("/proc/self/exe", self, sizeof self - 1);
  if (n <= 0) {
    fprintf(stderr, "fz_encode_stack: cannot resolve /proc/self/exe; "
                    "set VINYL_ENCODE_PROBE to build/bin/vinyl_encode_probe\n");
    _exit(1);
  }
  self[n] = '\0';
  snprintf(g_probe, sizeof g_probe, "%s/vinyl_encode_probe", dirname(self));
}

static void report(FILE *o) {
  fprintf(o,
          "[encode_stack] execs=%lu short=%lu overflow=%lu survived=%lu reject=%lu "
          "slow=%lu other_sig=%lu\n",
          g_execs, g_short, g_overflow, g_survived, g_reject, g_slow, g_other);
  bucket_report(o);
}

FUZZ_TARGET(.name = "fz_encode_stack",
            .summary = "C04 encoder non-tail recursion: bounded-stack child catalogues the ok->crash frontier",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 0, .init = init_probe, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size < 6) {
    g_short++;
    return 0;
  }
  int ch = 1 + (data[0] % 8);
  size_t bs = k_bs[data[1] % (sizeof k_bs / sizeof k_bs[0])];
  /* 24-bit sample count so the whole [MIN, SAMPLES_MAX] range -- and thus the
   * deeper frame counts a larger bounded stack needs -- is reachable. */
  size_t samples = SAMPLES_MIN + ((size_t)(data[2] | (data[3] << 8) | (data[4] << 16)) %
                                  (SAMPLES_MAX - SAMPLES_MIN));
  long stack_kb = k_stack_kb[data[5] % (sizeof k_stack_kb / sizeof k_stack_kb[0])];

  char a_samples[24], a_ch[8], a_bs[24];
  snprintf(a_samples, sizeof a_samples, "%zu", samples);
  snprintf(a_ch, sizeof a_ch, "%d", ch);
  snprintf(a_bs, sizeof a_bs, "%zu", bs);

  pid_t pid = fork();
  if (pid < 0) {
    fprintf(stderr, "fz_encode_stack: fork failed\n");
    _exit(1);
  }
  if (pid == 0) {
    /* Child: bound the stack BEFORE exec so the probe's fresh main-thread stack is
     * the small one, then hand off. A bounded main stack is what makes the per-
     * frame recursion overflow at a shallow, fast depth. */
    struct rlimit rl = {.rlim_cur = (rlim_t)stack_kb * 1024, .rlim_max = (rlim_t)stack_kb * 1024};
    setrlimit(RLIMIT_STACK, &rl);
    char *argv[] = {g_probe, a_samples, a_ch, a_bs, NULL};
    execv(g_probe, argv);
    _exit(127); /* exec failed -- parent sees 127 and flags it */
  }

  int status;
  while (waitpid(pid, &status, 0) < 0)
    ;

  if (WIFSIGNALED(status)) {
    int sig = WTERMSIG(status);
    if (sig == SIGSEGV || sig == SIGABRT || sig == SIGBUS) {
      /* The encoder overflowed at this (samples, ch, blockSize, stackKB): C04's
       * NEW un-swapped non-tail recursion -- a REGRESSION (C04 was fixed 2026-08). */
      g_overflow++;
      bucket_record("encode_stack_overflow", data, size);
      if (fuzz_env_strict() >= FUZZ_STRICT_LEN) {
        fprintf(stderr,
                "\n[ENCODER STACK OVERFLOW REGRESSION] Flac.encodePcm16Cfg overflowed the stack\n"
                "  samples/ch=%zu channels=%d blockSize=%zu frames=%zu RLIMIT_STACK=%ldKB sig=%d\n"
                "  (C04 was fixed via @[csimp] tail swaps; a witness = a NEW un-swapped per-frame\n"
                "   non-tail loop, e.g. in concatFrames / Emit.pushFrames / a heuristic)\n",
                samples, ch, bs, (samples + bs - 1) / bs, stack_kb, sig);
        FUZZ_ABORT();
      }
    } else {
      g_other++; /* SIGKILL (watchdog) or similar -- not attributable to the class */
    }
  } else if (WIFEXITED(status)) {
    switch (WEXITSTATUS(status)) {
    case 0: g_survived++; break;
    case 3: g_reject++; break;  /* encoder rejected the geometry */
    case 4: g_slow++; break;    /* child alarm -- healthy but slow, not a crash */
    case 127:
      fprintf(stderr, "fz_encode_stack: could not exec %s\n", g_probe);
      _exit(1);
    default: g_other++; break;
    }
  }

  fuzz_tick();
  return 0;
}
