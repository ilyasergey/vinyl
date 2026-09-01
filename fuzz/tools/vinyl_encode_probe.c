/* vinyl_encode_probe -- a single-shot, RLIMIT_STACK-bounded encode, the child
 * process fz_encode_stack forks + execs. Isolation lives in the exec: the parent
 * sets RLIMIT_STACK before execv, so THIS process's main-thread stack is sized to
 * the requested bound (the exact mechanism tools/stack_probe.sh uses via
 * `ulimit -s`; a running thread's already-mapped stack cannot be shrunk, an exec's
 * fresh one can). It then runs the SLOW encode path (Flac.encodePcm16Cfg, via
 * vm_encode_slow) on incompressible PCM and either exits 0 (survived) or dies with
 * a signal when the encoder's per-frame non-tail recursion overflows the stack.
 *
 *   vinyl_encode_probe <samples_per_channel> <channels> <blockSize>
 *
 * The overflow class this reaches is C04's REMAINING un-swapped encode loops:
 * Stream.writeFrames / Stream.chunkChannels recurse once per FLAC frame =
 * ceil(samples/blockSize), with no @[csimp] tail-recursive swap (the per-sample
 * loops bitsToByteList/pcm16OfByteList/deinterleaveN were swapped 2026-08-30, so
 * they no longer overflow). A small blockSize + many samples drives the frame
 * count -- and thus the recursion depth -- high; a small RLIMIT_STACK makes the
 * overflow reachable at a few thousand frames, so each probe is fast.
 *
 * The slow Cfg path is pure sequential List recursion (writeStream), NOT the fast
 * path's per-frame Task workers, so there is no task storm to confound the stack
 * depth -- the depth is exactly the frame count. Exit codes: 0 survived, 3 the
 * encoder rejected the geometry, 4 the watchdog alarm fired (too slow, not a
 * crash); a stack overflow is a SIGABRT ("Stack overflow detected. Aborting.")
 * or a SIGSEGV (guard page), never an exit code.
 */
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "vinyl_api.h"   /* vinyl_init */
#include "vinyl_modes.h" /* vm_encode_slow (Flac.encodePcm16Cfg, defaultAsgChooser 16) */

enum { EXIT_SURVIVED = 0, EXIT_REJECT = 3, EXIT_TOOSLOW = 4 };
enum { PROBE_ALARM_S = 8 };

/* SIGALRM default disposition is to KILL with a signal; the parent would then
 * see WIFSIGNALED and mistake a slow-but-healthy encode for a stack crash. Turn
 * it into a clean "too slow" exit instead. _exit is async-signal-safe. */
static void on_alarm(int sig) {
  (void)sig;
  _exit(EXIT_TOOSLOW);
}

/* xorshift32 incompressible s16le PCM -- the worst case for the serializer stack
 * (real audio compresses, zeros compress; the finding quotes the incompressible
 * number). frames = samples per channel, so the buffer is frames*ch*2 bytes. */
static uint8_t *make_pcm(size_t frames, int ch, size_t *out_len) {
  size_t n = frames * (size_t)ch * 2u;
  uint8_t *p = malloc(n ? n : 1);
  if (!p) {
    fprintf(stderr, "vinyl_encode_probe: OOM building %zuB PCM\n", n);
    _exit(1);
  }
  uint32_t s = 0x1234567u;
  for (size_t i = 0; i < frames * (size_t)ch; i++) {
    s ^= s << 13;
    s ^= s >> 17;
    s ^= s << 5;
    int16_t v = (int16_t)((s & 0xFFFF) - 32768);
    p[2 * i] = (uint8_t)(v & 0xFF);
    p[2 * i + 1] = (uint8_t)((v >> 8) & 0xFF);
  }
  *out_len = n;
  return p;
}

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: %s <samples_per_channel> <channels> <blockSize>\n", argv[0]);
    return 2;
  }
  size_t frames = (size_t)strtoull(argv[1], NULL, 10);
  int ch = atoi(argv[2]);
  size_t bs = (size_t)strtoull(argv[3], NULL, 10);
  if (ch < 1 || ch > 8 || bs < 1)
    return 2;

  /* A non-overflowing input still has to fully encode; alarm() bounds the wall
   * time so a large-stack/large-input survivor cannot hang the probe. */
  signal(SIGALRM, on_alarm);
  alarm(PROBE_ALARM_S);

  /* Probe the SLOW encoder on the MAIN thread, where RLIMIT_STACK bounds the
   * recursion; LEAN_NUM_THREADS=1 (set by the fleet job, defaulted here) keeps a
   * Task worker's separate stack from confounding it (stack_probe.sh's rule). */
  if (!getenv("LEAN_NUM_THREADS"))
    setenv("LEAN_NUM_THREADS", "1", 1);

  size_t plen;
  uint8_t *pcm = make_pcm(frames, ch, &plen);
  if (vinyl_init())
    return 1;

  uint8_t *out;
  size_t olen;
  int ok = vm_encode_slow(pcm, plen, bs, (size_t)ch, 44100, &out, &olen);
  /* Reaching here means no overflow. Report nothing on stdout (the parent reads
   * only the exit status); a rejected geometry is distinct from a survivor. */
  free(pcm);
  return ok ? EXIT_SURVIVED : EXIT_REJECT;
}
