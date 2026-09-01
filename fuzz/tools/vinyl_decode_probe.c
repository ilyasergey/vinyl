/* vinyl_decode_probe -- a single-shot, RLIMIT_STACK-bounded DECODE, the child
 * process fz_decode_stack forks + execs. It is the decode-side mirror of
 * tools/vinyl_encode_probe: isolation lives in the exec (the parent sets
 * RLIMIT_STACK before execv, so THIS process's fresh main-thread stack is sized
 * to the requested bound -- the mechanism tools/stack_probe.sh uses via
 * `ulimit -s`; a running thread's mapped stack cannot be shrunk, an exec's fresh
 * one can). It builds a decode-STRESS FLAC stream that maximizes per-frame decode
 * depth, then runs the PRODUCTION decoder (vm_decode_pcm16 -> Flac.decodePcm16A,
 * the CLI `--decode-pcm16` path) on it and either exits 0 (survived) or dies with a
 * signal if a per-frame non-tail decode loop overflows the bounded stack.
 *
 *   vinyl_decode_probe <samples_per_channel> <channels> <blockSize>
 *
 * WHY the production decoder (and why this is a PIN, not a hunt). This runs the
 * SHIPPED array decoder (vm_decode_pcm16 -> Flac.decodePcm16A), whose residual layer
 * is the tail ARRAY forms Flac.Decode.readRiceSeqScan / readSIntSeqGo / readPartsA /
 * restoreA -- verified stack-flat: it survives here at every stack size. This is a
 * forward GREEN regression PIN: a signal means a FUTURE change reintroduced a non-tail
 * loop into the shipped decode path, which the enumerative @[csimp] gate (it only pins
 * the swaps that EXIST) cannot see. A LARGE block size drives the residual length --
 * and thus every interior loop's depth -- toward the block size; a small RLIMIT_STACK
 * makes any regression reachable at a shallow, fast depth, so each probe stays quick.
 * NOTE: the shipped array decoder does NOT use Flac.Rice.readRiceSeq / readSIntSeq
 * (the IR confirms Flac/Native/Decode.c calls no Flac.Rice.readRiceSeq*); those readers
 * -- and the @[csimp] tail swaps readRiceSeqTR / readSIntSeqTR added to Native/Rice.lean
 * -- live only on the List-Bool reference decoder (Flac.Stream.decodeReference), which
 * is known to overflow on deep input by construction and is deliberately NOT probed
 * here. So this target does not exercise those two swaps; it pins the shipped decoder.
 *
 * Why encode-then-decode is honest here. Two emitters (arg 4; fz_decode_stack drives
 * "flac"):
 *   flac (default lane): libFLAC's encoder emits a LEGAL stream at bs up to 65535, which
 *     the checked Lean encoder cannot. It runs in C entirely outside the Lean codec, and
 *     its own stack use (~8 KB: lp_coeff[32][32] + small qlp/autoc arrays) is far below
 *     the probe's smallest RLIMIT_STACK (256 KB, k_stack_kb[0] in fz_decode_stack), so the
 *     BUILD step cannot overflow at any stack size the probe uses -- a SIGSEGV/SIGABRT is
 *     the DECODER, not the emitter.
 *   checked: Flac.encodePcm16Cfg (vm_encode_slow), @[csimp] tail-recursive and re-baselined
 *     overflow-free to 128 KB, capped at bs 4608 (so the builder clamps there). Kept for a
 *     Vinyl-encoded round-trip variant. (The raw Unchecked.encode is NOT used: it can emit
 *     bs up to 65535 but is not bounded-stack-safe out of the checked envelope, which would
 *     mis-attribute an ENCODE overflow to the decoder.)
 *
 * Exit codes mirror the encode probe: 0 survived, 3 the stream could not be built
 * or the decoder rejected it, 4 the watchdog alarm fired (too slow, not a crash);
 * a stack overflow is a SIGABRT ("Stack overflow detected. Aborting.") or a
 * SIGSEGV (guard page), never an exit code.
 */
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "vinyl_api.h"   /* vinyl_init, DEC_* */
#include "vinyl_modes.h" /* vm_encode_slow, vm_decode_pcm16 */
#include "flac_api.h"    /* flac_encode, ENC_OK -- the libFLAC emitter lane */

enum { EXIT_SURVIVED = 0, EXIT_REJECT = 3, EXIT_TOOSLOW = 4 };
enum { PROBE_ALARM_S = 8 };

/* SIGALRM default disposition is to KILL with a signal; the parent would then see
 * WIFSIGNALED and mistake a slow-but-healthy decode for a stack crash. Turn it
 * into a clean "too slow" exit instead. _exit is async-signal-safe. */
static void on_alarm(int sig) {
  (void)sig;
  _exit(EXIT_TOOSLOW);
}

/* Correlated s16le PCM: a triangle wave (predicted well by the fixed/LPC
 * predictors, so the encoder emits FIXED/LPC subframes with Rice-coded residuals
 * -- driving readResidual -> readParts -> readRiceSeq and Fixed.restore/undiff1 /
 * Lpc.restore/restoreAux) plus a tiny xorshift dither so the residuals are
 * consistently NONZERO (an exactly-predictable signal would collapse to a CONSTANT
 * subframe, whose reader does not recurse). The result is compressible but well
 * within Flac.Stream.decodeBudget (4096 * inputBytes + 65536), so the reference
 * decoder reaches the deep per-frame loop instead of bailing on the bomb bound.
 * frames = samples per channel, so the buffer is frames*ch*2 bytes. */
static uint8_t *make_pcm(size_t frames, int ch, size_t *out_len) {
  size_t n = frames * (size_t)ch * 2u;
  uint8_t *p = malloc(n ? n : 1);
  if (!p) {
    fprintf(stderr, "vinyl_decode_probe: OOM building %zuB PCM\n", n);
    _exit(1);
  }
  uint32_t s = 0x2468ace0u;
  for (size_t i = 0; i < frames; i++) {
    /* triangle of period 512, amplitude ~16384 (well inside 16-bit) */
    size_t m = i % 512u;
    int32_t tri = (int32_t)(m < 256u ? m : 512u - m) * 64;
    for (int c = 0; c < ch; c++) {
      s ^= s << 13;
      s ^= s >> 17;
      s ^= s << 5;
      int32_t dither = (int32_t)(s % 7u) - 3; /* [-3, 3] */
      int16_t v = (int16_t)(tri + dither + c); /* per-channel offset */
      size_t idx = (i * (size_t)ch + (size_t)c) * 2;
      p[idx] = (uint8_t)(v & 0xFF);
      p[idx + 1] = (uint8_t)((v >> 8) & 0xFF);
    }
  }
  *out_len = n;
  return p;
}

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: %s <samples_per_channel> <channels> <blockSize> [checked|flac]\n", argv[0]);
    return 2;
  }
  size_t frames = (size_t)strtoull(argv[1], NULL, 10);
  int ch = atoi(argv[2]);
  size_t bs = (size_t)strtoull(argv[3], NULL, 10);
  /* Emitter: "checked" = the Lean checked encoder (bs<=4608, the shipped envelope);
   * "flac" = libFLAC (bs up to 65535, a legal deep frame the checked encoder cannot
   * emit -- lets the pin reach the max block size, with the emitter entirely OUTSIDE
   * the Lean attribution chain so a decode signal is unambiguously the decoder). */
  const char *emit = argc >= 5 ? argv[4] : "checked";
  int use_flac = strcmp(emit, "flac") == 0;
  if (ch < 1 || ch > 8 || bs < 1 || frames < 1)
    return 2;

  /* A non-overflowing input still has to fully encode AND decode; alarm() bounds
   * the wall time so a large-stack/large-block survivor cannot hang the probe. */
  signal(SIGALRM, on_alarm);
  alarm(PROBE_ALARM_S);

  /* Decode on the MAIN thread, where RLIMIT_STACK bounds the recursion;
   * LEAN_NUM_THREADS=1 (set by the fleet job, defaulted here) keeps a Task
   * worker's separate stack from confounding the main recursion depth. */
  if (!getenv("LEAN_NUM_THREADS"))
    setenv("LEAN_NUM_THREADS", "1", 1);

  size_t plen;
  uint8_t *pcm = make_pcm(frames, ch, &plen);
  if (vinyl_init())
    return 1;

  /* Build the stress stream. Two emitters, both keeping the BUILD step off the
   * bounded-stack decoder's attribution:
   *   checked: Flac.encodePcm16Cfg (vm_encode_slow) -- @[csimp] tail-recursive loops,
   *     re-baselined stack-safe to 128 KB, so the build never overflows. Gates
   *     blockSize <= 4608, so clamp there (the shipped-encoder envelope).
   *   flac:    libFLAC's encoder (flac_encode, subset off) -- emits a LEGAL stream at
   *     bs up to 65535, which the checked encoder cannot, and runs in C entirely
   *     outside the Lean codec, so a SIGSEGV/SIGABRT from this process is unambiguously
   *     the Vinyl DECODER at a block size no other lane reaches. */
  /* Both emitters return an internally-owned buffer (flac_api's static e_out; or
   * vm_encode_slow's reused vm_buf) -- NOT a caller allocation, so neither is freed. */
  uint8_t *stream = NULL;
  size_t slen = 0;
  if (use_flac) {
    if (flac_encode(pcm, plen, (int)bs, ch, 44100, 5, &stream, &slen) != ENC_OK || !slen) {
      free(pcm);
      return EXIT_REJECT; /* libFLAC refused the geometry -- no stream to decode */
    }
  } else {
    size_t enc_bs = bs > 4608 ? 4608 : bs;
    if (!vm_encode_slow(pcm, plen, enc_bs, (size_t)ch, 44100, &stream, &slen)) {
      free(pcm);
      return EXIT_REJECT; /* unusable geometry -- no stream to decode */
    }
  }
  free(pcm);

  /* Re-arm the alarm so the DECODE gets its own full budget: the single alarm above
   * covers encode+decode, and the checked heuristic encoder at a large (samples,ch)
   * can plausibly burn most of it -- which would exit EXIT_TOOSLOW before the decoder
   * runs and make a "survived" verdict vacuous. Resetting here guarantees the decode
   * phase is actually exercised (or times out on its own merit). */
  alarm(PROBE_ALARM_S);

  /* Run the PRODUCTION decoder (vm_decode_pcm16 -> Flac.decodePcm16A, the CLI
   * `--decode-pcm16` path) over the deep stream under the bounded stack. Its
   * interior loops are the tail ARRAY forms (readPartsA / readRiceSeqScan / restoreA /
   * the tail undiff), so this is expected to SURVIVE at every stack size -- the
   * target is a regression PIN: a signal here means a future codec change introduced
   * a non-tail loop into the shipped decode path, which the enumerative @[csimp]
   * gate cannot see. (The List-Bool reference decoder decodeReference is known to
   * overflow on deep input by design -- that is prior art, not what this probes.) */
  uint8_t *out;
  size_t olen;
  int bps, dch, sr;
  int rc = vm_decode_pcm16(stream, slen, &out, &olen, &bps, &dch, &sr);
  return rc == DEC_OK ? EXIT_SURVIVED : EXIT_REJECT;
}
