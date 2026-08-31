/* measure_encode -- the encode-side resource MEASUREMENT harness,
 * the mirror of measure_decode. Not a fuzzer: the "finding" here is a RELATIONSHIP
 * (tasks = ceil(nframes / blockSize), and a stack-depth that grows with output
 * size), measured, not a crash at a machine-dependent size.
 *
 *   encoder task storm: `encode … 16 1` spawns ceil(n / blockSize) Tasks with
 *        NO cap -- the decoder caps at maxStepTasks = 1024, the encoder at nothing.
 *        This sweeps blockSize on a fixed input and reports task count, wall time
 *        and peak RSS, so the bs=16-vs-4096 blow-up is a number, not a claim.
 *   non-tail recursion: Unchecked.encode = bitsToBytes (writeStream cfg a),
 *        and bitsToByteList recurses once per OUTPUT byte, so minimum surviving
 *        stack grows with output size. This tool encodes one sizeable input; run
 *        it under a shrinking `ulimit -s` (tools/stack_probe.sh) to find the
 *        threshold -- the depth is what overflows, so it must be probed, not
 *        asserted.
 *
 *   measure_encode [frames_per_channel] [channels]
 *     default sweep: 8192 / 65536 / 262144 frames x blockSize {16, 576, 4096},
 *     stereo. A single (frames, channels) argument pins one input for the stack
 *     probe.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

#include "vinyl_api.h" /* vinyl_init */

/* encodePcm16Fast : Nat -> Nat -> Nat -> ByteArray -> Option ByteArray; the boxed
 * variant owns all args (it borrows sampleRate in the default convention). The
 * fast path is the task-storm surface. The Cfg path (default chooser) is
 * the bitsToByteList surface -- Flac.encodePcm16 routes through it. */
extern lean_object *lp_vinyl_Flac_encodePcm16Fast___boxed(lean_object *bs, lean_object *ch,
                                                          lean_object *sr, lean_object *bytes);
extern lean_object *lp_vinyl_Flac_encodePcm16Cfg(lean_object *cfg, lean_object *ch, lean_object *sr,
                                                 lean_object *bytes);
extern lean_object *lp_vinyl_Flac_Heuristics_defaultAsgChooser(lean_object *b, lean_object *fr);

/* EncoderCfg ⟨blockSize, defaultAsgChooser 16⟩ + uint8 variableBlocking. */
static lean_object *slow_cfg(size_t bs) {
  lean_object *chooser =
      lean_alloc_closure((void *)lp_vinyl_Flac_Heuristics_defaultAsgChooser, 2, 1);
  lean_closure_set(chooser, 0, lean_box(16));
  lean_object *cfg = lean_alloc_ctor(0, 2, 1);
  lean_ctor_set(cfg, 0, lean_usize_to_nat(bs));
  lean_ctor_set(cfg, 1, chooser);
  lean_ctor_set_uint8(cfg, sizeof(void *) * 2, 0);
  return cfg;
}

static long rss_kb(void) {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return ru.ru_maxrss; /* peak, KB on Linux */
}

static double now_s(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

/* Build a whole-frame s16 PCM buffer of `frames` frames x `ch` channels. */
static uint8_t *make_pcm(size_t frames, int ch, size_t *out_len) {
  size_t n = frames * (size_t)ch * 2u;
  uint8_t *p = malloc(n ? n : 1);
  if (!p) {
    fprintf(stderr, "OOM building %zuB PCM\n", n);
    exit(1);
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

static void run_one(size_t frames, int ch, size_t bs, int slow) {
  size_t plen;
  uint8_t *pcm = make_pcm(frames, ch, &plen);
  size_t tasks = (frames + bs - 1) / bs; /* ceil(frames / blockSize) */
  long rss0 = rss_kb();
  double t0 = now_s();

  lean_object *ba = lean_alloc_sarray(1, plen, plen);
  memcpy(lean_sarray_cptr(ba), pcm, plen);
  lean_object *r;
  if (slow)
    r = lp_vinyl_Flac_encodePcm16Cfg(slow_cfg(bs), lean_usize_to_nat((size_t)ch),
                                     lean_usize_to_nat(44100), ba);
  else
    r = lp_vinyl_Flac_encodePcm16Fast___boxed(lean_usize_to_nat(bs), lean_usize_to_nat((size_t)ch),
                                              lean_usize_to_nat(44100), ba);
  int ok = lean_obj_tag(r) == 1;
  size_t flen = ok ? lean_sarray_size(lean_ctor_get(r, 0)) : 0;
  lean_dec(r);

  double dt = now_s() - t0;
  long rss1 = rss_kb();
  printf("  %-4s bs=%-5zu frames=%-8zu ch=%d tasks=ceil(n/bs)=%-9zu enc=%-3s out=%-9zuB "
         "time=%7.3fs peakRSS=%ldMB (+%ldMB)\n",
         slow ? "slow" : "fast", bs, frames, ch, tasks, ok ? "ok" : "NONE", flen, dt, rss1 / 1024,
         (rss1 - rss0) / 1024);
  free(pcm);
}

int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IOLBF, 0); /* line-buffered: rows survive a later abort() */
  if (vinyl_init())
    return 1;
  int ch = argc > 2 ? atoi(argv[2]) : 2;
  if (ch < 1 || ch > 8)
    ch = 2;

  if (argc > 1) {
    /* Pinned single input on the SLOW (bitsToByteList) path: for the stack probe
     * (one encode under `ulimit -s`, tools/stack_probe.sh). bs=4096 keeps the task
     * count sane so the stack depth -- not the task storm -- is what is measured. */
    size_t frames = (size_t)strtoull(argv[1], NULL, 10);
    printf("# measure_encode: pinned input (slow/bitsToByteList path)\n");
    run_one(frames, ch, 4096, 1);
    printf("peak RSS=%ldMB\n", rss_kb() / 1024);
    return 0;
  }

  printf("# measure_encode: blockSize sweep (fast=task storm, slow=bitsToByteList)\n");
  const size_t sweep[] = {8192, 65536, 262144};
  const size_t bss[] = {16, 576, 4096};
  for (size_t si = 0; si < sizeof sweep / sizeof *sweep; si++)
    for (size_t bi = 0; bi < sizeof bss / sizeof *bss; bi++)
      run_one(sweep[si], ch, bss[bi], 0);
  /* Slow-path rows at sizes that SURVIVE the default stack, to show the
   * serialization cost trend. Larger sizes overflow -- that threshold is
   * what tools/stack_probe.sh deliberately finds; running it here would abort the
   * sweep, so it is left to the probe. */
  run_one(sweep[0], ch, 4096, 1); /* 8192 frames survives; 65536+ overflows */
  printf("(slow path overflows the default 8 MB stack at ~%zu frames -- see stack_probe.sh)\n",
         sweep[1]);

  printf("\n--- summary ---\n");
  printf("peak RSS=%ldMB\n", rss_kb() / 1024);
  printf("note: tasks = ceil(nframes/blockSize) with NO cap (the decoder caps at\n");
  printf("      maxStepTasks=1024; the encoder at nothing). bs=16 spawns 256x\n");
  printf("      the tasks of bs=4096 on the same input. bitsToByteList recurses once\n");
  printf("      per output byte; probe the stack threshold with stack_probe.sh.\n");
  return 0;
}
