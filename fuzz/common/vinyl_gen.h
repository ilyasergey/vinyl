/* vinyl_gen.h -- G1, the Lean-shim generator (the force-multiplier). Drives
 * Stream.Unchecked.encode with a fuzzer-controlled Audio at ARBITRARY bit depth
 * (1-32), channel count (1-8) and sample content, so it emits
 * CORRECT-BY-CONSTRUCTION FLAC across the whole legal option space -- not the
 * 16-bit-only slice every other encode path is stuck at.
 *
 * Why Vinyl's own proven writer is the generator: the bitstream
 * is correct by construction (Frame.write/Subframe.write/Rice.writeResidual are
 * the proven writers -- no CRC placement, no walker, no padding subtlety), and
 * the expected decode is free (the round-trip theorems say it is whatever you
 * handed in). It reaches depths and shapes no external encoder we can drive emits.
 *
 * Sample populations (the r09 caveat: the chooser must yield Valid configs or
 * orVerbatim silently eats the diversity):
 *   VALID       -- sample magnitudes within FitsSInt bps: round-trips cleanly.
 *                  A `population` selector shapes them (uniform noise -> VERBATIM;
 *                  ramp/random-walk/sine -> the chooser picks FIXED/LPC, so there
 *                  are real residuals to bound).
 *   ADVERSARIAL -- samples chosen to stress the estimator and to force the stereo
 *                  reconstruction where a channel's left/side decode lands
 *                  outside FitsSInt bps: the out-of-range witness generator.
 *
 * chooser_kind selects the EncoderCfg chooser: 0 = defaultAsgChooser, 1-3 = the
 * ADVERSARIAL choosers from ../FlacTest/FuzzGen.lean (@[export], arity 1), which
 * force LPC orders 9-32 / mid-side decorrelation / high partition orders the
 * default chooser never emits -- the regions COVERAGE.md claims but nothing
 * exercised. They escape-code every residual, so the output stays bounded, and
 * safeChooser's orVerbatim falls back to VERBATIM on any frame where the config
 * is not Valid. This is the FFI template vinyl_unchecked_encode (vinyl_modes.c)
 * generalized off its hardwired bps=16. */
#ifndef VINYL_GEN_H
#define VINYL_GEN_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
  int bps;             /* 1..32 */
  int ch;              /* 1..8  */
  uint32_t sr;         /* a libFLAC-friendly rate */
  size_t bs;           /* blockSize handed to the encoder */
  size_t nsamples;     /* per channel */
  int adversarial;     /* 0 = VALID population, 1 = ADVERSARIAL */
  int advkind;         /* which adversarial construction (see vinyl_gen.c) */
  int chooser_kind;    /* EncoderCfg chooser: 0 default, 1 hostileLpc32,
                          2 hostileStereo (mid/side), 3 hostilePartition,
                          4 hostileFixed (RICE-coded, reaches the residual-bound /
                          unary surface). The hostile ones (FlacTest/FuzzGen.lean)
                          reach LPC 9-32 / decorrelation / high partition-order /
                          out-of-bound-residual paths the default never emits. */
  int population;      /* VALID sample shape: 0 uniform, 1 ramp, 2 random-walk,
                          3 sine. Correlated shapes (1-3) make the chooser pick
                          FIXED/LPC instead of VERBATIM, so real residuals exist
                          to bound; uniform (0) is high-entropy -> VERBATIM. */
  int expect_contract; /* 1 = this construction is an out-of-range-reconstruction
                          candidate IF the default chooser picks the
                          decorrelating mode; 0 otherwise */
  int in_range;        /* 1 = every generated sample is within [-2^(bps-1), 2^(bps-1)-1]
                          (non-adversarial, or advkind 0). When 0, a residual
                          recomputed as x[i]-pred can be FABRICATED (the samples
                          themselves are out of range), so downstream residual/bound
                          checks must gate on this (Phase 8B). */
} GenParams;

/* Parse `data`/`size` into a GenParams, build the Audio + default-chooser
 * EncoderCfg, and drive Stream.Unchecked.encode. On success returns 1 with *out
 * pointing at an internal reused buffer of *len bytes (correct-by-construction
 * FLAC) and *gp filled; returns 0 if the input is too short to form an Audio. */
int vinyl_gen_encode(const uint8_t *data, size_t size, uint8_t **out, size_t *len, GenParams *gp);

/* Proven-pair variant: build ONE Audio+cfg from `data` and drive BOTH
 * Stream.Unchecked.encode (the reference writer) and Emit.emitFast (the fast
 * statically-verified emitter). On success returns 1 with the two outputs in
 * independent internal buffers -- byte-equal by Flac.Emit.emitFast_eq_encode, so
 * a divergence is a compiler/runtime defect on the encode side. Returns 0 on
 * too-short input. Buffers valid until the next vinyl_gen_encode* call. */
int vinyl_gen_encode_pair(const uint8_t *data, size_t size, uint8_t **unchecked, size_t *ulen,
                          uint8_t **fast, size_t *flen, GenParams *gp);

/* The exact samples of channel `c` from the LAST vinyl_gen_encode call (length
 * gp.nsamples), so a caller can compare a decode against ground truth. NULL if
 * c is out of range. Valid until the next vinyl_gen_encode. */
const int64_t *vinyl_gen_expected(int c);

#endif /* VINYL_GEN_H */
