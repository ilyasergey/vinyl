#include "vinyl_gen.h"

#include <lean/lean.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "ffi_util.h"

/* Stream.Unchecked.encode : EncoderCfg -> Audio -> ByteArray. EncoderCfg
 * ⟨blockSize, chooser⟩ + uint8 variableBlocking; Audio ⟨channels : List (List
 * Int), bps, sampleRate⟩. Layouts confirmed in vinyl_modes.c. */
extern lean_object *vlean_unchecked_encode(lean_object *cfg, lean_object *audio);
/* Phase 7C: stable @[export] name (FlacTest/FuzzGen.lean) not the mangled
 * lp_vinyl_Flac_Emit_emitFast, so a Lean-internal rename is caught by check-symbols. */
extern lean_object *vinyl_emit_fast(lean_object *cfg, lean_object *audio);
extern lean_object *vinyl_default_chooser(lean_object *b, lean_object *fr);
/* Adversarial choosers from FlacTest/FuzzGen.lean (@[export], arity 1). Each is
 * an EncoderCfg.chooser that forces a valid-but-non-default channel assignment. */
extern lean_object *vinyl_hostileLpc32(lean_object *fr);
extern lean_object *vinyl_hostileStereo(lean_object *fr);
extern lean_object *vinyl_hostilePartition(lean_object *fr);
extern lean_object *vinyl_hostileFixed(lean_object *fr);
/* Parameterized hostile choosers (B3, FlacTest/FuzzGen.lean). The captured-Nat
 * arms are arity-2 (captured argument, then the frame); vinyl_hostileInvalid is
 * arity-1. gen_build wraps each arity-2 one in a 1-argument closure over the
 * captured order/po/k/mode, yielding an EncoderCfg.chooser. safeChooser's
 * orVerbatim still keeps every result bounded and valid. */
extern lean_object *vinyl_hostileLpcN(lean_object *ord, lean_object *fr);
extern lean_object *vinyl_hostilePartitionPO(lean_object *po, lean_object *fr);
extern lean_object *vinyl_hostileRice2K(lean_object *k, lean_object *fr);
extern lean_object *vinyl_hostileStereoMode(lean_object *mode, lean_object *fr);
extern lean_object *vinyl_hostileInvalid(lean_object *fr);

/* A libFLAC/ffmpeg-friendly sample-rate set (all resolve without the code-0/15
 * traps), and a spread of block sizes. */
static const uint32_t k_sr[8] = {8000, 16000, 22050, 32000, 44100, 48000, 96000, 192000};
static const uint32_t k_bs[8] = {16, 192, 576, 1152, 2048, 4096, 4608, 1024};

/* Keep the output bounded: Unchecked.encode's bitsToByteList recurses once per
 * output byte, so an unbounded sample count is a stack-overflow DoS on the
 * generator itself, not a useful seed. */
#define GEN_MAX_SAMPLES 2048u

static uint32_t xs32(uint32_t *s) {
  uint32_t x = *s ? *s : 0x9E3779B9u;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  *s = x;
  return x;
}

/* One sample value for channel `c`, index `i`, per the chosen population. `half`
 * = 2^(bps-1), so [-half, half) is FitsSInt bps. */
static int64_t gen_sample(const GenParams *gp, uint32_t *rng, int c, size_t i, int64_t half) {
  if (!gp->adversarial) {
    /* VALID: uniform in [-half, half). */
    uint64_t span = (uint64_t)half * 2u;
    return (int64_t)(xs32(rng) % (span ? span : 1u)) - half;
  }
  switch (gp->advkind & 3) {
    case 0: /* alternating extremes at the FitsSInt boundary */
      return (i & 1) ? (half - 1) : -half;
    case 1: /* stereo out-of-range: constant left = -half, constant right = -3*half+1, so
             * side = left - right = 2*half - 1 (a constant that fits bps+1). The
             * decoder reconstructs right = left - side, OUT of [-half, half). Both
             * subframes are constant, biasing the chooser to pick left/side. */
      if (c == 0)
        return -half;
      if (c == 1)
        return -3 * half + 1;
      return 0;
    case 2: /* just past the boundary (stored value would need bps+1 bits) */
      return (i & 1) ? (half + (int64_t)(xs32(rng) % (uint64_t)(half ? half : 1)))
                     : -half - (int64_t)(xs32(rng) % (uint64_t)(half ? half : 1)) - 1;
    default: /* wide dynamic range around the extremes */
      return (int64_t)(xs32(rng)) - (int64_t)(xs32(rng));
  }
}

/* Fill vals[0..n) for channel `c`. The ADVERSARIAL population uses gen_sample
 * per index; the VALID population uses a CORRELATED shape (ramp / random-walk /
 * sine) so the encoder's chooser picks FIXED/LPC and emits real residuals to
 * bound -- uniform noise (population 0) is high-entropy and the chooser falls
 * back to VERBATIM, which is why fz_residual_bound otherwise analyses ~nothing.
 * Every shape stays within [-half, half-1] so the audio remains FitsSInt(bps). */
static void fill_channel(const GenParams *gp, int64_t *vals, size_t n, int c, int64_t half,
                         uint32_t seed) {
  uint32_t r = seed ^ (uint32_t)(0x1000193u * (uint32_t)(c + 1));
  if (gp->adversarial) {
    for (size_t i = 0; i < n; i++)
      vals[i] = gen_sample(gp, &r, c, i, half);
    return;
  }
  const int64_t lo = -half, hi = half - 1;
  switch (gp->population & 3) {
    case 1: { /* ramp / sawtooth: FIXED order 1-2 predicts it near-exactly */
      int64_t step = 1 + (int64_t)(xs32(&r) % (uint64_t)(half > 8 ? half / 8 : 1));
      int64_t v = lo;
      for (size_t i = 0; i < n; i++) {
        vals[i] = v;
        v += step;
        if (v > hi)
          v = lo;
      }
      break;
    }
    case 2: { /* bounded random walk: strongly FIXED/LPC-friendly */
      int64_t amp = half > 16 ? half / 16 : 1, v = 0;
      for (size_t i = 0; i < n; i++) {
        v += (int64_t)(xs32(&r) % (uint64_t)(2 * amp + 1)) - amp;
        if (v < lo)
          v = lo;
        else if (v > hi)
          v = hi;
        vals[i] = v;
      }
      break;
    }
    case 3: { /* sine: the classic LPC-friendly signal */
      double w = 0.005 + (double)(xs32(&r) % 200) / 4000.0, amp = (double)(half - 1);
      for (size_t i = 0; i < n; i++) {
        int64_t v = (int64_t)(amp * sin(w * (double)i));
        vals[i] = v < lo ? lo : (v > hi ? hi : v);
      }
      break;
    }
    default: /* uniform: high entropy -> VERBATIM */
      for (size_t i = 0; i < n; i++) {
        uint64_t span = (uint64_t)half * 2u;
        vals[i] = (int64_t)(xs32(&r) % (span ? span : 1u)) - half;
      }
  }
}

/* The exact generated samples, retained per channel so fz_gen_roundtrip can
 * compare Vinyl's decode against ground truth (the round-trip theorem says the
 * decode IS these samples) -- the one oracle that needs no referee and cannot be
 * fooled by a common-mode misreading, and the FFI-layout selftest in one. */
static int64_t *g_exp[8];
static size_t g_exp_cap[8];
const int64_t *vinyl_gen_expected(int c) { return (c >= 0 && c < 8) ? g_exp[c] : NULL; }

/* Build List Int for channel `c`, tail-to-head so it is in sample order. */
static lean_object *channel_list(const GenParams *gp, uint32_t seed, int c, int64_t half) {
  lean_object *lst = lean_box(0); /* List.nil */
  size_t n = gp->nsamples;
  int64_t *vals = malloc((n ? n : 1) * sizeof(int64_t));
  if (!vals)
    _exit(1);
  fill_channel(gp, vals, n, c, half, seed);
  if (c >= 0 && c < 8) {
    if (n > g_exp_cap[c]) {
      int64_t *p = realloc(g_exp[c], n * sizeof(int64_t));
      if (!p)
        _exit(1);
      g_exp[c] = p;
      g_exp_cap[c] = n;
    }
    memcpy(g_exp[c], vals, n * sizeof(int64_t));
  }
  for (size_t i = n; i-- > 0;) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, lean_int64_to_int(vals[i]));
    lean_ctor_set(cons, 1, lst);
    lst = cons;
  }
  free(vals);
  return lst;
}

static uint8_t *g_buf;
static size_t g_cap;
static uint8_t *g_buf2; /* second output buffer, for the proven-pair emitter */
static size_t g_cap2;

/* Build the Audio + EncoderCfg the generator's parameters denote, at refcount 1
 * each and WITHOUT consuming them, so a caller can drive one encoder or both.
 * Returns 0 (leaving the out-params untouched) on too-short input. */
static int gen_build(const uint8_t *data, size_t size, GenParams *gp, lean_object **out_audio,
                     lean_object **out_cfg) {
  if (size < 8)
    return 0;

  memset(gp, 0, sizeof *gp);
  gp->bps = 1 + (data[0] % 32);
  gp->ch = 1 + (data[1] % 8);
  gp->adversarial = data[2] & 1;
  gp->advkind = (data[2] >> 1) & 3;
  gp->population = (data[2] >> 3) & 3;    /* VALID sample shape (bits 3-4 of data[2]) */
  gp->chooser_kind = (data[3] >> 3) & 7;  /* EncoderCfg chooser (bits 3-5 of data[3]) */
  /* Captured-argument byte for the parameterized hostile choosers (slots 5-7).
   * gen_build only requires size>=8, so a slot-5/6/7 input with no ninth byte
   * falls back to arg=0 (LPC order 1 / partition order 0 / RICE2 k=0 -- all
   * safe under orVerbatim). */
  unsigned chooser_arg = (size > 8) ? data[8] : 0u;
  gp->bs = k_bs[data[3] & 7];
  gp->sr = k_sr[data[6] & 7];
  uint32_t seed = (uint32_t)data[7] | ((uint32_t)data[4] << 8) | ((uint32_t)data[5] << 16);
  for (size_t i = 8; i < size && i < 64; i++)
    seed = seed * 1000003u + data[i];
  size_t ns = 16u + (((size_t)data[4] | ((size_t)data[5] << 8)) % (GEN_MAX_SAMPLES - 16u));
  /* Unchecked.encode's bitsToByteList recurses once per OUTPUT byte, so the stack
   * cost is bps*ch*nsamples/8, NOT nsamples: at 32-bit x 8ch a 2048-sample block
   * is ~64 KB of output and overflows the (small, worker-thread) Lean stack -- the
   * known encoder-stack-overflow (findings/encoder-stack-overflow-CONFIRMED),
   * which otherwise crash-loops the encode targets on a KNOWN bug instead of
   * exploring. Bound the ESTIMATED output to ~8 KB (verbatim worst case) so every
   * depth/channel combo stays well under the overflow threshold. */
  size_t max_ns = (size_t)(8192u * 8u) / ((size_t)gp->bps * (size_t)gp->ch);
  if (max_ns < 16u)
    max_ns = 16u;
  if (ns > max_ns)
    ns = max_ns;
  gp->nsamples = ns;
  gp->expect_contract = (gp->adversarial && (gp->advkind & 3) == 1 && gp->ch == 2);
  /* 8B: in-range iff non-adversarial, or the adversarial construction is advkind 0
   * (the only adversarial case that stays within the bit-depth envelope -- gen_sample
   * cases 1/2/3 deliberately generate out-of-range samples). */
  gp->in_range = (!gp->adversarial || (gp->advkind & 3) == 0);

  int64_t half = (gp->bps >= 1 && gp->bps <= 62) ? (int64_t)1 << (gp->bps - 1) : 1;

  /* channels : List (List Int), tail-to-head over channel index. */
  lean_object *channels = lean_box(0);
  for (int c = gp->ch; c-- > 0;) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, channel_list(gp, seed, c, half));
    lean_ctor_set(cons, 1, channels);
    channels = cons;
  }
  lean_object *audio = lean_alloc_ctor(0, 3, 0); /* Audio ⟨channels, bps, sampleRate⟩ */
  lean_ctor_set(audio, 0, channels);
  lean_ctor_set(audio, 1, lean_usize_to_nat((size_t)gp->bps));
  lean_ctor_set(audio, 2, lean_usize_to_nat((size_t)gp->sr));

  /* EncoderCfg ⟨blockSize, chooser⟩ + variableBlocking := false. The default
   * chooser captures the ACTUAL bps (arity 2, 1 captured); the hostile choosers
   * are arity-1 EncoderCfg.chooser functions (FlacTest/FuzzGen.lean) that force a
   * valid-but-non-default assignment. safeChooser's orVerbatim keeps a hostile
   * config only when it is Valid for the frame and falls back to VERBATIM
   * otherwise, so every kind is safe. */
  lean_object *chooser;
  switch (gp->chooser_kind) {
    case 1: chooser = lean_alloc_closure((void *)vinyl_hostileLpc32, 1, 0); break;
    case 2: chooser = lean_alloc_closure((void *)vinyl_hostileStereo, 1, 0); break;
    case 3: chooser = lean_alloc_closure((void *)vinyl_hostilePartition, 1, 0); break;
    case 4: chooser = lean_alloc_closure((void *)vinyl_hostileFixed, 1, 0); break;
    /* B3 parameterized choosers. Each captures its Nat argument from chooser_arg
     * (data[8]) into a 1-argument closure over the arity-2 export. */
    case 5: { /* LPC order = 1 + (arg % 32): covers order 7 (the lpcResGo7 hole). */
      chooser = lean_alloc_closure((void *)vinyl_hostileLpcN, 2, 1);
      lean_closure_set(chooser, 0, lean_box((size_t)(1u + (chooser_arg % 32u))));
      break;
    }
    case 6: { /* FIXED partition order from {4,5,6,8}: common orders that keep
               * per-partition allocation bounded on any block size. A very high PO
               * (e.g. 15) on the fuzzer's small/adversarial blocks is degenerate and
               * OOM-prone, so it is intentionally NOT forced here (not remapped-away:
               * genuinely not exercised on the encode side). */
      static const unsigned po_set[4] = {4, 5, 6, 8};
      chooser = lean_alloc_closure((void *)vinyl_hostilePartitionPO, 2, 1);
      lean_closure_set(chooser, 0, lean_box((size_t)po_set[chooser_arg & 3u]));
      break;
    }
    case 7: /* multiplexed on arg's top two bits: RICE2 k / stereo mode / invalid. */
      switch ((chooser_arg >> 6) & 3u) {
        case 1: /* arg 64..127: mid/side stereo mode 0..3 (arg & 3). */
          chooser = lean_alloc_closure((void *)vinyl_hostileStereoMode, 2, 1);
          lean_closure_set(chooser, 0, lean_box((size_t)(chooser_arg & 3u)));
          break;
        case 2: /* arg 128..191: deliberately-invalid assignment (reject arms). */
          chooser = lean_alloc_closure((void *)vinyl_hostileInvalid, 1, 0);
          break;
        default: { /* arg 0..63 (and 192..255): RICE2 k from {18,24,28,30}. All > 17,
                    * so this is exactly the general k>17 readRiceSeqScan path -- the
                    * coverage goal. Small-k RICE2 (k<=17) uses the already-well-covered
                    * readRiceSeqScan3 fast path, and forcing a small k on adversarial
                    * high-bps residuals is an encode-side unary-output explosion (OOM),
                    * so it is intentionally NOT forced here.
                    *
                    * OOM-safety (findings/parallel-decode... sibling harness fix): the
                    * unary quotient per residual is ~zigzag(r)>>k, and a first-difference
                    * residual is ~2^bps, so bits/sample ~ 2^(bps+1-k). The base set is a
                    * COVERAGE criterion (k>17); OOM-safety is a SEPARATE criterion (k~=bps).
                    * At bps>=~22 the base k=18 makes 2^(bps+1-18) explode (8-9 B input ->
                    * ~3.6 GB List Bool before packing). Raise k to at least bps-3 so the
                    * quotient stays <=2^4 bits/sample; still k>17 (the same readRiceSeqScan
                    * path) and still Valid (k<31). Typical <=21-bit seeds keep {18,24,28,30}. */
          static const unsigned k_set[4] = {18, 24, 28, 30};
          unsigned k = k_set[chooser_arg & 3u];
          unsigned kmin = (gp->bps > 3) ? (unsigned)(gp->bps - 3u) : 0u;
          if (k < kmin)
            k = kmin;
          if (k > 30u)
            k = 30u; /* Partition.Valid (.rice k) requires k < 31 */
          chooser = lean_alloc_closure((void *)vinyl_hostileRice2K, 2, 1);
          lean_closure_set(chooser, 0, lean_box((size_t)k));
          break;
        }
      }
      break;
    default:
      chooser = lean_alloc_closure((void *)vinyl_default_chooser, 2, 1);
      lean_closure_set(chooser, 0, lean_box((size_t)gp->bps));
  }
  /* variableBlocking from data[2] bit5 (previously hardwired false). true makes
   * the frame number the RUNNING SAMPLE index (i*blockSize) instead of the frame
   * counter, so multi-frame streams reach the 2-6 byte W.pushUtf8 / W.pushConts
   * coded-number branches that a <128 frame counter never exercises. Unchecked.encode
   * is proven for ANY cfg and the output stays valid FLAC. gen_g1_flac seeds set
   * data[2]=(pop<<3) so bit5=0 -> unchanged; only new fuzzer inputs flip it. */
  uint8_t variable_blocking = (data[2] >> 5) & 1u;
  lean_object *cfg = lean_alloc_ctor(0, 2, 1);
  lean_ctor_set(cfg, 0, lean_usize_to_nat(gp->bs));
  lean_ctor_set(cfg, 1, chooser);
  lean_ctor_set_uint8(cfg, sizeof(void *) * 2, variable_blocking);

  *out_audio = audio;
  *out_cfg = cfg;
  return 1;
}

int vinyl_gen_encode(const uint8_t *data, size_t size, uint8_t **out, size_t *len, GenParams *gp) {
  *out = NULL;
  *len = 0;
  lean_object *audio, *cfg;
  if (!gen_build(data, size, gp, &audio, &cfg))
    return 0;
  lean_object *r = vlean_unchecked_encode(cfg, audio); /* consumes both */
  size_t sz = lean_sarray_size(r);
  memcpy(fuzz_grow(&g_buf, &g_cap, sz ? sz : 1), lean_sarray_cptr(r), sz);
  *out = g_buf;
  *len = sz;
  lean_dec(r);
  return 1;
}

/* Proven-pair driver: Emit.emitFast cfg a == Stream.Unchecked.encode cfg a
 * (Flac.Emit.emitFast_eq_encode -- the theorem the encode-side @[csimp] leans
 * on). Builds ONE Audio+cfg and runs BOTH the fast statically-verified emitter
 * and the reference writer, returning both byte strings in independent internal
 * buffers so a target can assert byte-equality at ARBITRARY depth/chooser. This
 * is the encoder analogue of the decode proven pairs, over the non-16-bit region
 * no other encode path exercises. Returns 0 on too-short input. */
int vinyl_gen_encode_pair(const uint8_t *data, size_t size, uint8_t **unchecked, size_t *ulen,
                          uint8_t **fast, size_t *flen, GenParams *gp) {
  *unchecked = *fast = NULL;
  *ulen = *flen = 0;
  lean_object *audio, *cfg;
  if (!gen_build(data, size, gp, &audio, &cfg))
    return 0;
  /* Both encoders consume one ref of cfg and audio; take a second ref so both
   * calls are well-typed and nothing leaks. */
  lean_inc(audio);
  lean_inc(cfg);
  lean_object *ru = vlean_unchecked_encode(cfg, audio); /* -1 ref each */
  size_t usz = lean_sarray_size(ru);
  memcpy(fuzz_grow(&g_buf, &g_cap, usz ? usz : 1), lean_sarray_cptr(ru), usz);
  lean_dec(ru);
  lean_object *rf = vinyl_emit_fast(cfg, audio); /* -1 ref each (last) */
  size_t fsz = lean_sarray_size(rf);
  memcpy(fuzz_grow(&g_buf2, &g_cap2, fsz ? fsz : 1), lean_sarray_cptr(rf), fsz);
  lean_dec(rf);
  *unchecked = g_buf;
  *ulen = usz;
  *fast = g_buf2;
  *flen = fsz;
  return 1;
}
