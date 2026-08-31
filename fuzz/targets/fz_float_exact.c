/* fz_float_exact (PHASE2 F5b) -- a SOUND differential on Vinyl's Float (=double)
 * LPC search. Heuristics.lean documents its autocorrelation/Levinson pass as
 * computing "every value an integer well inside 2^53", but at 24/32-bit the raw
 * autocorrelation lag sums Sigma_i s[i]*s[i+lag] reach ~2^75, far past a double's
 * 53-bit mantissa. So `double` autocorr is INEXACT there, and the quantized LPC
 * coefficient vector Vinyl selects can differ from what exact/higher-precision
 * arithmetic would select. Round-trip still holds (this is a search/claim defect,
 * class C), so no decoder-tolerance oracle sees it.
 *
 * Oracle per exec (all three stages are Vinyl's own compiled symbols):
 *   1. parse bps in {16,20,24,32} (biased 24/32), order 1..32, prec 5..15, and n
 *      integer samples each in [-2^(bps-1), 2^(bps-1)).
 *   2. w = FloatArray of the samples cast to double (NO window -- w = raw samples).
 *   3. r_float = autocorrF(w, ord)               (Array Float, lags 0..ord)
 *   4. r_exact[lag] = Sigma s[i]*s[i+lag] in __int128 (EXACT), SAME ascending range
 *      as acorr1/acorr3. VALIDATION: a lag is in the EXACT REGIME when every product
 *      s[i]*s[i+lag] (up to 2^62 at 32-bit) AND every partial sum stay < 2^53; there
 *      r_float MUST equal r_exact -- a mismatch is a RANGE/MODEL bug and aborts
 *      loudly (never a "finding"). This is the bps=16 self-test.
 *   5. autocorr diverged: outside the exact regime, (double)r_exact != r_float --
 *      i.e. a value exceeded 2^53 and the double search provably lost it.
 *   6. MAIN ORACLE: (coefs_v,shift_v) = quantizeCoefs(levinson(r_float,ord), prec)
 *      vs (coefs_ld,shift_ld) from a long double (80-bit) reimplementation of BOTH
 *      algorithms seeded with r_exact. On a difference with bps>16 AND the double
 *      autocorr provably diverged from exact -> float_exact_divergence (catalogue).
 *      Aborts under FUZZ_STRICT>=1; catalogue-only by default (a claim/quality
 *      finding, not a crash). A long-double CONTROL fed Vinyl's own r_float gates
 *      the finding so only autocorr-attributable divergences flag. SELF-TEST: at
 *      bps=16 the double autocorr is exact (diverged is false), so the finding can
 *      never fire there -- div16 counts any bps<=16 flag and is a required-0
 *      invariant of a correct model.
 *
 * Input kind: RAW. */
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h" /* oracle_dump_write */

/* Vinyl's compiled Float LPC-search primitives. Ownership (from the generated IR
 * + its ___boxed wrappers): autocorrF/levinson BORROW their array arg (the boxed
 * wrapper does the dec, so the caller keeps ownership); quantizeCoefs CONSUMES its
 * List Float. The Nat args are scalar boxes (lean_box), so never heap-freed.
 * VERIFIED (Phase 5D) against Heuristics.c: autocorrF___boxed calls autocorrF(w,..)
 * then `lean_dec_ref(w)`, and levinson___boxed calls levinson(r,..) then
 * `lean_dec_ref(r)` -- the unboxed callees do NOT consume, so the harness owning +
 * lean_dec'ing its own array ref (below) is correct; there is no double free. */
extern lean_object *lp_vinyl_Flac_Heuristics_autocorrF(lean_object *w, lean_object *maxLag);
extern lean_object *lp_vinyl_Flac_Heuristics_levinson(lean_object *r, lean_object *ord);
extern lean_object *lp_vinyl_Flac_Heuristics_quantizeCoefs(lean_object *cf, lean_object *prec);

#define MAX_N 4608
#define MAX_ORD 32
#define TWO53 ((__int128)1 << 53)

static unsigned long g_execs, g_analyzed, g_autocorr_inexact, g_float_div, g_div16;

static void report(FILE *o) {
  fprintf(o,
          "[float_exact] execs=%lu analyzed=%lu | autocorr_inexact(>=2^53)=%lu | "
          "float_exact_divergence=%lu | bps<=16_divergences=%lu (MUST be 0)\n",
          g_execs, g_analyzed, g_autocorr_inexact, g_float_div, g_div16);
}

FUZZ_TARGET(.name = "fz_float_exact",
            .summary = "sound differential: Vinyl Float LPC search vs exact/long-double recompute",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .report = report)

/* ---- long double (80-bit) reimplementations, EXACTLY matching the Lean bodies -- */

/* levinson (Heuristics.lean): order-`ord` forward predictor from autocorr `r`
 * (r[0..ord]); early-freeze when err <= 0 leaves the tail coefficients at 0, just
 * as `levinson`'s `if err <= f0 then return lpc`. */
static void levinson_ld(const long double *r, int ord, long double *lpc) {
  for (int j = 0; j < ord; j++)
    lpc[j] = 0.0L;
  long double err = r[0];
  for (int i = 0; i < ord; i++) {
    if (err <= 0.0L)
      return;
    long double acc = r[i + 1];
    for (int j = 0; j < i; j++)
      acc -= lpc[j] * r[i - j];
    long double k = acc / err;
    long double old[MAX_ORD];
    for (int j = 0; j < i; j++)
      old[j] = lpc[j];
    for (int j = 0; j < i; j++)
      lpc[j] = old[j] - k * old[i - 1 - j];
    lpc[i] = k;
    err = err * (1.0L - k * k);
  }
}

/* quantizeCoefs (Heuristics.lean): error-feedback quantization to `prec`-bit
 * integers with a shift. round() = round-half-away-from-zero (roundl); the shift
 * is floor(log2(maxval/cmax)) truncated toward zero and clamped to 15; floatToInt
 * of an already-integral q is its exact value; clampSInt prec -> [-2^(p-1),2^(p-1)-1]. */
static void quantize_ld(const long double *cf, int ord, int prec, long long *out, int *shift_out) {
  long double cmax = 0.0L;
  for (int i = 0; i < ord; i++) {
    long double a = fabsl(cf[i]);
    if (a > cmax)
      cmax = a;
  }
  if (cmax <= 0.0L) {
    for (int i = 0; i < ord; i++)
      out[i] = 0;
    *shift_out = 0;
    return;
  }
  long double maxval = (long double)((1u << (prec - 1)) - 1u);
  long double s0 = log2l(maxval / cmax);
  int shift;
  if (s0 <= 0.0L)
    shift = 0;
  else {
    unsigned long long f = (unsigned long long)floorl(s0); /* toUInt64 truncation */
    shift = f < 15 ? (int)f : 15;
  }
  long double scale = (long double)(1u << shift);
  long long lo = -(1LL << (prec - 1)), hi = (1LL << (prec - 1));
  long double e = 0.0L;
  for (int i = 0; i < ord; i++) {
    long double v = cf[i] * scale + e;
    long double q = roundl(v);
    e = v - q;
    long long qi = (long long)q; /* floatToInt of integral q */
    out[i] = qi < lo ? lo : (qi >= hi ? hi - 1 : qi);
  }
  *shift_out = shift;
}

/* ---- Lean FFI helpers ------------------------------------------------------- */

static lean_object *mk_float_list(const double *v, int n) {
  lean_object *lst = lean_box(0); /* [] */
  for (int i = n - 1; i >= 0; i--) {
    lean_object *cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, lean_box_float(v[i]));
    lean_ctor_set(cell, 1, lst);
    lst = cell;
  }
  return lst;
}

/* Read up to `n` Int elements (all far inside int64) out of a Lean List Int. */
static int read_int_list(lean_object *l, int n, long long *out) {
  int k = 0;
  for (; k < n && !lean_is_scalar(l); k++) {
    lean_object *h = lean_ctor_get(l, 0);
    out[k] = lean_is_scalar(h) ? lean_scalar_to_int64(h) : 0;
    l = lean_ctor_get(l, 1);
  }
  return k;
}

static inline __int128 i128abs(__int128 x) { return x < 0 ? -x : x; }

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size < 3 + 4 * 2)
    return 0;

  static const int bps_tab[8] = {16, 16, 20, 24, 24, 24, 32, 32};
  int bps = bps_tab[data[0] & 7];
  int ord = 1 + (data[1] % MAX_ORD);
  int prec = 5 + (data[2] % 11);

  size_t avail = (size - 3) / 4;
  int n = avail > MAX_N ? MAX_N : (int)avail;
  if (n < ord + 1)
    return 0;

  static int64_t s[MAX_N];
  const uint32_t mask = bps < 32 ? ((1u << bps) - 1u) : 0xFFFFFFFFu;
  const int64_t half = (int64_t)1 << (bps - 1);
  for (int i = 0; i < n; i++) {
    const uint8_t *p = data + 3 + 4 * i;
    uint32_t u = (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
                 ((uint32_t)p[3] << 24);
    int64_t v = (int64_t)(u & mask);
    if (v >= half)
      v -= (int64_t)1 << bps;
    s[i] = v;
  }

  /* Exact autocorrelation in __int128, ascending in i (acorr1/acorr3 order). The
   * double path is bit-exact for a lag ONLY when every intermediate is exactly
   * representable: each PRODUCT s[i]*s[i+lag] (up to 2^62 at 32-bit!) AND every
   * partial sum stay < 2^53. Tracking the max product separately is essential --
   * at >=24-bit a product alone can exceed 2^53 and round before it is ever
   * summed, so a small final |r| does NOT imply an exact double result. */
  static __int128 r_exact[MAX_ORD + 1], part_max[MAX_ORD + 1], prod_max[MAX_ORD + 1];
  static double r_dbl[MAX_ORD + 1];
  for (int lag = 0; lag <= ord; lag++) {
    __int128 acc = 0, mx = 0, pmx = 0;
    double d = 0.0;
    for (int i = lag; i < n; i++) {
      __int128 prod = (__int128)s[i] * (__int128)s[i - lag];
      acc += prod;
      __int128 pa = i128abs(prod);
      if (pa > pmx)
        pmx = pa;
      __int128 a = i128abs(acc);
      if (a > mx)
        mx = a;
      d += (double)s[i] * (double)s[i - lag];
    }
    r_exact[lag] = acc;
    part_max[lag] = mx;
    prod_max[lag] = pmx;
    r_dbl[lag] = d;
  }
  if (r_exact[0] == 0) /* all-zero block: both pipelines return zeros trivially */
    return 0;

  /* w = FloatArray of the raw samples cast to double. */
  lean_object *w = lean_alloc_sarray(sizeof(double), n, n);
  double *wc = (double *)lean_sarray_cptr(w);
  for (int i = 0; i < n; i++)
    wc[i] = (double)s[i];

  lean_object *r_arr = lp_vinyl_Flac_Heuristics_autocorrF(w, lean_box((size_t)ord)); /* borrows w */
  lean_dec(w);
  double rf[MAX_ORD + 1];
  size_t rsz = lean_array_size(r_arr);
  for (int lag = 0; lag <= ord; lag++)
    rf[lag] = (lag < (int)rsz) ? lean_unbox_float(lean_array_get_core(r_arr, lag)) : 0.0;

  /* Soundness self-test + inexactness census. A lag is in the EXACT REGIME when
   * every product and every partial sum is < 2^53; there the double autocorr must
   * equal the integer value (this is the bps=16 self-test). Outside it, a mismatch
   * is the false-invariant evidence: some value exceeded 2^53 and double lost it. */
  int diverged = 0; /* double autocorr provably differs from exact somewhere */
  for (int lag = 0; lag <= ord; lag++) {
    int exact_regime = prod_max[lag] < TWO53 && part_max[lag] < TWO53;
    if (exact_regime) {
      if (rf[lag] != (double)r_exact[lag] || r_dbl[lag] != (double)r_exact[lag]) {
        fprintf(stderr,
                "\n[DETECTOR BUG] autocorr range/model wrong: lag=%d exact-regime but\n"
                "  vinyl r_float=%.20g  r_dbl=%.20g  r_exact=%.20g (n=%d bps=%d ord=%d)\n"
                "  -- the exact model disagrees with Vinyl's own exact double result\n",
                lag, rf[lag], r_dbl[lag], (double)r_exact[lag], n, bps, ord);
        oracle_dump_write("float_detector_bug", data, size);
        abort();
      }
    } else if ((double)r_exact[lag] != rf[lag]) {
      /* a value exceeded 2^53 AND the double result differs from exact */
      diverged = 1;
    }
  }
  if (diverged) {
    g_autocorr_inexact++;
    oracle_dump_write("float_autocorr_inexact", data, size);
  }

  /* MAIN ORACLE: Vinyl levinson+quantize (double) vs long-double recompute. */
  lean_object *cf_arr = lp_vinyl_Flac_Heuristics_levinson(r_arr, lean_box((size_t)ord)); /* borrows r_arr */
  lean_dec(r_arr);
  double cvf[MAX_ORD];
  size_t csz = lean_array_size(cf_arr);
  for (int i = 0; i < ord; i++)
    cvf[i] = (i < (int)csz) ? lean_unbox_float(lean_array_get_core(cf_arr, i)) : 0.0;
  lean_object *cf_list = mk_float_list(cvf, ord);
  lean_dec(cf_arr);

  lean_object *qc = lp_vinyl_Flac_Heuristics_quantizeCoefs(cf_list, lean_box((size_t)prec)); /* consumes cf_list */
  long long coefs_v[MAX_ORD];
  int nv = read_int_list(lean_ctor_get(qc, 0), ord, coefs_v);
  lean_object *shf = lean_ctor_get(qc, 1);
  int shift_v = lean_is_scalar(shf) ? (int)lean_unbox(shf) : -1;
  lean_dec(qc);

  /* Two long-double recomputes of the SAME pipeline (levinson then quantize):
   *   coefs_ld   -- seeded with the EXACT autocorr r_exact (the high-precision
   *                 reference "what exact arithmetic would have selected").
   *   coefs_ctrl -- seeded with Vinyl's own lossy r_float. A CONTROL: it shares
   *                 Vinyl's exact input, so when it reproduces Vinyl's quantized
   *                 vector, the recompute faithfully models Vinyl for this input,
   *                 and any coefs_v vs coefs_ld difference is then attributable to
   *                 the autocorr precision loss (r_float != r_exact), NOT to
   *                 double-vs-long-double arithmetic. */
  long double r_ld[MAX_ORD + 1], r_ctrl[MAX_ORD + 1];
  for (int lag = 0; lag <= ord; lag++) {
    r_ld[lag] = (long double)r_exact[lag];
    r_ctrl[lag] = (long double)rf[lag];
  }
  long double cf_tmp[MAX_ORD];
  long long coefs_ld[MAX_ORD], coefs_ctrl[MAX_ORD];
  int shift_ld, shift_ctrl;
  levinson_ld(r_ld, ord, cf_tmp);
  quantize_ld(cf_tmp, ord, prec, coefs_ld, &shift_ld);
  levinson_ld(r_ctrl, ord, cf_tmp);
  quantize_ld(cf_tmp, ord, prec, coefs_ctrl, &shift_ctrl);

  g_analyzed++;

  int differs = (nv != ord) || (shift_v != shift_ld);
  for (int i = 0; i < ord && !differs; i++)
    if (coefs_v[i] != coefs_ld[i])
      differs = 1;
  /* the recompute reproduces Vinyl on the identical (lossy) autocorr */
  int attributable = (nv == ord) && (shift_v == shift_ctrl);
  for (int i = 0; i < ord && attributable; i++)
    if (coefs_v[i] != coefs_ctrl[i])
      attributable = 0;

  /* SOUND finding: Vinyl's selected vector differs from the exact recompute, the
   * difference is attributable to the autocorr precision loss, and that loss is
   * proven (diverged). bps<=16 can never reach here (diverged is false there),
   * which is the model self-test -- div16 must stay 0. */
  if (differs && attributable && diverged) {
    if (bps <= 16) {
      g_div16++;
    } else {
      g_float_div++;
      oracle_dump_write("float_exact_divergence", data, size);
      /* Catalogue-only by default (a quality/claim finding, not a crash). Under
       * FUZZ_STRICT>=1 print full triage and abort so a strict/regression run pins
       * it. Also print the first occurrence so a plain run shows one witness. */
      if (fuzz_env_strict() >= FUZZ_STRICT_LEN || g_float_div == 1) {
        fprintf(stderr,
                "\n[FLOAT-EXACT DIVERGENCE] Vinyl's Float LPC search selected a different quantized\n"
                "  coefficient vector than an exact-autocorr recompute (round-trip still holds).\n"
                "  bps=%d order=%d prec=%d | shift vinyl=%d exact=%d\n",
                bps, ord, prec, shift_v, shift_ld);
        fprintf(stderr, "  coefs vinyl =");
        for (int i = 0; i < ord; i++)
          fprintf(stderr, " %lld", coefs_v[i]);
        fprintf(stderr, "\n  coefs exact =");
        for (int i = 0; i < ord; i++)
          fprintf(stderr, " %lld", coefs_ld[i]);
        fprintf(stderr, "\n");
      }
      if (fuzz_env_strict() >= FUZZ_STRICT_LEN)
        abort();
    }
  }

  fuzz_tick();
  return 0;
}
