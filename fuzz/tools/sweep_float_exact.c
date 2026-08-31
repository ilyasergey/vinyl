/* sweep_float_exact -- the deterministic CI sibling of fz_float_exact. The fuzz
 * target proved (soundly) that Vinyl's Float (=double) LPC search can select a
 * different quantized coefficient vector than exact/long-double arithmetic once
 * the raw autocorrelation lag sums cross 2^53 (24/32-bit content). That crossing
 * is CONTENT-dependent, its coverage is flat, and it burns campaign executions on
 * a surface a fixed grid covers better. This tool sweeps a deterministic grid and
 * PINS the divergence set as a regression fixture:
 *
 *   grid = bps in {16,20,24,32}  x  LPC order 1..32  x  precision 5..15
 *          x  a fixed adversarial signal library {sine, altmax, noise, dc}.
 *
 * The signal axis is REQUIRED: the 2^53 crossing depends on the actual content,
 * so amplitude/shape (scaled to each bps) is what decides whether the double
 * autocorr diverges from exact. For each cell it drives Vinyl's own compiled
 * autocorrF/levinson/quantizeCoefs (the SAME externs + borrow discipline
 * fz_float_exact.c uses) and compares against a long-double (80-bit) recompute of
 * the identical pipeline (levinson_ld/quantize_ld, verbatim from the fuzz target).
 *
 * A cell is a DIVERGENCE when Vinyl's vector differs from the exact-autocorr
 * recompute (differs), the difference is attributable to the autocorr precision
 * loss rather than double-vs-long-double arithmetic (a long-double CONTROL fed
 * Vinyl's own lossy autocorr reproduces Vinyl), and that loss is proven (the
 * double autocorr provably differs from the __int128 exact value). bps<=16 can
 * never reach here -- the double autocorr is exact there -- which is the model
 * self-test (div16 must be 0).
 *
 * REGRESSION PIN: k_allow is the committed set of known-divergent (bps,order,prec,
 * signal) cells. A divergence NOT in k_allow is an unexpected regression and fails
 * the run; a listed cell that no longer diverges is flagged (the codec changed and
 * the pin is stale). Prints `sweep_float_exact: G cells, D divergences (all
 * expected)` and exits non-zero on an unexpected divergence (or a model self-test
 * violation). Set SWEEP_DUMP=1 to print every divergent cell (used to (re)build
 * k_allow after an intentional change).
 */
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "vinyl_api.h" /* vinyl_init */

/* Vinyl's compiled Float LPC-search primitives. Ownership (verified Phase 5D,
 * see fz_float_exact.c): autocorrF/levinson BORROW their array arg (the ___boxed
 * wrapper dec's it, so the caller keeps ownership and dec's its own ref);
 * quantizeCoefs CONSUMES its List Float. Nat args are scalar boxes. */
extern lean_object *lp_vinyl_Flac_Heuristics_autocorrF(lean_object *w, lean_object *maxLag);
extern lean_object *lp_vinyl_Flac_Heuristics_levinson(lean_object *r, lean_object *ord);
extern lean_object *lp_vinyl_Flac_Heuristics_quantizeCoefs(lean_object *cf, lean_object *prec);

#define N 4096
#define MAX_ORD 32
#define TWO53 ((__int128)1 << 53)
#define SINE_CYCLES 2.0 /* full-scale tone: cycles across the block. A low-frequency
                         * full-scale tone over-modelled at order>2 is rank-deficient,
                         * so the autocorr precision loss flips the (unstable) tail LPC
                         * coefficients -- this is the 24-bit order-4 finding fz_float_exact
                         * discovered, made deterministic. */

enum { SIG_SINE = 0, SIG_ALTMAX, SIG_NOISE, SIG_DC, SIG_COUNT };
static const char *sig_name[SIG_COUNT] = {"sine", "altmax", "noise", "dc"};
static const int bps_grid[] = {16, 20, 24, 32};

/* ---- expected-divergence allowlist (regression pin) ------------------------
 * The committed set of known-divergent cells. Seeded from the fz_float_exact
 * finding (a 24-bit full-scale sine selects a different LPC vector than exact
 * arithmetic) and completed from an SWEEP_DUMP=1 census of the grid. Regenerate
 * with SWEEP_DUMP=1 after any intentional change to the Float search. */
typedef struct {
  int bps, order, prec, sig;
} cell_t;

static const cell_t k_allow[] = {
    /* A 24-bit full-scale 2-cycle sine over-modelled at order>=3 is rank-deficient
     * (a single tone is a rank-2 process), so the double autocorr's 2^53 precision
     * loss flips the unstable tail LPC coefficients after quantization to prec=14.
     * This is fz_float_exact's finding (24-bit sine, order 4 included), made a
     * deterministic fixture. Census: SWEEP_DUMP=1. */
    {24, 3, 14, SIG_SINE},  {24, 4, 14, SIG_SINE},  {24, 5, 14, SIG_SINE},
    {24, 6, 14, SIG_SINE},  {24, 7, 14, SIG_SINE},  {24, 8, 14, SIG_SINE},
    {24, 9, 14, SIG_SINE},  {24, 10, 14, SIG_SINE}, {24, 11, 14, SIG_SINE},
    {24, 12, 14, SIG_SINE}, {24, 13, 14, SIG_SINE}, {24, 14, 14, SIG_SINE},
    {24, 15, 14, SIG_SINE}, {24, 16, 14, SIG_SINE}, {24, 17, 14, SIG_SINE},
    {24, 18, 14, SIG_SINE}, {24, 19, 14, SIG_SINE}, {24, 20, 14, SIG_SINE},
    {24, 21, 14, SIG_SINE}, {24, 22, 14, SIG_SINE}, {24, 23, 14, SIG_SINE},
    {24, 24, 14, SIG_SINE}, {24, 25, 14, SIG_SINE}, {24, 26, 14, SIG_SINE},
    {24, 27, 14, SIG_SINE}, {24, 28, 14, SIG_SINE}, {24, 29, 14, SIG_SINE},
    {24, 30, 14, SIG_SINE}, {24, 31, 14, SIG_SINE}, {24, 32, 14, SIG_SINE},
};
static unsigned char g_seen_allow[sizeof k_allow / sizeof k_allow[0] == 0
                                      ? 1
                                      : sizeof k_allow / sizeof k_allow[0]];

static int allow_index(int bps, int order, int prec, int sig) {
  size_t na = sizeof k_allow / sizeof k_allow[0];
  for (size_t i = 0; i < na; i++)
    if (k_allow[i].bps == bps && k_allow[i].order == order && k_allow[i].prec == prec &&
        k_allow[i].sig == sig)
      return (int)i;
  return -1;
}

/* ---- long double (80-bit) reimplementations, verbatim from fz_float_exact.c -- */

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
    unsigned long long f = (unsigned long long)floorl(s0);
    shift = f < 15 ? (int)f : 15;
  }
  long double scale = (long double)(1u << shift);
  long long lo = -(1LL << (prec - 1)), hi = (1LL << (prec - 1));
  long double e = 0.0L;
  for (int i = 0; i < ord; i++) {
    long double v = cf[i] * scale + e;
    long double q = roundl(v);
    e = v - q;
    long long qi = (long long)q;
    out[i] = qi < lo ? lo : (qi >= hi ? hi - 1 : qi);
  }
  *shift_out = shift;
}

/* ---- Lean FFI helpers, verbatim from fz_float_exact.c ----------------------- */

static lean_object *mk_float_list(const double *v, int n) {
  lean_object *lst = lean_box(0);
  for (int i = n - 1; i >= 0; i--) {
    lean_object *cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, lean_box_float(v[i]));
    lean_ctor_set(cell, 1, lst);
    lst = cell;
  }
  return lst;
}

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

/* ---- signal library --------------------------------------------------------
 * All signals are scaled to the bps (that is why the axis is required): the
 * autocorr magnitude, hence whether the double sum crosses 2^53, is a function
 * of amplitude. half = 2^(bps-1); full-scale positive = half-1, negative = -half. */
static uint64_t sig_rng;

static void gen_signal(int sig, int bps, int64_t *s) {
  const int64_t half = (int64_t)1 << (bps - 1);
  const int64_t amp = half - 1;
  switch (sig) {
  case SIG_SINE:
    for (int i = 0; i < N; i++) {
      double ph = 2.0 * M_PI * SINE_CYCLES * (double)i / (double)N;
      s[i] = (int64_t)llround((double)amp * sin(ph));
    }
    break;
  case SIG_ALTMAX:
    for (int i = 0; i < N; i++)
      s[i] = (i & 1) ? -half : amp;
    break;
  case SIG_NOISE:
    sig_rng = 0x123456789ABCDEF0ULL ^ ((uint64_t)bps << 40); /* fixed per (sig,bps) */
    for (int i = 0; i < N; i++) {
      uint64_t x = sig_rng;
      x ^= x << 13;
      x ^= x >> 7;
      x ^= x << 17;
      sig_rng = x;
      uint64_t span = (uint64_t)half * 2u;
      s[i] = (int64_t)(x % span) - half;
    }
    break;
  case SIG_DC:
    for (int i = 0; i < N; i++)
      s[i] = amp;
    break;
  }
}

/* ---- one grid cell ---------------------------------------------------------
 * Returns 1 if the cell diverges (a finding), 0 otherwise. Aborts on a detector
 * bug (exact-regime mismatch) or a bps<=16 divergence (model self-test). */
static int analyze(int bps, int ord, int prec, int sig, const int64_t *s) {
  static __int128 r_exact[MAX_ORD + 1], part_max[MAX_ORD + 1], prod_max[MAX_ORD + 1];
  static double r_dbl[MAX_ORD + 1];
  for (int lag = 0; lag <= ord; lag++) {
    __int128 acc = 0, mx = 0, pmx = 0;
    double d = 0.0;
    for (int i = lag; i < N; i++) {
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
  if (r_exact[0] == 0)
    return 0;

  lean_object *w = lean_alloc_sarray(sizeof(double), N, N);
  double *wc = (double *)lean_sarray_cptr(w);
  for (int i = 0; i < N; i++)
    wc[i] = (double)s[i];

  lean_object *r_arr = lp_vinyl_Flac_Heuristics_autocorrF(w, lean_box((size_t)ord)); /* borrows w */
  lean_dec(w);
  double rf[MAX_ORD + 1];
  size_t rsz = lean_array_size(r_arr);
  for (int lag = 0; lag <= ord; lag++)
    rf[lag] = (lag < (int)rsz) ? lean_unbox_float(lean_array_get_core(r_arr, lag)) : 0.0;

  int diverged = 0;
  for (int lag = 0; lag <= ord; lag++) {
    int exact_regime = prod_max[lag] < TWO53 && part_max[lag] < TWO53;
    if (exact_regime) {
      if (rf[lag] != (double)r_exact[lag] || r_dbl[lag] != (double)r_exact[lag]) {
        fprintf(stderr,
                "\n[DETECTOR BUG] autocorr range/model wrong: lag=%d exact-regime but\n"
                "  vinyl r_float=%.20g  r_dbl=%.20g  r_exact=%.20g (bps=%d ord=%d sig=%s)\n",
                lag, rf[lag], r_dbl[lag], (double)r_exact[lag], bps, ord, sig_name[sig]);
        abort();
      }
    } else if ((double)r_exact[lag] != rf[lag]) {
      diverged = 1;
    }
  }

  lean_object *cf_arr = lp_vinyl_Flac_Heuristics_levinson(r_arr, lean_box((size_t)ord)); /* borrows */
  lean_dec(r_arr);
  double cvf[MAX_ORD];
  size_t csz = lean_array_size(cf_arr);
  for (int i = 0; i < ord; i++)
    cvf[i] = (i < (int)csz) ? lean_unbox_float(lean_array_get_core(cf_arr, i)) : 0.0;
  lean_object *cf_list = mk_float_list(cvf, ord);
  lean_dec(cf_arr);

  lean_object *qc = lp_vinyl_Flac_Heuristics_quantizeCoefs(cf_list, lean_box((size_t)prec)); /* consumes */
  long long coefs_v[MAX_ORD];
  int nv = read_int_list(lean_ctor_get(qc, 0), ord, coefs_v);
  lean_object *shf = lean_ctor_get(qc, 1);
  int shift_v = lean_is_scalar(shf) ? (int)lean_unbox(shf) : -1;
  lean_dec(qc);

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

  int differs = (nv != ord) || (shift_v != shift_ld);
  for (int i = 0; i < ord && !differs; i++)
    if (coefs_v[i] != coefs_ld[i])
      differs = 1;
  int attributable = (nv == ord) && (shift_v == shift_ctrl);
  for (int i = 0; i < ord && attributable; i++)
    if (coefs_v[i] != coefs_ctrl[i])
      attributable = 0;

  if (differs && attributable && diverged) {
    if (bps <= 16) {
      fprintf(stderr,
              "\n[MODEL SELF-TEST VIOLATION] bps<=16 must never diverge (double autocorr is\n"
              "  exact there): bps=%d ord=%d prec=%d sig=%s\n",
              bps, ord, prec, sig_name[sig]);
      abort();
    }
    return 1;
  }
  return 0;
}

int main(void) {
  if (vinyl_init())
    return 1;
  int dump = getenv("SWEEP_DUMP") != NULL;
  static int64_t s[N];

  unsigned long cells = 0, divergences = 0, unexpected = 0;
  for (size_t bi = 0; bi < sizeof bps_grid / sizeof bps_grid[0]; bi++) {
    int bps = bps_grid[bi];
    for (int sig = 0; sig < SIG_COUNT; sig++) {
      gen_signal(sig, bps, s);
      for (int ord = 1; ord <= MAX_ORD; ord++) {
        for (int prec = 5; prec <= 15; prec++) {
          cells++;
          if (!analyze(bps, ord, prec, sig, s))
            continue;
          divergences++;
          int ai = allow_index(bps, ord, prec, sig);
          if (dump)
            printf("[div] {%d, %d, %d, SIG_%s},\n", bps, ord, prec,
                   sig == SIG_SINE ? "SINE" : sig == SIG_ALTMAX ? "ALTMAX"
                                          : sig == SIG_NOISE    ? "NOISE"
                                                                : "DC");
          if (ai < 0) {
            unexpected++;
            fprintf(stderr,
                    "[UNEXPECTED DIVERGENCE] bps=%d order=%d prec=%d sig=%s -- not in k_allow\n",
                    bps, ord, prec, sig_name[sig]);
          } else {
            g_seen_allow[ai] = 1;
          }
        }
      }
    }
  }

  /* Flag stale pins: allowlisted cells that no longer diverge (codec changed). */
  size_t na = sizeof k_allow / sizeof k_allow[0];
  unsigned long stale = 0;
  for (size_t i = 0; i < na; i++)
    if (!g_seen_allow[i]) {
      stale++;
      fprintf(stderr,
              "[FLAG] allowlisted cell no longer diverges: bps=%d order=%d prec=%d sig=%s\n",
              k_allow[i].bps, k_allow[i].order, k_allow[i].prec, sig_name[k_allow[i].sig]);
    }

  if (unexpected)
    printf("sweep_float_exact: %lu cells, %lu divergences (%lu UNEXPECTED)\n", cells, divergences,
           unexpected);
  else
    printf("sweep_float_exact: %lu cells, %lu divergences (all expected)%s\n", cells, divergences,
           stale ? " -- STALE pins flagged" : "");
  return unexpected ? 1 : 0;
}
