# Float LPC search selects a different quantized coefficient vector than exact arithmetic (>2⁵³)

**Status: CONFIRMATION of engagement item §1.4 / F5b — NOT claimed as novel, and NOT a
correctness finding.** Source review established that the encoder's `Float` exactness
argument is scoped to 16-bit and fails above 2⁵³. This entry records a dynamically
found, sound witness of the resulting coefficient-vector divergence.

## What Vinyl does

`Heuristics.autocorrF` / `levinson` / `quantizeCoefs` run the LPC search in IEEE-754
`Float`. The documented premise is that all intermediates stay integers below 2⁵³, so
the `Float` result equals exact arithmetic. That premise holds for 16-bit input but
fails by orders of magnitude at 24/32-bit (measured max intermediate: 24-bit ≈ 38×2⁵³,
32-bit ≈ 2.5M×2⁵³). Past 2⁵³, `Float` rounds, and the rounded autocorrelation can steer
Levinson + quantization to a **different** quantized coefficient vector than an exact
recompute would choose.

Detector: `fz_float_exact` reimplements the search in exact `__int128` autocorrelation
+ `long double` Levinson/quantize, and requires the exact regime (both max product and
max partial sum < 2⁵³) before it will judge — so a divergence is attributed to genuine
`Float` loss, not to the detector's own approximation (`float_autocorr_inexact` is the
separate, expected inexactness census). The 6h `official` run reported
**`float_exact_divergence = 517`**.

## Reproducer

`repro.bin` (RAW G1 parameter block that regenerates the exact Audio+cfg).
`sha256: 25d4889b1a01a753630870dea6583ef748b93475fc4496ff78b2996b0a346e43`

```sh
cd fuzz
FUZZ_STRICT=2 build/bin/fz_float_exact.fuzz -runs=1 findings/float-lpc-coefficient-divergence/repro.bin
# [FLOAT-EXACT DIVERGENCE] bps=32 order=11 prec=6 | shift vinyl=4 exact=4
#   coefs vinyl = 16 0 0 0 0 0 0 0 0 0 0
#   coefs exact = 16 0 0 0 0 0 0 0 0 0 -1
```

## Reference behaviour

None needed — this is Vinyl-internal (its `Float` search vs its own exact model). The
**round trip still holds**: whichever subframe the chooser picks is validated against a
decidable certificate and the capstone quantifies over the chooser, so the decoded
samples are unaffected. The divergence is in *which* valid encoding is emitted.

## Category

Claim-surface / compression-quality (engagement §1.4). The finding is not a bug in the
theorems; it is that the encoder's byte output is **not the exact-arithmetic optimum**
off the 16-bit path, while `COVERAGE.md` advertises encode at bit depths 1–32 and the
differential test that substitutes for the (impossible) `Float` theorem runs on 16-bit
material — so the pin is vacuous exactly where the reasoning stops holding. Companion
hazard (source, not fuzzable on one host): `Float.log2` in `quantizeCoefs`/`expectedBits`
is libm and not correctly-rounded, so the chosen bytes are deterministic per-platform,
not across platforms (§9.1).
