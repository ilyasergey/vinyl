/* wide_diff.h -- the ANY-DEPTH sample-level differential, the fix for the codec's
 * 16-bit-only test blind spot: the whole rig otherwise tests only at
 * 16 bits while the codec claims 1-32. This oracle compares decoded SAMPLES
 * (int planes), not s16le bytes, so it works at every bit depth libFLAC can
 * emit (4-32). It is additive: a new module + target, touching no existing one.
 *
 * Vinyl side: Flac.Decode.decodeArrays (any depth) -> List (Array Int); a sample
 *   that arrives as a GMP bignum (does not fit int64) is flagged `overflow` and
 *   the comparison for that stream is catalogued, not aborted (garbage-in on a
 *   corrupt stream can drive unbounded Int arithmetic -- undefined vs libFLAC's
 *   int32, so not a clean divergence).
 * libFLAC side: the native `const FLAC__int32 *const buffer[]` planes kept as-is
 *   (no s16le packing, no 16-bit gate).
 *
 * Policy mirrors common/oracle.c exactly: accept/reject and geometry mismatches
 * are catalogued + dumped (FUZZ_STRICT escalates); a genuine SAMPLE divergence
 * on two streams that both decode to the same geometry aborts -- both decoders
 * follow the same spec on a CRC-valid stream, so a disagreement is a real
 * finding. */
#ifndef WIDE_DIFF_H
#define WIDE_DIFF_H

#include <stddef.h>
#include <stdint.h>

#define WIDE_MAX_CH 8

typedef struct {
  const char *name;
  int rc; /* DEC_REJECT / DEC_OK */
  int nch, bps, sr;
  long nsamples;         /* samples per channel */
  int overflow;          /* a Vinyl sample did not fit int64 (bignum) */
  int64_t *plane[WIDE_MAX_CH];
  size_t cap[WIDE_MAX_CH];
} Wide;

/* Oracle tally codes. Exposed here (not a private enum in wide_diff.c) so the
 * targets switch on names rather than magic case-0..8 integers. */
enum {
  WD_BOTH_REJECT = 0,   /* nobody decoded audio                                    */
  WD_ALL_OK,            /* Vinyl agrees with >=1 reference and contradicts none    */
  WD_VINYL_ONLY,        /* Vinyl accepts, BOTH references reject (P5 / accept-set)  */
  WD_REF_ONLY,          /* Vinyl rejects, BOTH references accept (completeness gap) */
  WD_SKIP,              /* out of scope: metadata-only, bignum overflow             */
  WD_GEOM,              /* Vinyl geometry differs from the reference(s)             */
  WD_REF_DISAGREE,      /* the two references disagree; Vinyl sided with one        */
  WD_HDR_CLASH,         /* frame-vs-STREAMINFO clash: skipped, counted apart (F5)   */
  WD_OUT_OF_CONTRACT,   /* Vinyl's reconstruction escapes FitsSInt(bps), libFLAC-  */
                        /* corroborated -- the decoder-has-no-output-contract class */
};

/* Decode the same bytes three ways. Each fills a caller-owned Wide whose plane
 * buffers are reused across calls (call wide_reset before each). The two
 * references (libFLAC, ffmpeg/libavcodec) are a referee triangulation:
 * two independent decoders let the oracle tell "Vinyl is the
 * outlier" (a spec-reading bug) apart from "the two referees disagree and Vinyl
 * picked a side" (referee laxness, not a Vinyl defect). ffmpeg left-justifies
 * >16-bit samples into int32; ffmpeg_wide_decode normalizes them back to the
 * right-aligned values libFLAC and Vinyl report, so all three are comparable. */
void wide_reset(Wide *w, const char *name);
int flac_wide_decode(const uint8_t *in, size_t n, Wide *w);   /* libFLAC, native planes */
int vinyl_wide_decode(const uint8_t *in, size_t n, Wide *w);  /* Vinyl decodeArrays */
int ffmpeg_wide_decode(const uint8_t *in, size_t n, Wide *w); /* libavcodec, normalized planes */

/* Decode `in` with libFLAC MD5 CHECKING on and compare Vinyl's STREAMINFO MD5 to
 * libFLAC's MD5 of the decoded audio. MD5_MISMATCH is a sound finding (a non-zero
 * MD5 that did not match => Vinyl's MD5 convention diverges from RFC 9639 §9.2.2,
 * never validated above 16-bit); MD5_UNCHECKED means the stream had no comparable
 * MD5 or did not cleanly decode. */
enum { MD5_UNCHECKED = -1, MD5_MISMATCH = 0, MD5_MATCH = 1 };
int flac_md5_verify(const uint8_t *in, size_t n);

/* Compare vin (Vinyl) against the two references flc (libFLAC) and ffm (ffmpeg);
 * dumps + FUZZ_STRICT like oracle.c. A sample divergence in which Vinyl
 * contradicts every comparable reference and matches none abort()s -- both
 * references follow the same spec on a CRC-valid stream, so Vinyl is the
 * outlier. Returns a small tally code. */
int wide_diff_oracle(const uint8_t *data, size_t size, const Wide *vin, const Wide *flc,
                     const Wide *ffm);

#endif /* WIDE_DIFF_H */
