/* libFLAC 1.4.2 (reference/flac-src, instrumented) decode from a MEMORY buffer.
 * Same return codes and PCM layout as vinyl_api.h: interleaved s16le,
 * wrapper-owned buffer reused across calls. */
#ifndef FLAC_API_H
#define FLAC_API_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#include "vinyl_api.h" /* DEC_REJECT / DEC_OK / DEC_SKIP */

/* Full-stream decode with MD5 checking off. DEC_OK only if the decoder ends
 * in FLAC__STREAM_DECODER_END_OF_STREAM with no error callback fired; a
 * partial decode ending in e.g. FLAC__STREAM_DECODER_ABORTED is DEC_REJECT.
 * Any non-16-bit STREAMINFO or frame -> DEC_SKIP. */
int flac_decode(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len,
                int *bps, int *ch, int *sr);


/* --- encoder wrappers (folded in from encode_api.h) --- */
/* Encode-side wrappers for the differential fuzzer: Vinyl's proven fast
 * encoder (Flac.encodePcm16Fast) and libFLAC 1.4.2's stream encoder, both
 * from/to memory. PCM input is interleaved signed 16-bit little-endian;
 * output buffers are wrapper-owned, reused across calls, grown geometrically
 * (one buffer per wrapper, so vinyl and libFLAC outputs never alias). */


#define ENC_REJECT 0 /* encoder refused the parameters/payload */
#define ENC_OK 1     /* out+len hold a complete FLAC stream    */

/* libFLAC stream encoder to a memory buffer: verify off, streamable-subset
 * off (so blockSize/sampleRate combos legal for Vinyl are testable), 16-bit,
 * total_samples_estimate set so STREAMINFO carries the sample count. */
int flac_encode(const uint8_t *pcm, size_t n, int bs, int ch, int sr, int level,
                uint8_t **out, size_t *len);

/* --- strict flac -t validator (folded in from flac_validate.h) --- */
/* flac_validate.h — a strict `flac -t` equivalent used as an ASSERTION on
 * Vinyl's OWN encoder output. The existing flac_api.c disables MD5 checking, so
 * nothing in the decode-diff oracle catches a wrong STREAMINFO MD5 or a
 * frame-vs-STREAMINFO inconsistency. This wrapper turns MD5 checking ON and,
 * given the original PCM, verifies (a) the decoded stream matches it, (b) the
 * STREAMINFO MD5 matches, and (c) the STREAMINFO is self-consistent with the
 * frames per RFC 9639 §9.1 (Table 3, lines 773-795):
 *   - minBlock/maxBlock in [16,65535], minBlock <= maxBlock;
 *   - every NON-LAST frame's block size in [minBlock, maxBlock];
 *   - the LAST frame's block size <= maxBlock (it may be below minBlock -- the
 *     RFC explicitly excludes the last block from the minimum, so Vinyl's
 *     min==max fixed-block STREAMINFO with a short final frame is CONFORMANT,
 *     a verified negative, and must NOT abort);
 *   - every frame's (channels, bps) == STREAMINFO's, and sample_rate too when
 *     STREAMINFO's is nonzero;
 *   - totalSamples, when nonzero, equals the decoded interchannel count.
 * A failure is the client's bug class (b): corrupted output the reference
 * would reject. */


typedef struct {
  const char *why;   /* NULL if valid; else the failure reason */
  int decoded_ok;    /* stream reached END_OF_STREAM with no error callback */
  int md5_ok;        /* STREAMINFO MD5 matched the decoded audio */
  int streaminfo_ok; /* STREAMINFO consistent with the frames (RFC 9639 §9.1) */
  size_t decoded_len;
  int bps, ch, sr;
  /* STREAMINFO snapshot + observed framing, for the report. */
  int si_min_bs, si_max_bs, si_ch, si_bps, si_sr;
  unsigned long si_total, frames, samples, frame_min_bs, frame_max_bs;
} FlacValidation;

/* Returns 1 if `flac`/`flen` is a valid stream that decodes back to `pcm`/`plen`
 * with a matching STREAMINFO MD5 and a self-consistent STREAMINFO; 0 otherwise
 * (with v->why set). A metadata-only stream (plen==0, no frames) is valid. */
int flac_validate_strict(const uint8_t *flac, size_t flen, const uint8_t *pcm, size_t plen,
                         FlacValidation *v);

void flac_validate_report(FILE *o, const FlacValidation *v, const uint8_t *flac, size_t flen);

#endif
