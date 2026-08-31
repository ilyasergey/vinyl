/* Thin C wrappers over Vinyl's Lean-generated decode entry points.
 * Return codes shared with flac_api.h: see DEC_* below.
 * PCM output is interleaved signed 16-bit little-endian; the buffer is owned
 * by the wrapper, reused across calls, grown geometrically. */
#ifndef VINYL_API_H
#define VINYL_API_H

#include <stddef.h>
#include <stdint.h>

#define DEC_REJECT 0 /* decoder rejected the input                */
#define DEC_OK 1     /* full decode, PCM valid                    */
#define DEC_SKIP 2   /* stream is not 16-bit -> out of diff scope */

/* Initialize the Lean runtime + Vinyl module. Call once, from
 * LLVMFuzzerInitialize, before any vinyl_* call. Returns 0 on success. */
int vinyl_init(void);

/* The CLI `--decode-fast` path: Flac.Decode.decodeBytes with the
 * Flac.Decode.decodeArrays + Stream.pcmBytesRange fallback (exactly what
 * FuzzHarness.lean and FlacTest/Cli.lean do). On DEC_OK, pcm+len describe the
 * interleaved s16le buffer and bps, ch, sr the stream parameters. */
int vinyl_decode_fast(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len,
                      int *bps, int *ch, int *sr);

/* How many vinyl_decode_fast DEC_OK results the fused byte decoder served vs how
 * many fell back to the sample path. A target that cites decodeBytes_spec should
 * surface these so a fast-lane claim over a fallback-served decode is visible,
 * and a fused count of 0 flags that the byte decoder is never exercised. */
unsigned long vinyl_decode_fused_count(void);
unsigned long vinyl_decode_fallback_count(void);

#endif
