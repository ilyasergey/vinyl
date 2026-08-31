/* FLAC frame-structure layer: CRC-8/CRC-16, frame walking + repair, a
 * structure-aware mutator, and a generative CRC-correct stream emitter.
 *
 * Ported from an earlier standalone CRC-fuzz prototype (the bit-level layout, the
 * CRC polynomials, the fixed Rice unary order -- stop bit FIRST -- and the
 * contractive-LPC-coefficient rule all come from there; do not "simplify" them).
 *
 * CRC-8  : poly 0x07,   init 0, unreflected -- over the frame header bytes.
 * CRC-16 : poly 0x8005, init 0, unreflected -- over the whole frame, header
 *          and CRC-8 included, up to but excluding the two CRC-16 bytes.
 * Both match Flac/Native/Crc.lean. Self-check: crc8("123456789")  == 0xF4,
 *                                             crc16("123456789") == 0xFEE8. */
#ifndef FLAC_STRUCT_H
#define FLAC_STRUCT_H

#include <stddef.h>
#include <stdint.h>

uint8_t flac_crc8(const uint8_t *d, size_t n);
uint16_t flac_crc16(const uint8_t *d, size_t n);

/* One frame: [start, end), CRC-16 occupying the last two bytes. */
typedef struct {
  size_t start, end;
} FlacFrame;

#define FLAC_MAX_FRAMES 512

/* Walk a stream and record frame extents. Skips "fLaC" + metadata blocks when
 * present, then splits the remainder at frame-sync boundaries. `strict`
 * additionally requires each candidate sync to carry a *valid* CRC-8, which is
 * the right filter on unmutated input (it rejects false syncs inside subframe
 * bit soup); pass 0 after mutation, when header CRCs are stale.
 * Returns the number of frames written (<= max). */
size_t flac_scan_frames(const uint8_t *buf, size_t n, FlacFrame *out, size_t max, int strict);

/* Recompute CRC-8 and CRC-16 for every listed frame, in place. Header length is
 * re-derived from the *current* header bytes, so a mutation that changes the
 * block-size / sample-rate code (and hence where the CRC-8 byte lives) still
 * produces a self-consistent frame. */
void flac_repair(uint8_t *buf, size_t n, const FlacFrame *fr, size_t nf);

/* Convenience: scan (non-strict) + repair. Returns the frame count. */
size_t flac_rescan_repair(uint8_t *buf, size_t n);

/* 0 if any frame header contradicts STREAMINFO on channel count or bit depth.
 * This is the rule the reference `flac` CLI applies ("ERROR, channels is 1 in
 * frame but 2 in STREAMINFO") but libFLAC's *library* layer does not, so a
 * differential harness needs it explicitly: on such a stream libFLAC follows
 * the frame header and Vinyl follows STREAMINFO, and the PCM legitimately
 * differs without either being wrong about a well-formed input. */
int flac_hdr_consistent(const uint8_t *buf, size_t n);

/* Channel count declared by the first parseable frame header (0 if none). Used
 * to catch the extra-channels-dropped case: the decoder recombines to
 * STREAMINFO's channel count, so frames carrying MORE channels lose the excess
 * silently, and a STREAMINFO-vs-returned comparison stays equal. */
int flac_frame_channels(const uint8_t *buf, size_t n);

/* Total samples per channel the frame structure actually contains (sum of the
 * frame block sizes), or 0 if the stream does not walk cleanly. Lets a
 * differential oracle attribute a PCM-length mismatch to the side that
 * disagrees with the bitstream instead of guessing. */
uint64_t flac_expected_samples(const uint8_t *buf, size_t n);

/* ---- structure-aware mutator ------------------------------------------- */

/* Mutate `buf` (size `n`, capacity `max`) in place and return the new size.
 * Mixes byte-level edits biased into frame bodies, frame-level edits
 * (duplicate / drop / swap / reorder whole frames), an occasional freshly
 * generated stream, and an occasional plain libFuzzer mutation -- then repairs
 * every CRC. `rng` is a caller-held xorshift64 state (never 0). */
size_t flac_mutate(uint8_t *buf, size_t n, size_t max, uint64_t *rng);

/* Splice frames of `other` into `buf` (frame-granular crossover), repair, and
 * return the new size. Returns 0 if nothing sensible could be spliced. */
size_t flac_crossover(uint8_t *buf, size_t n, const uint8_t *other, size_t on, size_t max,
                      uint64_t *rng);

/* ---- generative CRC-correct emitter ------------------------------------ */

/* Emit one structurally valid, CRC-correct FLAC stream into buf (capacity max).
 * Returns its length, or 0 if it did not fit. Archetypes mirror crcfuzz.gen():
 * const / verbatim / fixed-rice / fixed-escape / fixed-order / high partition
 * order / LPC / stereo decorrelation / LPC-under-stereo. `bps16_only` forces
 * 16-bit streams (the only depth the diff oracle compares). */
size_t flac_generate(uint8_t *buf, size_t max, uint64_t *rng, int bps16_only);

#endif
