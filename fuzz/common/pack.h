/* pack.h — the encode-side input unpacker for the CHECKED encode targets
 * (fz_encode_diff, fz_roundtrip, fz_encode_validity). One unpacker so the
 * targets share a corpus and cannot drift on the sample-rate table.
 *
 * Input packing:
 *   byte 0    : channels   = 1 + (b % 8)
 *   byte 1..2 : blockSize  = 16 + (LE16 % 4593)   -> [16, 4608]
 *   byte 3..4 : sampleRate index (LE16 % 9) into k_sr_table[]
 *   byte 5    : libFLAC compression level = b % 9 (unused by fz_roundtrip,
 *               kept so corpora stay interchangeable between the targets)
 *   rest      : PCM s16le, truncated to a whole number of frames (2*ch bytes)
 *
 * BLOCK-SIZE CAP (fortified codec). The checked encoders `encodePcm16Fast` and
 * `encodeCheckedCfg` accept only `16 <= blockSize <= 4608` (Flac/Native/
 * Codec.lean: the P8/P11 Pcm16ShapeOk shape check). Exploring blockSize up to
 * 65535 here would waste the entire corpus on inputs the checked API rejects
 * outright. The out-of-envelope region (blockSize > 4608, sampleRate == 0,
 * oversized geometry) is the job of the encode/edge bundle and the UNCHECKED
 * target (fz_unchecked_encode / common/vinyl_modes.c), which drives
 * Stream.Unchecked.encode directly.
 */
#ifndef PACK_H
#define PACK_H

#include <stddef.h>
#include <stdint.h>

/* sr=0 is deliberately NOT in this table: the checked encoder accepts it
 * (only sampleRate < 2^20 is required), but libFLAC's decoder rejects a
 * resolved sample rate of 0 outright, so it is not a legal probe of "the
 * reference disagrees with Vinyl" -- it is a domain libFLAC's own encoder also
 * refuses. 1 and 1048575 stay: libFLAC's encoder refuses both while its
 * decoder is far more permissive, so they are genuinely interesting edges. */
static const uint32_t k_sr_table[9] = {22050, 1, 8000, 44100, 48000, 96000, 192000, 655350,
                                       1048575};

/* Highest blockSize the checked encoders accept (Codec.lean). */
#define PACK_BS_MAX 4608u

typedef struct {
  int ch;
  unsigned bs;
  uint32_t sr;
  int level;
  const uint8_t *pcm;
  size_t pcm_len;
} PackedInput;

/* Returns 0 (and leaves *out unset) if `size` is too short to hold the header;
 * 1 otherwise. Callers should skip the input (return 0) on failure. */
static inline int pack_decode(const uint8_t *data, size_t size, PackedInput *out) {
  if (size < 6)
    return 0;
  out->ch = 1 + (data[0] % 8);
  out->bs = 16u + ((unsigned)(data[1] | (data[2] << 8)) % (PACK_BS_MAX - 16u + 1u));
  out->sr = k_sr_table[(unsigned)(data[3] | (data[4] << 8)) % 9];
  out->level = data[5] % 9;
  out->pcm = data + 6;
  out->pcm_len = (size - 6) - ((size - 6) % (2 * (size_t)out->ch));
  return 1;
}

#endif /* PACK_H */
