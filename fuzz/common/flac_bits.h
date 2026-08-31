/* flac_bits.h -- the ONE FLAC bit/CRC/offset layer (Phase 4 dedup).
 *
 * The rig grew three CRC copies, five-plus bit reader/writers, and four
 * STREAMINFO-offset derivations, none cross-checked. This header is the single
 * source for the *primitives and offsets* every consumer shares:
 *
 *   - CRC-8 (poly 0x07) and CRC-16 (poly 0x8005), init 0, MSB-first, unreflected.
 *     Byte-for-byte the same as Flac/Native/Crc.lean. crc8("123456789")==0xF4,
 *     crc16("123456789")==0xFEE8 (verify with flac_bits_selftest).
 *   - an MSB-first bit reader and bit writer over a byte buffer.
 *   - the block-size / bit-depth code tables (RFC 9639 §9.1.1 / §9.1.4).
 *   - typed STREAMINFO and frame-header field accessors with the bit offsets
 *     named ONCE.
 *
 * Everything is `static inline` and header-only, exactly like rng.h: every
 * translation unit gets its own copy with no link coupling, so a behaviour-
 * frozen consumer (common/flac_struct.c) can consume the primitives without
 * dragging in a policy it must not change.
 *
 * POLICY IS NOT SHARED HERE. Two frame-header parsers are provided and kept
 * deliberately separate:
 *   - flac_hdr_parse_permissive: the mutator/repair view. Accepts the header a
 *     reference decoder would structurally accept, sizes truncated fields for
 *     CRC placement, and leaves wasted-bit saturation to the body walk.
 *   - flac_hdr_parse_strict: the conformance view. Same offsets, but also
 *     requires the header CRC-8 to be valid.
 * They share OFFSETS and PRIMITIVES, never a verdict policy.
 */
#ifndef FLAC_BITS_H
#define FLAC_BITS_H

#include <stddef.h>
#include <stdint.h>

/* ===================================================================== CRC
 * Bit-serial, table-free (the tables would be 256+512 bytes of cache the
 * decoder also wants). */
static inline uint8_t flac_bits_crc8(const uint8_t *d, size_t n) {
  unsigned c = 0;
  for (size_t i = 0; i < n; i++) {
    c ^= d[i];
    for (int k = 0; k < 8; k++)
      c = (c & 0x80) ? ((c << 1) ^ 0x07) & 0xFF : (c << 1) & 0xFF;
  }
  return (uint8_t)c;
}

static inline uint16_t flac_bits_crc16(const uint8_t *d, size_t n) {
  unsigned c = 0;
  for (size_t i = 0; i < n; i++) {
    c ^= (unsigned)d[i] << 8;
    for (int k = 0; k < 8; k++)
      c = (c & 0x8000) ? ((c << 1) ^ 0x8005) & 0xFFFF : (c << 1) & 0xFFFF;
  }
  return (uint16_t)c;
}

/* ============================================================== bit reader
 * MSB-first over a byte buffer. `err` latches on any read past the end; a
 * read that would overrun returns 0 and sets err (it never reads out of
 * bounds). This is the plain primitive -- the flac_struct.c mutator keeps its
 * own budget-bounded reader (a policy) rather than sharing this one. */
typedef struct {
  const uint8_t *b;
  size_t nbytes;
  size_t bitpos;
  int err;
} FlacBitReader;

static inline void fbr_init(FlacBitReader *r, const uint8_t *b, size_t nbytes, size_t start_bit) {
  r->b = b;
  r->nbytes = nbytes;
  r->bitpos = start_bit;
  r->err = 0;
}

static inline uint64_t fbr_read(FlacBitReader *r, int nbits) {
  uint64_t v = 0;
  for (int i = 0; i < nbits; i++) {
    size_t bp = r->bitpos + (size_t)i;
    if (bp / 8 >= r->nbytes) {
      r->err = 1;
      return 0;
    }
    v = (v << 1) | ((r->b[bp / 8] >> (7 - (bp % 8))) & 1);
  }
  r->bitpos += (size_t)nbits;
  return v;
}

/* nbits two's-complement, sign-extended to int64. */
static inline int64_t fbr_read_signed(FlacBitReader *r, int nbits) {
  uint64_t v = fbr_read(r, nbits);
  if (nbits > 0 && nbits < 64 && (v & (1ull << (nbits - 1))))
    return (int64_t)(v | (~0ull << nbits));
  return (int64_t)v;
}

static inline void fbr_skip(FlacBitReader *r, size_t nbits) {
  if (r->bitpos + nbits > r->nbytes * 8) {
    r->err = 1;
    return;
  }
  r->bitpos += nbits;
}

/* Zero bits before the next 1 bit; consumes the stop bit. */
static inline uint64_t fbr_unary(FlacBitReader *r) {
  uint64_t z = 0;
  for (;;) {
    if (r->err || r->bitpos >= r->nbytes * 8) {
      r->err = 1;
      return 0;
    }
    unsigned bit = (r->b[r->bitpos >> 3] >> (7 - (r->bitpos & 7))) & 1;
    r->bitpos++;
    if (bit)
      return z;
    z++;
  }
}

/* ============================================================== bit writer
 * MSB-first into a caller-owned byte buffer. `of` latches when output does not
 * fit. */
typedef struct {
  uint8_t *buf;
  size_t cap, len;
  unsigned cur;
  int nb;
  int of;
} FlacBitWriter;

static inline void fbw_init(FlacBitWriter *w, uint8_t *buf, size_t cap) {
  w->buf = buf;
  w->cap = cap;
  w->len = 0;
  w->cur = 0;
  w->nb = 0;
  w->of = 0;
}

static inline void fbw_byte(FlacBitWriter *w, uint8_t b) {
  if (w->len < w->cap)
    w->buf[w->len++] = b;
  else
    w->of = 1;
}

static inline void fbw_bits(FlacBitWriter *w, uint64_t v, int k) {
  while (k > 0) {
    int take = 8 - w->nb;
    if (take > k)
      take = k;
    unsigned chunk = (unsigned)((v >> (k - take)) & ((1u << take) - 1u));
    w->cur = ((w->cur << take) | chunk) & 0xFF;
    w->nb += take;
    k -= take;
    if (w->nb == 8) {
      fbw_byte(w, (uint8_t)w->cur);
      w->cur = 0;
      w->nb = 0;
    }
  }
}

static inline void fbw_zeros(FlacBitWriter *w, uint64_t k) {
  while (k && w->nb) {
    fbw_bits(w, 0, 1);
    k--;
  }
  while (k >= 8) {
    fbw_byte(w, 0);
    k -= 8;
    if (w->of)
      return;
  }
  if (k)
    fbw_bits(w, 0, (int)k);
}

static inline void fbw_align(FlacBitWriter *w) {
  if (w->nb)
    fbw_bits(w, 0, 8 - w->nb);
}

/* ================================================= random-access bit access
 * Absolute-bit get/put over a byte buffer, MSB-first. Used by targets that
 * rewrite one STREAMINFO field in place. */
static inline uint32_t flac_get_bits(const uint8_t *b, size_t bitpos, int nbits) {
  uint32_t v = 0;
  for (int i = 0; i < nbits; i++) {
    size_t bp = bitpos + (size_t)i;
    v = (v << 1) | ((b[bp / 8] >> (7 - (bp % 8))) & 1);
  }
  return v;
}

static inline void flac_put_bits(uint8_t *b, size_t bitpos, int nbits, uint32_t val) {
  for (int i = 0; i < nbits; i++) {
    size_t bp = bitpos + (size_t)i;
    int bit = (val >> (nbits - 1 - i)) & 1;
    size_t byte = bp / 8;
    int off = 7 - (int)(bp % 8);
    if (bit)
      b[byte] |= (uint8_t)(1 << off);
    else
      b[byte] &= (uint8_t)~(1 << off);
  }
}

/* ==================================================== FLAC code tables ==== */
/* Block size in samples per RFC 9639 §9.1.1 (0 = reserved/uncommon-explicit). */
static const unsigned FLAC_BLOCKSIZE_TAB[16] = {0,   192, 576,  1152, 2304, 4608, 0,     0,
                                                256, 512, 1024, 2048, 4096, 8192, 16384, 32768};
/* Bit depth per RFC 9639 §9.1.4 (0 = "from STREAMINFO", 3 = reserved). */
static const unsigned FLAC_BPS_TAB[8] = {0, 8, 12, 0, 16, 20, 24, 32};

/* Inverse of FLAC_BPS_TAB: frame bit-depth code for a base depth, 0 if none. */
static inline unsigned flac_bps_code(unsigned bps) {
  switch (bps) {
  case 8:
    return 1;
  case 12:
    return 2;
  case 16:
    return 4;
  case 20:
    return 5;
  case 24:
    return 6;
  case 32:
    return 7;
  default:
    return 0;
  }
}

/* Byte length of the byte-aligned UTF-8-like coded number whose lead byte is b.
 * 0 for a byte that cannot begin one (RFC 9639's 36-bit form uses 0xFE). */
static inline unsigned flac_utf8_len(uint8_t b) {
  if (b < 0x80)
    return 1;
  if ((b & 0xE0) == 0xC0)
    return 2;
  if ((b & 0xF0) == 0xE0)
    return 3;
  if ((b & 0xF8) == 0xF0)
    return 4;
  if ((b & 0xFC) == 0xF8)
    return 5;
  if ((b & 0xFE) == 0xFC)
    return 6;
  if (b == 0xFE)
    return 7;
  return 0;
}

/* ================================================= STREAMINFO field offsets
 * The STREAMINFO payload begins at file byte 8 (fLaC + one 4-byte metadata
 * block header) = file bit 64. Payload layout: minBlock:16 maxBlock:16
 * minFrame:24 maxFrame:24 sampleRate:20 channels:3 bps:5 totalSamples:36
 * md5:128. Named ONCE here; every consumer reads through these. */
#define FLAC_SI_PAYLOAD_BIT 64
#define FLAC_SI_MINBLOCK_BIT (FLAC_SI_PAYLOAD_BIT + 0)
#define FLAC_SI_MAXBLOCK_BIT (FLAC_SI_PAYLOAD_BIT + 16)
#define FLAC_SI_MINFRAME_BIT (FLAC_SI_PAYLOAD_BIT + 32)
#define FLAC_SI_MAXFRAME_BIT (FLAC_SI_PAYLOAD_BIT + 56)
#define FLAC_SI_SAMPLERATE_BIT (FLAC_SI_PAYLOAD_BIT + 80)
#define FLAC_SI_CHANNELS_BIT (FLAC_SI_PAYLOAD_BIT + 100)
#define FLAC_SI_BPS_BIT (FLAC_SI_PAYLOAD_BIT + 103)
#define FLAC_SI_TOTALSAMPLES_BIT (FLAC_SI_PAYLOAD_BIT + 108)

static inline unsigned flac_si_min_block(const uint8_t *b) {
  return flac_get_bits(b, FLAC_SI_MINBLOCK_BIT, 16);
}
static inline unsigned flac_si_max_block(const uint8_t *b) {
  return flac_get_bits(b, FLAC_SI_MAXBLOCK_BIT, 16);
}
static inline unsigned flac_si_sample_rate(const uint8_t *b) {
  return flac_get_bits(b, FLAC_SI_SAMPLERATE_BIT, 20);
}
static inline unsigned flac_si_channels(const uint8_t *b) {
  return flac_get_bits(b, FLAC_SI_CHANNELS_BIT, 3) + 1; /* stored channels-1 */
}
static inline unsigned flac_si_bps(const uint8_t *b) {
  return flac_get_bits(b, FLAC_SI_BPS_BIT, 5) + 1; /* stored bps-1 */
}
static inline uint64_t flac_si_total_samples(const uint8_t *b) {
  uint64_t hi = flac_get_bits(b, FLAC_SI_TOTALSAMPLES_BIT, 18);
  uint64_t lo = flac_get_bits(b, FLAC_SI_TOTALSAMPLES_BIT + 18, 18);
  return (hi << 18) | lo;
}

/* ================================================== frame-header accessors
 * A byte-aligned frame header starts at byte `s`: byte s[0]=0xFF, s[1] carries
 * the second sync nibble + blocking bit, s[2]=blocksize|samplerate codes,
 * s[3]=channel|bitdepth codes + reserved bit. */
typedef struct {
  size_t hlen;   /* header bytes before the CRC-8 byte */
  unsigned bs;   /* block size in samples */
  unsigned nch;  /* channel count */
  unsigned bps;  /* base bits per sample */
  unsigned side; /* 0 none, 1 = ch0 is side, 2 = ch1 is side */
} FlacFrameHeader;

static inline unsigned flac_fh_blocksize_code(const uint8_t *b, size_t s) { return b[s + 2] >> 4; }
static inline unsigned flac_fh_samplerate_code(const uint8_t *b, size_t s) { return b[s + 2] & 0xF; }
static inline unsigned flac_fh_channel_code(const uint8_t *b, size_t s) { return b[s + 3] >> 4; }
static inline unsigned flac_fh_bps_code(const uint8_t *b, size_t s) { return (b[s + 3] >> 1) & 7; }

/* Extra header bytes after the coded number for explicit block-size /
 * sample-rate codes (§9.1.1 / §9.1.2). */
static inline size_t flac_fh_bs_extra(unsigned bsc) { return bsc == 6 ? 1 : bsc == 7 ? 2 : 0; }
static inline size_t flac_fh_sr_extra(unsigned src) {
  return src == 12 ? 1 : (src == 13 || src == 14) ? 2 : 0;
}

/* Core, policy-free parse: fills `h` from the header at `p` bounded by `bound`,
 * enforcing only the structural constraints a reference decoder would (sync,
 * reserved bits clear, no reserved code points). Returns 1 on success. `si_bps`
 * supplies the depth when the frame's own code is 0. This is the shared kernel
 * the permissive and strict wrappers both call; it is NOT a verdict on the
 * whole frame. */
static inline int flac_hdr_parse_core(const uint8_t *b, size_t bound, size_t p, unsigned si_bps,
                                      FlacFrameHeader *h) {
  if (p + 5 > bound)
    return 0;
  if (b[p] != 0xFF || (b[p + 1] & 0xFE) != 0xF8)
    return 0; /* sync + reserved bit */
  unsigned bsc = flac_fh_blocksize_code(b, p), src = flac_fh_samplerate_code(b, p);
  unsigned chc = flac_fh_channel_code(b, p), bpc = flac_fh_bps_code(b, p);
  if (bsc == 0 || src == 15 || chc > 10 || bpc == 3 || (b[p + 3] & 1))
    return 0;
  unsigned u = flac_utf8_len(b[p + 4]);
  if (!u || p + 4 + u > bound)
    return 0;
  for (unsigned i = 1; i < u; i++)
    if ((b[p + 4 + i] & 0xC0) != 0x80)
      return 0;
  size_t q = p + 4 + u;
  size_t hlen = 4 + u + flac_fh_bs_extra(bsc) + flac_fh_sr_extra(src);
  if (p + hlen + 1 > bound)
    return 0;
  unsigned bs = FLAC_BLOCKSIZE_TAB[bsc];
  if (bsc == 6)
    bs = (unsigned)b[q] + 1;
  else if (bsc == 7)
    bs = ((unsigned)b[q] << 8 | b[q + 1]) + 1;
  unsigned bps = bpc ? FLAC_BPS_TAB[bpc] : si_bps;
  if (bps == 0 || bps > 32)
    return 0;
  h->hlen = hlen;
  h->bs = bs;
  h->nch = chc < 8 ? chc + 1 : 2;
  h->bps = bps;
  h->side = chc == 8 ? 2 : chc == 9 ? 1 : chc == 10 ? 2 : 0;
  return 1;
}

/* Permissive parse (mutator / repair / residual sizing): structural accept,
 * CRC not required -- header CRCs are stale mid-mutation and are rewritten by
 * the repair pass. */
static inline int flac_hdr_parse_permissive(const uint8_t *b, size_t bound, size_t p,
                                            unsigned si_bps, FlacFrameHeader *h) {
  return flac_hdr_parse_core(b, bound, p, si_bps, h);
}

/* Strict parse (conformance / clean resync): structural accept AND a valid
 * header CRC-8 at b[p+hlen]. */
static inline int flac_hdr_parse_strict(const uint8_t *b, size_t bound, size_t p, unsigned si_bps,
                                        FlacFrameHeader *h) {
  if (!flac_hdr_parse_core(b, bound, p, si_bps, h))
    return 0;
  return flac_bits_crc8(b + p, h->hlen) == b[p + h->hlen];
}

/* Byte offset of the subframe payload (just past header + CRC-8), or 0 on a
 * header that cannot be sized. Permissive: derives the offset from the header
 * code fields without demanding a full parse, for residual re-decode. */
static inline size_t flac_frame_body_offset(const uint8_t *b, size_t n, size_t fs) {
  if (fs + 4 >= n)
    return 0;
  unsigned bsc = flac_fh_blocksize_code(b, fs), src = flac_fh_samplerate_code(b, fs);
  unsigned u = flac_utf8_len(b[fs + 4]);
  if (!u)
    return 0;
  size_t off = fs + 4 + u + flac_fh_bs_extra(bsc) + flac_fh_sr_extra(src) + 1 /* CRC-8 */;
  return off <= n ? off : 0;
}

/* Known-answer selftest (flac_bits.c); returns the number of failures. */
int flac_bits_selftest(void);

#endif /* FLAC_BITS_H */
