#include "flac_struct.h"

#include <stdlib.h>
#include <string.h>

#include "flac_bits.h"
#include "rng.h"

/* ===================================================================== CRC
 * The CRC primitives and the code tables now come from common/flac_bits.h (the
 * single source). The public flac_crc8/flac_crc16 stay here as the exported
 * names other tools link against; they delegate to the shared kernel, so the
 * bytes they produce are unchanged. */
uint8_t flac_crc8(const uint8_t *d, size_t n) { return flac_bits_crc8(d, n); }
uint16_t flac_crc16(const uint8_t *d, size_t n) { return flac_bits_crc16(d, n); }

/* ============================================================== bit reader
 * g_budget bounds the total structural work per public call. Without it a
 * 16 KiB buffer of back-to-back tiny frame headers, each whose body scan runs
 * to end-of-buffer, is quadratic and drops exec/s off a cliff. */
static int64_t g_budget;

typedef struct {
  const uint8_t *b;
  uint64_t nbits;
  uint64_t bit;
  int err;
} BR;

static uint32_t br_read(BR *r, unsigned k) {
  if (k == 0)
    return 0;
  if (r->err || r->bit + k > r->nbits || --g_budget < 0) {
    r->err = 1;
    return 0;
  }
  uint32_t v = 0;
  for (unsigned i = 0; i < k; i++) {
    uint64_t p = r->bit + i;
    v = (v << 1) | ((r->b[p >> 3] >> (7 - (p & 7))) & 1);
  }
  r->bit += k;
  return v;
}

static void br_skip(BR *r, uint64_t k) {
  if (r->err || r->bit + k > r->nbits || --g_budget < 0) {
    r->err = 1;
    return;
  }
  r->bit += k;
}

/* Number of zero bits before the next 1 bit; consumes the stop bit. This is
 * the order crcfuzz.py had to fix: writeUnary q emits q zeros THEN the stop
 * bit, so readUnary counts zeros up to the first 1. Getting it backwards makes
 * every Rice partition mis-sized and therefore CRC-rejected. */
static uint64_t br_unary(BR *r) {
  uint64_t z = 0;
  for (;;) {
    if (r->err || r->bit >= r->nbits || --g_budget < 0) {
      r->err = 1;
      return 0;
    }
    unsigned bit = (r->b[r->bit >> 3] >> (7 - (r->bit & 7))) & 1;
    r->bit++;
    if (bit)
      return z;
    z++;
  }
}

/* ============================================================== bit writer */
typedef struct {
  uint8_t *buf;
  size_t cap, len;
  unsigned cur;
  int nb;
  int of; /* overflow: output did not fit */
} BW;

static void bw_byte(BW *w, uint8_t b) {
  if (w->len < w->cap)
    w->buf[w->len++] = b;
  else
    w->of = 1;
}

static void bw_bits(BW *w, uint64_t v, int k) {
  while (k > 0) {
    int take = 8 - w->nb;
    if (take > k)
      take = k;
    unsigned chunk = (unsigned)((v >> (k - take)) & ((1u << take) - 1u));
    w->cur = ((w->cur << take) | chunk) & 0xFF;
    w->nb += take;
    k -= take;
    if (w->nb == 8) {
      bw_byte(w, (uint8_t)w->cur);
      w->cur = 0;
      w->nb = 0;
    }
  }
}

static void bw_zeros(BW *w, uint64_t k) {
  while (k && w->nb) {
    bw_bits(w, 0, 1);
    k--;
  }
  while (k >= 8) {
    bw_byte(w, 0);
    k -= 8;
    if (w->of)
      return;
  }
  if (k)
    bw_bits(w, 0, (int)k);
}

static void bw_align(BW *w) {
  if (w->nb)
    bw_bits(w, 0, 8 - w->nb);
}

/* ================================================== frame header structure */
typedef struct {
  size_t hlen;   /* header bytes before the CRC-8 byte */
  unsigned bs;   /* block size in samples */
  unsigned nch;  /* channel count */
  unsigned bps;  /* base bits per sample */
  unsigned side; /* 0 none, 1 = ch0 is side, 2 = ch1 is side */
} FrameHdr;

/* Parse the frame header at `p`. `bound` is the exclusive byte limit.
 * Returns 1 only for a header the reference decoder would also accept
 * structurally (reserved bits clear, no reserved code points). */
static int hdr_parse(const uint8_t *b, size_t bound, size_t p, unsigned si_bps, FrameHdr *h) {
  if (p + 5 > bound)
    return 0;
  if (b[p] != 0xFF || (b[p + 1] & 0xFE) != 0xF8)
    return 0; /* sync + reserved bit */
  unsigned bsc = b[p + 2] >> 4, src = b[p + 2] & 0xF;
  unsigned chc = b[p + 3] >> 4, bpc = (b[p + 3] >> 1) & 7;
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

/* ============================ structural walk: exact frame length in bits ==
 * Mirrors libFLAC's read_subframe / read_residual_partitioned_rice. The point
 * is to learn where the decoder thinks the frame ENDS, so the CRC-16 can be
 * written there. A next-sync search is not good enough: flipping one residual
 * bit changes a Rice unary run and moves the true frame end. */
static int residual_bits(BR *r, unsigned bs, unsigned order) {
  unsigned method = br_read(r, 2);
  if (method > 1)
    return 0;
  unsigned pbits = method ? 5 : 4, esc = method ? 31 : 15;
  unsigned po = br_read(r, 4);
  if (r->err || po > 15)
    return 0;
  unsigned nparts = 1u << po;
  if (bs % nparts)
    return 0;
  unsigned base = bs >> po;
  if (base < order)
    return 0;
  for (unsigned i = 0; i < nparts; i++) {
    unsigned cnt = i ? base : base - order;
    unsigned prm = br_read(r, pbits);
    if (r->err)
      return 0;
    if (prm == esc) {
      unsigned w = br_read(r, 5);
      br_skip(r, (uint64_t)cnt * w);
    } else {
      for (unsigned j = 0; j < cnt; j++) {
        br_unary(r);
        br_skip(r, prm);
        if (r->err)
          return 0;
      }
    }
    if (r->err)
      return 0;
  }
  return 1;
}

static int subframe_bits(BR *r, unsigned bs, unsigned bps) {
  if (br_read(r, 1))
    return 0; /* subframe reserved bit */
  unsigned type = br_read(r, 6);
  if (r->err)
    return 0;
  if (br_read(r, 1)) { /* wasted-bits flag + unary(k-1) */
    uint64_t z = br_unary(r);
    if (r->err)
      return 0;
    /* The walker only needs a byte length so CRC-16 lands at the true frame
     * end; it does NOT model Vinyl's accept/reject decision (the fortified
     * decoder REJECTS wasted >= bps, Decode.lean readSubframe `if k+1 < b`).
     * Saturating to 0 here just keeps the length walk well-defined on such a
     * frame; both decoders' verdicts are adjudicated by the oracle, not here. */
    bps = (z + 1 >= bps) ? 0 : bps - (unsigned)z - 1;
  }
  if (r->err)
    return 0;
  /* bps == 0 is legal for Vinyl: a CONSTANT subframe then reads 0 bits and a
   * VERBATIM subframe reads bs*0 bits; the br_skip calls below handle 0. */
  if (type == 0) {
    br_skip(r, bps);
  } else if (type == 1) {
    br_skip(r, (uint64_t)bs * bps);
  } else if (type >= 8 && type <= 12) {
    unsigned o = type - 8;
    br_skip(r, (uint64_t)o * bps);
    if (!residual_bits(r, bs, o))
      return 0;
  } else if (type >= 32) {
    unsigned o = type - 31;
    br_skip(r, (uint64_t)o * bps);
    unsigned prec = br_read(r, 4);
    if (prec == 15)
      return 0; /* 1111 is invalid per RFC 9639 */
    prec += 1;
    unsigned sh = br_read(r, 5); /* quantisation shift, signed 5-bit */
    if (r->err || (sh & 0x10))
      return 0; /* negative shift: both Vinyl and libFLAC reject it */
    br_skip(r, (uint64_t)o * prec);
    if (!residual_bits(r, bs, o))
      return 0;
  } else {
    return 0; /* reserved subframe type */
  }
  return !r->err;
}

/* End-of-body bit offset for the frame starting at `p`, or 0 if unparseable. */
static uint64_t frame_end_bit(const uint8_t *b, size_t n, size_t p, const FrameHdr *h) {
  BR r = {b, (uint64_t)n * 8, (uint64_t)(p + h->hlen + 1) * 8, 0};
  for (unsigned c = 0; c < h->nch; c++) {
    unsigned bps = h->bps + ((h->side == 1 && c == 0) || (h->side == 2 && c == 1) ? 1 : 0);
    if (!subframe_bits(&r, h->bs, bps))
      return 0;
  }
  return r.err ? 0 : r.bit;
}

/* ================================================== metadata / resync walk */
static size_t meta_end_full(const uint8_t *b, size_t n, unsigned *si_bps, unsigned *si_ch,
                            int *have_si) {
  *si_bps = 16;
  *si_ch = 0;
  *have_si = 0;
  if (n < 4 || memcmp(b, "fLaC", 4) != 0)
    return 0;
  size_t p = 4;
  while (p + 4 <= n) {
    unsigned last = b[p] & 0x80, type = b[p] & 0x7F;
    size_t len = ((size_t)b[p + 1] << 16) | ((size_t)b[p + 2] << 8) | b[p + 3];
    if (p + 4 + len > n)
      return p; /* truncated block: treat here as the frame region */
    if (type == 0 && len >= 18) {
      const uint8_t *s = b + p + 4;
      /* STREAMINFO bit layout: 16+16+24+24 then sr:20 ch:3 bps:5 */
      *si_ch = (unsigned)(((s[12] >> 1) & 7) + 1);
      *si_bps = (unsigned)((((s[12] & 1) << 4) | (s[13] >> 4)) + 1);
      *have_si = 1;
    }
    p += 4 + len;
    if (last)
      break;
  }
  return p;
}

static size_t meta_end(const uint8_t *b, size_t n, unsigned *si_bps) {
  unsigned ch;
  int have;
  return meta_end_full(b, n, si_bps, &ch, &have);
}

static size_t next_sync(const uint8_t *b, size_t n, size_t from, unsigned si_bps, int strict) {
  FrameHdr h;
  for (size_t p = from; p + 5 <= n; p++) {
    if (b[p] != 0xFF || (b[p + 1] & 0xFE) != 0xF8)
      continue;
    if (!hdr_parse(b, n, p, si_bps, &h))
      continue;
    if (strict && flac_crc8(b + p, h.hlen) != b[p + h.hlen])
      continue;
    return p;
  }
  return n;
}

/* ==================================================== scan / repair (public) */
#define WORK_BUDGET(n) ((int64_t)32 * (int64_t)(n) + 65536)

size_t flac_scan_frames(const uint8_t *buf, size_t n, FlacFrame *out, size_t max, int strict) {
  unsigned si_bps;
  g_budget = WORK_BUDGET(n);
  size_t pos = meta_end(buf, n, &si_bps), nf = 0;
  FrameHdr h;
  while (pos + 5 <= n && nf < max) {
    if (!hdr_parse(buf, n, pos, si_bps, &h)) {
      pos = next_sync(buf, n, pos + 1, si_bps, strict);
      continue;
    }
    uint64_t eb = frame_end_bit(buf, n, pos, &h);
    size_t end;
    if (eb) {
      end = (size_t)((eb + 7) / 8) + 2; /* pad to byte + 2 CRC-16 bytes */
    } else {
      end = next_sync(buf, n, pos + h.hlen + 3, si_bps, strict); /* unparseable body */
    }
    if (end > n)
      end = n;
    if (end <= pos + h.hlen + 2)
      break;
    out[nf].start = pos;
    out[nf].end = end;
    nf++;
    pos = end;
  }
  return nf;
}

void flac_repair(uint8_t *buf, size_t n, const FlacFrame *fr, size_t nf) {
  unsigned si_bps;
  g_budget = WORK_BUDGET(n);
  meta_end(buf, n, &si_bps);
  for (size_t i = 0; i < nf; i++) {
    size_t s = fr[i].start, e = fr[i].end;
    FrameHdr h;
    if (e > n || e < s + 6)
      continue;
    if (hdr_parse(buf, e - 2, s, si_bps, &h))
      buf[s + h.hlen] = flac_crc8(buf + s, h.hlen);
    uint16_t c = flac_crc16(buf + s, e - 2 - s);
    buf[e - 2] = (uint8_t)(c >> 8);
    buf[e - 1] = (uint8_t)c;
  }
}

/* In-place, structure-exact repair: walk frames the way the decoder does, fix
 * CRC-8, zero the byte-alignment padding (libFLAC raises LOST_SYNC on non-zero
 * padding), and write CRC-16 at the true frame end. Byte-length preserving as
 * long as the header length is unchanged, so it never disturbs the walk. */
size_t flac_rescan_repair(uint8_t *buf, size_t n) {
  unsigned si_bps;
  g_budget = WORK_BUDGET(n);
  size_t pos = meta_end(buf, n, &si_bps), nf = 0;
  FrameHdr h;
  while (pos + 5 <= n) {
    if (!hdr_parse(buf, n, pos, si_bps, &h)) {
      size_t nx = next_sync(buf, n, pos + 1, si_bps, 0);
      if (nx >= n)
        break;
      pos = nx;
      continue;
    }
    buf[pos + h.hlen] = flac_crc8(buf + pos, h.hlen);
    uint64_t eb = frame_end_bit(buf, n, pos, &h);
    size_t bodyend;
    if (eb) {
      bodyend = (size_t)((eb + 7) / 8);
      unsigned pad = (unsigned)(bodyend * 8 - eb);
      if (pad && bodyend > 0)
        buf[bodyend - 1] &= (uint8_t)(0xFFu << pad);
    } else {
      /* Body does not parse; fall back to the next plausible sync so the frame
       * at least carries a consistent CRC-16 and the walk keeps its footing. */
      size_t nx = next_sync(buf, n, pos + h.hlen + 3, si_bps, 0);
      if (nx + 2 > n)
        break;
      bodyend = nx - 2;
      if (bodyend < pos + h.hlen + 1)
        break;
    }
    if (bodyend + 2 > n)
      break;
    uint16_t c = flac_crc16(buf + pos, bodyend - pos);
    buf[bodyend] = (uint8_t)(c >> 8);
    buf[bodyend + 1] = (uint8_t)c;
    nf++;
    pos = bodyend + 2;
  }
  return nf;
}

int flac_hdr_consistent(const uint8_t *buf, size_t n) {
  unsigned si_bps, si_ch;
  int have_si;
  g_budget = WORK_BUDGET(n);
  size_t pos = meta_end_full(buf, n, &si_bps, &si_ch, &have_si);
  if (!have_si)
    return 1; /* nothing to contradict */
  while (pos + 5 <= n) {
    FrameHdr h;
    if (!hdr_parse(buf, n, pos, si_bps, &h)) {
      /* strict=1: require a valid CRC-8 on the resync candidate. Without
       * this, a desync (e.g. a subframe body the walker can't parse, see the
       * wasted-bits fix above) latches onto a random 0xFF 0xF8-shaped byte
       * pair inside residual bit-soup, and the essentially-random h.nch/
       * h.bps that follow make this predicate return 0 with high probability
       * -- silently suppressing genuine PCM divergences on exactly the
       * streams whose deep-decoder paths are most interesting. */
      pos = next_sync(buf, n, pos + 1, si_bps, 1);
      if (pos >= n)
        break; /* cannot resync cleanly; no contradiction seen -> consistent */
      continue;
    }
    if (h.nch != si_ch || h.bps != si_bps)
      return 0;
    uint64_t eb = frame_end_bit(buf, n, pos, &h);
    if (!eb)
      break; /* cannot walk further; no contradiction seen so far */
    pos = (size_t)((eb + 7) / 8) + 2;
  }
  return 1;
}

/* The channel count the FIRST parseable frame header declares (0 if none). The
 * decoder recombines to STREAMINFO's channel count, truncating any EXTRA frame
 * channels, so comparing this against the decoder's returned channel count
 * catches the "frames carry more channels than STREAMINFO, the extras silently
 * dropped" case a STREAMINFO-vs-returned check (both == si_ch) cannot see. */
int flac_frame_channels(const uint8_t *buf, size_t n) {
  unsigned si_bps, si_ch;
  int have_si;
  g_budget = WORK_BUDGET(n);
  size_t pos = meta_end_full(buf, n, &si_bps, &si_ch, &have_si);
  if (!have_si)
    return 0;
  while (pos + 5 <= n) {
    FrameHdr h;
    if (!hdr_parse(buf, n, pos, si_bps, &h)) {
      pos = next_sync(buf, n, pos + 1, si_bps, 1);
      if (pos >= n)
        return 0;
      continue;
    }
    return (int)h.nch;
  }
  return 0;
}

/* Record the START bit offset of every subframe of the frame at byte
 * `frame_start`. This is the same structural walk `frame_end_bit` performs (init
 * a BR at the body -- byte `frame_start + hlen + 1`, one CRC-8 byte past the
 * header -- and skip each subframe with `subframe_bits`), except it captures each
 * subframe's start bit BEFORE advancing past it. It exists so the residual
 * analyzer can seek to subframe c (c >= 1, whose offset depends on the full Rice
 * length of the earlier subframes) without re-implementing the Rice grammar.
 *
 * `side_mode` names the decorrelation so the per-channel depth matches what the
 * encoder wrote (the side channel carries `bps + 1` bits, RFC 9639 L5):
 *   0 = independent (no side)
 *   1 = left/side   (side at channel 1)
 *   2 = right/side  (side at channel 0)
 *   3 = mid/side    (side at channel 1)
 * -- identical to `FrameHdr.side` in `frame_end_bit`: side_mode 2 <-> side==1
 * (ch0 side), side_mode 1/3 <-> side==2 (ch1 side). `out_start_bits` must hold
 * `nch` entries. Returns 1 on a clean full walk (all `nch` subframes parsed), 0
 * otherwise. Bounds-checked against `n` throughout. */
int flac_subframe_bit_offsets(const uint8_t *b, size_t n, size_t frame_start, unsigned hlen,
                              unsigned nch, unsigned bps, int side_mode, uint64_t *out_start_bits) {
  if (nch == 0 || bps < 1 || bps > 32 || out_start_bits == NULL)
    return 0;
  g_budget = WORK_BUDGET(n);
  /* Re-parse the header solely to recover the block size the subframe walk needs
   * (residual partition sizing, VERBATIM/CONSTANT run lengths). `bps` doubles as
   * the STREAMINFO fallback for a frame whose bit-depth code is 0. */
  FrameHdr h;
  if (!hdr_parse(b, n, frame_start, bps, &h) || h.hlen != hlen)
    return 0;
  BR r = {b, (uint64_t)n * 8, (uint64_t)(frame_start + hlen + 1) * 8, 0};
  for (unsigned c = 0; c < nch; c++) {
    int is_side = (side_mode == 1 && c == 1) || (side_mode == 2 && c == 0) ||
                  (side_mode == 3 && c == 1);
    out_start_bits[c] = r.bit;
    if (!subframe_bits(&r, h.bs, bps + (is_side ? 1u : 0u)))
      return 0;
  }
  return r.err ? 0 : 1;
}

/* ======================================================== generator (port of
 * crcfuzz.py: streaminfo / header_bits / subframe / residual writers). */
/* PRNG (xorshift64, a=13/b=7/c=17) and the bit-depth code table are the shared
 * primitives from rng.h / flac_bits.h -- identical constants, identical stream,
 * so the generator/mutator byte output is unchanged. */
static unsigned rr(uint64_t *s, unsigned lo, unsigned hi) {
  return hi <= lo ? lo : lo + rng_next32(s) % (hi - lo + 1);
}

static void wr_streaminfo(BW *w, unsigned bs, unsigned sr, unsigned ch, unsigned b,
                          uint64_t total) {
  bw_bits(w, bs, 16);
  bw_bits(w, bs, 16);
  bw_bits(w, 0, 24);
  bw_bits(w, 0, 24);
  bw_bits(w, sr, 20);
  bw_bits(w, ch - 1, 3);
  bw_bits(w, b - 1, 5);
  bw_bits(w, total >> 18, 18);
  bw_bits(w, total & 0x3FFFF, 18);
  for (int i = 0; i < 16; i++)
    bw_bits(w, 0, 8);
}

/* 56-bit (byte-aligned) header: bs-code 7 (explicit 16-bit block size),
 * sr-code 0 (from STREAMINFO), frame number 0. */
static void wr_header(BW *w, unsigned b, unsigned ch_code, unsigned bs) {
  bw_bits(w, 0x3FFE, 14);
  bw_bits(w, 0, 1);
  bw_bits(w, 0, 1);
  bw_bits(w, 7, 4);
  bw_bits(w, 0, 4);
  bw_bits(w, ch_code, 4);
  bw_bits(w, flac_bps_code(b), 3);
  bw_bits(w, 0, 1);
  bw_bits(w, 0, 8);
  bw_bits(w, bs - 1, 16);
}

static void wr_res_escape(BW *w, unsigned width, unsigned count) {
  bw_bits(w, 0, 2);
  bw_bits(w, 0, 4);
  bw_bits(w, 15, 4);
  bw_bits(w, width, 5);
  bw_zeros(w, (uint64_t)count * width);
}

static void wr_res_rice(BW *w, unsigned k, unsigned count) {
  bw_bits(w, 0, 2);
  bw_bits(w, 0, 4);
  bw_bits(w, k, 4);
  for (unsigned i = 0; i < count && !w->of; i++) {
    bw_bits(w, 1, 1); /* unary quotient 0 == the stop bit, written FIRST */
    if (k)
      bw_zeros(w, k);
  }
}

static void wr_res_parts(BW *w, unsigned po, unsigned order, unsigned bs, int esc, uint64_t *rng) {
  bw_bits(w, 0, 2);
  bw_bits(w, po, 4);
  unsigned nparts = 1u << po, base = bs >> po;
  for (unsigned i = 0; i < nparts && !w->of; i++) {
    unsigned cnt = i ? base : base - order;
    if (esc) {
      unsigned width = rr(rng, 0, 31);
      bw_bits(w, 15, 4);
      bw_bits(w, width, 5);
      bw_zeros(w, (uint64_t)cnt * width);
    } else {
      unsigned k = rr(rng, 0, 14);
      bw_bits(w, k, 4);
      for (unsigned j = 0; j < cnt && !w->of; j++) {
        bw_bits(w, 1, 1);
        if (k)
          bw_zeros(w, k);
      }
    }
  }
}

enum { S_CONST, S_VERBATIM, S_FIXED_ESC, S_FIXED_RICE, S_FIXED_ORD, S_FIXED_HP, S_LPC };

static void wr_subframe(BW *w, unsigned b, int stype, unsigned wasted, unsigned bs,
                        uint64_t *rng) {
  unsigned order = 0, tc;
  if (stype == S_FIXED_ORD) {
    order = rr(rng, 1, 4);
    tc = 8 + order;
  } else if (stype == S_LPC) {
    order = rr(rng, 1, 32);
    tc = 31 + order;
  } else {
    tc = stype == S_CONST ? 0 : stype == S_VERBATIM ? 1 : 8;
  }
  bw_bits(w, 0, 1);
  bw_bits(w, tc, 6);
  if (wasted == 0) {
    bw_bits(w, 0, 1);
  } else {
    bw_bits(w, 1, 1);
    bw_zeros(w, wasted - 1);
    bw_bits(w, 1, 1);
  }
  unsigned depth = b > wasted ? b - wasted : 0;
  switch (stype) {
  case S_CONST:
    bw_zeros(w, depth);
    break;
  case S_VERBATIM:
    bw_zeros(w, (uint64_t)bs * depth);
    break;
  case S_FIXED_ESC:
    wr_res_escape(w, depth < 31 ? depth : 31, bs);
    break;
  case S_FIXED_RICE:
    wr_res_rice(w, 4, bs);
    break;
  case S_FIXED_ORD:
    bw_zeros(w, (uint64_t)order * depth);
    wr_res_rice(w, rr(rng, 0, 8), bs - order);
    break;
  case S_FIXED_HP: {
    unsigned maxpo = 0;
    while ((1u << (maxpo + 1)) <= bs && maxpo < 12)
      maxpo++;
    wr_res_parts(w, maxpo ? rr(rng, 1, maxpo) : 0, 0, bs, (int)(rng_next32(rng) & 1), rng);
    break;
  }
  default: { /* LPC -- contractive coefficients: sum|c| < 2^shift, so the
              * predictor cannot diverge into the known bignum memory bomb
              * (crcfuzz.py issue 11). Keeps execs productive. */
    unsigned prec = rr(rng, 2, 15), sh = rr(rng, 4, 15);
    unsigned budget = (1u << sh) - 1;
    unsigned cap = (1u << (prec - 1)) - 1;
    unsigned lim = budget / order;
    if (lim < 1)
      lim = 1;
    if (cap > lim)
      cap = lim;
    bw_zeros(w, (uint64_t)order * depth); /* warm-up samples */
    bw_bits(w, prec - 1, 4);
    bw_bits(w, sh, 5);
    for (unsigned i = 0; i < order; i++) {
      int c = (int)rr(rng, 0, 2 * cap) - (int)cap;
      bw_bits(w, (uint64_t)((unsigned)c & ((1u << prec) - 1)), (int)prec);
    }
    wr_res_rice(w, rr(rng, 0, 8), bs - order);
    break;
  }
  }
}

static void wr_frame(BW *w, unsigned b, unsigned ch_code, unsigned nch, unsigned bs, int stype,
                     unsigned wasted, uint64_t *rng) {
  size_t s = w->len;
  wr_header(w, b, ch_code, bs);
  if (w->of)
    return;
  bw_bits(w, flac_crc8(w->buf + s, w->len - s), 8);
  for (unsigned c = 0; c < nch && !w->of; c++) {
    unsigned d = b;
    if (ch_code == 8 && c == 1)
      d = b + 1;
    else if (ch_code == 9 && c == 0)
      d = b + 1;
    else if (ch_code == 10 && c == 1)
      d = b + 1;
    wr_subframe(w, d, stype, wasted, bs, rng);
  }
  bw_align(w);
  if (w->of)
    return;
  bw_bits(w, flac_crc16(w->buf + s, w->len - s), 16);
}

size_t flac_generate(uint8_t *buf, size_t max, uint64_t *rng, int bps16_only) {
  static const unsigned bs_pool[4] = {16, 64, 256, 4096};
  static const unsigned depth_pool[6] = {8, 16, 16, 16, 24, 32};
  int kind = (int)(rng_next32(rng) % 12);
  unsigned b = bps16_only ? 16 : depth_pool[rng_next32(rng) % 6];
  unsigned bs = bs_pool[rng_next32(rng) % 4];
  unsigned nframes = rr(rng, 1, 4), nch = rr(rng, 1, 8), wasted = 0, ch_code;
  int stype;
  switch (kind) {
  case 0:
    stype = S_CONST;
    break;
  case 1:
    stype = S_VERBATIM;
    bs = bs_pool[rng_next32(rng) % 3];
    nch = rr(rng, 1, 2);
    break;
  case 2:
    stype = S_FIXED_RICE;
    break;
  case 3:
    stype = S_FIXED_ESC;
    break;
  case 4:
    stype = S_FIXED_ORD;
    break;
  case 5:
    stype = S_FIXED_HP;
    bs = 4096;
    nch = rr(rng, 1, 2);
    nframes = rr(rng, 1, 2);
    break;
  case 6:
  case 7:
    stype = S_LPC;
    nch = rr(rng, 1, 4);
    if (bs < 64)
      bs = 64;
    break;
  case 8: /* FIXED + a legal wasted-bits run */
    stype = S_FIXED_ESC;
    wasted = rr(rng, 1, b > 1 ? b - 1 : 1);
    break;
  case 9: /* 8-channel wide frame */
    stype = S_CONST;
    nch = 8;
    break;
  default: /* stereo decorrelation (kind 10, 11): Stereo.decode{LS,RS,MS} */
    stype = (rng_next32(rng) & 1) ? S_LPC : S_FIXED_ESC;
    nch = 2;
    if (bs < 64)
      bs = 64;
    break;
  }
  ch_code = kind >= 10 ? 8 + rng_next32(rng) % 3 : nch - 1;
  if (kind >= 10)
    nch = 2;
  if (stype == S_LPC && bs < 64)
    bs = 64;
  if (stype == S_FIXED_ORD && bs < 16)
    bs = 16;

  BW w = {buf, max, 0, 0, 0, 0};
  bw_bits(&w, 'f', 8);
  bw_bits(&w, 'L', 8);
  bw_bits(&w, 'a', 8);
  bw_bits(&w, 'C', 8);
  bw_bits(&w, 0x80, 8);
  bw_bits(&w, 0, 8);
  bw_bits(&w, 0, 8);
  bw_bits(&w, 0x22, 8);
  wr_streaminfo(&w, bs, 44100, nch, b, kind == 0 ? rr(rng, 0, 10000) : 0);
  size_t f0 = w.len;
  wr_frame(&w, b, ch_code, nch, bs, stype, wasted, rng);
  if (w.of)
    return 0;
  size_t flen = w.len - f0;
  for (unsigned i = 1; i < nframes; i++) {
    if (w.len + flen > w.cap)
      break;
    memcpy(w.buf + w.len, w.buf + f0, flen);
    w.len += flen;
  }
  return w.len;
}

/* ======================================================= mutation machinery */
/* libFuzzer's built-in mutator when we are linked into a libFuzzer target;
 * absent in the standalone benchmark tool, where the weak symbol stays NULL. */
__attribute__((weak)) size_t LLVMFuzzerMutate(uint8_t *data, size_t size, size_t max);

static uint8_t *g_scratch;
static size_t g_scratch_cap;

static uint8_t *scratch(size_t need) {
  if (need > g_scratch_cap) {
    size_t c = g_scratch_cap ? g_scratch_cap : 65536;
    while (c < need)
      c *= 2;
    g_scratch = realloc(g_scratch, c);
    g_scratch_cap = c;
  }
  return g_scratch;
}

/* One byte-level edit somewhere in [lo, hi). */
static void byte_op(uint8_t *buf, size_t n, size_t lo, size_t hi, uint64_t *rng) {
  static const uint8_t interesting[8] = {0x00, 0x01, 0x0F, 0x10, 0x7F, 0x80, 0xFE, 0xFF};
  if (n == 0)
    return;
  if (hi > n)
    hi = n;
  if (lo >= hi) {
    lo = 0;
    hi = n;
  }
  size_t p = lo + rng_next32(rng) % (hi - lo);
  switch (rng_next32(rng) % 6) {
  case 0:
    buf[p] ^= (uint8_t)(1u << (rng_next32(rng) & 7));
    break;
  case 1:
    buf[p] = (uint8_t)rng_next32(rng);
    break;
  case 2:
    buf[p] += (uint8_t)(1 + rng_next32(rng) % 15) * ((rng_next32(rng) & 1) ? 1 : -1);
    break;
  case 3:
    buf[p] = interesting[rng_next32(rng) & 7];
    break;
  case 4: { /* copy a short run from elsewhere in the buffer */
    size_t len = 1 + rng_next32(rng) % 16, src = rng_next32(rng) % n;
    if (src + len > n)
      len = n - src;
    if (p + len > hi)
      len = hi - p;
    memmove(buf + p, buf + src, len);
    break;
  }
  default: { /* repeat one byte */
    size_t len = 1 + rng_next32(rng) % 16;
    if (p + len > hi)
      len = hi - p;
    memset(buf + p, (uint8_t)rng_next32(rng), len);
    break;
  }
  }
}

/* Whole-frame edits: duplicate / drop / swap / reverse a run. These are the
 * ones plain byte mutation can essentially never produce, and they drive the
 * multi-frame paths (frame-number continuity, mid-stream parameter changes). */
static size_t frame_op(uint8_t *buf, size_t n, size_t max, uint64_t *rng) {
  FlacFrame fr[FLAC_MAX_FRAMES];
  size_t nf = flac_scan_frames(buf, n, fr, FLAC_MAX_FRAMES, 0);
  if (nf == 0)
    return n;
  size_t idx[FLAC_MAX_FRAMES * 2];
  size_t ni = 0;
  for (size_t i = 0; i < nf; i++)
    idx[ni++] = i;
  switch (rng_next32(rng) % 4) {
  case 0: { /* duplicate */
    size_t i = rng_next32(rng) % ni;
    memmove(idx + i + 1, idx + i, (ni - i) * sizeof(idx[0]));
    ni++;
    break;
  }
  case 1: /* drop */
    if (ni > 1) {
      size_t i = rng_next32(rng) % ni;
      memmove(idx + i, idx + i + 1, (ni - i - 1) * sizeof(idx[0]));
      ni--;
    }
    break;
  case 2: { /* swap */
    size_t a = rng_next32(rng) % ni, b = rng_next32(rng) % ni, t = idx[a];
    idx[a] = idx[b];
    idx[b] = t;
    break;
  }
  default: { /* reverse a run */
    size_t a = rng_next32(rng) % ni, b = rng_next32(rng) % ni;
    if (a > b) {
      size_t t = a;
      a = b;
      b = t;
    }
    while (a < b) {
      size_t t = idx[a];
      idx[a] = idx[b];
      idx[b] = t;
      a++;
      b--;
    }
    break;
  }
  }
  size_t head = fr[0].start, tail_off = fr[nf - 1].end, tail = n - tail_off;
  uint8_t *s = scratch(max + 64);
  if (!s)
    return n;
  memcpy(s, buf, head);
  size_t o = head;
  for (size_t i = 0; i < ni; i++) {
    size_t len = fr[idx[i]].end - fr[idx[i]].start;
    if (o + len + tail > max)
      break;
    memcpy(s + o, buf + fr[idx[i]].start, len);
    o += len;
  }
  if (o + tail <= max) {
    memcpy(s + o, buf + tail_off, tail);
    o += tail;
  }
  memcpy(buf, s, o);
  return o;
}

/* Rewrite one frame-header field to a different *legal* value. Keeping the
 * header legal is what keeps the frame repairable: an illegal block-size or
 * sample-rate code makes the walk lose the frame entirely, so its CRCs are
 * never fixed and libFLAC reports LOST_SYNC instead of reaching a subframe. */
static void header_field_op(uint8_t *buf, size_t n, size_t p, uint64_t *rng) {
  static const uint8_t bs_ok[13] = {1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15};
  static const uint8_t bps_ok[7] = {0, 1, 2, 4, 5, 6, 7};
  if (p + 5 > n)
    return;
  switch (rng_next32(rng) % 4) {
  case 0:
    buf[p + 2] = (uint8_t)((bs_ok[rng_next32(rng) % 13] << 4) | (buf[p + 2] & 0x0F));
    break;
  case 1:
    buf[p + 2] = (uint8_t)((buf[p + 2] & 0xF0) | (rng_next32(rng) % 15)); /* sr code, 15 excluded */
    break;
  case 2:
    buf[p + 3] = (uint8_t)((rng_next32(rng) % 11) << 4 | (buf[p + 3] & 0x0F));
    break;
  default:
    buf[p + 3] = (uint8_t)((buf[p + 3] & 0xF0) | (bps_ok[rng_next32(rng) % 7] << 1));
    break;
  }
  buf[p] = 0xFF;
  /* Sync tail + reserved bit clear, but PRESERVE b0 (blocking strategy): the
   * old `&= 0xFE` / `|= 0xF8` cleared it unconditionally, forcing
   * fixed-blocksize on every mutated header and starving the mutator of
   * variable-blocksize streams (where the coded value is a sample number,
   * not a frame number, exercising readUtf8's 5/6/7-byte/36-bit encodings). */
  buf[p + 1] = (uint8_t)(0xF8 | (buf[p + 1] & 0x01));
  buf[p + 3] &= 0xFE; /* frame header's own reserved bit clear */
}

/* Every frame parses and the stream ends exactly on a frame boundary -- i.e.
 * the decoder will run all subframes to completion instead of bailing at a
 * reserved code point or resynchronising. */
static int walk_clean(const uint8_t *buf, size_t n, uint64_t *samples) {
  unsigned si_bps;
  g_budget = WORK_BUDGET(n);
  size_t pos = meta_end(buf, n, &si_bps), nf = 0;
  uint64_t tot = 0;
  if (samples)
    *samples = 0;
  if (pos == 0 || pos >= n)
    return 0;
  while (pos < n) {
    FrameHdr h;
    if (!hdr_parse(buf, n, pos, si_bps, &h))
      return 0;
    uint64_t eb = frame_end_bit(buf, n, pos, &h);
    if (!eb)
      return 0;
    size_t end = (size_t)((eb + 7) / 8) + 2;
    if (end > n || end <= pos)
      return 0;
    pos = end;
    tot += h.bs;
    nf++;
  }
  if (samples)
    *samples = tot;
  return nf > 0;
}

uint64_t flac_expected_samples(const uint8_t *buf, size_t n) {
  uint64_t s;
  return walk_clean(buf, n, &s) ? s : 0;
}

static uint8_t *g_orig;
static size_t g_orig_cap;

static size_t mutate_once(uint8_t *buf, size_t n, size_t max, uint64_t *rng) {
  uint32_t roll = rng_next32(rng) % 100;
  if (roll < 18 && LLVMFuzzerMutate) {
    /* Keep a slice of plain libFuzzer mutation for length changes and splices;
     * the repair pass below still fixes whatever frames survive. */
    n = LLVMFuzzerMutate(buf, n, max);
  } else {
    if (rng_next32(rng) % 100 < 25)
      n = frame_op(buf, n, max, rng);
    FlacFrame fr[FLAC_MAX_FRAMES];
    size_t nf = flac_scan_frames(buf, n, fr, FLAC_MAX_FRAMES, 0);
    unsigned nops = 1 + rng_next32(rng) % 8;
    for (unsigned i = 0; i < nops; i++) {
      if (nf == 0) {
        byte_op(buf, n, 0, n, rng);
        continue;
      }
      const FlacFrame *f = &fr[rng_next32(rng) % nf];
      uint32_t what = rng_next32(rng) % 100;
      if (what < 6 && fr[0].start > 0) {
        byte_op(buf, n, 0, fr[0].start, rng); /* STREAMINFO / metadata blocks */
      } else if (what < 16) {
        header_field_op(buf, n, f->start, rng);
      } else {
        /* Frame body: subframe headers, wasted-bits unary, residual bit soup.
         * Skip the header and the CRC-16 tail -- both get rewritten anyway. */
        FrameHdr h;
        unsigned si_bps;
        meta_end(buf, n, &si_bps);
        size_t lo = hdr_parse(buf, n, f->start, si_bps, &h) ? f->start + h.hlen + 1 : f->start;
        size_t hi = f->end > lo + 2 ? f->end - 2 : f->end;
        byte_op(buf, n, lo, hi, rng);
      }
    }
  }
  flac_rescan_repair(buf, n);
  return n;
}

/* Rejection sampling: a body edit that lands on a subframe type code or a
 * residual-method field usually makes the frame unparseable, and an
 * unparseable frame stops the decoder before Lpc.restoreA / readParts -- the
 * whole point of this target. Retrying a few times until the structural walk
 * is clean costs three cheap in-process walks and roughly triples the share of
 * mutants libFLAC actually decodes. The last attempt is kept either way, so
 * malformed inputs still occur (just not exclusively). */
size_t flac_mutate(uint8_t *buf, size_t n, size_t max, uint64_t *rng) {
  if (rng_next32(rng) % 100 < 3) { /* inject a freshly generated, deep-structure stream */
    size_t g = flac_generate(buf, max, rng, 1);
    if (g)
      return g;
  }
  if (n > g_orig_cap) {
    size_t c = g_orig_cap ? g_orig_cap : 65536;
    while (c < n)
      c *= 2;
    g_orig = realloc(g_orig, c);
    g_orig_cap = c;
  }
  if (!g_orig)
    return mutate_once(buf, n, max, rng);
  memcpy(g_orig, buf, n);
  size_t on = n, out = n;
  for (int attempt = 0; attempt < 4; attempt++) {
    if (attempt)
      memcpy(buf, g_orig, on);
    out = mutate_once(buf, on, max, rng);
    if (walk_clean(buf, out, 0))
      break;
  }
  return out;
}

size_t flac_crossover(uint8_t *buf, size_t n, const uint8_t *other, size_t on, size_t max,
                      uint64_t *rng) {
  FlacFrame a[FLAC_MAX_FRAMES], b[FLAC_MAX_FRAMES];
  size_t na = flac_scan_frames(buf, n, a, FLAC_MAX_FRAMES, 0);
  size_t nb = flac_scan_frames(other, on, b, FLAC_MAX_FRAMES, 0);
  if (na == 0 || nb == 0)
    return 0;
  /* Keep A's stream header (STREAMINFO decides bit depth / channel count),
   * then interleave frames from both parents in order. */
  size_t head = a[0].start;
  uint8_t *s = scratch(max + 64);
  if (!s || head > max)
    return 0;
  memcpy(s, buf, head);
  size_t o = head, ia = 0, ib = 0;
  while (ia < na || ib < nb) {
    int take_b = ib < nb && (ia >= na || (rng_next32(rng) & 1));
    const uint8_t *src = take_b ? other : buf;
    FlacFrame f = take_b ? b[ib++] : a[ia++];
    size_t len = f.end - f.start;
    if (o + len > max)
      break;
    memcpy(s + o, src + f.start, len);
    o += len;
  }
  if (o <= head)
    return 0;
  memcpy(buf, s, o);
  flac_rescan_repair(buf, o);
  return o;
}
