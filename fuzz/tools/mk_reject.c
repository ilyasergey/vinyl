/* mk_reject (B5) -- emit the shared rejection-microseed corpus: one FLAC per
 * single-field RFC 9639 violation, each derived from ONE minimal valid one-frame
 * 16-bit template with the frame-header CRC-8 REPAIRED after the edit. Repairing
 * the CRC is the whole point: a decoder that rejected these on a stale header CRC
 * would never reach the field-level reject arm the seed is meant to probe
 * (readFields / resolveBlockSize / readChannels / the subframe-type table), and
 * the pre-existing hand-built seeds kept a stale 0x4c (the A4b rot). Everything
 * here is deterministic and self-contained -- the template and every mutation are
 * in-source, using only common/flac_bits.h primitives (flac_bits_crc8,
 * flac_put_bits, the FLAC_SI_* offsets).
 *
 *   mk_reject <output-dir>
 *
 * Template (55 bytes, byte-for-byte the reference minimal stream): fLaC + a
 * last-block STREAMINFO (34 B, mono 16-bit 44100, 16-sample block) + one
 * fixed-blocking frame carrying a single CONSTANT subframe. Frame header starts
 * at byte 42, is 7 bytes (explicit 16-bit block size), CRC-8 at byte 49.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#include "flac_bits.h"

/* The minimal valid template. Frame header: 42=FF 43=F8 44=79(bs7|sr9)
 * 45=08(ch0|bps4) 46=00(frame#) 47=00 48=0F(explicit bs-1 = 15 -> 16 samples)
 * 49=4C(header CRC-8); body: 50=00(CONSTANT subframe) 51=00 52=00(16-bit sample)
 * 53=B5 54=AE(frame CRC-16). */
static const uint8_t k_base[55] = {
    0x66, 0x4c, 0x61, 0x43,                         /* fLaC                              */
    0x80, 0x00, 0x00, 0x22,                         /* meta: last, STREAMINFO, len 34    */
    0x00, 0x10,                                     /* minBlockSize = 16                 */
    0x00, 0x10,                                     /* maxBlockSize = 16                 */
    0x00, 0x00, 0x00,                               /* minFrameSize                      */
    0x00, 0x00, 0x00,                               /* maxFrameSize                      */
    0x0a, 0xc4, 0x40, 0xf0, 0x00, 0x00, 0x00, 0x10, /* sr 44100 / ch 1 / bps 16 / total  */
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* md5[0..7]                         */
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* md5[8..15]                        */
    0xff, 0xf8, 0x79, 0x08, 0x00, 0x00, 0x0f,       /* frame header (7 bytes)            */
    0x4c,                                           /* frame header CRC-8                */
    0x00, 0x00, 0x00,                               /* CONSTANT subframe + 16-bit sample */
    0xb5, 0xae,                                     /* frame CRC-16                      */
};

#define FRAME_OFF 42u
#define HDR_LEN 7u
#define CRC8_OFF (FRAME_OFF + HDR_LEN) /* 49 */
#define S2_OFF (FRAME_OFF + 2u)        /* 44: block-size | sample-rate codes */
#define S3_OFF (FRAME_OFF + 3u)        /* 45: channel | bit-depth codes + reserved */
#define BSX_OFF (FRAME_OFF + 5u)       /* 47: explicit 16-bit block size (2 bytes) */
#define SUBFRAME_OFF 50u

static void repair_hdr_crc(uint8_t *b) { b[CRC8_OFF] = flac_bits_crc8(b + FRAME_OFF, HDR_LEN); }

static unsigned long g_written;

static int emit(const char *dir, const char *name, const uint8_t *b, size_t len) {
  char path[1024];
  snprintf(path, sizeof path, "%s/%s", dir, name);
  FILE *f = fopen(path, "wb");
  if (!f) {
    fprintf(stderr, "mk_reject: cannot open %s\n", path);
    return 1;
  }
  if (len && fwrite(b, 1, len, f) != len) {
    fprintf(stderr, "mk_reject: short write %s\n", path);
    fclose(f);
    return 1;
  }
  fclose(f);
  g_written++;
  return 0;
}

/* Frame-header field edit: clone, set b[off]=val, repair CRC-8, write 55 bytes. */
static int emit_hdr_field(const char *dir, const char *name, size_t off, uint8_t val) {
  uint8_t b[55];
  memcpy(b, k_base, sizeof b);
  b[off] = val;
  repair_hdr_crc(b);
  return emit(dir, name, b, sizeof b);
}

/* Subframe-body reject: keep the valid marker + STREAMINFO + frame header, repair
 * the header CRC-8 so parsing reaches the subframe body, then splice a
 * hand-packed malformed subframe over bytes 50+. No frame CRC-16 is appended --
 * every seed here trips a structural reject inside readSubframe/readContent/
 * readPartA before the CRC-16 gate. `w` holds the MSB-first body bits; it is
 * byte-aligned (zero-padded) before splicing. */
static int emit_body(const char *dir, const char *name, FlacBitWriter *w) {
  fbw_align(w);
  if (w->of) {
    fprintf(stderr, "mk_reject: body overflow %s\n", name);
    return 1;
  }
  uint8_t b[700];
  memcpy(b, k_base, 50); /* fLaC + STREAMINFO + 7-byte frame header + CRC-8 slot */
  repair_hdr_crc(b);
  memcpy(b + 50, w->buf, w->len);
  return emit(dir, name, b, 50 + w->len);
}

/* Subframe header byte: top padding bit 0, 6-bit type, wasted-flag LSB. */
static uint8_t subframe_hdr(unsigned type, unsigned wasted_flag) {
  return (uint8_t)(((type & 0x3f) << 1) | (wasted_flag & 1));
}

/* RICE2 residual truncated either inside the unary quotient (no stop bit) or
 * inside the k-bit remainder (a lone stop bit, then EOF before k bits). FIXED
 * order 0 so the body reaches the residual immediately (no warm-up / coeffs). */
static int emit_rice2_trunc(const char *dir, const char *name, unsigned k, int in_remainder) {
  uint8_t buf[64];
  FlacBitWriter w;
  fbw_init(&w, buf, sizeof buf);
  fbw_bits(&w, subframe_hdr(8, 0), 8); /* FIXED order 0 */
  fbw_bits(&w, 1, 2);                  /* residual method 1 = RICE2 (5-bit params) */
  fbw_bits(&w, 0, 4);                  /* partition order 0 -> one partition */
  fbw_bits(&w, k, 5);                  /* Rice2 parameter k */
  if (in_remainder)
    fbw_bits(&w, 1, 1); /* quotient 0 stop bit; the k remainder bits never arrive */
  else
    fbw_bits(&w, 0, 3); /* start of an unterminated unary run (all zeros to EOF) */
  return emit_body(dir, name, &w);
}

/* RICE escape (param 0b1111) with a 5-bit raw sample width, then `sampledatabits`
 * of the raw partition samples -- fewer than the full 16*width, so width 31 runs
 * off the end; width 0 leaves an incomplete frame (no CRC-16). */
static int emit_escape_trunc(const char *dir, const char *name, unsigned width, unsigned sampledatabits) {
  uint8_t buf[64];
  FlacBitWriter w;
  fbw_init(&w, buf, sizeof buf);
  fbw_bits(&w, subframe_hdr(8, 0), 8); /* FIXED order 0 */
  fbw_bits(&w, 0, 2);                  /* residual method 0 = RICE (4-bit params) */
  fbw_bits(&w, 0, 4);                  /* partition order 0 */
  fbw_bits(&w, 15, 4);                 /* escape parameter 0b1111 */
  fbw_bits(&w, width, 5);              /* raw sample width */
  if (sampledatabits)
    fbw_bits(&w, 0, sampledatabits);
  return emit_body(dir, name, &w);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <output-dir>\n", argv[0]);
    return 2;
  }
  const char *dir = argv[1];
  mkdir(dir, 0755); /* best-effort; existing dir is fine */

  int rc = 0;

  /* 00 baseline: the valid template, so the corpus carries its own control. */
  rc |= emit(dir, "00_baseline_valid.flac", k_base, sizeof k_base);

  /* ---- frame-header field violations (CRC-8 repaired) ---------------------- */
  /* block-size code 0 (reserved): s[2] high nibble 0, keep sample-rate code 9. */
  rc |= emit_hdr_field(dir, "10_blocksize_code_0.flac", S2_OFF, 0x09);
  /* sample-rate code 15 (forbidden): s[2] low nibble 15, keep block-size code 7. */
  rc |= emit_hdr_field(dir, "11_samplerate_code_15.flac", S2_OFF, 0x7f);
  /* bit-depth code 3 (reserved): s[3] bps field = 3, channel 0. */
  rc |= emit_hdr_field(dir, "12_bitdepth_code_3.flac", S3_OFF, 0x06);
  /* reserved channel assignments 11..15: s[3] = (chc<<4) | (bpsCode 4 << 1). */
  for (unsigned chc = 11; chc <= 15; chc++) {
    char name[64];
    snprintf(name, sizeof name, "13_channel_code_%u.flac", chc);
    rc |= emit_hdr_field(dir, name, S3_OFF, (uint8_t)((chc << 4) | 0x08));
  }

  /* explicit block size 65536 (V4): bs code 7 with the 16-bit payload = 0xFFFF,
   * so resolveBlockSize yields v+1 = 65536, one past the RFC max. */
  {
    uint8_t b[55];
    memcpy(b, k_base, sizeof b);
    b[BSX_OFF] = 0xff;
    b[BSX_OFF + 1] = 0xff;
    repair_hdr_crc(b);
    rc |= emit(dir, "18_blocksize_65536.flac", b, sizeof b);
  }

  /* ---- subframe-body violations (frame-header CRC stays valid) ------------- */
  /* reserved subframe type codes (type field = bits 1-6 of the subframe header).
   * 0x04 -> type 2 (in the 000010..000111 reserved band); 0x20 -> type 16 (the
   * 010000..011111 reserved band). */
  rc |= emit_hdr_field(dir, "17_reserved_subframe_type_low.flac", SUBFRAME_OFF, 0x04);
  rc |= emit_hdr_field(dir, "17_reserved_subframe_type_mid.flac", SUBFRAME_OFF, 0x20);

  /* ---- STREAMINFO field violations (no frame-header CRC involved; V3) ------- */
  /* min block size < 16 (RFC: minimum block size must be >= 16). */
  {
    uint8_t b[55];
    memcpy(b, k_base, sizeof b);
    flac_put_bits(b, FLAC_SI_MINBLOCK_BIT, 16, 8);
    rc |= emit(dir, "30_streaminfo_minblock_lt16.flac", b, sizeof b);
  }
  /* min block size > max block size. */
  {
    uint8_t b[55];
    memcpy(b, k_base, sizeof b);
    flac_put_bits(b, FLAC_SI_MINBLOCK_BIT, 16, 32);
    rc |= emit(dir, "31_streaminfo_min_gt_max.flac", b, sizeof b);
  }
  /* sample rate 0 with audio present (RFC 9639 forbids a resolved rate of 0). */
  {
    uint8_t b[55];
    memcpy(b, k_base, sizeof b);
    flac_put_bits(b, FLAC_SI_SAMPLERATE_BIT, 20, 0);
    rc |= emit(dir, "40_streaminfo_sr0_with_audio.flac", b, sizeof b);
  }

  /* ---- reserved metadata block type 127 ----------------------------------- */
  /* STREAMINFO cannot itself be retyped (it must be type 0), so clear its
   * last-block flag and append an empty type-127 block (0xff = last|type 127)
   * before the frame. The frame header and its CRC are untouched. */
  {
    uint8_t b[59];
    memcpy(b, k_base, 42);            /* fLaC + STREAMINFO payload */
    b[4] = 0x00;                      /* STREAMINFO no longer the last block */
    b[42] = 0xff;                     /* meta block: last | type 127            */
    b[43] = 0x00; b[44] = 0x00; b[45] = 0x00; /* length 0 */
    memcpy(b + 46, k_base + 42, 13);  /* the valid frame follows */
    rc |= emit(dir, "34_metadata_type_127.flac", b, sizeof b);
  }

  /* ---- truncations -------------------------------------------------------- */
  rc |= emit(dir, "20_trunc_after_frame_header.flac", k_base, 50); /* header+CRC, no body */
  rc |= emit(dir, "21_trunc_mid_frame_header.flac", k_base, 47);   /* inside the header    */
  rc |= emit(dir, "22_trunc_streaminfo.flac", k_base, 20);         /* STREAMINFO cut short */

  /* ---- subframe-body reject frontier (header CRC-8 valid, body malformed) --- */
  /* LPC (type >= 32) with forbidden predictor precision code 0b1111 (V2/§9.2.4). */
  {
    uint8_t buf[64];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(32, 0), 8); /* LPC order 1 */
    fbw_bits(&w, 0, 16);                  /* one 16-bit warm-up sample */
    fbw_bits(&w, 15, 4);                  /* precision code 15 -> invalid */
    rc |= emit_body(dir, "50_lpc_precision_15.flac", &w);
  }
  /* LPC with a negative quantization shift (5-bit signed field, top bit set). */
  {
    uint8_t buf[64];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(32, 0), 8); /* LPC order 1 */
    fbw_bits(&w, 0, 16);                  /* warm-up sample */
    fbw_bits(&w, 11, 4);                  /* precision code 11 -> precision 12 (valid) */
    fbw_bits(&w, 0x10, 5);                /* shift = -16 (top bit set) -> reject */
    rc |= emit_body(dir, "51_lpc_negative_shift.flac", &w);
  }
  /* Reserved residual coding methods 2 and 3 (only 0/1 are defined). */
  for (unsigned m = 2; m <= 3; m++) {
    uint8_t buf[16];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(8, 0), 8); /* FIXED order 0 */
    fbw_bits(&w, m, 2);                  /* reserved residual method */
    char name[64];
    snprintf(name, sizeof name, "52_residual_method_%u.flac", m);
    rc |= emit_body(dir, name, &w);
  }
  /* Partition order that does not divide the block size (16 % 2^5 != 0). */
  {
    uint8_t buf[16];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(8, 0), 8); /* FIXED order 0 */
    fbw_bits(&w, 0, 2);                  /* RICE */
    fbw_bits(&w, 5, 4);                  /* partition order 5 -> 16 not divisible by 32 */
    rc |= emit_body(dir, "53_partition_indivisible.flac", &w);
  }
  /* Partition order too high for the predictor order (ord 4 >= bs>>po = 2). */
  {
    uint8_t buf[32];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(12, 0), 8); /* FIXED order 4 */
    for (int i = 0; i < 4; i++)
      fbw_bits(&w, 0, 16); /* four 16-bit warm-up samples */
    fbw_bits(&w, 0, 2);    /* RICE */
    fbw_bits(&w, 3, 4);    /* partition order 3 -> bs>>3 = 2 < order 4 -> reject */
    rc |= emit_body(dir, "53_partition_order_too_large.flac", &w);
  }
  /* RICE2 large k truncated inside the unary run and inside the remainder. */
  {
    static const unsigned ks[] = {18, 24, 28, 30};
    for (size_t i = 0; i < sizeof ks / sizeof ks[0]; i++) {
      char name[64];
      snprintf(name, sizeof name, "54_rice2_k%u_unary.flac", ks[i]);
      rc |= emit_rice2_trunc(dir, name, ks[i], 0);
      snprintf(name, sizeof name, "54_rice2_k%u_remainder.flac", ks[i]);
      rc |= emit_rice2_trunc(dir, name, ks[i], 1);
    }
  }
  /* RICE escape sample widths 0 and 31 truncated in the raw sample data. */
  rc |= emit_escape_trunc(dir, "55_escape_width_0.flac", 0, 0);
  rc |= emit_escape_trunc(dir, "55_escape_width_31.flac", 31, 8);
  /* Wasted-bits count equal to the bit depth (exhausts the sample). CONSTANT
   * subframe, wasted flag set; unary 0^15 1 encodes 16 wasted bits (bps = 16). */
  {
    uint8_t buf[16];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(0, 1), 8); /* CONSTANT, wasted flag set */
    fbw_bits(&w, 0, 15);                 /* 15 leading zeros ... */
    fbw_bits(&w, 1, 1);                  /* ... stop bit -> 16 wasted bits == bps */
    rc |= emit_body(dir, "56_wasted_equals_depth.flac", &w);
  }
  /* Unterminated wasted-bits unary run (all zeros to EOF, no stop bit). */
  {
    uint8_t buf[16];
    FlacBitWriter w;
    fbw_init(&w, buf, sizeof buf);
    fbw_bits(&w, subframe_hdr(0, 1), 8); /* CONSTANT, wasted flag set */
    fbw_bits(&w, 0, 7);                  /* zeros only; the unary never terminates */
    rc |= emit_body(dir, "56_wasted_unterminated.flac", &w);
  }

  /* ---- staged STREAMINFO truncation ladder (prefixes of the valid base) ----
   * Each length stops one field short: 8 before minBlock, 10 before maxBlock,
   * 12 before minFrame, 15 before maxFrame, 18 before sampleRate, 21/22 around
   * bps, 26 before MD5, 41 one byte short of the MD5 end. */
  {
    static const size_t si_stops[] = {8, 10, 12, 15, 18, 21, 22, 26, 41};
    for (size_t i = 0; i < sizeof si_stops / sizeof si_stops[0]; i++) {
      char name[64];
      snprintf(name, sizeof name, "60_trunc_streaminfo_%zu.flac", si_stops[i]);
      rc |= emit(dir, name, k_base, si_stops[i]);
    }
  }

  /* ---- staged frame truncation ladder: complete STREAMINFO, partial frame ----
   * N = 43..54 walks the sync/header/UTF number/explicit block size/CRC-8/
   * subframe-header/sample/CRC-16 stages (frame starts at byte 42). */
  for (size_t n = 43; n <= 54; n++) {
    char name[64];
    snprintf(name, sizeof name, "70_trunc_frame_%zu.flac", n);
    rc |= emit(dir, name, k_base, n);
  }

  printf("mk_reject: wrote %lu rejection seeds to %s\n", g_written, dir);
  return rc ? 1 : 0;
}
