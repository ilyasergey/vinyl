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

  printf("mk_reject: wrote %lu rejection seeds to %s\n", g_written, dir);
  return rc ? 1 : 0;
}
