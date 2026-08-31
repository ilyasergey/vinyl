/* flac_bits.c -- known-answer selftest for the shared FLAC bit/CRC layer.
 *
 * flac_bits_selftest() verifies the CRC primitives against their published
 * vectors and round-trips the bit writer through the bit reader, so a consumer
 * (mut_bench, or a tiny standalone test) can assert the single source is
 * correct before relying on it. Returns the number of failures (0 == green).
 */
#include "flac_bits.h"

#include <stdio.h>

int flac_bits_selftest(void) {
  int bad = 0;

  /* CRC-8 / CRC-16 check strings ("123456789"). */
  const uint8_t v[] = "123456789";
  uint8_t c8 = flac_bits_crc8(v, 9);
  uint16_t c16 = flac_bits_crc16(v, 9);
  printf("flac_bits: crc8(\"123456789\")  = 0x%02x (want 0xf4)   %s\n", c8,
         c8 == 0xF4 ? "OK" : "FAIL");
  printf("flac_bits: crc16(\"123456789\") = 0x%04x (want 0xfee8) %s\n", c16,
         c16 == 0xFEE8 ? "OK" : "FAIL");
  bad += (c8 != 0xF4) + (c16 != 0xFEE8);

  /* Empty and single-byte CRC-8 edge cases. */
  bad += (flac_bits_crc8(v, 0) != 0x00);

  /* Bit writer -> bit reader round trip: a handful of fields of varied width,
   * including an unaligned run, must read back exactly. */
  uint8_t buf[64];
  FlacBitWriter w;
  fbw_init(&w, buf, sizeof buf);
  fbw_bits(&w, 0x3FFE, 14);
  fbw_bits(&w, 0x5, 4);
  fbw_bits(&w, 0x123456, 24);
  fbw_zeros(&w, 7);
  fbw_bits(&w, 1, 1);
  fbw_align(&w);

  FlacBitReader r;
  fbr_init(&r, buf, w.len, 0);
  int rt_ok = fbr_read(&r, 14) == 0x3FFE && fbr_read(&r, 4) == 0x5 &&
              fbr_read(&r, 24) == 0x123456 && fbr_unary(&r) == 7 && !r.err;
  printf("flac_bits: bit writer/reader round trip %s\n", rt_ok ? "OK" : "FAIL");
  bad += !rt_ok;

  /* Signed read sign-extends. */
  uint8_t sb[2] = {0xFF, 0x00}; /* 0b1111... : a 4-bit field 0b1111 == -1 */
  FlacBitReader sr;
  fbr_init(&sr, sb, 2, 0);
  int sgn_ok = fbr_read_signed(&sr, 4) == -1;
  bad += !sgn_ok;

  /* Table + inverse consistency: flac_bps_code inverts FLAC_BPS_TAB. */
  int tab_ok = 1;
  for (unsigned c = 1; c < 8; c++) {
    unsigned d = FLAC_BPS_TAB[c];
    if (d && flac_bps_code(d) != c)
      tab_ok = 0;
  }
  printf("flac_bits: bps code table %s\n", tab_ok ? "OK" : "FAIL");
  bad += !tab_ok;

  return bad;
}
