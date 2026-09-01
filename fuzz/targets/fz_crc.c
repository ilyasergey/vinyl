/* fz_crc -- differential the codec's CRC primitives (Flac.Crc.crc8 / crc16, over a
 * ByteArray) against the independent C clone in flac_bits.h (flac_bits_crc8/16, a
 * separate bitwise implementation). CRC is the second-largest component that is
 * NOT double-checked on the compiled binary, and it is SHARED by both the encoder
 * (frame CRC-8 header + CRC-16 footer) and the decoder (verification): a wrong
 * table row or polynomial would silently corrupt every CRC-aware target at once,
 * yet nothing else exercises the Lean CRC directly. The whole-stream proven pairs
 * cannot see it -- both Vinyl ends share the same primitive, so agreement is free.
 *
 * Oracle: for every input (any length/content) crc8/crc16 of the raw bytes must
 * match the C reference. A single deterministic startup vector pins the canonical
 * "123456789" values (crc8=0xF4, crc16=0xFEE8) on the Lean side too, so a broken
 * CRC aborts immediately rather than waiting for a differing input. A divergence is
 * a broken primitive in a verified codec (flac -t would reject Vinyl's output while
 * every round-trip theorem still holds). Input kind: raw. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "../common/ffi_util.h"
#include "../common/flac_bits.h"
#include "../common/fuzz_target.h"

/* @[export] wrappers from FlacTest/FuzzGen.lean; each consumes its ByteArray. */
extern uint8_t vinyl_lean_crc8(lean_object *ba);
extern uint16_t vinyl_lean_crc16(lean_object *ba);

static unsigned long g_execs, g_crcs;

static void report(FILE *o) { fprintf(o, "[crc] execs=%lu crcs=%lu\n", g_execs, g_crcs); }

static void demand_equal(const uint8_t *d, size_t n) {
  uint8_t ref8 = flac_bits_crc8(d, n);
  uint16_t ref16 = flac_bits_crc16(d, n);
  uint8_t lean8 = vinyl_lean_crc8(mk_ba(d, n));   /* consumes the ByteArray */
  uint16_t lean16 = vinyl_lean_crc16(mk_ba(d, n)); /* consumes a fresh ByteArray */
  g_crcs++;
  if (lean8 != ref8) {
    fprintf(stderr,
            "\n[CRC8 DIVERGENCE] len=%zu Flac.Crc.crc8=0x%02x C flac_bits_crc8=0x%02x\n"
            "  a broken CRC primitive in a verified codec: shared by encoder+decoder, so this\n"
            "  silently corrupts every CRC-aware target; no round-trip theorem covers it\n",
            n, lean8, ref8);
    FUZZ_ABORT();
  }
  if (lean16 != ref16) {
    fprintf(stderr,
            "\n[CRC16 DIVERGENCE] len=%zu Flac.Crc.crc16=0x%04x C flac_bits_crc16=0x%04x\n"
            "  a broken CRC-16 (frame footer) primitive in a verified codec\n",
            n, lean16, ref16);
    FUZZ_ABORT();
  }
}

/* Pin the canonical CRC vectors on the Lean side once at startup (after vinyl_init),
 * so a wrong table/poly aborts deterministically even before the differential finds
 * a distinguishing input. flac_bits_selftest already pins the C side; this pins that
 * the LEAN CRC agrees with it on the standard "123456789" check values. */
static void crc_init(void) {
  static const uint8_t v[9] = {'1', '2', '3', '4', '5', '6', '7', '8', '9'};
  if (vinyl_lean_crc8(mk_ba(v, 9)) != 0xF4 || vinyl_lean_crc16(mk_ba(v, 9)) != 0xFEE8) {
    fprintf(stderr, "\n[CRC SELFTEST] Flac.Crc disagrees with the canonical vector "
                    "(crc8 want 0xF4, crc16 want 0xFEE8)\n");
    FUZZ_ABORT();
  }
  demand_equal(v, 9);
}

FUZZ_TARGET(.name = "fz_crc",
            .summary = "Flac.Crc.crc8/crc16 vs the independent C clone (flac_bits_crc8/16)",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .init = crc_init, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  demand_equal(data, size);
  fuzz_tick();
  return 0;
}
