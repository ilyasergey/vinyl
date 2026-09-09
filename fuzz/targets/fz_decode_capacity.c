/* fz_decode_capacity -- the decodeBytes output-buffer pre-size is depth-wrong.
 *
 * `Decode.decodeBytes` pre-sizes its PCM output buffer with
 *   outCapacity (2 * si.channels * si.totalSamples + 64) br.data.size
 *   where  outCapacity declared inputBytes = min declared (16*inputBytes + 65536)
 * (`Flac.Decode.outCapacity`). The `2 *` hardcodes 16-bit (2 bytes/sample),
 * but the serialized output is `ceil(bps/8)` bytes/sample -- 3 at 24-bit, 4 at
 * 32-bit. So on EVERY valid 24/32-bit fast decode with a correct totalSamples,
 * the initial buffer is short by ~(ceil(bps/8)-2)/ceil(bps/8) of the output and
 * the ByteArray reallocs its way up (PHASE2 missed-lead #1: 24-bit short by
 * ~52 MB, 32-bit by ~105 MB on a large file). This is a performance / capacity
 * defect, not a correctness one -- the output is right, just built the slow way,
 * exactly in the least-exercised (non-16-bit) region.
 *
 * Oracle: recompute the decoder's own pre-size from the STREAMINFO it parsed and
 * the file size, and compare to the ACTUAL decoded output length. `capacity <
 * output` means the buffer must grow. Reported by class:
 *   - bps>16, totalSamples>0  -> the depth under-allocation (the finding)
 *   - totalSamples==0         -> the RFC-legal streaming case (known separately)
 *   - bps<=16                 -> a totalSamples-lie (STREAMINFO class), counted apart
 * Catalogues + counts by default; aborts under FUZZ_STRICT>=ACCEPT to pin a
 * witness. Input: FLAC_STREAM. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/ffi_util.h"
#include "../common/flac_bits.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"

/* Decode.decodeBytes : ByteArray -> Option (ByteArray × Nat) (bytes, bit depth). */
extern lean_object *vinyl_decode_bytes(lean_object *bytes);

static unsigned long g_execs, g_decoded, g_hi, g_total0, g_lo;
static long long g_max_shortfall;

static void report(FILE *o) {
  fprintf(o,
          "[capacity] execs=%lu decoded=%lu | underalloc: depth(bps>16,total>0)=%lu "
          "streaming(total=0)=%lu totalSamples-lie(bps<=16)=%lu | max_shortfall=%lld B\n",
          g_execs, g_decoded, g_hi, g_total0, g_lo, g_max_shortfall);
}

/* STREAMINFO is the mandatory first block: sampleRate(20) channels(3) bps(5)
 * totalSamples(36) live at the packed offsets named in common/flac_bits.h.
 * Returns 0 if the marker is absent or the payload is truncated. */
static int parse_streaminfo(const uint8_t *d, size_t n, unsigned *ch, uint64_t *total,
                            unsigned *bps) {
  if (n < 26 || memcmp(d, "fLaC", 4) != 0)
    return 0;
  *ch = flac_si_channels(d);
  *bps = flac_si_bps(d);
  *total = flac_si_total_samples(d);
  return 1;
}

FUZZ_TARGET(.name = "fz_decode_capacity",
            .summary = "decodeBytes output pre-size is 2 bytes/sample (16-bit) -> 24/32-bit reallocs",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  lean_object *r = vinyl_decode_bytes(mk_ba(data, size));
  if (lean_obj_tag(r) == 0) { /* rejected / fell back */
    lean_dec(r);
    return 0;
  }
  g_decoded++;
  lean_object *pair = lean_ctor_get(r, 0); /* ByteArray × Nat */
  size_t actual = lean_sarray_size(lean_ctor_get(pair, 0));
  lean_object *bpso = lean_ctor_get(pair, 1);
  long bps = lean_is_scalar(bpso) ? (long)lean_unbox(bpso) : -1;
  lean_dec(r);

  unsigned ch, sbps;
  uint64_t total;
  if (!parse_streaminfo(data, size, &ch, &total, &sbps))
    return 0;

  /* the decoder's own pre-size, verbatim from Decode.decodeBytes. */
  uint64_t declared = 2ULL * (uint64_t)ch * total + 64;
  uint64_t cap16 = 16ULL * (uint64_t)size + 65536;
  uint64_t capacity = declared < cap16 ? declared : cap16;
  if (capacity >= actual)
    return 0; /* buffer was large enough -- no realloc */

  long long shortfall = (long long)actual - (long long)capacity;
  if (shortfall > g_max_shortfall)
    g_max_shortfall = shortfall;

  if (bps > 16 && total > 0) {
    g_hi++;
    oracle_dump_write("decode_capacity_underalloc", data, size);
    if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
      fprintf(stderr,
              "\n[CAPACITY] decodeBytes pre-sizes 2 bytes/sample but bps=%ld needs %u\n"
              "  ch=%u totalSamples=%llu filesize=%zu: capacity=%llu < output=%zu (short by %lld B)\n"
              "  -- the `2 *` in outCapacity's `declared` should be ceil(bps/8); every valid\n"
              "  24/32-bit fast decode reallocs its output buffer\n",
              bps, (unsigned)((sbps + 7) / 8), ch, (unsigned long long)total, size,
              (unsigned long long)capacity, actual, shortfall);
      FUZZ_ABORT();
    }
  } else if (total == 0) {
    g_total0++; /* RFC-legal streaming length-unknown case (separately known) */
    oracle_dump_write("decode_capacity_total0", data, size);
  } else {
    g_lo++; /* bps<=16 with total>0: a totalSamples lie, not the depth finding */
  }
  fuzz_tick();
  return 0;
}
