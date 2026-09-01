/* fz_metamorphic -- metamorphic relations on the decoder, executed on the
 * binary. Relation: re-encode idempotence, decode(encode(decode x)) == decode(x)
 * (Flac.decode_encode on the decoder's own output). A violation is a compiler/
 * runtime/csimp defect. Garbage-in whose decoded samples do not fit the declared
 * depth is not WellFormed, so encode returns none and the relation is skipped --
 * no false positive on corrupt streams. Input: flac_stream (CRC mutator). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_checks.h"

static unsigned long g_execs, g_ok, g_skip, g_na;

static void report(FILE *o) {
  const char *lane = getenv("VM_REENC_LANE");
  fprintf(o,
          "[metamorph] execs=%lu reencode_ok=%lu skip=%lu no_decode=%lu | lane=%s | "
          "encode_capped=%lu (re-encode suppressed on decode bombs, D7)\n",
          g_execs, g_ok, g_skip, g_na, lane ? lane : "encode", vinyl_encode_capped_count());
}

FUZZ_TARGET(.name = "fz_metamorphic",
            .summary = "metamorphic: decode(encode(decode x)) == decode(x) on the binary",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (fuzz_over_sample_cap(data, size)) /* 6E: skip declared-bomb inputs */
    return 0;
  switch (vinyl_metamorphic_reencode(data, size)) {
    case MM_OK: g_ok++; break;
    case MM_SKIP: g_skip++; break;
    case MM_NA: g_na++; break;
    case MM_VIOLATION:
      fprintf(stderr,
              "\n[METAMORPHIC VIOLATION — THEOREM ON THE BINARY] decode(encode(decode x)) !=\n"
              "  decode(x) (input=%zuB): re-encoding the decoded audio and decoding again did not\n"
              "  recover it -- contradicts Flac.decode_encode; a compiler/runtime/csimp defect\n",
              size);
      oracle_dump_write("metamorphic_reencode", data, size);
      FUZZ_ABORT();
  }
  fuzz_tick();
  return 0;
}
