/* fz_decode_diff — coverage-guided differential decode: Vinyl (--decode-fast
 * path) vs libFLAC 1.4.2, both instrumented, in one process.
 *
 * Driven by whichever engine's own mutation is in front of it (default mutator
 * PLAIN), so it spends most of its time in the malformed-header space that the
 * CRC-aware mutator (fz_decode_structured) biases away from. Same oracle as
 * fz_decode_structured (common/oracle.c), so the two cannot drift apart. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_api.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_api.h"

static unsigned long g_execs, g_both_ok, g_both_rej, g_vinyl_only, g_flac_only, g_skip;
static unsigned long g_param_only, g_inconsistent, g_flac_overrun, g_len_diff;

static void report(FILE *o) {
  fprintf(o,
          "[diff] execs=%lu both_ok=%lu both_rej=%lu vinyl_only=%lu flac_only=%lu skip=%lu "
          "param_only=%lu inconsistent=%lu overrun=%lu len_diff=%lu\n",
          g_execs, g_both_ok, g_both_rej, g_vinyl_only, g_flac_only, g_skip, g_param_only,
          g_inconsistent, g_flac_overrun, g_len_diff);
}

FUZZ_TARGET(.name = "fz_decode_diff",
            .summary = "Vinyl decode vs libFLAC 1.4.2, differential (malformed-header space)",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 1, .needs_flac = 1, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  OracleResult v = {.name = "vinyl"}, f = {.name = "libFLAC"};
  v.rc = vinyl_decode_fast(data, size, &v.pcm, &v.len, &v.bps, &v.ch, &v.sr);
  f.rc = flac_decode(data, size, &f.pcm, &f.len, &f.bps, &f.ch, &f.sr);
  g_execs++;

  switch (oracle_decode_diff(data, size, &v, &f)) {
  case ORACLE_SKIP: g_skip++; break;
  case ORACLE_BOTH_OK: g_both_ok++; break;
  case ORACLE_BOTH_REJECT: g_both_rej++; break;
  case ORACLE_A_ONLY: g_vinyl_only++; break;
  case ORACLE_B_ONLY: g_flac_only++; break;
  case ORACLE_INCONSISTENT: g_inconsistent++; break;
  case ORACLE_PARAM_ONLY: g_param_only++; break;
  case ORACLE_OVERRUN: g_flac_overrun++; break;
  case ORACLE_LEN_DIFF: g_len_diff++; break;
  }
  fuzz_tick();
  return 0;
}
