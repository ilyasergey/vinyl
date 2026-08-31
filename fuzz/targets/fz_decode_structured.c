/* fz_decode_structured — the fz_decode_diff oracle (Vinyl `--decode-fast` vs
 * libFLAC 1.4.2) driven by a CRC-aware structured mutator instead of plain
 * byte mutation.
 *
 * A FLAC frame carries a CRC-8 over the header and a CRC-16 over the whole
 * frame; flip one byte and every mutant dies at the CRC gate before it reaches
 * Lpc.restoreA, readResidualA/readPartsA, the wasted-bits shiftUp path,
 * Fixed.restoreA warm-up, or Stereo.decode{LS,RS,MS} -- exactly where the
 * deep-decoder defects live. The mutator (engine/{libfuzzer,afl}_mutator.c,
 * over flac_mutate/flac_crossover in common/flac_struct.c) opens that gate;
 * this target supplies the oracle. default_mutator = crc. */
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
static unsigned long g_muts, g_flac_accept; /* mutator output acceptance rate */

static void report(FILE *o) {
  fprintf(o,
          "[structured] execs=%lu both_ok=%lu both_rej=%lu vinyl_only=%lu flac_only=%lu skip=%lu "
          "param_only=%lu inconsistent=%lu overrun=%lu len_diff=%lu libflac_accept=%.2f%%\n",
          g_execs, g_both_ok, g_both_rej, g_vinyl_only, g_flac_only, g_skip, g_param_only,
          g_inconsistent, g_flac_overrun, g_len_diff,
          g_muts ? 100.0 * (double)g_flac_accept / (double)g_muts : 0.0);
}

FUZZ_TARGET(.name = "fz_decode_structured",
            .summary = "Vinyl vs libFLAC decode, CRC-aware structured mutator (deep-decoder space)",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC,
            .needs_vinyl = 1, .needs_flac = 1, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  OracleResult v = {.name = "vinyl"}, f = {.name = "libFLAC"};
  v.rc = vinyl_decode_fast(data, size, &v.pcm, &v.len, &v.bps, &v.ch, &v.sr);
  f.rc = flac_decode(data, size, &f.pcm, &f.len, &f.bps, &f.ch, &f.sr);
  g_execs++;
  g_muts++;
  if (f.rc == DEC_OK)
    g_flac_accept++;

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
