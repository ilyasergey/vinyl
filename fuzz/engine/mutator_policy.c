#include "mutator_policy.h"

#include <stdlib.h>
#include <string.h>

FuzzMutator fuzz_mutator_policy(void) {
  static int v = -1;
  if (v < 0) {
    const char *p = getenv("FUZZ_MUTATOR"); /* crc | pcm | plain */
    if (p && *p)
      v = strcmp(p, "crc") == 0   ? FUZZ_MUT_CRC
          : strcmp(p, "pcm") == 0 ? FUZZ_MUT_PCM
                                  : FUZZ_MUT_PLAIN;
    else
      v = (int)fuzz_target_info.default_mutator;
    /* A structure-aware mutator on a mismatched input format is never right:
     * CRC edits FLAC streams; PCM edits packed-PCM / RAW param blocks. */
    if (v == FUZZ_MUT_CRC && fuzz_target_info.input_kind != FUZZ_INPUT_FLAC_STREAM)
      v = FUZZ_MUT_PLAIN;
    if (v == FUZZ_MUT_PCM && fuzz_target_info.input_kind == FUZZ_INPUT_FLAC_STREAM)
      v = FUZZ_MUT_PLAIN;
  }
  return (FuzzMutator)v;
}
