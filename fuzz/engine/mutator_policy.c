#include "mutator_policy.h"

#include <stdlib.h>
#include <string.h>

FuzzMutator fuzz_mutator_policy(void) {
  static int v = -1;
  if (v < 0) {
    const char *p = getenv("FUZZ_MUTATOR"); /* crc | plain */
    v = p && *p ? (strcmp(p, "crc") == 0 ? FUZZ_MUT_CRC : FUZZ_MUT_PLAIN)
                : (int)fuzz_target_info.default_mutator;
    /* A structure-aware mutator on a non-FLAC input format is never right. */
    if (fuzz_target_info.input_kind != FUZZ_INPUT_FLAC_STREAM)
      v = FUZZ_MUT_PLAIN;
  }
  return (FuzzMutator)v;
}
