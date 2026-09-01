/* mutator_policy.h — the ONE decision of which mutator a libFuzzer target uses,
 * resolved at run time so the mutator is a variant axis, not a relink. */
#ifndef MUTATOR_POLICY_H
#define MUTATOR_POLICY_H

#include "../common/fuzz_target.h" /* FuzzMutator (PLAIN=0, CRC=1) */

/* PCM policy (common/pcm_mutator.c): sample-aware mutation of the encode-side
 * packed-PCM corpora and the G1 RAW param block. The FuzzMutator enum itself
 * lives in the frozen common/fuzz_target.h; this extends it with the next value
 * rather than editing that header. */
enum { FUZZ_MUT_PCM = 2 };

/* Reads $FUZZ_MUTATOR (crc|pcm|plain) else fuzz_target_info.default_mutator, then
 * drops any structure-aware policy onto a mismatched input_kind back to PLAIN
 * (CRC only edits FLAC streams; PCM only edits packed-PCM / RAW). Cached after
 * the first call. */
FuzzMutator fuzz_mutator_policy(void);

#endif /* MUTATOR_POLICY_H */
