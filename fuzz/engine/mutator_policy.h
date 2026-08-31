/* mutator_policy.h — the ONE decision of which mutator a libFuzzer target uses,
 * resolved at run time so the mutator is a variant axis, not a relink. */
#ifndef MUTATOR_POLICY_H
#define MUTATOR_POLICY_H

#include "../common/fuzz_target.h" /* FuzzMutator */

/* Reads $FUZZ_MUTATOR (crc|plain) else fuzz_target_info.default_mutator, and
 * forces PLAIN on any non-FLAC_STREAM input_kind (structure-aware mutation of
 * packed-PCM is never right). Cached after the first call. */
FuzzMutator fuzz_mutator_policy(void);

#endif /* MUTATOR_POLICY_H */
