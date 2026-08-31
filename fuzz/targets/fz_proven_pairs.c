/* fz_proven_pairs -- the standing proven-pair TCB oracle. Runs BOTH sides
 * of a kernel-checked equality on the compiled binary and compares. A divergence
 * cannot be a spec gap (the theorem is machine-checked); it is a miscompilation,
 * a Lean-runtime defect, an @[extern] mismatch, or a @[csimp] swap that changed
 * behaviour -- "the theorem holds and the binary disagrees." This is the highest-
 * value target on a verified codebase and the one component that transplants
 * directly to any machine-checked-equality benchmark suite.
 *
 * Pair 1 (flagship, no Lean shim): Flac.Decode.decodeOption vs
 * Flac.Stream.decodeReference, proven equal by Decode.decodeOption_eq_reference.
 * The production fused byte decoder and the bit-list reference model are two
 * independently compiled programs; on every input they must return byte-
 * identical Audio. Input kind: flac_stream (CRC mutator reaches the deep paths).
 * Severity: L (the binary contradicts a kernel-checked theorem). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_checks.h"

static unsigned long g_execs, g_both_some, g_both_none;

static void report(FILE *o) {
  fprintf(o, "[pairs] execs=%lu decodeOption==decodeReference: both_some=%lu both_none=%lu\n",
          g_execs, g_both_some, g_both_none);
}

FUZZ_TARGET(.name = "fz_proven_pairs",
            .summary = "execute both sides of a kernel-proven equality (decodeOption==decodeReference)",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .report = report)

/* decodeReference is the bit-list reference MODEL: deeply non-tail, it overflows
 * the Lean stack on large inputs (a documented property of the model, not a
 * codec defect -- fz_roundtrip caps its own decode_ref calls for the same
 * reason). Bound the pair to the size the model can evaluate so a model stack
 * overflow is never mistaken for a proven-pair divergence. */
#define VM_PAIR_MAX 4096

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size > VM_PAIR_MAX)
    return 0;
  PairResult r;
  if (vinyl_pair_decode(data, size, &r)) {
    if (r.prod_some)
      g_both_some++;
    else
      g_both_none++;
    fuzz_tick();
    return 0;
  }
  fprintf(stderr,
          "\n[PROVEN-PAIR DIVERGENCE — THEOREM VIOLATION ON THE BINARY] %s\n"
          "  decodeOption(some=%d) vs decodeReference(some=%d)  channel=%d index=%d\n"
          "  contradicts Flac.Decode.decodeOption_eq_reference: a compiler/runtime/csimp defect,\n"
          "  NOT a spec gap -- both programs are the SAME kernel-checked function\n",
          r.why ? r.why : "(unknown)", r.prod_some, r.ref_some, r.bad_ch, r.bad_idx);
  oracle_dump_write("proven_pair_decode", data, size);
  abort();
}
