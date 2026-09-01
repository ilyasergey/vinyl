/* fz_encode_pair -- the ENCODER proven pair, over the whole depth space.
 *
 * `Flac.Emit.emitFast` (the fast, statically-verified byte emitter) and
 * `Flac.Stream.Unchecked.encode` (the reference writer) are proven BYTE-IDENTICAL
 * for every config and audio (`Flac.Emit.emitFast_eq_encode`). This target drives
 * BOTH on one G1-generated Audio at ARBITRARY bit depth (1-32), channel count
 * (1-8) and chooser, then asserts byte-equality.
 *
 * Why it matters:
 *  - It is the encode-side analogue of fz_proven_pairs (decodeOption ==
 *    decodeReference): a divergence is a compiler / runtime / @[csimp] defect that
 *    no round-trip or referee oracle can see -- both sides are Vinyl's own code,
 *    and the theorem says they are equal.
 *  - The @[csimp] that routes the shipped slow encoder (`--encode-slow` via
 *    `Unchecked.encode`) through `emitFast` makes THIS pair load-bearing: if the
 *    compiled emitFast ever drifts from the reference writer, that swap ships a
 *    different encoder than the one the capstones quantify over.
 *  - It exercises the non-16-bit encode region (bps 17-32, mid/side, LPC 9-32 via
 *    the hostile choosers) that PHASE2 measured as having ~zero direct coverage --
 *    almost all encoder testing goes through the 16-bit PCM wrappers.
 *
 * Any divergence is a genuine defect, so it ABORTS unconditionally (like
 * fz_proven_pairs), independent of FUZZ_STRICT. The reproducer dumped is the RAW
 * G1 parameter block, which regenerates the exact Audio+cfg. Input: RAW. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_gen.h"

static unsigned long g_execs, g_pairs, g_len_diff, g_byte_diff;

static void report(FILE *o) {
  fprintf(o,
          "[encpair] execs=%lu pairs(emitFast vs Unchecked, any depth)=%lu | "
          "len_diff=%lu byte_diff=%lu (both MUST be 0 -- emitFast_eq_encode)\n",
          g_execs, g_pairs, g_len_diff, g_byte_diff);
}

FUZZ_TARGET(.name = "fz_encode_pair",
            .summary = "encoder proven pair: Emit.emitFast == Stream.Unchecked.encode (any depth)",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  uint8_t *uc, *fast;
  size_t ulen, flen;
  GenParams gp;
  if (!vinyl_gen_encode_pair(data, size, &uc, &ulen, &fast, &flen, &gp))
    return 0;
  g_pairs++;

  if (ulen != flen) {
    g_len_diff++;
    fprintf(stderr,
            "\n[ENCODER PROVEN-PAIR VIOLATION] emitFast and Unchecked.encode differ in LENGTH\n"
            "  bps=%d ch=%d blockSize=%zu chooser=%d: Unchecked=%zuB emitFast=%zuB\n"
            "  Flac.Emit.emitFast_eq_encode proves these byte-identical -- a compiled divergence\n",
            gp.bps, gp.ch, gp.bs, gp.chooser_kind, ulen, flen);
    oracle_dump_write("encpair_len_diff", data, size);
    FUZZ_ABORT();
  }
  if (memcmp(uc, fast, ulen) != 0) {
    size_t off = 0;
    while (off < ulen && uc[off] == fast[off])
      off++;
    g_byte_diff++;
    fprintf(stderr,
            "\n[ENCODER PROVEN-PAIR VIOLATION] emitFast != Unchecked.encode at byte %zu\n"
            "  bps=%d ch=%d blockSize=%zu chooser=%d: Unchecked[%zu]=%02x emitFast[%zu]=%02x "
            "(len=%zuB)\n"
            "  Flac.Emit.emitFast_eq_encode is falsified in compiled code -- the encode @[csimp]\n"
            "  ships an emitter that is not the reference writer\n",
            off, gp.bps, gp.ch, gp.bs, gp.chooser_kind, off, uc[off], off, fast[off], ulen);
    oracle_dump_write("encpair_byte_diff", data, size);
    FUZZ_ABORT();
  }
  fuzz_tick();
  return 0;
}
