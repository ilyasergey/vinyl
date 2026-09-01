/* fz_decode_par_eq -- decodeBytes_spec ON THE BINARY, in the PARALLEL region.
 *
 * The fused byte decoder `Flac.Decode.decodeBytes` and the array decoder
 * `Flac.Decode.decodeArrays` are DISTINCT compiled programs. The capstone
 * theorem `Flac.Spec.PcmBytes.decodeBytes_spec` ties them together:
 *
 *     decodeBytes bytes = some (out, bps)
 *       ->  exists chs sr, decodeArrays bytes = some (chs, bps, sr)
 *             /\ out = pcmBytesRange bps chs 0 (chs.headD #[]).size
 *
 * So a `some` fused result must be byte-for-byte the interleaved PCM
 * serialization (`pcmBytesRange`, the array serializer) of what the array
 * decoder returns, at the SAME bit depth. This target runs both programs on
 * the same input and asserts exactly that.
 *
 * WHY A NEW TARGET. Above `Flac.Decode.parThreshold` (1<<16 = 65536 bytes of
 * input) `decodeBytes` dispatches to `byteStepsPar` and, under a live task pool
 * (LEAN_NUM_THREADS>1), the per-frame chunks decode genuinely concurrently; the
 * array path runs its own parallel `readFramesFastB`. A deterministic-but-WRONG
 * parallel stitch -- a bad csimp swap, a Task/runtime miscompilation, an
 * off-by-a-window serialization -- would be invisible to the repeat-determinism
 * targets (identical every run) and to fz_self_consistent's byte lane (which is
 * coupled to the List-Bool reference lane's stack limit and only runs at
 * n <= 8192, BELOW parThreshold). This target drops the reference lane, uses
 * `decodeArrays` directly (not `decodeOption`), and runs uncapped so it exercises
 * decodeBytes_spec exactly in the region no current target checks. A mismatch is
 * decodeBytes_spec failing on the shipped binary.
 *
 * The oracle is thread-count agnostic: the SAME check runs once with
 * LEAN_NUM_THREADS=1 (serial variant) and once with N (par variant); this code
 * sets no threads. Input kind: flac_stream (CRC mutator). */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <lean/lean.h>

#include "../common/ffi_util.h"    /* mk_ba, nat_small */
#include "../common/fuzz_target.h"
#include "../common/oracle.h"      /* oracle_dump_write */

/* Flac.Decode.parThreshold (Flac/Native/Decode.lean): decodeBytes takes the
 * parallel byteStepsPar branch when the WHOLE input ByteArray's size is >= this.
 * Kept here only to COUNT how many inputs land in the parallel region; the oracle
 * itself does not gate on it (the equality must hold at every size). */
#define PAR_THRESHOLD 65536u

/* Vinyl entry points, exported by the Lean-generated C. Lean's default calling
 * convention consumes each lean_object* argument; the ___boxed serializer wrapper
 * consumes all four of its. These externs mirror common/vinyl_api.c and
 * common/vinyl_checks.c verbatim -- this target adds no new codec surface. */
extern lean_object *vinyl_decode_bytes(lean_object *bytes);  /* -> Option (ByteArray x Nat)            */
extern lean_object *vinyl_decode_arrays(lean_object *bytes); /* -> Option (List(Array Int) x Nat x Nat)*/
extern lean_object *lp_vinyl_Flac_Stream_pcmBytesRange___boxed(lean_object *b, lean_object *arrs,
                                                               lean_object *lo, lean_object *len);

static unsigned long g_execs, g_compared, g_both_some, g_par_region;

static void report(FILE *o) {
  fprintf(o,
          "[par_eq] execs=%lu compared=%lu (decodeBytes some) both_some=%lu (fused vs array, "
          "bytes checked) par_region=%lu (input >= %uB, byteStepsPar dispatch)\n",
          g_execs, g_compared, g_both_some, g_par_region, PAR_THRESHOLD);
}

FUZZ_TARGET(.name = "fz_decode_par_eq",
            .summary = "decodeBytes_spec on the binary: fused byte decode == array decode + "
                       "serializer, in the parallel region",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .needs_flac = 0, .report = report)

/* Consumes `db` (the decodeBytes result, tag==1) -- so every path here decs it
 * before returning. `out_bytes` is borrowed out of `db` and stays live for the
 * final memcmp because `db` is not dec'd until the end. */
static void check_against_arrays(const uint8_t *data, size_t size, lean_object *db) {
  lean_object *dbp = lean_ctor_get(db, 0);      /* ByteArray x Nat (borrowed) */
  lean_object *out_bytes = lean_ctor_get(dbp, 0);
  lean_object *db_bps = lean_ctor_get(dbp, 1);  /* Nat (borrowed) */
  size_t dsz = lean_sarray_size(out_bytes);

  /* decodeBytes said some -> decodeArrays MUST say some (decodeBytes_spec). A
   * none here is itself a fused-vs-array divergence, not a legitimate fallback. */
  lean_object *da = vinyl_decode_arrays(mk_ba(data, size)); /* consumes its ByteArray */
  if (lean_obj_tag(da) != 1) {
    fprintf(stderr,
            "\n[decodeBytes_spec VIOLATION ON THE BINARY] decodeBytes accepted but decodeArrays\n"
            "  rejected the SAME input (input=%zuB, out_len=%zu, bps=%d)\n"
            "  contradicts decodeBytes_spec (some fused result implies decodeArrays some)\n",
            size, dsz, nat_small(db_bps));
    oracle_dump_write("par_eq_arrays_reject", data, size);
    lean_dec(da);
    lean_dec(db);
    FUZZ_ABORT();
  }

  lean_object *ap = lean_ctor_get(da, 0);  /* List(Array Int) x (Nat x Nat) (borrowed) */
  lean_object *chs = lean_ctor_get(ap, 0); /* List (Array Int)               (borrowed) */
  lean_object *aq = lean_ctor_get(ap, 1);  /* Nat x Nat                      (borrowed) */
  lean_object *a_bps = lean_ctor_get(aq, 0);

  /* Same bit depth (decodeBytes_spec pins the bps of both results equal). Compare
   * as Nat so a bignum depth can never alias through a truncated int. */
  if (!lean_nat_dec_eq(db_bps, a_bps)) {
    fprintf(stderr,
            "\n[decodeBytes_spec VIOLATION ON THE BINARY] fused and array decoders disagree on\n"
            "  bit depth (input=%zuB): decodeBytes bps=%d vs decodeArrays bps=%d\n"
            "  contradicts decodeBytes_spec (some (out, bps) implies decodeArrays some (chs, bps, sr))\n",
            size, nat_small(db_bps), nat_small(a_bps));
    oracle_dump_write("par_eq_bps_mismatch", data, size);
    lean_dec(da);
    lean_dec(db);
    FUZZ_ABORT();
  }

  /* channel count + serialization window = size of the first channel array
   * ((chs.headD #[]).size in the theorem; 0 for an empty channel list). */
  size_t nch = 0, head = 0;
  for (lean_object *c = chs; !lean_is_scalar(c); c = lean_ctor_get(c, 1)) {
    if (nch == 0)
      head = lean_array_size(lean_ctor_get(c, 0));
    nch++;
  }

  /* Serialize the array-path planes exactly as decodeBytes_spec does:
   * pcmBytesRange bps chs 0 (chs.headD #[]).size. Pass the decodeArrays bps Nat
   * (equal to the fused bps just above) rather than a reconstructed scalar. The
   * ___boxed wrapper consumes all four arguments, so inc the two we borrow. */
  lean_inc(a_bps);
  lean_inc(chs);
  lean_object *exp = lp_vinyl_Flac_Stream_pcmBytesRange___boxed(
      a_bps, chs, lean_usize_to_nat(0), lean_usize_to_nat(head));
  size_t esz = lean_sarray_size(exp);

  size_t off = 0;
  int mismatch = (esz != dsz);
  if (!mismatch && esz) {
    const uint8_t *ep = (const uint8_t *)lean_sarray_cptr(exp);
    const uint8_t *dp = (const uint8_t *)lean_sarray_cptr(out_bytes);
    while (off < esz && ep[off] == dp[off])
      off++;
    mismatch = (off < esz);
  }

  if (mismatch) {
    const uint8_t *ep = (const uint8_t *)lean_sarray_cptr(exp);
    const uint8_t *dp = (const uint8_t *)lean_sarray_cptr(out_bytes);
    int e_at = (off < esz) ? ep[off] : -1;
    int d_at = (off < dsz) ? dp[off] : -1;
    fprintf(stderr,
            "\n[decodeBytes_spec VIOLATION ON THE BINARY] fused byte decode != array decode + "
            "serializer\n"
            "  input=%zuB  bps=%d  channels=%zu  first_diff_off=%zu\n"
            "  decodeBytes out_len=%zu  pcmBytesRange(decodeArrays) len=%zu  byte %d vs %d\n"
            "  contradicts decodeBytes_spec (out = pcmBytesRange bps (decodeArrays bytes))\n",
            size, nat_small(db_bps), nch, off, dsz, esz, d_at, e_at);
    oracle_dump_write("par_eq_bytes_diff", data, size);
    lean_dec(exp);
    lean_dec(da);
    lean_dec(db);
    FUZZ_ABORT();
  }

  g_both_some++;
  lean_dec(exp);
  lean_dec(da);
  lean_dec(db);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size >= PAR_THRESHOLD)
    g_par_region++;
  if (fuzz_over_sample_cap(data, size)) /* 6E: skip declared-bomb inputs */
    return 0;

  /* Run the fused byte decoder. `none` means the fused path declined (the CLI
   * would fall back to the sample path); decodeBytes_spec constrains only the
   * `some` case, so there is nothing to compare -- return without decoding twice. */
  lean_object *db = vinyl_decode_bytes(mk_ba(data, size)); /* consumes its ByteArray */
  if (lean_obj_tag(db) != 1) {
    lean_dec(db);
    return 0;
  }
  g_compared++;
  check_against_arrays(data, size, db); /* consumes db */
  fuzz_tick();
  return 0;
}
