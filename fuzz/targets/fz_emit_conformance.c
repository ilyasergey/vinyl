/* fz_emit_conformance -- an RFC-clause checker over Vinyl's OWN
 * emitted bytes. fz_encode_validity's oracle is libFLAC's DECODER, which accepts
 * every emit-set violation source review confirmed (a frame sample-rate code of 0
 * on every frame, a bit-depth code of 0, non-canonical block-size codes, ...), so
 * the rig reports PASS on all of them: an INTEROP oracle where a CONFORMANCE one
 * is needed. This target checks the normative clauses directly, so the emit-set
 * profile is visible.
 *
 * Streams come from G1 (vinyl_gen -> Stream.Unchecked.encode), so the clauses are
 * checked at EVERY depth 1-32, not just 16-bit. The header violations fire on
 * essentially every Vinyl stream -- this is a known constant, so the target is a
 * STANDING GATE (count + dump per clause by default; abort only under
 * FUZZ_STRICT>=ACCEPT, to verify the finding is present and, once Vinyl fixes it,
 * that it stays fixed). Residual-magnitude (§9.2.7.3) needs full subframe Rice
 * decoding and belongs to fz_residual_bound (P9), not here.
 *
 * Input kind: RAW (G1 parameters). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_bits.h"
#include "../common/flac_struct.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/vinyl_gen.h"

static unsigned long g_execs, g_gen_ok, g_streams_checked;
/* Per-clause violation counts (streams, or frames where noted). */
static unsigned long g_sr_code0, g_bps_code0, g_bs_code67, g_si_block_bad, g_si_bps_bad,
    g_si_varblock_bad, g_no_frames;

static void report(FILE *o) {
  fprintf(o,
          "[emit] execs=%lu gen_ok=%lu checked=%lu | frame_sr_code0=%lu frame_bps_code0=%lu "
          "bs_code6or7=%lu | §8.2 block_bad=%lu bps_bad=%lu varblock_bad=%lu no_frames=%lu\n",
          g_execs, g_gen_ok, g_streams_checked, g_sr_code0, g_bps_code0, g_bs_code67, g_si_block_bad,
          g_si_bps_bad, g_si_varblock_bad, g_no_frames);
}

FUZZ_TARGET(.name = "fz_emit_conformance",
            .summary = "RFC-clause checker over Vinyl's emitted bytes (emit-set)",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .report = report)

static int strict_abort(const char *cls, const uint8_t *d, size_t n, const char *msg) {
  oracle_dump_write(cls, d, n);
  if (fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
    fprintf(stderr, "\n[EMIT-SET CONFORMANCE] %s\n", msg);
    return 1;
  }
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  /* A3a: drive BOTH the reference writer and Emit.emitFast (byte-equal by
   * emitFast_eq_encode) and run the RFC-clause checker on the `fast` bytes, so this
   * target actually executes Emit.emitFast. The oracle is unchanged (the buffers
   * are byte-identical); the unchecked buffer is emitted here purely to exercise
   * the pair helper. */
  uint8_t *unchecked, *flac;
  size_t ulen, flen;
  GenParams gp;
  if (!vinyl_gen_encode_pair(data, size, &unchecked, &ulen, &flac, &flen, &gp))
    return 0;
  (void)unchecked;
  (void)ulen;
  g_gen_ok++;
  if (flen < 42 || memcmp(flac, "fLaC", 4) != 0 || (flac[4] & 0x7f) != 0)
    return 0; /* not a STREAMINFO-led stream we can parse */
  g_streams_checked++;

  /* ---- STREAMINFO clauses (one-shot per stream) ---- */
  uint32_t minBlock = flac_si_min_block(flac);
  uint32_t maxBlock = flac_si_max_block(flac);
  uint32_t si_bps = flac_si_bps(flac);

  int fatal = 0;
  /* §8.2: min/max block ∈ [16,65535], min ≤ max. */
  if (minBlock < 16 || maxBlock < 16 || minBlock > maxBlock) {
    g_si_block_bad++;
    fatal |= strict_abort("emit_si_block", flac, flen, "STREAMINFO block-size bounds violate §8.2");
  }
  /* Table 3: 4 ≤ bps ≤ 32. */
  if (si_bps < 4 || si_bps > 32) {
    g_si_bps_bad++;
    fatal |= strict_abort("emit_si_bps", flac, flen, "STREAMINFO bps outside [4,32] (Table 3)");
  }
  /* §8.2: variableBlocking (min≠max) is NOT what Vinyl emits (fixed min=max), but
   * if a fixed stream carried min≠max that is the mismatch -- record it. */
  if (minBlock != maxBlock) {
    g_si_varblock_bad++;
  }

  /* ---- frame-header clauses (per frame) ---- */
  static FlacFrame frames[FLAC_MAX_FRAMES];
  size_t nf = flac_scan_frames(flac, flen, frames, FLAC_MAX_FRAMES, 1);
  if (nf == 0) {
    g_no_frames++; /* §6/§9: numSamples>0 must have ≥1 frame (G1 always emits some) */
  }
  /* Per-STREAM locals: the strict-abort decision below must be about THIS stream,
   * not the cumulative g_ counters (which would abort every stream after the first
   * violation and print the current stream's params for a past one -- bug 12). */
  int sr_code0_here = 0, bps_code0_here = 0;
  for (size_t k = 0; k < nf; k++) {
    size_t s = frames[k].start;
    if (s + 4 > flen)
      break;
    int bs_code = (int)flac_fh_blocksize_code(flac, s);
    int sr_code = (int)flac_fh_samplerate_code(flac, s);
    int bps_code = (int)flac_fh_bps_code(flac, s);
    /* §7 subset: frame sample-rate code MUST be 0b0001..0b1110 (not 0 "from
     * STREAMINFO"); Vinyl emits 0 on every frame. */
    if (sr_code == 0) {
      g_sr_code0++;
      sr_code0_here = 1;
    }
    /* §7 subset: frame bit-depth code MUST be 0b001..0b111 (not 0); Vinyl emits 0
     * on every frame. */
    if (bps_code == 0) {
      g_bps_code0++;
      bps_code0_here = 1;
    }
    /* block-size code 6/7 (explicit 8/16-bit) used where a table code
     * exists is non-canonical. Count as a profile signal. */
    if (bs_code == 6 || bs_code == 7)
      g_bs_code67++;
  }
  /* header violations fire on every stream; only abort under strict, on a stream
   * that ITSELF violates. */
  if ((sr_code0_here || bps_code0_here) && fuzz_env_strict() >= FUZZ_STRICT_ACCEPT) {
    oracle_dump_write("emit_frame_code0", flac, flen);
    fprintf(stderr,
            "\n[EMIT-SET CONFORMANCE] frame sample-rate/bit-depth code 0 emitted (§7 subset)\n"
            "  bps=%d ch=%d: an interop decoder accepts this; the RFC subset does not\n",
            gp.bps, gp.ch);
    fatal = 1;
  }

  if (fatal)
    FUZZ_ABORT();
  fuzz_tick();
  return 0;
}
