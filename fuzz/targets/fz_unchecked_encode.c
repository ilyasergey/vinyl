/* fz_unchecked_encode — the P7 surface (Stream.Unchecked.encode).
 *
 * P7 split the raw, precondition-free encoders under an `Unchecked` namespace
 * and made the public encoders check their preconditions. This target drives
 * the raw path directly (common/vinyl_unchecked_api.c) and:
 *
 *  1. On the domain the CHECKED encoder accepts (blockSize <= 4608, well-shaped
 *     geometry), the unchecked encoder with the same cfg must produce
 *     byte-identical output -- the checked encoder is exactly the unchecked one
 *     under a precondition, so a mismatch means the P7 rename changed
 *     behaviour. Abort.
 *  2. On the out-of-envelope domain (blockSize > 4608), the checked encoder
 *     rejects while the unchecked encoder still runs. The point is a footgun
 *     hunt: the raw path must not crash, and whatever it emits must decode back
 *     to the input PCM under Vinyl's own decoder (else the raw encoder produced
 *     a stream even Vinyl cannot read). Counted; a decode mismatch aborts.
 *
 * Uses a WIDE block-size unpacker (up to 16384) so the >4608 region is actually
 * reached -- common/pack.h caps at 4608 for the checked targets on purpose. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../common/fuzz_target.h"
#include "../common/pack.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_modes.h"

static unsigned long g_execs, g_short, g_agree, g_wide_run, g_wide_rt;
static unsigned long g_checked_reject, g_wide_unreadable;

static void report(FILE *o) {
  fprintf(o,
          "[unchecked] execs=%lu short=%lu checked_agree=%lu checked_reject=%lu wide_run=%lu "
          "wide_roundtrip=%lu wide_unreadable=%lu\n",
          g_execs, g_short, g_agree, g_checked_reject, g_wide_run, g_wide_rt, g_wide_unreadable);
}

FUZZ_TARGET(.name = "fz_unchecked_encode",
            .summary = "Stream.Unchecked.encode (P7) agrees with the checked encoder / no footgun",
            .input_kind = FUZZ_INPUT_PACKED_PCM, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 1, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size < 6) {
    g_short++;
    return 0;
  }
  int ch = 1 + (data[0] % 8);
  /* WIDE: [16, 16399] so the >4608 out-of-envelope region is reached. */
  unsigned bs = 16u + ((unsigned)(data[1] | (data[2] << 8)) % 16384u);
  uint32_t sr = k_sr_table[(unsigned)(data[3] | (data[4] << 8)) % 9];
  const uint8_t *pcm = data + 6;
  size_t pn = (size - 6) - ((size - 6) % (2 * (size_t)ch));

  uint8_t *uraw;
  size_t ulen;
  if (!vinyl_unchecked_encode(pcm, pn, bs, (size_t)ch, sr, &uraw, &ulen))
    return 0;
  /* Snapshot the raw output: the checked encoder reuses shared Lean buffers. */
  static uint8_t *snap;
  static size_t snapcap;
  if (ulen > snapcap) {
    snapcap = ulen * 2 + 64;
    snap = realloc(snap, snapcap);
    if (!snap)
      _exit(1);
  }
  memcpy(snap, uraw, ulen);

  if (bs <= PACK_BS_MAX) {
    /* Checked slow encoder uses the same defaultAsgChooser 16 as the raw call. */
    uint8_t *sc;
    size_t sl;
    if (vm_encode_slow(pcm, pn, bs, (size_t)ch, sr, &sc, &sl)) {
      if (sl != ulen || memcmp(sc, snap, ulen) != 0) {
        fprintf(stderr,
                "\n[CLAIM VIOLATION — P7] checked encoder disagrees with Unchecked.encode\n"
                "  ch=%d blockSize=%u sampleRate=%u pcm=%zuB checked=%zuB unchecked=%zuB\n",
                ch, bs, sr, pn, sl, ulen);
        FUZZ_ABORT();
      }
      g_agree++;
    } else {
      /* The unchecked encoder accepted; in this in-envelope domain (bs<=4608,
       * whole-frame PCM, table sr) Pcm16ShapeOk holds, so the checked encoder
       * should accept too (P7: checked == unchecked under its precondition). A
       * reject is a genuine accept-set divergence -- surface it, do not drop it. */
      g_checked_reject++;
      fprintf(stderr,
              "[note] checked encoder rejected an input Unchecked.encode accepted "
              "(ch=%d bs=%u sr=%u pcm=%zuB)\n",
              ch, bs, sr, pn);
    }
  } else {
    /* Out of the checked envelope: the raw encoder ran. Its output must decode
     * back to the input PCM under Vinyl's own decoder, or the raw encoder
     * emitted a stream Vinyl cannot read. */
    g_wide_run++;
    uint8_t *dp;
    size_t dl;
    int db, dc, ds;
    if (vinyl_decode_fast(snap, ulen, &dp, &dl, &db, &dc, &ds) == DEC_OK) {
      if (dl != pn || (pn && memcmp(dp, pcm, pn) != 0)) {
        fprintf(stderr,
                "\n[ROUND-TRIP FAILURE] Unchecked.encode(bs>%u) output does not decode to input\n"
                "  ch=%d blockSize=%u sampleRate=%u pcm=%zuB decoded=%zuB\n",
                PACK_BS_MAX, ch, bs, sr, pn, dl);
        FUZZ_ABORT();
      }
      g_wide_rt++;
    } else {
      /* Vinyl's own decoder cannot read what Vinyl's unchecked encoder emitted
       * out of envelope. Not a theorem violation (the raw path is precondition-
       * free by design -- that is the footgun), but no longer silently dropped. */
      g_wide_unreadable++;
    }
  }
  fuzz_tick();
  return 0;
}
