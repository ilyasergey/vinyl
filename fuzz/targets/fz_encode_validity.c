/* fz_encode_validity — does Vinyl's OWN output pass a strict `flac -t`
 * equivalent? The rest of the fleet only asks whether libFLAC's library layer
 * can read Vinyl's stream back with MD5 checking OFF; nothing catches a wrong
 * STREAMINFO MD5 or a frame-vs-STREAMINFO inconsistency. common/flac_validate.c
 * turns MD5 checking ON and asserts the decoded audio equals the input PCM. A
 * failure is the client's bug class (b): corrupted output the reference
 * rejects. Severity V. Input packing: common/pack.h (checked-encode domain). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/flac_api.h"
#include "../common/fuzz_target.h"
#include "../common/pack.h"
#include "../common/vinyl_modes.h"

static unsigned long g_execs, g_encoded, g_rejected, g_bad;

static void report(FILE *o) {
  fprintf(o, "[validity] execs=%lu encoded=%lu enc_rejected=%lu invalid=%lu\n", g_execs, g_encoded,
          g_rejected, g_bad);
}

FUZZ_TARGET(.name = "fz_encode_validity",
            .summary = "Vinyl's own output must pass a strict flac -t equivalent (MD5 + PCM)",
            .input_kind = FUZZ_INPUT_PACKED_PCM, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 1, .needs_flac = 1, .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  PackedInput in;
  g_execs++;
  if (!pack_decode(data, size, &in))
    return 0;

  uint8_t *out;
  size_t outlen;
  if (!vm_encode_fast(in.pcm, in.pcm_len, in.bs, (size_t)in.ch, in.sr, &out, &outlen)) {
    g_rejected++; /* a clean reject is not a finding */
    return 0;
  }
  g_encoded++;

  FlacValidation v;
  if (!flac_validate_strict(out, outlen, in.pcm, in.pcm_len, &v)) {
    g_bad++;
    flac_validate_report(stderr, &v, out, outlen);
    fprintf(stderr, "  params: ch=%d blockSize=%u sampleRate=%u pcm=%zuB\n", in.ch, in.bs, in.sr,
            in.pcm_len);
    abort(); /* class (b): corrupted output the reference rejects */
  }
  fuzz_tick();
  return 0;
}
