/* fz_encode_pcm16_eq -- the largest missing proven pair (Phase 6G).
 *
 * `Flac.Encode.encodePcm16 bs ch sr bytes` (the shipped 16-bit PCM encoder) is
 * proven byte-identical to `Stream.Unchecked.encode ⟨bs,false,fastChooser 16⟩
 * ⟨deinterleave ch (pcm16OfByteList bytes), 16, sr⟩` (`Flac.encodePcm16_eq`,
 * preconds: 0<ch, ch≤8, 0<bs, bytes.size % (2*ch) == 0). This drives BOTH sides on
 * the same packed PCM and asserts equality -- a divergence is a compiler / runtime
 * / @[csimp] defect no round-trip or referee oracle can see. Aborts unconditionally
 * like the other proven-pair targets. Input: PACKED_PCM. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "../common/ffi_util.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"
#include "../common/pack.h"

/* Phase 7C: stable @[export] names (FlacTest/FuzzGen.lean) instead of mangled
 * lp_vinyl_Flac_* forms, so a Lean-internal rename is caught by check-symbols. */
extern lean_object *vinyl_encode_pcm16(lean_object *bs, lean_object *ch,
                                       lean_object *sr, lean_object *bytes);
extern lean_object *vinyl_deinterleave(lean_object *ch, lean_object *l);
extern lean_object *vinyl_pcm16_of_byte_list(lean_object *l);
extern lean_object *vlean_unchecked_encode(lean_object *cfg, lean_object *audio);
extern lean_object *vinyl_fastChooser(lean_object *b, lean_object *fr); /* FlacTest/FuzzGen.lean */

int vinyl_init(void);
static unsigned long g_execs, g_pairs, g_len_diff, g_byte_diff;

static void report(FILE *o) {
  fprintf(o, "[encpcm16] execs=%lu pairs=%lu len_diff=%lu byte_diff=%lu "
             "(both MUST be 0 -- encodePcm16_eq)\n",
          g_execs, g_pairs, g_len_diff, g_byte_diff);
}

FUZZ_TARGET(.name = "fz_encode_pcm16_eq",
            .summary = "proven pair: Encode.encodePcm16 == Unchecked.encode(fastChooser 16)",
            .input_kind = FUZZ_INPUT_PACKED_PCM, .default_mutator = FUZZ_MUT_PLAIN,
            .needs_vinyl = 1, .report = report)

/* List UInt8 from a raw byte buffer, built tail-to-head at refcount 1. */
static lean_object *byte_list(const uint8_t *p, size_t n) {
  lean_object *l = lean_box(0); /* List.nil */
  for (size_t i = n; i-- > 0;) {
    lean_object *c = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(c, 0, lean_box(p[i]));
    lean_ctor_set(c, 1, l);
    l = c;
  }
  return l;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  PackedInput in;
  if (!pack_decode(data, size, &in))
    return 0;
  size_t ch = in.ch ? in.ch : 1;
  if (ch > 8)
    ch = 8;
  size_t bs = in.bs ? in.bs : 4096;
  /* precondition: bytes.size % (2*ch) == 0 -- trim to whole frames. */
  size_t frame = 2u * ch;
  size_t plen = in.pcm_len - (in.pcm_len % frame);
  if (plen < frame)
    return 0;
  /* Bound PCM for throughput. This WAS a bitsToByteList stack-overflow workaround;
   * that recursion now has an @[csimp] tail swap (re-baselined overflow-free, P0.2),
   * so the bound is raised 16 KB -> 64 KB to reach deeper frame counts (concatFrames,
   * multi-task encode workers, frame-boundary chunking). */
  if (plen > 65536u)
    plen = 65536u - (65536u % frame);

  /* LHS: encodePcm16 bs ch sr bytes (consumes its ByteArray). */
  lean_object *lhs = vinyl_encode_pcm16(
      lean_usize_to_nat(bs), lean_usize_to_nat(ch), lean_usize_to_nat((size_t)in.sr),
      mk_ba(in.pcm, plen));

  /* RHS: Unchecked.encode ⟨bs,false,fastChooser 16⟩ ⟨deinterleave ch (pcm16OfByteList bytes),16,sr⟩. */
  lean_object *pcm16 = vinyl_pcm16_of_byte_list(byte_list(in.pcm, plen));   /* List Int */
  lean_object *channels = vinyl_deinterleave(lean_usize_to_nat(ch), pcm16); /* List (List Int) */
  lean_object *audio = lean_alloc_ctor(0, 3, 0); /* Audio ⟨channels, bps, sampleRate⟩ */
  lean_ctor_set(audio, 0, channels);
  lean_ctor_set(audio, 1, lean_usize_to_nat(16));
  lean_ctor_set(audio, 2, lean_usize_to_nat((size_t)in.sr));
  lean_object *chooser = lean_alloc_closure((void *)vinyl_fastChooser, 2, 1); /* fastChooser 16 */
  lean_closure_set(chooser, 0, lean_usize_to_nat(16));
  lean_object *cfg = lean_alloc_ctor(0, 2, 1); /* EncoderCfg ⟨blockSize, chooser⟩ + uint8 varBlk */
  lean_ctor_set(cfg, 0, lean_usize_to_nat(bs));
  lean_ctor_set(cfg, 1, chooser);
  lean_ctor_set_uint8(cfg, sizeof(void *) * 2, 0); /* variableBlocking := false */
  lean_object *rhs = vlean_unchecked_encode(cfg, audio);

  size_t ll = lean_sarray_size(lhs), rl = lean_sarray_size(rhs);
  const uint8_t *lb = lean_sarray_cptr(lhs), *rb = lean_sarray_cptr(rhs);
  if (ll != rl) {
    g_len_diff++;
    fprintf(stderr, "\n[PROVEN-PAIR VIOLATION] encodePcm16 vs Unchecked.encode LENGTH: "
                    "bs=%zu ch=%zu sr=%u -> %zuB vs %zuB (encodePcm16_eq falsified)\n",
            bs, ch, in.sr, ll, rl);
    oracle_dump_write("encpcm16_len_diff", data, size);
    lean_dec(lhs); lean_dec(rhs);
    FUZZ_ABORT();
  }
  if (memcmp(lb, rb, ll) != 0) {
    size_t off = 0;
    while (off < ll && lb[off] == rb[off]) off++;
    g_byte_diff++;
    fprintf(stderr, "\n[PROVEN-PAIR VIOLATION] encodePcm16 != Unchecked.encode at byte %zu "
                    "(bs=%zu ch=%zu sr=%u len=%zuB) -- encodePcm16_eq falsified in compiled code\n",
            off, bs, ch, in.sr, ll);
    oracle_dump_write("encpcm16_byte_diff", data, size);
    lean_dec(lhs); lean_dec(rhs);
    FUZZ_ABORT();
  }
  g_pairs++;
  lean_dec(lhs);
  lean_dec(rhs);
  fuzz_tick();
  return 0;
}
