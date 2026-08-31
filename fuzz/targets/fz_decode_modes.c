/* fz_decode_modes — the highest-value target on the fortified codec. Decode the
 * SAME bytes with all three proven-equal Vinyl entry points and demand
 * agreement, AND (the parallel upgrade) demand that the fast path is
 * deterministic across repeats under a live task pool.
 *
 *   vinyl_decode_fast  — Flac.Decode.decodeBytes   (--decode-fast)
 *   vm_decode_pcm16    — Flac.decodePcm16A         (--decode-pcm16)
 *   vm_decode_ref      — Stream.decodeReference    (--decode)
 *
 * These three CLI paths are proven equal, but by DIFFERENT theorems at
 * different levels, so each lane's abort cites the exact composition that backs
 * it (see demand_agreement) rather than one blanket list:
 *   - fast vs pcm16 (bytes): decodeBytes_spec + pcm16FastA_eq_range +
 *     decodePcm16A_eq -- both reduce to pcmBytesRange 16 (decodeArrays …).
 *   - fast vs ref (bytes): decodeBytes_spec + decodeOption_eq_reference +
 *     pcmBytesA_eq -- decodeOption_eq_reference equates the SAMPLES (Option
 *     Audio), then pcmBytesA_eq equates the two serializers; it is NOT a
 *     byte-level guarantee on its own.
 * `decodeBytes` is also the P6 `@[csimp]` surface: the compiled function is
 * swapped for a proven-equal one, and above `parThreshold` (1<<16) it dispatches
 * to `byteStepsPar`. So a mismatch here -- between modes, or across repeats of
 * the SAME mode with LEAN_NUM_THREADS>1 -- is a claim about the BINARY: a
 * miscompilation, a Lean-runtime bug, or a Task-parallelism defect. Aborts.
 *
 * Variants (targets/fz_decode_modes.toml): `serial` (LEAN_NUM_THREADS=1,
 * baseline), `par` (4 threads + VM_REPEAT), `par-forced` (VM_FORCE_PAR).
 * max_len=131072 (2x parThreshold) so decodeBytes's parallel branch is reached. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../common/fuzz_target.h"
#include "../common/vinyl_api.h"
#include "../common/vinyl_modes.h"

/* The List-Bool reference decoder is ~128B of cons cells per input byte plus a
 * quadratic skipBits, so it only runs on inputs up to this size. This 8192 bound is
 * the stack-safety limit: the recursion depth tracks input size, and inputs above it
 * overflow the default stack (an 8884 B multichannel seed decoding to ~148 KB aborts
 * the reference decoder -- the decode-side analogue of encoder-stack-overflow). Do NOT
 * raise it; extending ref-lane coverage to the non-canonical block-size / multichannel
 * seeds needs <=8192 B variants of them, not a larger cap. */
#define VM_REF_MAX_INPUT 8192

static unsigned long g_execs, g_all_ok, g_all_rej, g_skip16, g_ref_run, g_ref_skipped;
static unsigned long g_meta_notes, g_repeats;

static void report(FILE *o) {
  fprintf(o,
          "[modes] execs=%lu ok=%lu rej=%lu skip16=%lu ref_run=%lu ref_skipped=%lu repeat=%lu "
          "fused=%lu fallback=%lu\n",
          g_execs, g_all_ok, g_all_rej, g_skip16, g_ref_run, g_ref_skipped, g_repeats,
          vinyl_decode_fused_count(), vinyl_decode_fallback_count());
}

FUZZ_TARGET(.name = "fz_decode_modes",
            .summary = "three proven-equal decode entry points + parallel determinism (P6 @[csimp])",
            .input_kind = FUZZ_INPUT_FLAC_STREAM, .default_mutator = FUZZ_MUT_CRC, .needs_vinyl = 1,
            .report = report)

typedef struct {
  const char *name;
  int rc;
  uint8_t *pcm;
  size_t len;
  int bps, ch, sr;
} mode_result;

static const char *rc_name(int rc) { return rc == DEC_OK ? "OK" : rc == DEC_REJECT ? "REJECT" : "SKIP"; }

/* The theorems constrain the accept/reject decision, the PCM BYTES, and bps --
 * NOT the derived (ch,sr), which this harness computes inconsistently across
 * modes by construction. So (ch,sr) mismatches are a meta-note, never an abort.
 *
 * `theorems` names the EXACT composition that backs this particular lane pair's
 * byte equality (all three modes are 16-bit-gated by vm_meta_check, so every
 * cited lemma's hypotheses hold). The two lanes are backed by DIFFERENT lemmas
 * and must not share one blanket citation:
 *   fast (decodeBytes) vs pcm16 (decodePcm16A):
 *     decodeBytes_spec + pcm16FastA_eq_range + decodePcm16A_eq  -- both sides
 *     reduce to `pcmBytesRange 16 (decodeArrays …)`; decodeOption_eq_reference
 *     plays NO role here and citing it (as this rig once did) is a false
 *     attribution: it is a SAMPLE-level (Option Audio) theorem, not a byte one.
 *   fast (decodeBytes) vs ref (decodeReference ∘ pcmBytes):
 *     decodeBytes_spec + decodeOption_eq_reference + pcmBytesA_eq  -- the
 *     reference's samples equal decodeArrays' (decodeOption_eq_reference), then
 *     the list serializer pcmBytes equals the array serializer pcmBytesRange
 *     (pcmBytesA_eq). Here decodeOption_eq_reference is a genuine link in the
 *     chain -- but for the SAMPLES, composed with the serializer lemma, never as
 *     the byte guarantee on its own. */
static void demand_agreement(size_t insz, const char *theorems, const mode_result *a,
                             const mode_result *b) {
  const char *what = NULL;
  size_t off = 0;
  if (a->rc != b->rc) {
    what = "accept/reject decision differs";
  } else if (a->rc == DEC_OK) {
    if (a->len != b->len)
      what = "PCM length differs";
    else if (memcmp(a->pcm, b->pcm, a->len) != 0)
      what = "PCM bytes differ";
    else if (a->bps != b->bps)
      what = "bps differs";
    else if (a->ch != b->ch || a->sr != b->sr) {
      if (++g_meta_notes <= 5)
        fprintf(stderr,
                "[meta-note] derived (ch,sr) differ, PCM identical: %s ch=%d sr=%d vs %s ch=%d "
                "sr=%d (input=%zuB, len=%zu)\n",
                a->name, a->ch, a->sr, b->name, b->ch, b->sr, insz, a->len);
      return;
    }
    if (what) {
      size_t m = a->len < b->len ? a->len : b->len;
      while (off < m && a->pcm[off] == b->pcm[off])
        off++;
    }
  }
  if (!what)
    return;
  fprintf(stderr,
          "\n[MODE DIVERGENCE — THEOREM VIOLATION ON THE BINARY] %s\n"
          "  input=%zuB  first_diff_off=%zu\n"
          "  %-6s: rc=%-6s len=%zu bps=%d ch=%d sr=%d\n"
          "  %-6s: rc=%-6s len=%zu bps=%d ch=%d sr=%d\n",
          what, insz, off, a->name, rc_name(a->rc), a->len, a->bps, a->ch, a->sr, b->name,
          rc_name(b->rc), b->len, b->bps, b->ch, b->sr);
  fprintf(stderr, "  contradicts %s\n", theorems);
  abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  mode_result fast = {.name = "fast"}, pcm16 = {.name = "pcm16"}, ref = {.name = "ref"};
  g_execs++;
  if (fuzz_over_sample_cap(data, size)) /* 6E: skip declared-bomb inputs */
    return 0;

  /* Fast path with a determinism repeat under the live task pool. */
  int stable = 1;
  fast.rc = vm_decode_stable(data, size, fuzz_env_repeat(), &fast.pcm, &fast.len, &fast.bps,
                             &fast.ch, &fast.sr, &stable);
  if (fuzz_env_repeat() > 1)
    g_repeats++;
  if (!stable) {
    fprintf(stderr,
            "\n[NONDETERMINISM — THEOREM VIOLATION ON THE BINARY] decodeBytes produced different\n"
            "  output across repeats of the same input (input=%zuB, LEAN_NUM_THREADS live pool)\n"
            "  contradicts the @[csimp] proven-equal parallel decode (docs/06-recursion-shape.md)\n",
            size);
    abort();
  }

  /* VM_FORCE_PAR: exercise byteStepsPar DIRECTLY (bypassing parThreshold and the
   * density bail that keep the corpus off the parallel path -- coverage proved
   * it unreached otherwise) and demand it is deterministic across repeats under
   * the live pool. A difference is a Task/runtime defect in the parallel decode. */
  if (fuzz_env_force_par()) {
    int ran = 0, par_stable = 1;
    vm_force_par_stable(data, size, fuzz_env_repeat() > 1 ? fuzz_env_repeat() : 3, &ran, &par_stable);
    /* `ran` is now honest: it is 1 only when byteStepsPar actually emitted a
     * non-empty step array (an empty one means syncCandidates took the density
     * bail and the parallel path never engaged), so this no longer counts execs
     * as parallel coverage they did not have. A comparison of the concatenated
     * byteStepsPar bytes against the serial fused decode is deliberately NOT done:
     * the two byte layouts are not directly comparable (a direct byteStepsPar
     * invocation is not decodeBytes's internal one), so such a comparison would
     * manufacture false divergences. Determinism across repeats is the sound
     * oracle here. */
    if (ran && !par_stable) {
      fprintf(stderr,
              "\n[NONDETERMINISM — PARALLEL DECODE] byteStepsPar produced different concatenated\n"
              "  frame bytes across repeats of the same input (input=%zuB, live task pool)\n"
              "  a Task-parallelism / Lean-runtime defect in the forced parallel decode path\n",
              size);
      abort();
    }
  }

  pcm16.rc = vm_decode_pcm16(data, size, &pcm16.pcm, &pcm16.len, &pcm16.bps, &pcm16.ch, &pcm16.sr);

  if (fast.rc == DEC_SKIP && pcm16.rc == DEC_SKIP) {
    g_skip16++;
  } else {
    demand_agreement(size, "decodeBytes_spec + pcm16FastA_eq_range + decodePcm16A_eq (16-bit byte layout)",
                     &fast, &pcm16);
    if (size <= VM_REF_MAX_INPUT) {
      ref.rc = vm_decode_ref(data, size, &ref.pcm, &ref.len, &ref.bps, &ref.ch, &ref.sr);
      demand_agreement(size,
                       "decodeBytes_spec + decodeOption_eq_reference + pcmBytesA_eq (samples then "
                       "serializer; 16-bit)",
                       &fast, &ref);
      g_ref_run++;
    } else {
      g_ref_skipped++;
    }
    if (fast.rc == DEC_OK)
      g_all_ok++;
    else
      g_all_rej++;
  }
  fuzz_tick();
  return 0;
}
