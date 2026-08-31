#include "vinyl_api.h"

#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "ffi_util.h"

/* Vinyl entry points, exported by the Lean-generated C (.lake/build/ir).
 * Lean's default calling convention: lean_object* arguments are consumed. */
extern lean_object *vinyl_decode_bytes(lean_object *bytes);
extern lean_object *vinyl_decode_arrays(lean_object *bytes);
extern lean_object *vinyl_read_meta(lean_object *fuel, lean_object *br);
/* ___boxed variant: safe to call with fully-owned boxed args. */
extern lean_object *lp_vinyl_Flac_Stream_pcmBytesRange___boxed(lean_object *b, lean_object *arrs,
                                                               lean_object *lo, lean_object *len);
extern lean_object *initialize_vinyl_Flac(uint8_t builtin);
/* Declared in the lean_main glue rather than a public header. */
extern void lean_initialize_runtime_module(void);
extern void lean_init_task_manager(void);

/* Wrapper-owned PCM buffer, reused across calls, geometric growth. */
static uint8_t *g_buf;
static size_t g_cap;

/* How many decode_fast calls the FUSED decodeBytes served vs how many fell back
 * to the decodeArrays + pcmBytesRange sample path. A "fast-lane" finding must
 * not cite decodeBytes_spec if the comparison actually ran the fallback, and a
 * fused count of 0 means the byte decoder is never being exercised. */
static unsigned long g_fused_ok, g_fallback_ok;
unsigned long vinyl_decode_fused_count(void) { return g_fused_ok; }
unsigned long vinyl_decode_fallback_count(void) { return g_fallback_ok; }

int vinyl_init(void) {
  lean_initialize_runtime_module();
  lean_object *res = initialize_vinyl_Flac(1);
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
  } else {
    lean_io_result_show_error(res);
    return 1;
  }
  lean_io_mark_end_initialization();
  /* Create the task pool, exactly as the shipped `vinyl` CLI's main does after
     module init. Without it `Task.spawn` runs inline on the calling thread, so
     the codec's parallel decode/encode paths (stepsPar, byteStepsPar,
     pcm16FastPar, the per-frame encode workers) are never actually concurrent
     and would go untested. `LEAN_NUM_THREADS` sizes this pool. */
  lean_init_task_manager();
  return 0;
}

int vinyl_decode_fast(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len,
                      int *bps, int *ch, int *sr) {
  *pcm = NULL;
  *len = 0;
  *bps = *ch = *sr = 0;
  if (n < 4)
    return DEC_REJECT; /* cannot even hold the fLaC marker */

  lean_object *ba = mk_ba(in, n);

  /* Header info (bps/ch/sr), exactly FuzzHarness.headerInfo: readMeta on a
   * BitReader positioned after the 32-bit marker. readMeta succeeding is a
   * prerequisite inside decodeBytes/decodeArrays too, so short-circuiting a
   * readMeta failure to REJECT matches the decoders. */
  if (memcmp(in, "fLaC", 4) != 0) {
    lean_dec(ba);
    return DEC_REJECT;
  }
  lean_inc(ba);
  lean_object *br = lean_alloc_ctor(0, 2, 0); /* BitReader ⟨data, pos⟩ */
  lean_ctor_set(br, 0, ba);
  lean_ctor_set(br, 1, lean_usize_to_nat(32));
  lean_object *mi = vinyl_read_meta(lean_usize_to_nat(8 * n - 32), br);
  if (lean_obj_tag(mi) == 0) { /* none */
    lean_dec(mi);
    lean_dec(ba);
    return DEC_REJECT;
  }
  {
    lean_object *pair = lean_ctor_get(mi, 0); /* Info × BitReader (borrowed) */
    lean_object *info = lean_ctor_get(pair, 0);
    /* Info fields: 0 minBlock, 1 maxBlock, 2 sampleRate, 3 channels, 4 bps */
    *sr = nat_small(lean_ctor_get(info, 2));
    *ch = nat_small(lean_ctor_get(info, 3));
    *bps = nat_small(lean_ctor_get(info, 4));
  }
  lean_dec(mi);
  if (*bps != 16) { /* byte pipeline is 16-bit only */
    lean_dec(ba);
    return DEC_SKIP;
  }

  /* Primary path: fused byte decoder. */
  lean_inc(ba); /* keep one ref for the fallback */
  lean_object *r = vinyl_decode_bytes(ba);
  if (lean_obj_tag(r) == 1) { /* some (pcm, bps) */
    lean_object *p = lean_ctor_get(r, 0);
    lean_object *bytes = lean_ctor_get(p, 0);
    *bps = nat_small(lean_ctor_get(p, 1));
    size_t sz = lean_sarray_size(bytes);
    memcpy(fuzz_grow(&g_buf, &g_cap, sz ? sz : 1), lean_sarray_cptr(bytes), sz);
    *pcm = g_buf;
    *len = sz;
    lean_dec(r);
    lean_dec(ba);
    g_fused_ok++;
    return DEC_OK;
  }
  lean_dec(r);

  /* Fallback (mirrors the CLI): sample-path decode + serializer. */
  lean_object *r2 = vinyl_decode_arrays(ba); /* consumes ba */
  if (lean_obj_tag(r2) == 0) {
    lean_dec(r2);
    return DEC_REJECT;
  }
  lean_object *p = lean_ctor_get(r2, 0);  /* List (Array Int) × Nat × Nat */
  lean_object *chs = lean_ctor_get(p, 0); /* borrowed */
  lean_object *q = lean_ctor_get(p, 1);
  int b = nat_small(lean_ctor_get(q, 0));
  *sr = nat_small(lean_ctor_get(q, 1));
  size_t nch = 0, head = 0;
  for (lean_object *c = chs; !lean_is_scalar(c); c = lean_ctor_get(c, 1)) {
    if (nch == 0)
      head = lean_array_size(lean_ctor_get(c, 0));
    nch++;
  }
  lean_inc(chs);
  lean_object *out = lp_vinyl_Flac_Stream_pcmBytesRange___boxed(
      lean_usize_to_nat((size_t)b), chs, lean_usize_to_nat(0), lean_usize_to_nat(head));
  size_t sz = lean_sarray_size(out);
  memcpy(fuzz_grow(&g_buf, &g_cap, sz ? sz : 1), lean_sarray_cptr(out), sz);
  *pcm = g_buf;
  *len = sz;
  *bps = b;
  *ch = (int)nch;
  lean_dec(out);
  lean_dec(r2);
  g_fallback_ok++;
  return DEC_OK;
}
