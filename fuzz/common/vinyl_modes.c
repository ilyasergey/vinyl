#include "vinyl_modes.h"

#include <lean/lean.h>

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "ffi_util.h"
#include "vinyl_api.h"
#include "vinyl_symbols.h" /* DEC_REJECT / DEC_OK / DEC_SKIP */

/* Lean-generated entry points (all arguments consumed unless noted).
 * vinyl_encode_pcm16_fast borrows sampleRate, so the ___boxed
 * variant — which owns everything — is used instead. */
extern lean_object *vinyl_read_meta(lean_object *fuel, lean_object *br);
extern lean_object *vinyl_decode_pcm16a(lean_object *flac);
extern lean_object *vinyl_decode_reference(lean_object *bytes);
extern lean_object *lp_vinyl_Flac_Stream_pcmBytes___boxed(lean_object *b, lean_object *chs);
extern lean_object *lp_vinyl_Flac_encodePcm16Fast___boxed(lean_object *bs, lean_object *ch,
                                                          lean_object *sr, lean_object *bytes);
extern lean_object *vinyl_encode_pcm16_cfg(lean_object *cfg, lean_object *ch,
                                                 lean_object *sr, lean_object *bytes);
extern lean_object *vinyl_default_chooser(lean_object *b, lean_object *fr);

/* Per-wrapper output buffer, reused across calls, geometric growth. */
typedef struct {
  uint8_t *p;
  size_t cap;
} vm_buf;

/* Copy a Lean ByteArray into `b` and expose it through pcm/len. */
static void vm_copy_out(vm_buf *b, lean_object *bytes, uint8_t **pcm, size_t *len) {
  size_t sz = lean_sarray_size(bytes);
  memcpy(fuzz_grow(&b->p, &b->cap, sz ? sz : 1), lean_sarray_cptr(bytes), sz);
  *pcm = b->p;
  *len = sz;
}

/* The same STREAMINFO pre-check vinyl_decode_fast performs: marker +
 * Flac.Decode.readMeta, then DEC_SKIP for non-16-bit streams (the byte
 * pipeline is 16-bit only). readMeta succeeding is a prerequisite inside
 * every decode path, so short-circuiting a failure to DEC_REJECT matches
 * the decoders. On DEC_OK, *out_ba is an OWNED ByteArray of the input for
 * the subsequent decode call. */
static int vm_meta_check(const uint8_t *in, size_t n, lean_object **out_ba, int *bps, int *ch,
                         int *sr) {
  *bps = *ch = *sr = 0;
  if (n < 4 || memcmp(in, "fLaC", 4) != 0)
    return DEC_REJECT;
  lean_object *ba = mk_ba(in, n);
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
  if (*bps != 16) {
    lean_dec(ba);
    return DEC_SKIP;
  }
  *out_ba = ba;
  return DEC_OK;
}

/* The CLI `--decode-pcm16` path: Flac.decodePcm16A (Except String ByteArray;
 * tag 0 = error, tag 1 = ok). */
int vm_decode_pcm16(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len, int *bps, int *ch,
                    int *sr) {
  static vm_buf buf;
  *pcm = NULL;
  *len = 0;
  lean_object *ba;
  int rc = vm_meta_check(in, n, &ba, bps, ch, sr);
  if (rc != DEC_OK)
    return rc;
  lean_object *r = vinyl_decode_pcm16a(ba);
  if (lean_obj_tag(r) == 0) { /* .error */
    lean_dec(r);
    return DEC_REJECT;
  }
  vm_copy_out(&buf, lean_ctor_get(r, 0), pcm, len);
  lean_dec(r);
  return DEC_OK;
}

/* The CLI `--decode` path: Flac.Stream.decodeReference (Option Audio),
 * serialized with Stream.pcmBytes exactly as the CLI does. Audio fields:
 * 0 channels (List (List Int)), 1 bps, 2 sampleRate. */
int vm_decode_ref(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len, int *bps, int *ch,
                  int *sr) {
  static vm_buf buf;
  *pcm = NULL;
  *len = 0;
  lean_object *ba;
  int rc = vm_meta_check(in, n, &ba, bps, ch, sr);
  if (rc != DEC_OK)
    return rc;
  lean_object *r = vinyl_decode_reference(ba);
  if (lean_obj_tag(r) == 0) { /* none */
    lean_dec(r);
    return DEC_REJECT;
  }
  lean_object *audio = lean_ctor_get(r, 0); /* borrowed */
  lean_object *chs = lean_ctor_get(audio, 0);
  lean_object *bnat = lean_ctor_get(audio, 1);
  *bps = nat_small(bnat);
  *sr = nat_small(lean_ctor_get(audio, 2));
  size_t nch = 0;
  for (lean_object *c = chs; !lean_is_scalar(c); c = lean_ctor_get(c, 1))
    nch++;
  *ch = (int)nch;
  lean_inc(chs);
  lean_inc(bnat);
  lean_object *out = lp_vinyl_Flac_Stream_pcmBytes___boxed(bnat, chs);
  vm_copy_out(&buf, out, pcm, len);
  lean_dec(out);
  lean_dec(r);
  return DEC_OK;
}

/* The CLI `--encode` path: Flac.encodePcm16Fast (Option ByteArray). */
int vm_encode_fast(const uint8_t *pcm, size_t n, size_t bs, size_t ch, size_t sr, uint8_t **out,
                   size_t *len) {
  static vm_buf buf;
  *out = NULL;
  *len = 0;
  lean_object *r = lp_vinyl_Flac_encodePcm16Fast___boxed(
      lean_usize_to_nat(bs), lean_usize_to_nat(ch), lean_usize_to_nat(sr), mk_ba(pcm, n));
  if (lean_obj_tag(r) == 0) { /* none */
    lean_dec(r);
    return 0;
  }
  vm_copy_out(&buf, lean_ctor_get(r, 0), out, len);
  lean_dec(r);
  return 1;
}

/* The CLI `--encode-slow` path: Flac.encodePcm16Cfg with
 * EncoderCfg ⟨bs, false, Heuristics.defaultAsgChooser 16⟩ — ctor layout
 * confirmed against the generated encodeSlowMain: lean_alloc_ctor(0, 2, 1),
 * obj fields {blockSize, chooser}, variableBlocking as uint8 scalar. */
int vm_encode_slow(const uint8_t *pcm, size_t n, size_t bs, size_t ch, size_t sr, uint8_t **out,
                   size_t *len) {
  static vm_buf buf;
  *out = NULL;
  *len = 0;
  lean_object *chooser = lean_alloc_closure((void *)vinyl_default_chooser, 2, 1);
  lean_closure_set(chooser, 0, lean_box(16));
  lean_object *cfg = lean_alloc_ctor(0, 2, 1);
  lean_ctor_set(cfg, 0, lean_usize_to_nat(bs));
  lean_ctor_set(cfg, 1, chooser);
  lean_ctor_set_uint8(cfg, sizeof(void *) * 2, 0); /* variableBlocking := false */
  lean_object *r = vinyl_encode_pcm16_cfg(cfg, lean_usize_to_nat(ch), lean_usize_to_nat(sr),
                                                mk_ba(pcm, n));
  if (lean_obj_tag(r) == 0) { /* none */
    lean_dec(r);
    return 0;
  }
  vm_copy_out(&buf, lean_ctor_get(r, 0), out, len);
  lean_dec(r);
  return 1;
}

/* ================= folded in from vinyl_md5.c ================= */


/* Flac.Md5.md5 : ByteArray -> ByteArray (16 bytes). Default calling convention:
 * the argument is consumed. */
extern lean_object *vlean_md5(lean_object *msg);

size_t vinyl_md5(const uint8_t *msg, size_t len, uint8_t out[16]) {
  lean_object *digest = vlean_md5(mk_ba(msg, len));
  size_t dn = lean_sarray_size(digest);
  memcpy(out, lean_sarray_cptr(digest), dn < 16 ? dn : 16);
  lean_dec(digest);
  return dn;
}

/* Flac.Md5.md5Hex : ByteArray -> String (the 32-char lowercase digest, via the
 * flatMapTR nibble->hex helper). Default calling convention consumes the arg. */
extern lean_object *vlean_md5_hex(lean_object *msg);

size_t vinyl_md5_hex(const uint8_t *msg, size_t len, char out[33]) {
  lean_object *s = vlean_md5_hex(mk_ba(msg, len));
  const char *cs = lean_string_cstr(s);
  size_t n = strlen(cs);
  size_t cpy = n < 32 ? n : 32;
  memcpy(out, cs, cpy);
  out[cpy] = '\0';
  lean_dec(s);
  return n;
}

/* ================= folded in from vinyl_unchecked_api.c ================= */
/* Stream.Unchecked.encode : EncoderCfg -> Audio -> ByteArray.
 * EncoderCfg <blockSize, variableBlocking, chooser> and
 * Audio <channels : List (List Int), bps, sampleRate> ctor layouts confirmed
 * against the generated encodeSlow glue / Stream.decodeReference reader. */
extern lean_object *vlean_unchecked_encode(lean_object *cfg, lean_object *audio);
extern lean_object *vinyl_default_chooser(lean_object *b, lean_object *fr);

static uint8_t *g_buf;
static size_t g_cap;

/* Build List Int for channel `c` of `ch` from `frames` interleaved s16 samples,
 * constructed tail-to-head so the list is in sample order. */
static lean_object *channel_list(const uint8_t *pcm, size_t frames, size_t ch, size_t c) {
  lean_object *lst = lean_box(0); /* List.nil */
  for (size_t i = frames; i-- > 0;) {
    size_t idx = (i * ch + c) * 2;
    int16_t s = (int16_t)(pcm[idx] | (pcm[idx + 1] << 8));
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, lean_int64_to_int((int64_t)s));
    lean_ctor_set(cons, 1, lst);
    lst = cons;
  }
  return lst;
}

int vinyl_unchecked_encode(const uint8_t *pcm, size_t n, size_t bs, size_t ch, size_t sr,
                           uint8_t **out, size_t *len) {
  *out = NULL;
  *len = 0;
  if (ch == 0 || n % (2 * ch) != 0)
    return 0;
  size_t frames = n / (2 * ch);

  /* channels : List (List Int), built tail-to-head over channel index. */
  lean_object *channels = lean_box(0);
  for (size_t c = ch; c-- > 0;) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, channel_list(pcm, frames, ch, c));
    lean_ctor_set(cons, 1, channels);
    channels = cons;
  }
  lean_object *audio = lean_alloc_ctor(0, 3, 0); /* Audio <channels, bps, sampleRate> */
  lean_ctor_set(audio, 0, channels);
  lean_ctor_set(audio, 1, lean_usize_to_nat(16));
  lean_ctor_set(audio, 2, lean_usize_to_nat(sr));

  lean_object *chooser = lean_alloc_closure((void *)vinyl_default_chooser, 2, 1);
  lean_closure_set(chooser, 0, lean_box(16));
  lean_object *cfg = lean_alloc_ctor(0, 2, 1); /* <blockSize, chooser> + uint8 variableBlocking */
  lean_ctor_set(cfg, 0, lean_usize_to_nat(bs));
  lean_ctor_set(cfg, 1, chooser);
  lean_ctor_set_uint8(cfg, sizeof(void *) * 2, 0); /* variableBlocking := false */

  lean_object *r = vlean_unchecked_encode(cfg, audio); /* ByteArray */
  size_t sz = lean_sarray_size(r);
  memcpy(fuzz_grow(&g_buf, &g_cap, sz ? sz : 1), lean_sarray_cptr(r), sz);
  *out = g_buf;
  *len = sz;
  lean_dec(r);
  return 1;
}

/* ================= folded in from vinyl_parallel.c ================= */
#include "vinyl_api.h" /* vinyl_decode_fast, DEC_* */

/* vinyl_symbols.h (generated by mk/lean.mk) records which lp_vinyl_* the codec
 * exports. The forced-serial/parallel entry points below are compiled in only
 * when their symbols exist; otherwise the determinism repeat is the whole test. */

/* Module-owned snapshot of the first decode, so repeats (which reuse
 * vinyl_decode_fast's shared buffer) can be compared against it. */
static uint8_t *g_snap;
static size_t g_snap_cap, g_snap_len;

static void snap_store(const uint8_t *p, size_t n) {
  memcpy(fuzz_grow(&g_snap, &g_snap_cap, n ? n : 1), p, n);
  g_snap_len = n;
}

int vm_decode_stable(const uint8_t *in, size_t n, int repeat, uint8_t **pcm, size_t *len, int *bps,
                     int *ch, int *sr, int *stable) {
  *stable = 1;
  uint8_t *p;
  size_t l;
  int b, c, s;
  int rc0 = vinyl_decode_fast(in, n, &p, &l, &b, &c, &s);
  if (rc0 == DEC_OK)
    snap_store(p, l);
  if (repeat < 1)
    repeat = 1;
  for (int i = 1; i < repeat; i++) {
    uint8_t *p2;
    size_t l2;
    int b2, c2, s2;
    int rc = vinyl_decode_fast(in, n, &p2, &l2, &b2, &c2, &s2);
    if (rc != rc0) {
      *stable = 0;
      break;
    }
    if (rc0 == DEC_OK && (l2 != g_snap_len || (l2 && memcmp(p2, g_snap, l2) != 0) || b2 != b)) {
      *stable = 0;
      break;
    }
  }
  if (rc0 == DEC_OK) {
    *pcm = g_snap;
    *len = g_snap_len;
    *bps = b;
    *ch = c;
    *sr = s;
  } else {
    *pcm = NULL;
    *len = 0;
    *bps = *ch = *sr = 0;
  }
  return rc0;
}

#if defined(HAVE_LP_VINYL_FLAC_DECODE_BYTESTEPSPAR) &&                                              \
    defined(HAVE_LP_VINYL_FLAC_DECODE_SYNCCANDIDATES) &&                                            \
    defined(HAVE_LP_VINYL_FLAC_DECODE_READMETA)
extern lean_object *vinyl_read_meta(lean_object *fuel, lean_object *br);
extern lean_object *lp_vinyl_Flac_Decode_syncCandidates(lean_object *d, lean_object *start);
extern lean_object *lp_vinyl_Flac_Decode_byteStepsPar(lean_object *b0, lean_object *bps,
                                                      lean_object *ch, lean_object *d,
                                                      lean_object *cands);

/* Concatenated frame bytes of one byteStepsPar run, into a reusable buffer. */
static uint8_t *fp_run(const uint8_t *in, size_t n, int bps, int ch, size_t start_byte,
                       uint8_t **buf, size_t *cap, size_t *out_len) {
  lean_object *d = mk_ba(in, n);
  lean_inc(d); /* one ref for syncCandidates, one for byteStepsPar */
  lean_object *cands = lp_vinyl_Flac_Decode_syncCandidates(d, lean_usize_to_nat(start_byte));
  lean_object *steps = lp_vinyl_Flac_Decode_byteStepsPar(
      lean_usize_to_nat((size_t)bps), lean_usize_to_nat((size_t)bps), lean_usize_to_nat((size_t)ch),
      d, cands);
  size_t ns = lean_array_size(steps), total = 0;
  for (size_t i = 0; i < ns; i++)
    total += lean_sarray_size(lean_ctor_get(lean_array_get_core(steps, i), 1)); /* field 1 = bytes */
  fuzz_grow(buf, cap, total ? total : 1);
  size_t off = 0;
  for (size_t i = 0; i < ns; i++) {
    lean_object *b = lean_ctor_get(lean_array_get_core(steps, i), 1);
    size_t sz = lean_sarray_size(b);
    memcpy(*buf + off, lean_sarray_cptr(b), sz);
    off += sz;
  }
  lean_dec(steps);
  *out_len = total;
  return *buf;
}

void vm_force_par_stable(const uint8_t *in, size_t n, int repeat, int *ran, int *stable) {
  *ran = 0;
  *stable = 1;
  if (n < 4 || memcmp(in, "fLaC", 4) != 0)
    return;

  /* Header: (bps, ch, first-frame byte offset), exactly as decodeBytes derives
   * them before the byteStepsPar call. */
  lean_object *d0 = mk_ba(in, n);
  lean_inc(d0);
  lean_object *br = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(br, 0, d0);
  lean_ctor_set(br, 1, lean_usize_to_nat(32));
  lean_object *mi = vinyl_read_meta(lean_usize_to_nat(8 * n - 32), br);
  if (lean_obj_tag(mi) == 0) {
    lean_dec(mi);
    lean_dec(d0);
    return;
  }
  lean_object *pair = lean_ctor_get(mi, 0);
  lean_object *info = lean_ctor_get(pair, 0);
  lean_object *brp = lean_ctor_get(pair, 1);
  lean_object *bpsN = lean_ctor_get(info, 4), *chN = lean_ctor_get(info, 3);
  lean_object *posN = lean_ctor_get(brp, 1);
  int bps = lean_is_scalar(bpsN) ? (int)lean_unbox(bpsN) : -1;
  int ch = lean_is_scalar(chN) ? (int)lean_unbox(chN) : -1;
  size_t start_byte = lean_is_scalar(posN) ? lean_unbox(posN) / 8 : 0;
  lean_dec(mi);
  lean_dec(d0);
  if (bps < 1 || ch < 1)
    return;

  static uint8_t *cur, *snap;
  static size_t cur_cap, snap_cap;
  size_t cur_len = 0, snap_len = 0;
  int produced = 0;
  if (repeat < 1)
    repeat = 1;
  for (int r = 0; r < repeat; r++) {
    fp_run(in, n, bps, ch, start_byte, &cur, &cur_cap, &cur_len);
    if (r == 0) {
      /* byteStepsPar returns #[] when syncCandidates took the density bail: the
       * parallel path did NOT engage, so this exec must NOT report that it did
       * (it would count as parallel coverage it never had). */
      produced = (cur_len > 0);
      memcpy(fuzz_grow(&snap, &snap_cap, cur_len ? cur_len : 1), cur, cur_len);
      snap_len = cur_len;
    } else if (cur_len != snap_len || (cur_len && memcmp(cur, snap, cur_len) != 0)) {
      *stable = 0;
      break;
    }
  }
  *ran = produced;
}
#else
void vm_force_par_stable(const uint8_t *in, size_t n, int repeat, int *ran, int *stable) {
  (void)in;
  (void)n;
  (void)repeat;
  *ran = 0;
  *stable = 1;
}
#endif
