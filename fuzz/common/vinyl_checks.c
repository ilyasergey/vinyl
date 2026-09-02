#include "vinyl_checks.h"

#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

#include "flac_struct.h" /* flac_frame_channels */
#include "vinyl_api.h"    /* DEC_OK / DEC_REJECT (unused values, kept for parity) */

/* Production sample-path decoder (any depth): ByteArray -> Option Audio, with
 * Audio = { channels : List (List Int), bps : Nat, sampleRate : Nat }. */
extern lean_object *vinyl_decode_option(lean_object *bytes);
extern lean_object *vinyl_decode_reference(lean_object *bytes);
/* Shipped public entrypoints: Flac.decode : ByteArray -> Except String Audio
 * (Except.ok = ctor tag 1); Flac.Stream.peekInfo : ByteArray -> Option Info. */
extern lean_object *vinyl_decode(lean_object *bytes);
extern lean_object *vinyl_peek_info(lean_object *bytes);
extern lean_object *vinyl_encode(lean_object *audio); /* some iff Audio.WellFormed */
extern lean_object *vinyl_read_meta(lean_object *fuel, lean_object *br);
/* 16-bit byte pipeline: ByteArray -> Option (ByteArray × Nat). */
extern lean_object *vinyl_decode_bytes(lean_object *bytes);
/* Flac.Stream.pcmBytes : Nat -> List (List Int) -> ByteArray (consumes both). */
extern lean_object *vinyl_pcm_bytes(lean_object *bps, lean_object *chs);
/* Metamorphic re-encode lanes (env VM_REENC_LANE): the fast statically-verified
 * emitter and the 16-bit byte encoder, plus the default chooser they need. Each
 * @[export] wrapper owns (consumes) all of its arguments. */
extern lean_object *vinyl_emit_fast(lean_object *cfg, lean_object *audio);
extern lean_object *vinyl_encode_pcm16_fast(lean_object *bs, lean_object *ch, lean_object *sr,
                                            lean_object *bytes);
extern lean_object *vinyl_default_chooser(lean_object *b, lean_object *fr);

/* ---- shared helpers (one copy for all three checks) ------------------- */
static lean_object *mk_ba(const uint8_t *in, size_t n) {
  lean_object *ba = lean_alloc_sarray(1, n, n);
  if (n)
    memcpy(lean_sarray_cptr(ba), in, n);
  return ba;
}

static long nat_ll(lean_object *n) { return lean_is_scalar(n) ? (long)lean_unbox(n) : -1; }

/* Times an encode-based check skipped the re-encode on a decode bomb (D7). */
static unsigned long g_encode_capped;
unsigned long vinyl_encode_capped_count(void) { return g_encode_capped; }

static unsigned long list_len(lean_object *l) {
  unsigned long k = 0;
  for (; !lean_is_scalar(l); l = lean_ctor_get(l, 1))
    k++;
  return k;
}

/* numSamples = length of the first channel. */
static unsigned long first_plane_len(lean_object *audio) {
  lean_object *chs = lean_ctor_get(audio, 0);
  return lean_is_scalar(chs) ? 0 : list_len(lean_ctor_get(chs, 0));
}

/* STREAMINFO's declared channel count via readMeta, or -1 if the header does not
 * parse. Mirrors vm_meta_check's borrow discipline (vinyl_modes.c): the BitReader
 * owns the one ByteArray ref, readMeta consumes the reader, Info fields are
 * borrowed out of the result before it is decremented. Info field 3 = channels. */
static int streaminfo_channels(const uint8_t *in, size_t n) {
  if (n < 4 || memcmp(in, "fLaC", 4) != 0)
    return -1;
  lean_object *ba = mk_ba(in, n);
  lean_object *br = lean_alloc_ctor(0, 2, 0); /* BitReader ⟨data, pos=32⟩ */
  lean_ctor_set(br, 0, ba);
  lean_ctor_set(br, 1, lean_usize_to_nat(32));
  lean_object *mi = vinyl_read_meta(lean_usize_to_nat(8 * n - 32), br);
  int ch = -1;
  if (lean_obj_tag(mi) != 0) {
    lean_object *pair = lean_ctor_get(mi, 0); /* Info × BitReader (borrowed) */
    lean_object *info = lean_ctor_get(pair, 0);
    ch = (int)nat_ll(lean_ctor_get(info, 3));
  }
  lean_dec(mi);
  return ch;
}

/* Deep Audio equality (bps, sampleRate, and every sample), scalar or bignum. */
static int audio_eq(lean_object *a, lean_object *b, const char **why, int *bad_ch, int *bad_idx) {
  if (!lean_nat_dec_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1))) {
    if (why) *why = "decoded bps differs";
    return 0;
  }
  if (!lean_nat_dec_eq(lean_ctor_get(a, 2), lean_ctor_get(b, 2))) {
    if (why) *why = "decoded sampleRate differs";
    return 0;
  }
  lean_object *ca = lean_ctor_get(a, 0), *cb = lean_ctor_get(b, 0);
  int chi = 0;
  while (!lean_is_scalar(ca) && !lean_is_scalar(cb)) {
    lean_object *pa = lean_ctor_get(ca, 0), *pb = lean_ctor_get(cb, 0);
    int idx = 0;
    while (!lean_is_scalar(pa) && !lean_is_scalar(pb)) {
      if (!lean_int_dec_eq(lean_ctor_get(pa, 0), lean_ctor_get(pb, 0))) {
        if (why) *why = "decoded sample differs";
        if (bad_ch) *bad_ch = chi;
        if (bad_idx) *bad_idx = idx;
        return 0;
      }
      pa = lean_ctor_get(pa, 1);
      pb = lean_ctor_get(pb, 1);
      idx++;
    }
    if (lean_is_scalar(pa) != lean_is_scalar(pb)) {
      if (why) *why = "channel length differs";
      if (bad_ch) *bad_ch = chi;
      return 0;
    }
    ca = lean_ctor_get(ca, 1);
    cb = lean_ctor_get(cb, 1);
    chi++;
  }
  if (lean_is_scalar(ca) != lean_is_scalar(cb)) {
    if (why) *why = "channel count differs";
    return 0;
  }
  return 1;
}

/* ---- self-consistency ------------------------------------------------ */
void vinyl_self_consistency(const uint8_t *in, size_t n, SelfConsistency *sc) {
  memset(sc, 0, sizeof *sc);
  sc->reencodes = -1;
  sc->fit_ok = 1;

  lean_object *r = vinyl_decode_option(mk_ba(in, n));
  if (lean_obj_tag(r) == 0) {
    lean_dec(r);
    return;
  }
  sc->decoded = 1;
  lean_object *audio = lean_ctor_get(r, 0);
  lean_object *chs = lean_ctor_get(audio, 0);
  long bps_ll = nat_ll(lean_ctor_get(audio, 1)), sr_ll = nat_ll(lean_ctor_get(audio, 2));
  sc->bps = (int)bps_ll;
  sc->sr = (int)sr_ll;
  int bps = sc->bps;
  long long lo = 0, hi = 0;
  if (bps >= 1 && bps <= 32) {
    hi = 1LL << (bps - 1);
    lo = -hi;
  }
  unsigned long nchan = list_len(chs), num_samples = 0;
  sc->ch = (int)nchan;
  int chi = 0, first = 1;
  for (lean_object *c = chs; !lean_is_scalar(c); c = lean_ctor_get(c, 1)) {
    unsigned long plen = 0;
    int idx = 0;
    for (lean_object *s = lean_ctor_get(c, 0); !lean_is_scalar(s); s = lean_ctor_get(s, 1)) {
      lean_object *x = lean_ctor_get(s, 0);
      if (!lean_is_scalar(x)) {
        if (!sc->saw_bignum) {
          sc->saw_bignum = 1;
          sc->fit_ok = 0;
          sc->bad_ch = chi;
          sc->bad_idx = idx;
        }
      } else if (sc->fit_ok && bps >= 1 && bps <= 32) {
        long long v = lean_scalar_to_int64(x);
        if (v < lo || v >= hi) {
          sc->fit_ok = 0;
          sc->bad_val = v;
          sc->bad_ch = chi;
          sc->bad_idx = idx;
        }
      }
      plen++;
      idx++;
    }
    if (first) {
      num_samples = plen;
      first = 0;
    } else if (plen != num_samples) {
      sc->ragged = 1;
    }
    chi++;
  }
  sc->samples = num_samples;
  /* Clause 3a: the decoder just parsed a STREAMINFO; the Audio it returns must
   * carry the channel count that STREAMINFO declared. A mismatch is recombine's
   * silent truncation -- internally-incoherent output, not garbage-in tolerance. */
  sc->si_ch = streaminfo_channels(in, n);
  sc->frame_ch = flac_frame_channels(in, n);
  /* Incoherent if the returned channel count disagrees with EITHER the STREAMINFO
   * declaration OR the frames' own channel count. The frame direction is the
   * headline §3.6(a) case: when frames carry MORE channels than STREAMINFO,
   * recombine truncates to si_ch and the returned count == si_ch, so an
   * si-vs-returned check stays silent while channels are silently dropped. */
  sc->channel_incoherent = (sc->si_ch >= 1 && (int)nchan != sc->si_ch) ||
                           (sc->frame_ch >= 1 && (int)nchan != sc->frame_ch);
  sc->bad_channels = (nchan < 1 || nchan > 8);
  sc->bad_bps = (bps_ll < 1 || bps_ll > 32);
  sc->bad_rate = (sr_ll < 0 || sr_ll >= (1LL << 20));
  sc->bad_count = ((long long)num_samples >= (1LL << 36));
  sc->structural_ok =
      !(sc->bad_channels || sc->bad_bps || sc->ragged || sc->bad_rate || sc->bad_count);

  /* Cross-check: WellFormed = structural && fit, and encode returns some iff
   * WellFormed. Skip the encode on a decode bomb OR a high-depth/multichannel audio
   * whose re-encoded output would overflow bitsToByteList (guard both sample count
   * AND estimated output bytes -- see VINYL_ENCODE_BYTE_CAP). */
  long long est_out = (long long)bps * (long long)nchan * (long long)num_samples / 8;
  if (num_samples <= VINYL_ENCODE_SAMPLE_CAP && est_out <= VINYL_ENCODE_BYTE_CAP) {
    lean_inc(audio);
    lean_object *enc = vinyl_encode(audio);
    sc->reencodes = (lean_obj_tag(enc) == 1) ? 1 : 0;
    lean_dec(enc);
  } else {
    g_encode_capped++;
  }

  /* Cross-decoder lanes, gated on INPUT SIZE for throughput: vinyl_decode_reference
   * is the List-Bool reader whose skipBits is quadratic in input bytes AND is
   * NON-TAIL (it stack-overflows on large inputs -- fz_decode_modes caps it at
   * VM_REF_MAX_INPUT=8192B for the same reason), so it is bounded by its OWN cap
   * VINYL_REF_MAX_BYTES=8192 (decoupled from the raised encode caps in P0.2, which
   * must not apply here). Both decoders re-parse the ORIGINAL input; a disagreement
   * with the production decoder's decision or output is a compiler/runtime/csimp
   * defect (decodeOption_eq_reference, decodeBytes_spec + pcmBytesA_eq), not
   * garbage-in tolerance. */
  if (n <= VINYL_REF_MAX_BYTES) {
    /* REFERENCE lane: decodeOption == decodeReference on the binary. */
    lean_object *ref = vinyl_decode_reference(mk_ba(in, n));
    if (lean_obj_tag(ref) != 1) {
      sc->reference_disagreed = 1; /* production accepted, reference rejected */
    } else if (!audio_eq(audio, lean_ctor_get(ref, 0), NULL, &sc->bad_ch, &sc->bad_idx)) {
      sc->reference_disagreed = 1; /* both accepted, audio differs */
    }
    lean_dec(ref);

    /* BYTE lane (ANY depth): decodeBytes' (bytes,bps) must equal pcmBytes of the
     * Audio the production decoder just returned (decodeBytes_spec + pcmBytesA_eq).
     * Both sides are depth-parameterised: decodeBytes returns (out, si.bps) with
     * out = pcmBytesRange bps chs ... (PcmBytes.lean:778, holds at any bps), and
     * pcmBytes/pcmRowsGo serialize ⌈bps/8⌉ bytes/sample at any depth
     * (Stream.lean:178-233). The Audio carries that same si.bps, so the expected
     * bytes are pcmBytes bps chs at 8/12/16/20/24/32-bit alike -- so db_bps must
     * equal the decoded bps (`bps`), not the constant 16. decodeBytes returning
     * NONE is the legitimate fused->sample fallback (vinyl_decode_fast), NOT a
     * divergence -- the spec only constrains the SOME case, so only then compare. */
    lean_object *db = vinyl_decode_bytes(mk_ba(in, n));
    if (lean_obj_tag(db) == 1) {
      lean_object *p = lean_ctor_get(db, 0); /* ByteArray × Nat (borrowed) */
      lean_object *bytes = lean_ctor_get(p, 0);
      long db_bps = nat_ll(lean_ctor_get(p, 1));
      lean_object *bnat = lean_ctor_get(audio, 1);
      lean_inc(bnat);
      lean_inc(chs);
      lean_object *exp = vinyl_pcm_bytes(bnat, chs); /* consumes bnat + chs */
      size_t esz = lean_sarray_size(exp), dsz = lean_sarray_size(bytes);
      if (db_bps != bps || esz != dsz ||
          (esz && memcmp(lean_sarray_cptr(exp), lean_sarray_cptr(bytes), esz) != 0))
        sc->byte_disagreed = 1;
      lean_dec(exp);
    }
    lean_dec(db);
  }
  lean_dec(r);
}

/* ---- proven pair: decodeOption vs decodeReference ------------------- */
int vinyl_pair_decode(const uint8_t *in, size_t n, PairResult *r) {
  memset(r, 0, sizeof *r);
  lean_object *prod = vinyl_decode_option(mk_ba(in, n));
  lean_object *ref = vinyl_decode_reference(mk_ba(in, n));
  r->prod_some = (lean_obj_tag(prod) == 1);
  r->ref_some = (lean_obj_tag(ref) == 1);
  int ok = 1;
  if (r->prod_some != r->ref_some) {
    r->why = r->prod_some ? "production decoded but reference rejected"
                          : "reference decoded but production rejected";
    ok = 0;
  } else if (r->prod_some) {
    ok = audio_eq(lean_ctor_get(prod, 0), lean_ctor_get(ref, 0), &r->why, &r->bad_ch, &r->bad_idx);
  }
  lean_dec(prod);
  lean_dec(ref);
  return ok;
}

/* ---- shipped public entrypoint: Flac.decode + Stream.peekInfo ------- */
void vinyl_decode_peek(const uint8_t *in, size_t n, PeekProbe *p) {
  memset(p, 0, sizeof *p);
  lean_object *d = vinyl_decode(mk_ba(in, n));
  p->decode_ok = (lean_obj_tag(d) == 1); /* Except.ok */
  lean_dec(d);
  lean_object *pi = vinyl_peek_info(mk_ba(in, n));
  p->peek_some = (lean_obj_tag(pi) == 1); /* Option.some */
  lean_dec(pi);
}

/* ---- metamorphic: decode(encode(decode x)) == decode(x) ------------- */
int vinyl_metamorphic_reencode(const uint8_t *in, size_t n) {
  lean_object *a1 = vinyl_decode_option(mk_ba(in, n));
  if (lean_obj_tag(a1) == 0) {
    lean_dec(a1);
    return MM_NA;
  }
  lean_object *audio1 = lean_ctor_get(a1, 0);
  /* Skip the re-encode on a decode bomb OR a high-depth/multichannel audio whose
   * output would overflow bitsToByteList: bound sample count AND estimated output
   * bytes (bps*ch*samples/8), same guard as vinyl_self_consistency. */
  unsigned long mm_len = first_plane_len(audio1);
  long mm_bps = nat_ll(lean_ctor_get(audio1, 1));
  unsigned long mm_ch = list_len(lean_ctor_get(audio1, 0));
  long long mm_est = (long long)(mm_bps > 0 ? mm_bps : 0) * (long long)mm_ch * (long long)mm_len / 8;
  if (mm_len > VINYL_ENCODE_SAMPLE_CAP || mm_est > VINYL_ENCODE_BYTE_CAP) {
    g_encode_capped++;
    lean_dec(a1);
    return MM_SKIP;
  }
  lean_inc(audio1);
  lean_object *enc = vinyl_encode(audio1);
  if (lean_obj_tag(enc) == 0) { /* not WellFormed: relation's precondition fails */
    lean_dec(enc);
    lean_dec(a1);
    return MM_SKIP;
  }

  /* Re-encode lane (env VM_REENC_LANE). The default lane re-decodes Flac.encode's
   * bytes; the alternates route the SAME WellFormed audio through a different
   * verified encoder so the fuzzer actually executes Emit.emitFast /
   * encodePcm16Fast. audio1 is WellFormed here (encode returned some), so every
   * lane is expected to round-trip; a mismatch is the same theorem-on-the-binary
   * defect. `flacba` is the OWNED re-encoded FLAC stream the tail decodes. */
  const char *lane = getenv("VM_REENC_LANE");
  lean_object *flacba;
  if (lane && strcmp(lane, "pcm16-fast") == 0) {
    if (mm_bps != 16) { /* the byte encoder is 16-bit only */
      lean_dec(enc);
      lean_dec(a1);
      return MM_SKIP;
    }
    lean_object *bnat = lean_ctor_get(audio1, 1);
    lean_object *chs = lean_ctor_get(audio1, 0);
    lean_object *srN = lean_ctor_get(audio1, 2);
    lean_inc(bnat);
    lean_inc(chs);
    lean_inc(srN);
    lean_object *pcm = vinyl_pcm_bytes(bnat, chs); /* interleaved s16 PCM */
    lean_object *er =
        vinyl_encode_pcm16_fast(lean_usize_to_nat(4096), lean_usize_to_nat(mm_ch), srN, pcm);
    lean_dec(enc);
    if (lean_obj_tag(er) == 0) { /* encoder preconditions (sr<2^20, ...) not met */
      lean_dec(er);
      lean_dec(a1);
      return MM_SKIP;
    }
    flacba = lean_ctor_get(er, 0);
    lean_inc(flacba);
    lean_dec(er);
  } else if (lane && strcmp(lane, "emit") == 0) {
    /* EncoderCfg ⟨blockSize, chooser⟩ + variableBlocking := false, the default
     * chooser capturing the decoded audio's bps -- built exactly like vinyl_gen.c /
     * vinyl_modes.c. emitFast is total (ByteArray), so no WellFormed re-check. */
    lean_object *chooser = lean_alloc_closure((void *)vinyl_default_chooser, 2, 1);
    lean_closure_set(chooser, 0, lean_box((size_t)(mm_bps > 0 ? mm_bps : 16)));
    lean_object *cfg = lean_alloc_ctor(0, 2, 1);
    lean_ctor_set(cfg, 0, lean_usize_to_nat(4096));
    lean_ctor_set(cfg, 1, chooser);
    lean_ctor_set_uint8(cfg, sizeof(void *) * 2, 0); /* variableBlocking := false */
    lean_inc(audio1);
    flacba = vinyl_emit_fast(cfg, audio1); /* consumes cfg + audio1 */
    lean_dec(enc);
  } else {
    flacba = lean_ctor_get(enc, 0);
    lean_inc(flacba);
    lean_dec(enc);
  }

  size_t sz = lean_sarray_size(flacba);
  lean_object *ba2 = lean_alloc_sarray(1, sz, sz);
  memcpy(lean_sarray_cptr(ba2), lean_sarray_cptr(flacba), sz);
  lean_dec(flacba);
  lean_object *a2 = vinyl_decode_option(ba2);
  int verdict = (lean_obj_tag(a2) == 0)
                    ? MM_VIOLATION
                    : (audio_eq(audio1, lean_ctor_get(a2, 0), NULL, NULL, NULL) ? MM_OK
                                                                               : MM_VIOLATION);
  lean_dec(a2);
  lean_dec(a1);
  return verdict;
}
