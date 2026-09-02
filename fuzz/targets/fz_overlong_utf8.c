/* fz_overlong_utf8 -- the decoder REJECTS non-minimal (overlong) coded numbers.
 *
 * Regression pin for the 2026-08-31 fix. Frame/sample numbers are coded numbers (a
 * UTF-8-like scheme). `Flac.Decode.readUtf8` dispatches on the leading byte's class
 * and `readContsMin` now gates the decoded value against `Utf8Num.contsFloor` (the
 * RFC 3629 minimality floor), so an overlong form -- V encoded with more
 * continuations than its minimal one -- is rejected. Previously readConts had no
 * minimality check, so 0 was accepted as `00`, `C0 80`, `E0 80 80`, ... up to the
 * 7-byte form (the classic UTF-8 overlong class, a known-bad security precedent).
 * This target pins the fix in BOTH directions: minimal forms still decode exactly,
 * overlong forms are now rejected, and an overlong ACCEPT is a hard regression.
 *
 * This is a CONSTRUCTIVE unit-differential, not a stream mutator: from the input we
 * derive a value V (<2^36) and a continuation count k (0..6), build the k-continuation
 * encoding of V, and drive `readUtf8` on exactly those bytes. The scheme's payload
 * widths (bits carried by lead + k*6 continuations) are:
 *     k =   0    1    2    3    4    5    6
 *   W(k) =   7   11   16   21   26   31   36
 * so minimal_k(V) is the smallest k with V < 2^W(k); k > minimal_k(V) is overlong.
 *
 *   ABORT (regressions -- all must stay 0):
 *     - reject_bug: the MINIMAL (k == minimal_k) encoding was rejected, or
 *     - value_bug: an accepted minimal form decoded to the WRONG value/length, or
 *     - overlong_accepted: a non-minimal (k > minimal_k) encoding was ACCEPTED --
 *       the minimality guard regressed.
 *   COUNT (the fix working):
 *     - minimal_accepted: minimal forms decode exactly (the control), and
 *     - overlong_rejected: non-minimal forms are rejected (the guard).
 *
 * Second lane -- the WRITER, a proven pair on the binary. `Flac.Utf8Num.write` (the
 * List-Bool coded-number writer behind the checked `Flac.encode` frame headers) and
 * `Flac.Utf8Num.read` are kernel-proven inverse: `read (write n ++ rest) = some (n, rest)`
 * for n < 2^36 (Spec/Utf8Num.lean `read_write`). We run both sides on V and require
 * `some (V, [])` AND that `write` picked the MINIMAL width (8*(minimal_k+1) bits -- the
 * writer's own if-chain, checked against this file's independent W(k) model). A
 * disagreement is a compiler/runtime defect (the theorem is machine-checked), never a
 * spec gap. This is the only way to execute write's 4/5/6-byte arms: they need a frame
 * index >= 2^16, i.e. a >1M-sample encode, far beyond any fuzz input -- no stream-level
 * target can reach them, a direct pair can.
 *     - rt_bug: read(write V) != some (V, []) or a non-minimal width -- MUST stay 0.
 * Input: RAW (plain mutator). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#include "../common/ffi_util.h"
#include "../common/fuzz_target.h"
#include "../common/oracle.h"

/* readUtf8 : BitReader -> Option (Nat x BitReader). BitReader = <ByteArray, pos:Nat>. */
extern lean_object *lp_vinyl_Flac_Decode_readUtf8(lean_object *br);
/* The List-Bool pair (stable @[export] names, FuzzGen.lean): write : Nat -> BitStream,
 * read : BitStream -> Option (Nat x BitStream). Each consumes its argument. */
extern lean_object *vinyl_utf8_write(lean_object *n);
extern lean_object *vinyl_utf8_read(lean_object *bits);

static unsigned long g_execs, g_built, g_minimal, g_overlong, g_overlong_rejected,
    g_reject_bug, g_value_bug, g_rt_ok, g_rt_bug;

static void report(FILE *o) {
  fprintf(o,
          "[overlong] execs=%lu built=%lu | minimal_accepted=%lu overlong_rejected=%lu "
          "(RFC 3629 minimality guard) | overlong_accepted=%lu reject_bug=%lu value_bug=%lu "
          "(all MUST be 0) | write/read pair: rt_ok=%lu rt_bug=%lu (MUST be 0)\n",
          g_execs, g_built, g_minimal, g_overlong_rejected, g_overlong, g_reject_bug, g_value_bug,
          g_rt_ok, g_rt_bug);
}

static unsigned long list_len(lean_object *l) { /* borrows */
  unsigned long k = 0;
  for (; !lean_is_scalar(l); l = lean_ctor_get(l, 1))
    k++;
  return k;
}

/* Proven pair on the binary: Utf8Num.read (Utf8Num.write v) must be some (v, []) and
 * write must have chosen the minimal width. Returns 1 on agreement. */
static int utf8_roundtrip(uint64_t v, unsigned kmin, unsigned long *nbits, uint64_t *got, int *rest_nil) {
  lean_object *bits = vinyl_utf8_write(lean_usize_to_nat((size_t)v)); /* owned List Bool */
  *nbits = list_len(bits);
  lean_object *r = vinyl_utf8_read(bits); /* consumes bits */
  *got = UINT64_MAX;
  *rest_nil = 0;
  if (lean_obj_tag(r) == 1) {
    lean_object *pair = lean_ctor_get(r, 0);
    lean_object *n2 = lean_ctor_get(pair, 0);
    *got = lean_is_scalar(n2) ? (uint64_t)lean_unbox(n2) : UINT64_MAX;
    *rest_nil = lean_is_scalar(lean_ctor_get(pair, 1)); /* [] is the scalar nil */
  }
  lean_dec(r);
  return *got == v && *rest_nil && *nbits == 8ul * (kmin + 1ul);
}

/* total payload width for a k-continuation encoding; W(k)=7 at k=0 then 11,16,21,... */
static const unsigned WBITS[7] = {7, 11, 16, 21, 26, 31, 36};
/* leading-byte class markers, indexed by continuation count k. */
static const unsigned LEAD[7] = {0x00, 0xC0, 0xE0, 0xF0, 0xF8, 0xFC, 0xFE};

static unsigned minimal_k(uint64_t v) {
  for (unsigned k = 0; k < 7; k++)
    if (v < (1ULL << WBITS[k]))
      return k;
  return 6;
}

/* Emit the k-continuation encoding of v into out[0..k]; returns byte count (k+1).
 * lead carries L(k)=W(k)-6k high bits; each continuation carries the next 6 bits. */
static size_t encode_k(uint64_t v, unsigned k, uint8_t *out) {
  unsigned lead_bits = WBITS[k] - 6u * k; /* 7,5,4,3,2,1,0 */
  uint64_t lead = lead_bits ? (v >> (6u * k)) & ((1ULL << lead_bits) - 1) : 0;
  out[0] = (uint8_t)(LEAD[k] | lead);
  for (unsigned i = 0; i < k; i++) {
    unsigned shift = 6u * (k - 1u - i);
    out[1 + i] = (uint8_t)(0x80u | ((v >> shift) & 0x3Fu));
  }
  return (size_t)k + 1;
}

FUZZ_TARGET(.name = "fz_overlong_utf8",
            .summary = "readUtf8 rejects non-minimal (overlong) coded frame numbers (RFC 3629 guard, regression pin)",
            .input_kind = FUZZ_INPUT_RAW, .default_mutator = FUZZ_MUT_PLAIN, .needs_vinyl = 1,
            .report = report)

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  g_execs++;
  if (size < 6)
    return 0; /* need 5 value bytes + 1 selector */

  /* value V in [0, 2^36) and a continuation count k in [0,6] from the input. */
  uint64_t v = 0;
  for (int i = 0; i < 5; i++)
    v = (v << 8) | data[i];
  v &= (1ULL << 36) - 1;
  unsigned k = data[5] % 7u;
  unsigned kmin = minimal_k(v);

  /* Lane 2 (every exec, independent of k): the writer, as a proven pair (Spec/Utf8Num.lean read_write on the binary). */
  unsigned long rt_bits;
  uint64_t rt_got;
  int rt_rest_nil;
  if (utf8_roundtrip(v, kmin, &rt_bits, &rt_got, &rt_rest_nil)) {
    g_rt_ok++;
  } else {
    g_rt_bug++;
    fprintf(stderr,
            "\n[UTF8 PROVEN-PAIR DIVERGENCE -- THEOREM VIOLATION ON THE BINARY]\n"
            "  Utf8Num.read (Utf8Num.write %llu): got value=%llu rest_nil=%d bits=%lu (minimal width %u bits)\n"
            "  contradicts Flac.Utf8Num.read_write (n < 2^36): a compiler/runtime defect, NOT a spec gap\n",
            (unsigned long long)v, (unsigned long long)rt_got, rt_rest_nil, rt_bits, 8u * (kmin + 1u));
    oracle_dump_write("utf8_roundtrip_bug", data, size);
    FUZZ_ABORT();
  }

  if (k < kmin)
    k = kmin; /* cannot represent V in fewer than kmin continuations */

  uint8_t seq[8];
  size_t seqlen = encode_k(v, k, seq);
  g_built++;

  lean_object *br = lean_alloc_ctor(0, 2, 0); /* BitReader <data, pos=0> */
  lean_ctor_set(br, 0, mk_ba(seq, seqlen));
  lean_ctor_set(br, 1, lean_box(0)); /* pos = 0 */
  lean_object *r = lp_vinyl_Flac_Decode_readUtf8(br);

  if (lean_obj_tag(r) == 0) { /* none: readUtf8 rejected the constructed sequence */
    lean_dec(r);
    if (k > kmin) {
      /* An overlong (non-minimal) form correctly rejected -- the RFC 3629
       * minimality guard (Native/Utf8Num.contsFloor, the 2026-08-31 fix). This is
       * the intended behaviour: count it, do not abort. */
      g_overlong_rejected++;
      fuzz_tick();
      return 0;
    }
    /* The MINIMAL encoding was rejected -- a real defect (the guard must never
     * reject a well-formed minimal coded number). */
    g_reject_bug++;
    fprintf(stderr,
            "\n[readUtf8 BUG] rejected the MINIMAL %zu-byte coded number for value %llu (k=%u)\n",
            seqlen, (unsigned long long)v, k);
    oracle_dump_write("overlong_reject_bug", data, size);
    FUZZ_ABORT();
  }

  lean_object *pair = lean_ctor_get(r, 0); /* Nat x BitReader */
  lean_object *vo = lean_ctor_get(pair, 0);
  lean_object *br2 = lean_ctor_get(pair, 1);
  uint64_t got = lean_is_scalar(vo) ? (uint64_t)lean_unbox(vo) : UINT64_MAX;
  lean_object *poso = lean_ctor_get(br2, 1);
  size_t consumed = lean_is_scalar(poso) ? (size_t)lean_unbox(poso) : SIZE_MAX;
  lean_dec(r);

  if (got != v || consumed != 8u * seqlen) {
    g_value_bug++;
    fprintf(stderr,
            "\n[readUtf8 BUG] coded number mis-decoded: built value=%llu (%zu bytes) but readUtf8\n"
            "  returned value=%llu consumed=%zu bits (expected %zu)\n",
            (unsigned long long)v, seqlen, (unsigned long long)got, consumed, 8u * seqlen);
    oracle_dump_write("overlong_value_bug", data, size);
    FUZZ_ABORT();
  }

  if (k > kmin) {
    /* readUtf8 accepted a non-minimal encoding. Post-fix (Utf8Num.contsFloor) this
     * MUST NOT happen -- an overlong accept is now a REGRESSION of the minimality
     * guard, not a catalogued behaviour. Abort so the campaign surfaces it (the
     * two-way regression pin: overlong_rejected should climb, overlong_accepted
     * stay 0). */
    g_overlong++;
    oracle_dump_write("overlong_accepted", data, size);
    fprintf(stderr,
            "\n[OVERLONG CODED NUMBER ACCEPTED -- REGRESSION] readUtf8 decoded value %llu from a\n"
            "  %zu-byte (k=%u continuation) encoding; the minimal form needs only k=%u (%u byte(s)).\n"
            "  The RFC 3629 minimality guard (Native/Utf8Num.contsFloor) should have rejected it.\n",
            (unsigned long long)v, seqlen, k, kmin, kmin + 1u);
    FUZZ_ABORT();
  } else {
    g_minimal++; /* the minimal encoding -- the control that must keep passing */
  }
  fuzz_tick();
  return 0;
}
