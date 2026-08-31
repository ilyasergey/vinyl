/* ffi_util.h — the small helpers that were copy-pasted across the wrappers:
 * one geometric byte-buffer reallocator, one "make a Lean ByteArray", one
 * "unbox a small Nat". Header-only static inlines (no new object), so each
 * translation unit gets its own copy and there is a single definition to fix. */
#ifndef FFI_UTIL_H
#define FFI_UTIL_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Geometric (x2) growth of a byte buffer, initial 64 KiB, _exit(1) on OOM so the
 * fuzzing engine records it rather than crashing on a NULL store. Returns *p.
 * Replaces buf_ensure / vm_ensure / out_ensure / dup_base's grow / ... */
static inline uint8_t *fuzz_grow(uint8_t **p, size_t *cap, size_t need) {
  if (need > *cap) {
    size_t c = *cap ? *cap : (1u << 16);
    while (c < need)
      c *= 2;
    uint8_t *q = realloc(*p, c);
    if (!q)
      _exit(1);
    *p = q;
    *cap = c;
  }
  return *p;
}

/* A Lean ByteArray (sarray, elem size 1) holding a copy of in[0..n). */
static inline lean_object *mk_ba(const uint8_t *in, size_t n) {
  lean_object *ba = lean_alloc_sarray(1, n, n);
  if (n)
    memcpy(lean_sarray_cptr(ba), in, n);
  return ba;
}

/* A small Nat field -> int; -1 if it is a bignum (does not fit a scalar). The
 * STREAMINFO-derived fields we read (bps/ch/sampleRate) are always scalars. */
static inline int nat_small(lean_object *n) {
  return lean_is_scalar(n) ? (int)lean_unbox(n) : -1;
}

#endif /* FFI_UTIL_H */
