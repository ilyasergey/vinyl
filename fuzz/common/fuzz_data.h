/* fuzz_data.h -- a C99, FRONT-consuming parameter cursor (Phase 6B).
 *
 * A deliberate C port of libFuzzer's FuzzedDataProvider idea. FDP is C++ and
 * consumes from the BACK of the buffer; this rig is C and its seeds encode
 * parameters in the FRONT (see common/vinyl_gen.c: bps=data[0]%32, ch=data[1]%8,
 * bit-packed flags in data[2..3], ...). A back-consuming provider would break
 * every parameter seed and every RAW reproducer, so this cursor consumes from the
 * front, preserving seed layout.
 *
 * It still reduces MODULARLY (val % span), exactly like the hand-written
 * `data[i] % N` sites it replaces -- its wins are one implementation, uniform
 * carving, and honest exhaustion handling (a short seed yields deterministic
 * lo/0/false instead of reading past the end). It is NOT a uniform-distribution
 * generator; the fuzzer's feedback, not statistical uniformity, drives coverage.
 *
 * Header-only, no allocation, no dependencies beyond stdint/stddef/string.
 */
#ifndef FUZZ_DATA_H
#define FUZZ_DATA_H

#include <stddef.h>
#include <stdint.h>
#include <string.h>

typedef struct {
  const uint8_t *p;   /* next unconsumed byte (front cursor) */
  size_t remaining;   /* bytes left */
} FuzzData;

static inline FuzzData fuzz_data_init(const uint8_t *data, size_t size) {
  FuzzData fd = {data, data ? size : 0};
  return fd;
}

static inline size_t fuzz_remaining(const FuzzData *fd) { return fd->remaining; }

/* Consume up to `nbytes` (capped at 8) from the front, big-endian. Missing bytes
 * past exhaustion contribute 0 -- deterministic, never reads past the buffer. */
static inline uint64_t fuzz_consume_uint(FuzzData *fd, unsigned nbytes) {
  if (nbytes > 8) nbytes = 8;
  uint64_t v = 0;
  for (unsigned i = 0; i < nbytes; i++) {
    uint8_t b = 0;
    if (fd->remaining) { b = *fd->p++; fd->remaining--; }
    v = (v << 8) | b;
  }
  return v;
}

/* Uniform-ish value in [lo, hi] (inclusive), reduced modulo the span. Consumes
 * exactly as many front bytes as the span needs. hi<=lo yields lo (no consume). */
static inline uint64_t fuzz_consume_range(FuzzData *fd, uint64_t lo, uint64_t hi) {
  if (hi <= lo) return lo;
  uint64_t range = hi - lo;              /* span-1; range == UINT64_MAX => full 64-bit */
  unsigned nbytes = 0;
  for (uint64_t r = range; r; r >>= 8) nbytes++;
  uint64_t v = fuzz_consume_uint(fd, nbytes);
  uint64_t span = range + 1;             /* 0 iff range == UINT64_MAX */
  return span ? lo + (v % span) : lo + v;
}

/* [0, n): an enum/index selector. n==0 yields 0 and consumes nothing. */
static inline uint32_t fuzz_consume_enum(FuzzData *fd, uint32_t n) {
  return n ? (uint32_t)fuzz_consume_range(fd, 0, n - 1) : 0u;
}

/* One byte's low bit (consumes one byte; 0 past exhaustion). */
static inline int fuzz_consume_bool(FuzzData *fd) {
  if (!fd->remaining) return 0;
  uint8_t b = *fd->p++;
  fd->remaining--;
  return b & 1;
}

/* Copy up to `n` bytes from the front into dst, zero-filling any shortfall past
 * exhaustion. Returns the number of real (non-zero-fill) bytes copied. */
static inline size_t fuzz_consume_bytes(FuzzData *fd, uint8_t *dst, size_t n) {
  size_t take = n < fd->remaining ? n : fd->remaining;
  if (take) memcpy(dst, fd->p, take);
  if (n > take) memset(dst + take, 0, n - take);
  fd->p += take;
  fd->remaining -= take;
  return take;
}

#endif /* FUZZ_DATA_H */
