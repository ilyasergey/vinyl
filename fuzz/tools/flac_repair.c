/* flac_repair -- stdin -> stdout wrapper around flac_rescan_repair.
 *
 * Reads a whole FLAC stream from stdin, runs the structure-exact in-place CRC
 * repair (common/flac_struct.c: walk each frame the way the decoder does, fix
 * CRC-8, zero byte-alignment padding, write CRC-16 at the true frame end), and
 * writes the repaired bytes to stdout. Length preserving. This is the single
 * repair engine the Python drivers (tools/shrink.py, conformance/mustreject.py)
 * shell out to instead of re-porting the bit/CRC layer. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "flac_struct.h"

int main(void) {
  size_t cap = 1 << 16, n = 0;
  uint8_t *buf = malloc(cap);
  if (!buf)
    return 1;
  for (;;) {
    if (n == cap) {
      cap *= 2;
      uint8_t *nb = realloc(buf, cap);
      if (!nb) {
        free(buf);
        return 1;
      }
      buf = nb;
    }
    size_t got = fread(buf + n, 1, cap - n, stdin);
    n += got;
    if (got == 0)
      break;
  }
  flac_rescan_repair(buf, n);
  if (n && fwrite(buf, 1, n, stdout) != n) {
    free(buf);
    return 1;
  }
  free(buf);
  return 0;
}
