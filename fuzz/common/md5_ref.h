/* md5_ref.h -- a standalone RFC 1321 MD5, the independent reference for Vinyl's
 * hand-written Flac.Md5.md5 (fz_md5) and for content-real STREAMINFO digests in
 * the generator. Deliberately NOT libFLAC's internal MD5: an independent second
 * implementation is the whole point of a differential. */
#ifndef MD5_REF_H
#define MD5_REF_H

#include <stddef.h>
#include <stdint.h>

void md5_ref(const uint8_t *msg, size_t len, uint8_t out[16]);

#endif /* MD5_REF_H */
