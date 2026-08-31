/* vinyl_checks.h -- the referee-free, any-depth checks on Vinyl's own decoder,
 * over decodeOption/decodeReference/encode. All three share one Audio deep-equal
 * and one ByteArray builder (see vinyl_checks.c).
 *
 *  - self-consistency: the PRODUCTION decoder's output must be structurally
 *    valid (rectangular planes, channel/bps/rate bounds); out-of-range samples
 *    are garbage-in tolerated (Bits.lean), measured not aborted.
 *  - proven pair: decodeOption == decodeReference on the binary
 *    (Decode.decodeOption_eq_reference) -- a divergence is a compiler/runtime/
 *    csimp defect, not a spec gap.
 *  - metamorphic: decode(encode(decode x)) == decode(x) (Flac.decode_encode).
 *
 * The encode-based checks skip audio above VINYL_ENCODE_SAMPLE_CAP samples:
 * Flac.encode's per-chunk recursion overflows the Lean stack on a decode bomb
 * (a P3/P4-shape DoS on garbage-in, not the property under test). */
#ifndef VINYL_CHECKS_H
#define VINYL_CHECKS_H

#include <stddef.h>
#include <stdint.h>

#define VINYL_ENCODE_SAMPLE_CAP 8192
/* The re-encode stack cost is bitsToByteList's per-OUTPUT-byte recursion, so the
 * sample cap alone is insufficient: a decoded 8192-sample audio at 32-bit x 8ch is
 * ~256 KB of output and overflows (findings/encoder-stack-overflow-CONFIRMED). Also
 * bound the ESTIMATED output bytes (bps*ch*samples/8). 16 KB is verified
 * overflow-free and re-encodes 16-bit stereo up to 4096 samples. */
#define VINYL_ENCODE_BYTE_CAP 16384

/* ---- self-consistency ---- */
typedef struct {
  int decoded, bps, ch, sr;
  unsigned long samples;
  int bad_channels, bad_bps, ragged, bad_rate, bad_count, structural_ok;
  int fit_ok, saw_bignum;
  long long bad_val;
  int bad_ch, bad_idx;
  int reencodes; /* -1 decode failed / not attempted; 1 encode some; 0 none */
  /* Clause 3a (output-contract): STREAMINFO's declared channel count and whether
   * the decoded Audio's channel count disagrees with it. recombine's
   * `zipWith (·++·)` truncates, so a stream whose frames carry more channels than
   * STREAMINFO returns FEWER channels than declared -- success with silent data
   * loss. si_ch = -1 when the header did not re-parse. frame_ch is the channel
   * count the first frame header declares (0 if none) -- the frames-vs-returned
   * direction that catches extra channels dropped by recombine truncation. */
  int si_ch, frame_ch, channel_incoherent;
  /* Cross-decoder lanes (guarded by VINYL_ENCODE_SAMPLE_CAP for throughput): a
   * REFERENCE lane (decodeOption == decodeReference, decodeOption_eq_reference) and
   * a 16-bit-only BYTE lane (decodeBytes' (bytes,bps) == pcmBytes of the decoded
   * Audio, decodeBytes_spec + pcmBytesA_eq). Either set on an accept-decision or
   * output mismatch -- a compiler/runtime/csimp defect, not garbage-in tolerance. */
  int reference_disagreed, byte_disagreed;
} SelfConsistency;

void vinyl_self_consistency(const uint8_t *in, size_t n, SelfConsistency *sc);

/* ---- proven pair: decodeOption vs decodeReference ---- */
typedef struct {
  int prod_some, ref_some;
  const char *why; /* NULL if the pair agreed */
  int bad_ch, bad_idx;
} PairResult;

int vinyl_pair_decode(const uint8_t *in, size_t n, PairResult *r); /* 1 = agree */

/* How many times an encode-based check skipped the re-encode because the decoded
 * audio exceeded VINYL_ENCODE_SAMPLE_CAP. That cap works around Flac.encode's
 * per-chunk non-tail recursion overflowing the Lean stack on a decode bomb (D7,
 * feeds P8 fz_stack_encode). A high skip rate means the encode-side assertions
 * ran on far fewer inputs than the exec count suggests; surface it, do not hide
 * it. */
unsigned long vinyl_encode_capped_count(void);

/* ---- metamorphic: re-encode idempotence ---- */
enum { MM_NA = 0, MM_SKIP, MM_OK, MM_VIOLATION };
int vinyl_metamorphic_reencode(const uint8_t *in, size_t n);

#endif /* VINYL_CHECKS_H */
