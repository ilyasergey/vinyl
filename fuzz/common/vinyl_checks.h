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
 * The encode-based checks skip audio above VINYL_ENCODE_SAMPLE_CAP samples. This
 * WAS a stack-overflow workaround (Flac.encode's per-chunk / bitsToByteList
 * per-output-byte recursion). Those loops now carry @[csimp] tail swaps
 * (writeFramesTR/chunkChannelsTR/bitsToByteListTR/diff1TR/residualAuxTR, 2026-08),
 * and a re-baseline (tools/vinyl_encode_probe) confirms no overflow down to a
 * 128 KB stack. The cap is now a THROUGHPUT bound: a tiny-blockSize decode bomb
 * re-encodes slowly (compute, not stack), so keep a moderate ceiling. Raised
 * 8192->32768 after the re-baseline (P0.2). */
#ifndef VINYL_CHECKS_H
#define VINYL_CHECKS_H

#include <stddef.h>
#include <stdint.h>

#define VINYL_ENCODE_SAMPLE_CAP 32768
/* Also bound the ESTIMATED output bytes (bps*ch*samples/8) so a wide/multichannel
 * decode doesn't re-encode a huge buffer. 64 KB stays in the fast encode regime
 * (16k samples/ch was fast in the re-baseline, 64k was alarm-slow at bs=16) while
 * unlocking multi-frame + wide-depth re-encode assertions. Raised 16384->65536. */
#define VINYL_ENCODE_BYTE_CAP 65536

/* Input-byte cap for the decodeReference (List-Bool) reference lane. This is the
 * NON-TAIL decode model (skipBits quadratic, recurses O(input)); it overflows the
 * stack on large inputs regardless of the ENCODER fix, so it must stay small --
 * exactly like fz_proven_pairs' VM_PAIR_MAX and fz_decode_modes' VM_REF_MAX_INPUT.
 * Decoupled from VINYL_ENCODE_SAMPLE_CAP in P0.2: the encode caps were raised after
 * the encoder stack re-baseline, but this decode-model cap must NOT be. */
#define VINYL_REF_MAX_BYTES 8192

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
   * an ANY-DEPTH BYTE lane (decodeBytes' (bytes,bps) == pcmBytes of the decoded
   * Audio, decodeBytes_spec + pcmBytesA_eq -- the bps==16 gate was removed in P1.1,
   * so 8/12/20/24/32-bit pcmBytes serialization is now checked). Either set on an
   * accept-decision or output mismatch -- a compiler/runtime/csimp defect. */
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
