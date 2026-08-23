# RFC 9639 coverage

What of [RFC 9639](references/rfc9639.txt) Vinyl implements: everything
needed to *decode the "streamable subset"* of FLAC and to *encode within
it*. Decode support always comes with the production/reference
equivalence proof; the round-trip theorems cover every encode feature
listed here.

## Supported

(decode, with the equivalence proof; encode where noted)

| feature | decode | encode |
|---|---|---|
| `fLaC` marker + STREAMINFO; all other metadata blocks (padding, application, seektable, Vorbis comment, cuesheet, picture, …) | ✓ (parsed / skipped) | STREAMINFO only |
| block sizes: all codes incl. explicit 8/16-bit (192, 576·2ᵏ, 256·2ᵏ, arbitrary 1–65536) | ✓ | 16–65535, explicit code |
| both frame-numbering strategies (fixed / variable block size) | ✓ | ✓ |
| sample rates: STREAMINFO up to 2²⁰−1 Hz; all frame-header codes incl. explicit 8/16-bit | ✓ | STREAMINFO code |
| bit depths 1–32; per-frame bit-depth codes (8/12/16/20/24/32 + STREAMINFO) | ✓ | STREAMINFO code, 1–32 |
| channels 1–8 independent; stereo decorrelation left/side, right/side, mid/side (b+1-bit side) | ✓ | ✓ |
| subframes: CONSTANT, VERBATIM, FIXED orders 0–4, LPC orders 1–32 (any precision 1–15, shift 0–15) | ✓ | ✓ |
| wasted bits (any count < bit depth) | ✓ | ✓ (detected) |
| residuals: 4-bit Rice, 5-bit Rice2, escaped partitions, partition orders 0–15 | ✓ | ✓ |
| CRC-8 (frame header) and CRC-16 (frame) verification | ✓ (checked, by theorem) | ✓ (emitted) |
| MD5 signature of the unencoded data | emitted by encoder | emitted |
| coded frame numbers (extended UTF-8, up to 36 bits) | ✓ | ✓ |

## Not supported

(decode rejects with an error rather than guessing)

- streams that do not begin with `fLaC` + STREAMINFO — e.g. files
  starting mid-stream at a frame header, or with leading garbage/ID3
  tags (RFC 9639 makes STREAMINFO mandatory; resynchronization is a
  player feature, not part of the format);
- reserved codes anywhere (block-size code 0, sample-rate code 15,
  bit-depth code 3, channel codes 11–15, reserved header bits ≠ 0) —
  rejected, as the RFC requires;
- MD5 *verification* on decode (the decoder is exact by theorem on
  every stream it accepts; MD5 is validated in differential tests);
- metadata *content* (Vorbis comments, seek tables, pictures …) is
  skipped, not surfaced to the caller;
- the encoder always emits the streamable subset: it does not produce
  uncommon block sizes/rates requiring explicit frame-header codes.

## Conformance-corpus results

On the [IETF FLAC conformance corpus](https://github.com/ietf-wg-cellar/flac-test-files)
(run via [`conformance/ietf.sh`](conformance/ietf.sh), see
[`conformance/README.md`](conformance/README.md)), the **must-decode
`subset/` set passes 61/61** files that the `flac` CLI itself can
compare against raw output (the remaining 3 are 12/20-bit files the
reference *CLI* refuses to emit as raw; Vinyl decodes them too). Of the
`uncommon/` edge set, everything comparable passes except the
deliberately headerless "file starting at frame header".
