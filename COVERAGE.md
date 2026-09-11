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
| block sizes: all codes incl. explicit 8/16-bit (192, 576·2ᵏ, 256·2ᵏ, arbitrary 1–65536) | ✓ | 16–4608, explicit code |
| both frame-numbering strategies (fixed / variable block size) | ✓ | ✓ |
| sample rates: STREAMINFO up to 2²⁰−1 Hz; all frame-header codes incl. explicit 8/16-bit | ✓ | STREAMINFO code |
| bit depths 4–32; per-frame bit-depth codes (8/12/16/20/24/32 + STREAMINFO) | ✓ | STREAMINFO code, 4–32 |
| channels 1–8 independent; stereo decorrelation left/side, right/side, mid/side (b+1-bit side) | ✓ | ✓ |
| subframes: CONSTANT, VERBATIM, FIXED orders 0–4, LPC orders 1–32 (any precision 1–15, shift 0–15) | ✓ | ✓ |
| wasted bits (any count < bit depth) | ✓ | ✓ (detected) |
| residuals: 4-bit Rice, 5-bit Rice2, escaped partitions, partition orders 0–15 | ✓ | ✓ |
| CRC-8 (frame header) and CRC-16 (frame) verification | ✓ (checked, by theorem) | ✓ (emitted) |
| MD5 signature of the unencoded data | emitted; **proven = RFC 1321** (`md5_eq_rfc1321`) | emitted |
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
  every stream it accepts; the encoder's MD5 is now proven equal to
  RFC 1321, `md5_eq_rfc1321`, not merely differential-tested);
- metadata *content* (Vorbis comments, seek tables, pictures …) is
  skipped, not surfaced to the caller;
- the encoder always emits the streamable subset: it does not produce
  uncommon block sizes/rates requiring explicit frame-header codes.

The byte-level PCM16 entry points (`Flac.encodePcm16Fast` and
`Flac.encodePcm16Cfg`) check the preconditions of the rows above at run
time and return `none` rather than guessing, sharing one O(1) guard
(`Flac.Pcm16ShapeOk`, audit finding P8) that runs before anything sized
by its arguments is built: 1–8 channels, a byte count that is a whole
number of frames, and a nonzero sample rate whenever the input is
nonempty (RFC 9639 §8.2, audit finding P11). The fast path additionally
requires `16 ≤ blockSize ≤ 4608` (RFC 9639 §9.1 requires ≥ 16; the
encoder stops at 4608 so its output always clears the decoder's
decompression-bomb budget, keeping the round-trip guarantee
unconditional), sample rate below 2²⁰ and sample count below 2³⁶ (the
STREAMINFO field widths). Everything else the encoder needs —
equal-length channels, samples in range for the bit depth — is a
*theorem* about the derived audio (`Flac.Encode.audio_wellFormed`), not
a scan.

## Known deviations from RFC MUSTs

The table [`docs/spec-validation.md`](docs/spec-validation.md) calls for:
places where the verified model (`Audio.WellFormed` and the readers) is
knowingly laxer than RFC 9639's normative text, what covers the gap, and why
the model was left alone.

| RFC clause | model behavior | covered by | why the model stays lax |
|---|---|---|---|
| §8.2: sample rate MUST NOT be 0 when audio is present | *(was)* `Audio.WellFormed` admitted `sampleRate = 0`, so the sample-level encoders (`Flac.encode`, `encodeCheckedCfg`) emitted it | fixed **in the model and both `readStreamInfo` twins** (2026-09-11, audit finding P11): `0 < a.sampleRate` in `Audio.WellFormed`, a `0 < sr` decode guard, and `Pcm16ShapeOk` tightened to `0 < sampleRate` ([`docs/11-spec-adequacy.md`](docs/11-spec-adequacy.md)) | no longer a deviation — the accept-set fix landed on both sides, threaded through every capstone, IETF must-decode still 61/61 |
| §9.2.2/§5: wasted-bits count MUST leave a positive depth | *(was)* `Nat` saturation accepted `w ≥ b` on every decode path | fixed **in the model and production readers** in the P5 round ([`docs/05-saturating-arithmetic.md`](docs/05-saturating-arithmetic.md)); listed here as the deviation-table's origin story | no longer a deviation — the accept-set fix landed on both sides |

## Conformance-corpus results

On the [IETF FLAC conformance corpus](https://github.com/ietf-wg-cellar/flac-test-files)
(run via [`conformance/ietf.sh`](conformance/ietf.sh), see
[`conformance/README.md`](conformance/README.md)), the **must-decode
`subset/` set passes 61/61** files that the `flac` CLI itself can
compare against raw output (the remaining 3 are 12/20-bit files the
reference *CLI* refuses to emit as raw; Vinyl decodes them too). Of the
`uncommon/` edge set, everything comparable passes except the
deliberately headerless "file starting at frame header".
