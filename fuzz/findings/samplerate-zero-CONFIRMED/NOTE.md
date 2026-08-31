# Sample rate 0 accepted with audio (RFC 9639 §9.1.7 MUST NOT)

**Status: CONFIRMATION of a known issue — NOT claimed as novel.**
This behaviour was already identified by source review: the per-frame sample rate
is never compared, and `readStreamInfo` does not check for a zero rate. This entry
records a dynamic reproduction with a minimized stream and the exact decode
behaviour.

## What Vinyl does

`Flac.Decode.readStreamInfo` does not reject a STREAMINFO whose sample rate is 0.
Vinyl accepts such a stream and decodes its audio with a success result, so the
decoded stream reports a sample rate of 0 — RFC 9639 §9.1.7 says the sample rate
MUST NOT be 0 when audio is present.

Detector: `fz_streaminfo_contradict` (variant c) reported **sr0_with_audio =
940/940** — i.e. EVERY base stream, once its STREAMINFO sample rate is rewritten
to 0, is still decoded to audio by Vinyl. `fz_self_consistent`'s `bad_rate` check
(`sr >= 2^20`) does not catch `sr == 0`, so this is the uniquely-uncaught
sample-rate sub-case among the existing targets.

## Reproducer

`repro.flac` (61 bytes): a valid 16-bit mono stream with STREAMINFO sample rate
rewritten to 0 (STREAMINFO carries no CRC, so no repair is needed).
`sha256: 3b9c7f4a75e3e03a7c527597946c096bd71fa1866e8961d4e66605ebc382d91b`

```sh
V=.lake/build/bin/vinyl
metaflac --show-sample-rate repro.flac    # -> 0
$V --decode repro.flac /tmp/out.raw       # -> "decoded 512 samples x 1 channels", exit 0
```

## Reference behaviour

libFLAC's `flac -t` ALSO accepts this stream (exit 0), so this is a **conformance**
finding, not an interop divergence: both decoders tolerate a forbidden value. The
point is specific to Vinyl's claim — a formally-verified, RFC-conformant decoder
should enforce the §9.1.7 MUST, and its own `Info`/`Audio` contract offers no
guarantee that a decoded stream carries a valid (non-zero) sample rate.

## Category

Output contract / conformance: reject `sampleRate == 0` in `readStreamInfo` when
frames follow (or define the decoded-`Audio` invariant `sampleRate ≠ 0`). Fix
class, not instance: the same missing check underlies the frame sample-rate-code-0
variant.
