# Findings

Reproduced real bugs in Vinyl, each labelled by status. A previously-known issue
re-reported as new adds no value, so every entry states whether it is NOVEL or a
CONFIRMATION of a known (source-reviewed) issue, with the three-way reference
behaviour and a minimized reproducer.

| dir | status | RFC clause | one line |
|---|---|---|---|
| `channel-truncation-CONFIRMED` | CONFIRMATION | RFC 9639 §9.1 | decoder returns fewer channels than STREAMINFO declares (recombine `zipWith` truncation); libFLAC rejects, Vinyl accepts→1ch |
| `samplerate-zero-CONFIRMED` | CONFIRMATION | RFC 9639 §9.1.7 | STREAMINFO sample rate 0 accepted with audio; `readStreamInfo` does not check |
| `encoder-stack-overflow-CONFIRMED` | CONFIRMATION | robustness | slow encoder (`bitsToByteList`) overflows the default 8 MB stack at ~65536 frames (~1.5 s stereo) |
| `decoder-output-contract-stereo` | CONFIRMATION (§1.1 gap) | RFC 9639 §4.2 / output-contract | stereo decorrelation undo is not wrapped to `bps`, so `decodeArrays` returns samples in `FitsSInt(bps+2)` not `FitsSInt(bps)`; libFLAC rejects, Vinyl accepts→out-of-range→two's-complement-wrapped PCM |
| `decode-capacity-underalloc` | CONFIRMATION (missed-lead #1) | capacity / P3 class | `decodeBytes` output pre-size hardcodes 2 bytes/sample; every 24/32-bit decode reallocs (short by `(⌈bps/8⌉−2)/⌈bps/8⌉`). Proof-invisible; `underalloc=109,679` in the 6h run |
| `float-lpc-coefficient-divergence` | CONFIRMATION (§1.4 / F5b) | claim-surface / quality | Float LPC search selects a different quantized coefficient vector than exact arithmetic above 2⁵³ (24/32-bit); round-trip still holds. `float_exact_divergence=517` |
| `overlong-coded-number` | CONFIRMATION (§3.7) | RFC 9639 §9.1.5 / RFC 3629 | `readUtf8`/`readConts` accept non-minimal (overlong) coded frame numbers (no minimality check); the UTF-8 overlong class. New detector `fz_overlong_utf8`, two-way regression pin |

The output-contract entry is the highest-value class the `official` campaign
tripped: the decoder has **no output contract**, confirmed on both a generated
`b+2` construction and a mutated *real* 16-bit stream. It is a tier correction
(P1 is marked **T** but the boundedness holds only at subframe depth) and P7's
mirror (`Flac.encode (decode bytes) = none` on a stream Vinyl accepted), not a
soundness break — see its `NOTE.md`. The remaining catalogue classes
(`wide_ref_split`/`_disagree` = referee-vs-referee, `a_only`/`b_only` = mutator
accept-set noise) are manufactured, not Vinyl defects.

## How these were produced

Divergences dump to `runs/<ts>/<label>/divergences/<class>/` during a campaign;
curated reproducers are promoted here with a NOTE. The `FUZZ_STRICT>=2` escalation
turns the corresponding catalogue into an `abort()` for regression-pinning a filed
witness.
