# Decoder has no output contract: stereo reconstruction escapes `FitsSInt(bps)`

**Status: FIXED (2026-08-30) — patch applied and verified.** The four stereo undo
functions (`Stereo.decodeLS/RS/MSL/MSR` and the `…A` array forms) now take a depth
parameter and wrap their output with `Bits.wrapSInt b`, in both the production
Array path and the reference List path; the round-trip and `decodeOption ==
decodeReference` proofs go through unchanged (the wrap is identity on the encoder
image). `lake build` / `flactest` (155) / `scripts/check.sh` all green, no
sorry/axiom. Post-fix the mutated-16-bit witness decodes to `-9124` (in
`FitsSInt(16)`, was `56412`) and `fz_self_consistent` reports `unfit=0` (was
`unfit=1`) — the decoder now honors its output contract. History below.

**Original status: CONFIRMATION of a self-documented gap — NOT a soundness break,
NOT a crash.** The Vinyl authors already flagged the end-to-end statement as future
work: P1's note records that "every sample array `decodeArrays` returns has all
elements `FitsSInt (bps + 2)`" is unproven and that "all local pieces now exist",
and `common/vinyl_checks.h` documents out-of-range decoded samples as
"garbage-in tolerated (Bits.lean), measured not aborted." This entry records the
*dynamic* reproduction across two independent input provenances, the exact
overflow arithmetic, and the source-level mechanism, so the gap can be judged
from evidence rather than intuition. Its value is the **tier correction** and the
**codomain gap** below, not a novelty claim.

## What Vinyl does

`Flac.Decode.decodeOption` / `decodeArrays` **accept** a stream and return an
`Audio` whose samples fall **outside `FitsSInt(bps)`** — the declared bit depth
cannot hold them. libFLAC rejects such streams; ffmpeg accepts and container-wraps
to the depth; Vinyl accepts and returns the un-wrapped value, and `--decode` then
serializes it through `Stream.pcmBytes` / `pcmBytesRange`, which wraps in two's
complement (`x % 2^bps`) — **silent incorrect PCM** where a conformant decoder
errors.

## Mechanism (source-confirmed)

P1's fix wraps every reconstructed sample to the bit depth **inside the predictor
recurrence** — `Fixed.restoreA` (`Native/Fixed.lean:46,66`, `res.map (Bits.wrapSInt b)`)
and `Lpc.restoreA` (`Native/Lpc.lean:60,225`, `Bits.wrapSInt b (...)`). Stereo
decorrelation undo runs **after** that and applies **no wrap** — `Native/Stereo.lean`
`decodeLSA/decodeRSA/decodeMSLA/decodeMSRA` are plain `Array.zipWith` of `a - v`,
`b + v`, `sar (2*m + parity ± s) 1` with no `wrapSInt`. `Native/Decode.lean:440-454`
routes production stereo frames through exactly those un-wrapped functions.

The side channel is stored at `b+1` bits, the other at `b`. Left/side decode is
`R = L - S` with `L ∈ [-2^(b-1), 2^(b-1))` and `S ∈ [-2^b, 2^b)`, so
`R ∈ (-1.5·2^b, 1.5·2^b)` — up to `b+2` bits. The boundedness invariant holds at
**subframe depth** but not **end to end**, because the fix was placed where the
bug was (the predictor) rather than where the invariant must hold (the decoder's
output).

## Reproducers

### `repro_gen_bps19.flac` — 59 B, the exact §1.1 construction
`sha256: 6646f2723d1079aac967bd430c5bf05a0f3575f61aa4f6248cd7aa36d575d6f5`
Two CONSTANT subframes in left/side mode, `bps=19 ch=2 sr=16000`, produced by
`Stream.Unchecked.encode` with the hostile-stereo chooser (`fz_gen_roundtrip`).

| decoder | verdict |
|---|---|
| **Vinyl** `decodeArrays` | ACCEPT — `channel 1 index 0 = -786431` (≈ `-1.5·2^19`, needs `b+2 = 21` bits) |
| **libFLAC** 1.4.2 | REJECT (bps 19 not representable / stream invalid) |
| **ffmpeg** | ACCEPT — `-262143` (container-wrapped to 19 bits: `-786431 ≡ -262143 mod 2^19`) |

`fz_self_consistent` on this file reports `unfit=1` — the decoded audio is **not
`Audio.WellFormed`**.

### `repro_mutated_bps16.flac` — 267 B, a *real* 16-bit stereo stream (not generated)
`sha256: 2afe88d668c66179606ae271d860b3566854ab9a959fe29bad0c92d321dab78f`
A committed 16-bit corpus stream mutated by the CRC-aware mutator (`fz_samples_diff`),
CRC-repaired — so libFLAC's rejection is **not** a checksum artifact. `bps=16 ch=2 sr=44100`.

| decoder | verdict |
|---|---|
| **Vinyl** `decodeArrays` | ACCEPT — `channel 1 index 4 = 56412` (needs `b+1 = 17` bits) |
| **libFLAC** 1.4.2 | REJECT — `ERROR during decoding` |
| **ffmpeg** | ACCEPT — `32767` (container-wrapped / clamped to 16 bits) |

This second witness shows the gap is not a property of the unchecked encoder: an
arbitrary byte stream reaches the same place.

## Why it matters (the judgment half)

1. **A new taxonomy row: the decoder has no output contract.** The project's whole
   discipline — `WellFormed`, decoder guards, `api-contracts.md` — is about
   *inputs*. There is no theorem `decode bytes = .ok a → a.WellFormed`, and nothing
   bounds `decodeArrays`' output end-to-end.
2. **P7's mirror image.** After P7 made `Flac.encode` the checked public entry
   point, `Flac.encode (decodeOption bytes) = none` on a stream Vinyl itself
   accepted (the decoded `Audio` is not `WellFormed`, and `encode` returns `some`
   iff `WellFormed`). The decoder's codomain is not the encoder's domain. Nobody has
   stated this.
3. **A tier correction.** `docs/README.md` marks P1 **T** (secured by
   kernel-checked theorems). The value-boundedness property is secured *at the
   subframe*, not end to end; the end-to-end statement is on P1's own future-work
   list. The row overstates its coverage.
4. **User-visible effect.** libFLAC enforces this contract (rejects); Vinyl does
   not, and `--decode` emits two's-complement-wrapped PCM (`56412 → -9124` at 16-bit)
   with a success result — silent corruption exactly where a conformant decoder errors.

## The patch this points to (engagement §1.6)

The missing theorem — every element of every array `decodeArrays` returns is
`FitsSInt (bps + 2)` for arbitrary bytes — is what turns this from a hole into a
hole with its own fix. Either wrap the stereo undo to `bps` (as the predictor is
wrapped), making the output `FitsSInt bps` and re-encodable; or state and prove the
`bps + 2` bound and make it the decoder's declared output contract. P1's note says
the local pieces exist.

## Reproduce

```
FUZZ_STRICT=2 build/bin/fz_samples_diff.fuzz findings/decoder-output-contract-stereo/repro_mutated_bps16.flac
FUZZ_STRICT=1 build/bin/fz_self_consistent.fuzz findings/decoder-output-contract-stereo/repro_gen_bps19.flac
```
The first aborts with the `[WIDE DIVERGENCE] output-contract` report; the second
counts `unfit=1`.
