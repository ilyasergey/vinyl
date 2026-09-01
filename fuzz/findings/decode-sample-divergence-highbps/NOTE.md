# Decoder sample divergence on bps=31 streams (Vinyl vs libFLAC+ffmpeg consensus)

**Status: TRIAGED 2026-08-31 — RESOLVED as two accept-set differences on invalid/malformed
input, NOT Vinyl bugs. 215B: malformed (frame/STREAMINFO sample-rate contradiction); the
wide libFLAC referee was fixed to reject it like the CLI. 561B: root-caused to the
coded-depth wrap in `Lpc.restoreA` on an out-of-coded-range reconstruction — RFC 9639 §5
leaves this unspecified; no codec fix. Details per case below.**

## What was observed

`fz_samples_diff` (the any-depth 3-way sample differential) aborted on two distinct
CRC-valid inputs. In both, Vinyl decodes to **different PCM samples than libFLAC and
ffmpeg, which agree with each other**. Two independent decoders (separate codebases)
forming a consensus that Vinyl contradicts is the rig's highest-confidence signal —
`wide_diff.c` aborts on it unconditionally (not gated by `FUZZ_STRICT`).

Both witnesses have **STREAMINFO bit depth 31, 2 channels**.

| repro | Vinyl | libFLAC | ffmpeg | divergence |
|---|---|---|---|---|
| `repro-561B.flac` | rc=ok bps=31 ch=2 sr=44100 n=48 | sr=44100 | sr=44100 | ch0[43]: vinyl `214977311` vs consensus `206588703` (Δ = exactly 2^23 = 8388608) |
| `repro-min-215B.flac` | rc=ok bps=31 ch=2 **sr=44100** n=16 | **sr=88200** | **sr=88200** | ch0[10]: vinyl `-889622280` vs consensus `184119544` |

The 215-byte case is the more diagnostic one: Vinyl reads the frame **sample rate**
as 44100 where both references read 88200, and the decoded audio diverges wildly —
i.e. this is a **frame-header parse / high-bit-depth reconstruction** divergence, not
a mere metadata-label difference. The 561-byte case differs by exactly 2^23, which is
suspiciously bit-precise (a dropped/added bit or a shift/sign error in the bps=31 path).

The common factor is bps=31 (an unusual, high, odd bit depth). This strongly suggests
a Vinyl bug specific to high/odd bit depths, though on these adversarial CRC-mutated
streams "correct" must still be confirmed against RFC 9639.

## Reproduce

```sh
cd fuzz
build/bin/fz_samples_diff.fuzz findings/decode-sample-divergence-highbps/repro-min-215B.flac
build/bin/fz_samples_diff.fuzz findings/decode-sample-divergence-highbps/repro-561B.flac
```

After the `wide_diff.c` sample-rate-contradiction fix (below), the two behave differently:
`repro-561B.flac` still prints `[WIDE DIVERGENCE] ... Vinyl vs a libFLAC+ffmpeg consensus`
and aborts (the genuine out-of-coded-range case); `repro-min-215B.flac` now prints the
NON-fatal `... Vinyl vs a single reference (uncorroborated)` and exits 0 (the libFLAC
referee rejects its frame/STREAMINFO sample-rate contradiction, so no consensus forms).

sha256:
- `repro-min-215B.flac` `1958775ccf4c4ef2320c9d94569fad9212e22b5b7b16528675d4a42277c49d2b`
- `repro-561B.flac`      `bdb56a9c24dab2797c26f123d93ac78048d5162ac423d3821d15c3d6ca7f427e`

## How it was surfaced (and why it was previously masked)

This class was **under-adjudicated before**. Prior fleet runs (20260831_163422,
20260831_183805) catalogued only the non-fatal `wide_sample_diff_1ref` variant —
Vinyl disagreeing with a *single* reference, which the oracle does not trust enough to
abort on. The lazy ffmpeg gate skipped the second referee on most inputs, so a
libFLAC+ffmpeg *consensus* rarely formed, and a real Vinyl divergence stayed a quiet
1-ref catalogue entry.

The P0.4 fix in this session (`ffm_adjudication_skippable` no longer auto-skips ffmpeg
when both decoders reject, plus `fz_trailing_data` forcing ffmpeg on its base) makes
the second referee run on far more inputs. On the first bps=31 divergence it reached,
libFLAC and ffmpeg agreed, forming the consensus that escalates this from a
catalogued-and-ignored `_1ref` note into a confirmed, fatal `wide_sample_diff`.

**This is the ffmpeg-gate improvement working as designed**: an accept-set / one-ref
divergence that libFLAC alone flagged, and that the skipped second referee never
corroborated, is now adjudicated. It is NOT a regression introduced by the rig
changes: `git diff fuzz/common/wide_diff.c` shows the Vinyl decode
(`vinyl_wide_decode`), the sample comparison (`wide_cmp`), and the abort site are
unchanged; only the ffmpeg gating/refactor was touched. The divergent Vinyl behaviour
is pre-existing.

## Triage (2026-08-31) — the two repros are DIFFERENT cases

Both repros are **MID/SIDE stereo at bps=31** (frame channel-assignment nibble `0b1010`).
libFLAC analysis (`flac -a`) and the raw header bytes were used to separate them.

### 215B — malformed input, NOT a Vinyl bug (resolved)

The frame's sample-rate code is `0b0001` = **88200**, contradicting STREAMINFO's 44100.
The strict **libFLAC 1.4.2 CLI rejects this as fatal**:

```
repro-min-215B.flac: ERROR, sample rate is 88200 in frame but 44100 in STREAMINFO
```

The rig's *linked* libFLAC referee (`flac_wide_decode`) did **not** make this check, so it
was more lenient than the CLI, decoded with the frame's 88200, and formed a false
libFLAC+ffmpeg "consensus" against Vinyl (which accepts the stream, reports STREAMINFO's
44100, and reconstructs mid/side differently). On a stream the two libFLAC entry points
themselves disagree about, there is no RFC-correct PCM — this is an accept-set difference
on malformed input, not a Vinyl soundness bug.

**Fix applied** (`common/wide_diff.c`): `fw_write` now rejects a frame whose sample rate
contradicts STREAMINFO (`fw.sr_mismatch`), matching the libFLAC CLI and the rig's own
`vwr` path (`flac_api.c:362`). The wide libFLAC referee no longer forms a consensus on a
frame/STREAMINFO sample-rate contradiction, so the 215B class becomes a non-fatal
single-referee `_1ref` catalogue entry instead of a spurious fatal `wide_sample_diff`.

### 561B — structurally valid; root-caused to the coded-depth wrap; NOT a bug (resolved)

No sample-rate contradiction (frame code = from-STREAMINFO = 44100). libFLAC's CLI
**decodes all four frames cleanly** (only the trailing MD5 mismatches, expected for a
mutated stream), so the stream is structurally valid FLAC. Frame structure:
`MID_SIDE, LPC order 8, qlp_coeff_precision=15, residual ESCAPE raw_bits=31`. Vinyl's
ch0[43] differs from the libFLAC+ffmpeg consensus by exactly **2^23**.

**Root cause (two independent analyses, with the exact intermediate values computed):**
`Lpc.restoreA` (`Flac/Native/Lpc.lean:256`, reached via `Decode.lean:298`) folds every
reconstructed history sample to the *coded subframe depth* with `Bits.wrapSInt b`. In this
MID_SIDE frame the mid subframe is coded at `b=31` bits. At frame 2, mid local sample 10,
the LPC recurrence (coeffs `[1,0,0,0,0,0,903,-15872]`, shift 8) reconstructs
`-1420933233` — **outside the coded 31-bit range `[-2^30, 2^30)` but inside signed 32-bit**.
Vinyl wraps it to 31 bits (`+2^31 → 726550415`); libFLAC/ffmpeg keep the raw value in an
`int32` container (RFC 9639 A.2, "sufficient for … up to 31 bits"). At local sample 11 the
coefficient `cs[0]=1` reads that one divergent history cell, so the prediction differs by
`2^31 >> shift(8) = 2^23`, which passes through `decodeMSLA` unchanged mod 2^31 → the
observed `214977311` (Vinyl) vs `206588703` (consensus). The side subframe (coded `b+1=32`)
is bit-identical to the references — `wrapSInt 32` *is* int32 truncation — so only the mid
channel, only at bps=31 (the unique depth where exactly one subframe's modulus differs by
one bit of width and both referees still accept), diverges.

**Verdict: defensible accept-set difference on INVALID input — NOT an RFC violation, no
codec fix.** The divergence can only arise once a reconstructed sample leaves the coded bit
depth, which RFC 9639 §5 (`references/rfc9639.txt:553-561`) explicitly makes "decoder
behavior … left unspecified," naming exactly "one or more decoded sample values exceed the
range offered by the bit depth as coded for that frame." On a *valid* stream Vinyl's wrap is
the identity (`Flac/Spec/Bits.lean` `wrapSInt_eq_of_fits`) and the references' int32 never
overflows, so all three agree bit-for-bit; a divergence of this shape is self-certifying
evidence the input is invalid. Vinyl's fold-to-coded-depth is the deliberate P1 output
hardening (bounds every history entry to one limb — `fitsSInt_wrapSInt` — defeating the
adversarial geometric blowup `Lpc.lean:78-86` documents) and is strictly safer than the
references' machine-width storage. Removing the recurrence wrap to match them would re-open
the `decoder-output-contract-stereo` hole on independent-channel frames (nothing downstream
re-wraps there) — trading an RFC-permitted difference on invalid input for a real
output-contract regression. RFC A.2 is descriptive ("Most FLAC decoders store…"), not
normative; A.4 requires only that the *addition* use a wide enough type, which Vinyl's
bignum `Int` does exactly. This is the same class as `decoder-output-contract-stereo`, at
the one depth where both referees accept.

**Rig-classification limitation (documented, not fixed):** the invalidity is invisible in
the final PCM (both `214977311` and `206588703` fit 31 bits), so no post-hoc sample-range
check can auto-classify this witness; the only sound discriminator is a debug Vinyl decode
with the `restoreA` wrap forced to 32-bit (if it then matches the consensus, it is this
policy class). That would require adding a debug decode path to the verified codec, which is
not worth it for a confirmed non-bug — so `repro-561B.flac` is recorded here as a **known
accept-set witness**: a fatal `wide_sample_diff` on a bps=31 mid/side stream whose mid
subframe reconstructs out of coded range is this class, not a new defect.
