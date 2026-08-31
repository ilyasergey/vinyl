# Silent channel truncation with a success result

**Status: CONFIRMATION of a known issue — NOT claimed as novel.**
This behaviour was already identified by source review of the decoder (the
`si.channels`-vs-decoded-channels check was a proposed detector for it). This
entry records a *dynamic* reproduction: a minimized stream on which the compiled
binary exhibits the behaviour, plus the three-way reference verdicts. Its value is
the reproducer + proof-to-binary triangulation, not a novelty claim.

## What Vinyl does

The decoder **accepts** a stream whose frame channel layout contradicts its
STREAMINFO, and returns an `Audio` with **fewer channels than STREAMINFO
declared**, with a success result — silent data loss. The mechanism is
`Stream.recombine` / `recombineGo` merging channels with `List.zipWith (· ++ ·)`,
which truncates to the shorter list.

## Reproducer

`repro.flac` (172 bytes, minimized by libFuzzer from `fz_self_consistent`).
`sha256: 4c825fa4cc3cd513b868ad986c07983a238135d7caa304cc300ef0ec9156eafb`

STREAMINFO (`metaflac --show-channels --show-bps --show-total-samples`):
`channels=2  bps=16  total_samples=3254`.

## Three-way reference verdicts

| decoder | verdict |
|---|---|
| **Vinyl** `--decode` | ACCEPT — `decoded 448 samples x 1 channels (16-bit)` (896 B PCM) |
| **Vinyl** `--decode-fast` | ACCEPT — identical: `448 samples x 1 channels` |
| **libFLAC** `flac -t` (1.4.2) | REJECT — `FLAC__STREAM_DECODER_ABORTED`, exit 1 |
| **ffmpeg** (libavcodec) | decodes partial output (384 B) |

The decoded Audio carries **1 channel** under a STREAMINFO that declared **2** —
output that contradicts its own header. libFLAC applies the frame-vs-STREAMINFO
consistency rule and rejects; Vinyl follows the frame and silently drops the
missing channel while reporting success.

## Reproduce

```sh
V=.lake/build/bin/vinyl
metaflac --show-channels repro.flac          # -> 2
$V --decode repro.flac /tmp/out.raw          # -> "decoded 448 samples x 1 channels", exit 0
flac -st repro.flac                          # -> ERROR while decoding data, exit 1
```

## Detector

`fz_self_consistent` clause-3a (`common/vinyl_checks.c:streaminfo_channels` +
`SelfConsistency.channel_incoherent`). Because the CRC mutator manufactures
channel/bps contradictions constantly, the detector **catalogues + counts** by
default (`selfcon_channel_incoherent` dumps; `channel_incoherent=` in the report
line) and escalates to `abort()` only under `FUZZ_STRICT>=ACCEPT`, so a campaign
stays runnable while a specific witness can be regression-pinned.

## Category

Output contract: the decoder's result must be coherent with the STREAMINFO it
parsed. Fix class (not instance): either reject frame-vs-STREAMINFO channel
disagreement (libFLAC's policy), or define and enforce a post-decode invariant
`decoded.channels.length = si.channels`.
