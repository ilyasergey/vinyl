# Encoder non-tail recursion overflows the stack on ordinary inputs

**Status: FIXED (2026-08-30) — patch applied and verified.** The three
per-sample non-tail functions on the slow-encode path were made tail-recursive
via the P6 `@[csimp]` pattern (kernel-proven equal to the structural forms, which
all theorems keep reading): `Codec.pcm16OfByteList` (input parse), `Bits.bitsToByteList`
(output pack), and `Codec.deinterleaveN` (the per-sample transpose — the true
dominant cost; `writeFrames`/`chunkChannels` recurse per *frame* = blockCount, not
per sample, and the serializers/Md5 were already tail/loop). `lake build` /
`flactest` (155) / `scripts/check.sh` all green, no sorry/axiom; `measure_encode
65536` now completes (`enc=ok out=267498B`, and 262144-mono `out=525034B`) where it
previously aborted. History and the measured threshold below.

**Original status: CONFIRMATION of a known issue — NOT claimed as novel.**
The encoder's non-tail recursion was already identified by source review. This
entry adds a MEASURED threshold and a one-command reproducer.

## What Vinyl does

`Flac.encodePcm16 = bitsToBytes (writeStream cfg a)`, and `bitsToByteList`
recurses once per OUTPUT byte, so the minimum surviving stack grows with the
output size. The slow/Cfg encode path (`Flac.encodePcm16Cfg`, the path
`Flac.encodePcm16` — the README's second headline theorem — routes through)
overflows the Lean runtime stack on ordinary inputs.

## Measured threshold

`tools/measure_encode` (slow path, `bitsToByteList`), default 8 MB stack
(`ulimit -s 8192`), stereo 44.1 kHz:

| frames/channel | ≈ duration | result |
|---|---|---|
| 8192 | 0.19 s | ok |
| 65536 | 1.49 s | **Stack overflow detected. Aborting.** |

So a **~1.5-second stereo clip** overflows the stack of the slow encoder at the
default stack size. This is a total function whose stack need grows with output
size (a class relationship), not a fixed-size bug.

## Reproduce

```sh
cd vinyl/fuzz && make            # builds build/bin/measure_encode
( ulimit -s 8192; build/bin/measure_encode 65536 )   # -> "Stack overflow detected. Aborting."
build/bin/measure_encode 8192                          # -> ok (0.19s)
tools/stack_probe.sh                                   # sweeps the ok->CRASH threshold vs input size
```

`tools/stack_probe.sh` demonstrates the CLASS relationship: the ok→crash threshold
MOVES with input size (sweep 2), i.e. the finding is not a single magic size.

## Related

The `fast` encode path (`encodePcm16Fast`) does not hit `bitsToByteList`; its
resource issue is the task storm (`measure_encode` sweep: bs=16 spawns
`ceil(n/blockSize)` = 256× the tasks of bs=4096, with no cap vs the decoder's
`maxStepTasks = 1024`). `VINYL_ENCODE_SAMPLE_CAP = 8192` in the fuzz rig exists
precisely to work around this overflow (surfaced now as `encode_capped` in the
`fz_self_consistent` / `fz_metamorphic` reports).

## Manifestation 2: overflow from a 32-byte input via high depth × channels

The `official` campaign surfaced this on the *unchecked* encoder too
(`Stream.Unchecked.encode`, which `fz_gen_roundtrip` / `fz_emit_conformance` /
`fz_residual_bound` drive). Because the stack cost is `bps·ch·nsamples/8` OUTPUT
bytes — not frame count — a **32-byte seed** that selects `bps=32, ch=8` and a
few thousand samples produces ~64 KB of output and overflows immediately.

`repro_gen_highdepth_32B.flac`
(`sha256: 87448c565c32d33af2896de776fb1e919acf105eeebece85bf0d7d96388b1e04`) is
such a seed: `build/bin/fz_gen_roundtrip.fuzz repro_gen_highdepth_32B.flac` →
`Stack overflow detected. Aborting.` before the fix below. This sharpens the
finding: the trigger is **output bytes**, so a tiny high-depth/multichannel input
reaches it, not only a 1.5-second clip.

The same overflow is reachable wherever the harness runs the encoder on
non-trivial output, all the same root cause:
- `Stream.Unchecked.encode` / `encodePcm16Cfg` on generated or packed PCM
  (`fz_gen_roundtrip`, `fz_emit_conformance`, `fz_residual_bound`,
  `fz_unchecked_encode`, `fz_roundtrip`).
- **The re-encode of DECODED audio** in `fz_self_consistent` and `fz_metamorphic`
  (`Flac.encode` of a decoded high-depth/multichannel `Audio`) — the decode itself
  is fine (verified: three decode-only targets do not overflow on the same
  witness), only the re-encode overflows.

**Harness mitigation (does NOT fix the Vinyl bug), so a campaign explores new
behaviour instead of crash-looping on this known overflow:**
- `common/vinyl_gen.c` bounds generated audio to ~8 KB estimated output.
- `common/vinyl_checks.c` bounds the re-encode by estimated output bytes
  (`VINYL_ENCODE_BYTE_CAP`), not just sample count.
- `fz_unchecked_encode` / `fz_roundtrip` `max_len` lowered to 16384 (verified
  overflow-free).

The source fix remains as below (make `bitsToByteList` tail-recursive, the P6
class applied to the encode side), which would remove the need for every one of
these bounds.

## Category

Robustness / totality-in-practice: `bitsToByteList` (and `pcm16OfByteList`) are
non-tail-recursive. Fix class: make the byte serialization tail-recursive /
iterative (as the decoder's `*TR` variants already are), or chunk the output.
Severity is a calibrated robustness note — user-supplied input size drives it — but
the threshold (~1.5 s of audio) is well within ordinary use.
