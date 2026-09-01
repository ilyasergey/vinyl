# Encoder non-tail recursion overflows the stack on ordinary inputs

## Update 2026-08-31 — the PER-FRAME loops fixed; a dedicated prober added

The 2026-08-30 patch below retired the three per-SAMPLE encode loops. The
per-FRAME loops named in the audit's C04 (`Stream.writeFrames`,
`Stream.chunkChannels`) still carried no compiled-swap: each recurses once per
FLAC frame = `ceil(samples/blockSize)`, so a small block size over long audio
drives the recursion depth with the frame count. This is the class the gate
could not see — a MISSING swap is invisible to a gate that pins the swaps that
exist.

**New target `fz_encode_stack`** rediscovers it autonomously. It forks a child
with a small `RLIMIT_STACK` (set before an `execv`, the mechanism
`tools/stack_probe.sh` uses via `ulimit -s`; a running thread's mapped stack
cannot be shrunk, an exec's fresh one can), runs the SLOW encoder
(`vm_encode_slow` → `Flac.encodePcm16Cfg`) on incompressible PCM, and reads the
child's `SIGABRT`/`SIGSEGV` as the witness — cataloguing the ok→crash
`(samples, channels, blockSize, stackKB)` frontier WITHOUT aborting the fuzzer.
A 10-minute run (`runs/20260831_175244`, 6 workers) recorded **464
`encode_stack_overflow` occurrences / 327 witness files across 74 worker
processes, 0 fuzzer crashes / 0 OOM / 0 timeouts** — the overflow is the
child's, catalogued as a divergence. It is a resource prober, not a codepath
differential: the work is in the forked child, so it is `engines=("libfuzzer",)`
and catalogue-by-default (`FUZZ_STRICT>=1` escalates an overflow to a filed
abort).

**Source fix applied (this session).** `Stream.writeFrames` and
`Stream.chunkChannels` were made tail-recursive with the repo's established
`@[csimp]` swap (accumulator form + bridging equation, exactly as
`bitsToByteListAcc`/`recombineTR`): `writeFramesAcc`/`writeFramesTR`,
`chunkChannelsAcc`/`chunkChannelsTR`. Every theorem keeps the structural
definition through the kernel (the swap is compiler-only); `Flac.Spec.Encode`,
which inducts on `chunkChannels`, is unchanged. `#print axioms` of both swaps is
`[propext, Quot.sound]` — no `sorry`, no new axiom. `lake build`, `lake exe
flactest` (155), and `scripts/check.sh` are all green; `make check` mutator
selftest stays 400/400 byte-identical. After the fix the many-frame probes that
crashed at 256–512 KB (e.g. `128000` samples `bs=16`, 8000 frames) run to
completion (they hit only the probe's slow-encode alarm), so the per-frame class
is retired — `fz_encode_stack` is now the regression guard that catches the next
un-swapped encode loop.

## Update 2 (2026-08-31) — three MORE non-tail encode loops, found by the prober and FIXED

With the per-frame class retired, `fz_encode_stack` kept flagging a `bs=4096`
overflow whose depth scaled with samples-PER-frame (not frame count). A gdb
backtrace under a shrunk stack pinned the actual culprits — **three loops NOT in
C04's enumerated six**, exactly the "enumerative guarantee" gap the prober exists
to close (my first guess, `writeRiceSeq`'s `List.flatMap`, was WRONG — core
`flatMap` is tail-recursive via `@[csimp] flatMap_eq_flatMapTR`):

- **`Heuristics.partitionSearch`** summed each partition's residuals with
  `List.sum`, which compiles to a non-tail `foldr` (`List_foldr___at___List_sum`
  in the backtrace) — depth = partition size. This was the dominant one on the
  checked-encoder path. Fixed by `us.foldl (·+·) 0` / `p.foldl (·+·) 0` (same
  value, tail-recursive; `Heuristics` is unverified-by-design so no theorem reads
  the fold shape).
- **`Fixed.diff1`** (fixed-predictor residual, `(y-x) :: diff1 (y::t)`) and
  **`Lpc.residualAux`** (LPC residual, `(x - predict …) :: residualAux …`) — both
  per-sample, depth = block size. Fixed with the `@[csimp]` accumulator swap
  (`diff1TR`, `residualAuxTR`; `#print axioms` = `[propext, Quot.sound]`).

Depth was bounded by samples-per-subframe = block size. The CHECKED encoder caps
`blockSize ≤ 4608` (≈288 KB, safe under an 8 MB stack, so the shipped CLI never
hit it), but **`Stream.Unchecked.encode` with a large block size is unbounded** —
the same footgun tier as the other unchecked findings. Post-fix the encoder
survives every `blockSize ≤ 4608` case down to a **128 KB** stack; `lake build` /
`flactest` (155) / `scripts/check.sh` green. `fz_encode_stack` is now a clean
regression guard (0 overflows across the checked range).

---

`repro_*` below is the original per-frame witness.

---

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
