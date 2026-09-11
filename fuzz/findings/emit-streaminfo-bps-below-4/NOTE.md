# The checked encoder emitted STREAMINFO bit depths below 4 (RFC 9639 Table 3)

**Status: NOVEL, FIXED 2026-09-11.** Both sides — the encoder emitted them, the decoder accepted them.

## What was wrong

RFC 9639 Table 3 restricts the STREAMINFO bit-depth field to **4–32**. The 5-bit encoding can represent
1–32, but depths 1–3 have no conforming stream. `Audio.WellFormed` required only `1 ≤ a.bps`:

```lean
1 ≤ a.channels.length ∧ a.channels.length ≤ 8 ∧
1 ≤ a.bps ∧ a.bps ≤ 32 ∧ …          -- `1 ≤` should have been `4 ≤`
```

`encodeCheckedCfg` gates on `a.WellFormed ∧ 16 ≤ cfg.blockSize ∧ cfg.blockSize ≤ 4608` and adds no bit-depth
bound of its own, so this was reachable through the **checked, theorem-covered** entry points, not only
through `Stream.Unchecked.encode` (which by contract does not validate).

`Flac.Native.Stream.readStreamInfo` and its `Flac.Native.Decode` twin performed no bit-depth validation at
all, so Vinyl also *accepted* such streams on decode.

## Behaviour

`repro-bps3-emitted.flac` — 59 B, emitted by Vinyl at bps=3, from the `fz_emit_conformance` catalogue:

```
flac 1.5.0 : ERROR: bits per sample is 3, must be 4-32
ffmpeg     : invalid bps: 3
vinyl      : decoded ... (3-bit)        ← accepted its own out-of-spec output
```

`repro-bps1-decoded.flac` — 73 B at bps=1, from `corpus/decode/regress`; before the fix Vinyl decoded it to
16 samples, after the fix it is `DECODE ERROR`.

The round-trip capstone was never false: it guarantees `decodeReference (Unchecked.encode cfg a) = some a`,
and that held. It simply says nothing about whether the emitted artifact is a FLAC stream, so the guarantee
ranged over files no other decoder accepts.

## Why it went unreported

`fz_emit_conformance` has carried the Table 3 clause the whole time and **fired it 11,532 times** in the 12 h
campaign, dumping 1062 reproducers to `divergences/emit_si_bps/`. It only escalates to an abort under
`FUZZ_STRICT`, so in catalogue-by-default mode it counted silently and nobody opened the directory. Grep for
`emit_si_bps` across `findings/`, `TODO.md`, `PLAN.md`, the Lean sources and the external review returned
nothing before this note.

The oracle was also mis-scoped: it drove the *unchecked* writer over the generator's full 1–32 depth range,
so most hits were the generator asking for something inexpressible rather than an emitter defect. That is
why a real finding sat inside a counter everyone had learned to read as noise.

## The fix

- `Audio.WellFormed` now carries `4 ≤ a.bps` (`Flac/Native/Stream.lean`). `readStreamInfo_writeStreamInfo`
  and `readMeta_spec` take `4 ≤ b`; `encode_cost_le_budget` still takes `1 ≤ a.bps`, bridged by `omega`.
- Both `readStreamInfo` twins reject `bps < 4`. Safe for the capstone in the required direction: the encoder
  can no longer emit one, so no decoder-tightening breaks `decode ∘ encode`.
- `fz_emit_conformance` gates the clause on an in-spec request and reports `bps_oos_skipped` separately, so
  `bps_bad` is now a true MUST-be-0 pin rather than a running tally.
- `common/vinyl_checks.c`'s `bad_bps` mirrors the new bound, keeping `structural_ok` equal to `WellFormed`
  (`fz_self_consistent` cross-checks the two and aborted until this was aligned).

## Verification

```sh
lake build && lake exe flactest              # ALL TESTS PASSED (177 checks)
bash scripts/check.sh                        # CHECK: ALL GREEN
bash conformance/ietf.sh <flac-test-files>   # IETF MUST-DECODE: ALL GREEN (61/61)
bash conformance/smoke.sh                    # CONFORMANCE SMOKE: ALL GREEN
cd fuzz && bash scripts/regress.sh           # REGRESS: ALL DETECTORS FIRE

build/bin/fz_emit_conformance.fuzz corpus/encode/gen   # bps_bad=0 (was 140)
.lake/build/bin/vinyl --decode findings/emit-streaminfo-bps-below-4/repro-bps1-decoded.flac /tmp/o
                                                       # DECODE ERROR (was: decoded 16 samples)
```

The decoder tightening rejects no valid stream: the IETF must-decode corpus is unchanged at 61/61, and the
one `uncommon/10 - file starting at frame header.flac` failure predates this change.
