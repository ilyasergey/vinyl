# Vinyl fuzzing — open work

Guardrails: `common/flac_struct.c` (the reference CRC mutator) is frozen
(byte-identity gate in `make check`). Codec source fixes ARE now landing in
`Flac/Native/` (with `@[export]` additions in `FlacTest/FuzzGen.lean` as before):
each fix must keep `lake build` / `flactest` / `../scripts/check.sh` green with no
`sorry`/new axiom, and preserve the capstone theorems (a decoder-tightening is only
safe if the encoder never emits the newly-rejected form). The former
`bitsToByteList` encoder-stack hazard that kept encode inputs small is retired
(C04 fixed), so the encode `max_len` caps were lifted to 64 KB.

## Codec findings ledger

Each has a curated reproducer + a standing detector under `findings/`.

**FIXED at source (detector flipped to a two-way regression pin):**
- **encoder-stack-overflow** (C04 + extensions) — the original per-sample loops
  (2026-08-30), then FOUR more the `fz_encode_stack` prober found autonomously
  beyond C04's enumerated six (2026-08-31): per-frame `writeFrames`/`chunkChannels`,
  per-sample `Fixed.diff1` / `Lpc.residualAux`, and the dominant
  `Heuristics.partitionSearch` `List.sum` (a non-tail `foldr`). All now
  tail-recursive (`@[csimp]` swaps / `foldl`); encoder stack-safe to 128 KB across
  the checked block range. Prober + pin: `fz_encode_stack` (forks a bounded-stack
  child), now a clean regression guard.
- **readRiceSeq / readSIntSeq tail twins (reference decoder — NOT a shipped bug)** —
  `Flac.Rice.readRiceSeq` / `readSIntSeq` (`Flac/Native/Rice.lean`) build their residual
  list with a non-tail `x :: rec`, but they are on the REFERENCE decoder path only
  (`decodeReference` → `Subframe.read` → `Rice.readResidual`). The SHIPPED array decoder
  (`decodeArrays` / `decodePcm16A`) uses the already-tail `Flac.Decode.readRiceSeqScan` /
  `readSIntSeqGo` and calls no `Flac.Rice.readRiceSeq*` (IR-verified in `Decode.c`). An
  earlier draft misattributed a `vm_decode_ref` gdb trace to the shipped decoder; that
  was wrong. The `readRiceSeqTR` / `readSIntSeqTR` `@[csimp]` twins landed anyway (sound,
  theorems intact, pinned by name in `scripts/check.sh`) as a minor hardening of the
  reference path's two residual loops. `fz_decode_stack` verifies the SHIPPED decoder is
  stack-flat in its residual layer (green at every stack size, up to the legal max
  blockSize 65535 via the libFLAC-emitter lane). See
  `findings/decoder-stack-overflow-readriceseq/`.
- **overlong-coded-number** — `Utf8Num.contsFloor` minimality gate in both reader
  twins rejects non-minimal coded numbers (2026-08-31). Two-way pin:
  `fz_overlong_utf8` (`overlong_accepted` 114M→0, `overlong_rejected` climbs).
- **decoder-output-contract-stereo** — `Stereo.decode*` wrap to `bps` (2026-08-30).
  Pin: `fz_self_consistent` (`unfit`) / `fz_samples_diff` (`wide_output_contract`).

**OPEN (documented; detector fires under `FUZZ_STRICT`, ready to become a strict
gate once a fix lands):**
- **samplerate-zero** — STREAMINFO sample-rate 0 accepted with audio. Fix requires
  a `0 < sampleRate` conjunct in `Audio.WellFormed` threaded through
  `readStreamInfo` (both twins) → `readMeta_spec` → the `decode_encode`/`encodePcm16`
  capstones. Pin: `fz_streaminfo_contradict`.
- **channel-truncation** — silent channel truncation in `recombine` (`zipWith`).
  Fix requires a frame-vs-STREAMINFO channel-count reject in the decode loop,
  threaded through `decodeBytes_spec`/`recombine` proofs. Pin: `fz_self_consistent`
  clause-3a.
- **decode-capacity-underalloc** — `decodeBytes` `outCapacity` hardcodes 2 B/sample;
  24/32-bit output reallocs. A perf/capacity issue (output is correct), not a
  correctness bug. Pin: `fz_decode_capacity`.
- **float-lpc-coefficient-divergence** — encoder Float LPC search diverges from
  exact arithmetic above 2^53 (24/32-bit); round-trip still holds. A claim/quality
  gap in unverified-by-design `Heuristics`, not a correctness break. Pin:
  `fz_float_exact`.
- **decode-sample-divergence-highbps** — TRIAGED 2026-08-31, RESOLVED as accept-set
  differences on invalid/malformed input, NOT Vinyl bugs (two independent root-cause
  analyses). **215B**: malformed — frame sample rate 88200 contradicts STREAMINFO 44100;
  the strict libFLAC CLI rejects it but the rig's lenient linked referee accepted it and
  manufactured a false consensus. FIXED: `wide_diff.c` `fw_write` now rejects the
  frame/STREAMINFO sr contradiction (`fw.sr_mismatch`), matching the CLI and the `vwr`
  path — 215B downgrades to a non-fatal `_1ref` entry. **561B**: structurally valid but
  RFC-invalid audio — `Lpc.restoreA`'s per-sample coded-depth `wrapSInt b` (mid at 31
  bits) folds a reconstructed sample that left the coded 31-bit range (still valid 32-bit)
  where libFLAC/ffmpeg keep int32; the divergence re-enters the LPC recurrence as
  `2^31>>shift = 2^23`. RFC 9639 §5 leaves out-of-coded-range decode unspecified; Vinyl's
  wrap is the P1 output-contract hardening (safer; removing it re-opens
  `decoder-output-contract-stereo`). No codec fix. Recorded as a known accept-set witness.
  Residual rig limitation (documented, not built): the final PCM cannot classify this;
  the sound discriminator is a wrap-width-32 debug decode, not worth a codec debug path
  for a confirmed non-bug. Detector: `fz_samples_diff`.

## Referee discipline

- **libFLAC 1.5.0 referee — DONE (2026-08-31).** Version-stamp: every run's `build.info`
  and SUMMARY header already record `libflac_src` (the linked source-tree version) and
  `flac_cli`, so every referee-derived counter is stamped with its libFLAC version.
  1.5.0 second referee: `scripts/build_flac150.sh` fetches + builds libFLAC 1.5.0 as a
  SEPARATE static lib (`build/lib/libflac.plain150.a`) and builds `flac150_decode` (a
  1.5.0-linked accept/reject probe) plus `flac142_decode` (the same source on the pinned
  1.4.2 lib) — an apples-to-apples cross-version differential. `scripts/flac_version_diff.sh`
  runs it reproducibly over the decode corpora and reports a concrete accept-set shift:
  `decode/regress/r2_libflac_phantom_frames.flac` is **accepted by 1.4.2, rejected by
  1.5.0** (1 of 2026 files) — exactly the version dependence that makes the stamp
  necessary. (Both probes read the WHOLE file — no fixed-prefix truncation — so verdicts
  on the large-input corpora are sound.) Flipping the whole fleet to 1.5.0 remains a
  deliberate `FLAC_TAG=1.5.0 scripts/deps_fetch.sh` + rebuild (not forced, to keep the
  1.4.2-calibrated pins stable); the 65536 two-sided pin is one instance of this class.
- **ffmpeg emit-side referee — DONE (2026-08-31).** `fz_encode_referee` encodes real
  PCM with BOTH shipped production encoders (`encodePcm16Fast` and the checked
  `encodePcm16Cfg`) over the `encode/gen`+`encode/shapes` matrix, then runs the emitted
  bytes through the 3-way decode consensus (Vinyl / libFLAC every exec / ffmpeg lazy
  gate, `wide_diff_oracle`). On Vinyl's own valid encoder output all three must decode to
  the same samples; a libFLAC/ffmpeg contradiction (or a Vinyl-only accept) is an encoder
  conformance bug. A byte-level comparison to ffmpeg's ENCODER was deliberately NOT done:
  divergent LPC/Rice/partition heuristics and Vinyl's non-correctly-rounded `Float.log2`
  cost make the emitted bytes legitimately differ across encoders/platforms, so there is
  no host-portable byte oracle -- the decode consensus is the sound, tolerance-free
  alternative. Verified clean (`all_agree`, zero divergence) on the production encoders;
  enrolled in `campaign.official`.

## Coverage

- **Reference-lane diversity — DONE.** `decode/ref_small` adds <=8 KB (1-2 frame)
  seeds carrying non-canonical block-size codes (1-5, 8-11), 3-8 channel geometries,
  mid/side stereo, and explicit sample-rate codes (12-14), so they reach the
  `fz_decode_modes` reference lane (`VM_REF_MAX_INPUT=8192`) and drive
  `decodeReference` / `Frame.readChannels` / `resolveBlockSize` / `skipSampleRate` /
  `Stereo.c` on shapes Vinyl's own writer never emits. Remaining minor gap: a
  forced FIXED-order 0-4 sweep (libFLAC auto-selects order, so this needs the G1
  hostile-fixed chooser at <=8 KB rather than a libFLAC seed).
- **Encoder search branches.** `Encode.lpcFold7/8` stay cold behind the
  `lpcMaxOrder=6` heuristic ceiling, and `Heuristics.lpcSearch`'s multi-candidate
  loop behind the `lpcCandidates=[est]` singleton. These need a codec-side knob to
  reach and are not corpus-fixable.
- **`fz_float_exact` windowing lane — DONE (2026-08-31).** `run_windowed_lane` calls
  Vinyl's `welchF` (`lp_vinyl_Flac_Heuristics_welchF`) then `autocorrF`, i.e. the actual
  production search input `autocorrF (welchF s)` (Heuristics.lean:387), and validates the
  selected quantized coefficients against a long-double windowed recompute. The window
  makes the samples non-integer, so there is no integer-exact anchor; instead a
  bit-exact C-`double` replica of `welchF`+autocorr is the faithfulness self-test (a
  mismatch is a `[DETECTOR BUG]` abort, never a finding), long double is the trusted
  reference, and the `attributable` control isolates the autocorr precision loss. Unlike
  the unwindowed lane, bps<=16 is not a required-0 anchor (window products exceed 2^53 of
  mantissa, so double loses precision at every depth). Verified: self-test clean on 175k
  analyzed inputs while surfacing `float_win_divergence` findings the unwindowed lane
  misses. The original unwindowed lane (integer-exact anchor) still runs as a component
  test.
- Re-run variant-merged coverage after each campaign (`make coverage`,
  `cov/per_target.py`) and confirm the new seeds' payoff.
