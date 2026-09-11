# Vinyl fuzzing — open work

Open items only. Fixed findings live in `findings/` (each with a reproducer, a
status line in `findings/README.md`, and a standing detector); completed rig work
is documented where it lives (`README.md`, `cov/`, the target source).

Guardrails: `common/flac_struct.c` (the reference CRC mutator) is frozen
(byte-identity gate in `make check`). Codec source fixes ARE now landing in
`Flac/Native/` (with `@[export]` additions in `FlacTest/FuzzGen.lean` as before):
each fix must keep `lake build` / `flactest` / `../scripts/check.sh` green with no
`sorry`/new axiom, and preserve the capstone theorems (a decoder-tightening is only
safe if the encoder never emits the newly-rejected form). Encode `max_len` caps are
64 KB: the encoder is stack-safe to 128 KB and its frame loop is linear in emitted
bits, so neither bound forces small encode inputs.

## Codec findings ledger — OPEN

Documented; the detector fires under `FUZZ_STRICT` and is ready to become a strict
gate once a fix lands.

- **samplerate-zero** — STREAMINFO sample-rate 0 accepted with audio. Fix requires
  a `0 < sampleRate` conjunct in `Audio.WellFormed` threaded through
  `readStreamInfo` (both twins) → `readMeta_spec` → the `decode_encode`/`encodePcm16`
  capstones. Pin: `fz_streaminfo_contradict`. (The `4 ≤ bps` fix for
  `emit-streaminfo-bps-below-4` threaded exactly this shape and is a worked template.)
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

## Coverage — open gaps

- **Encoder search branches.** `Encode.lpcFold7/8` stay cold behind the
  `lpcMaxOrder=6` heuristic ceiling, and `Heuristics.lpcSearch`'s multi-candidate
  loop behind the `lpcCandidates=[est]` singleton. These need a codec-side knob to
  reach and are not corpus-fixable.
- **Remaining, NOT corpus-fixable (needs a codec-side knob or is size-bound):**
  `Encode.lpcFold7/8` (`lpcMaxOrder=6`), the multi-candidate `Heuristics.lpcSearch` loop
  (`lpcCandidates=[est]`), `Encode.pushPartsR`'s RICE2 arm (`riceChoices` clamps k<=14),
  and the `Emit.W.pushUtf8` / `Encode.BitWriter.pushUtf8` 4-6-byte frame-index arms
  (>=2^16 frames per stream). Everything else uncovered is dead-by-design or an
  impossible-by-invariant arm — `cov/structural_zero.py` classifies which, and
  `make coverage` prints the effective figure over genuine targets.
- Re-run variant-merged coverage after each campaign (`make coverage`,
  `cov/per_target.py`) and confirm the new seeds' payoff.

## Standing discipline

- **Triage the catalogue, not just the aborts.** Catalogue-by-default means a real
  finding can present as a counter that climbs quietly. Two did:
  `emit_si_bps` (11,532 hits, 1062 dumped reproducers) was an RFC 9639 Table 3
  violation in the checked encoder, and 248 `blockSize=16` slow-unit artifacts were
  a quadratic frame loop. Both were live across billion-execution campaigns that
  reported clean. After a campaign, read `SUMMARY.md`'s divergence columns and the
  `artifacts/` directory, not only the crash count.
