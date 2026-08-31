# Vinyl fuzzing — open work

Guardrails: `Flac/` is off-limits except `@[export]` additions in
`FlacTest/FuzzGen.lean`; `common/flac_struct.c` (the reference CRC mutator) is
frozen (byte-identity gate in `make check`); large-input variants stay
decode-only / fast-only (the `bitsToByteList` encoder-stack hazard). The codec
findings below are DOCUMENTED-NOT-APPLIED — `Flac/` is fixed by its owners, the
rig only pins them.

## Codec findings ledger (documented, not applied)

Each has a curated reproducer + a standing regression detector under `findings/`.
Handed to the codec owners; the rig keeps the pins green.

- **decode-capacity-underalloc** — `decodeBytes` `outCapacity` hardcodes 2 B/sample;
  24/32-bit output reallocs. Pin: `fz_decode_capacity`.
- **samplerate-zero** — STREAMINFO sample-rate 0 accepted with audio. Pin:
  `fz_streaminfo_contradict`.
- **overlong-coded-number** — non-minimal coded frame numbers accepted (`readConts`
  has no minimality guard). Two-way pin: `fz_overlong_utf8`.
- **channel-truncation** — silent channel truncation in `recombine`. Pin:
  `fz_self_consistent` clause-3a.
- **decoder-output-contract-stereo** & **encoder-stack-overflow** — already fixed
  upstream; keep their pins.
- **float-lpc-coefficient-divergence** — encoder Float LPC search diverges from
  exact arithmetic above 2^53 (24/32-bit); round-trip still holds. Claim-surface,
  not a correctness break. Pin: `fz_float_exact`.

## Referee discipline

- **Rebuild the libFLAC referee against 1.5.0.** The oracle is built against
  libFLAC 1.4.2; 1.5.0 changed accept-set behaviour — notably it **rejects block
  size 65536** (1.4.2 accepted it), which turns the 65536 probe into a two-sided
  pin. Version-stamp every referee-derived counter (`wide_ref_disagree`,
  `wide_ref_split`, `selfcon_channel_incoherent`, `streaminfo_bps_incoherent`,
  `decode_capacity_underalloc`, `float_exact_divergence`, `emit_si_bps`) — each is
  meaningless without its libFLAC version.
- **ffmpeg emit-side referee.** Add a third encode-side referee comparing Vinyl's
  emitted bytes to ffmpeg's FLAC encoder over the `encode/shapes` matrix, scoped
  like the existing libFLAC referee. Caveat: `Float.log2` is not correctly-rounded,
  so any host-portable byte oracle must tolerate platform drift.

## Coverage

- **Reference-lane diversity.** `fz_decode_modes` runs the List-Bool reference
  decoder only on inputs <= `VM_REF_MAX_INPUT` (8192 B, a stack-safety bound). The
  new non-canonical block-size / multichannel seeds (`decode/blocksizes`,
  `decode/multichan`) are larger, so they reach only the fast lane. To cover the
  `Frame.c`/`Subframe.c`/`Stereo.c` reference residual on those shapes, add <=8 KB
  variants of them (not a larger cap).
- **Encoder search branches.** `Encode.lpcFold7/8` stay cold behind the
  `lpcMaxOrder=6` heuristic ceiling, and `Heuristics.lpcSearch`'s multi-candidate
  loop behind the `lpcCandidates=[est]` singleton. These need a codec-side knob to
  reach and are not corpus-fixable.
- Re-run variant-merged coverage after each campaign (`make coverage`,
  `cov/per_target.py`) and confirm the new seeds' payoff.
