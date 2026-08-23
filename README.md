# Soundproof

**A formally verified FLAC codec in pure Lean 4.**

Soundproof implements a FLAC ([RFC 9639](references/rfc9639.txt)) encoder
and decoder with no FFI, together with machine-checked proofs — the goal is
a kernel-certified losslessness theorem:

```lean
theorem Flac.decode_encode (pcm : Audio) (opts : EncoderOptions)
    (hwf : pcm.WellFormed) (hopts : opts.WellFormed pcm) :
    Flac.decode (Flac.encode pcm opts) = .ok pcm
```

quantified over *all* well-formed audio and *all* encoder settings, so every
heuristic knob (LPC order search, apodization, partition search, …) is
correctness-irrelevant by construction. The methodology mirrors
[`lean-zip`](https://github.com/kim-em/lean-zip) (verified DEFLATE):
verified reference decoder, round-trip theorem as the merge ratchet,
reference→production transfer proof, and differential fuzzing against
libFLAC/ffmpeg for interoperability.

## Status

Early days — milestone **M0 of 7** is complete (see `PLAN.md §8` for the
roadmap and `PROGRESS.md` for the session log):

- [x] **M0** — bit-level I/O with round-trip proofs, CRC-8/CRC-16,
      extended-UTF-8 coded numbers with round-trip proof, pure-Lean MD5
      (RFC 1321 suite green)
- [ ] **M1** — Rice/zigzag/escape coding + partition proofs
- [ ] **M2** — CONSTANT/VERBATIM/FIXED subframes; first `decode ∘ encode`
      theorem on a restricted profile
- [ ] **M3** — LPC + its restore proof; first heuristics
- [ ] **M4** — stereo modes, wasted bits, frames/stream; **reference
      capstone** over the full option space
- [ ] **M5** — production decoder + accept-set transfer; **shipped capstone**
- [ ] **M6** — performance work under the ratchet
- [ ] **M7** — (stretch) two-sided verification against RFC 9639

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain
(Lean 4.33.0) is pinned in `lean-toolchain`. No external Lean dependencies.

```sh
lake build          # library + proofs (no sorry, no axioms in Flac/Spec/)
lake exe flactest   # golden-vector unit tests
```

## Reading guide

- [`ARCHITECTURE.md`](ARCHITECTURE.md) — how the repository is organized
  and why (the trusted/tested split, the theorem layering L0–L6).
- [`PLAN.md`](PLAN.md) — the complete working plan: capstone statement,
  scope, theorem stack, known hard points, fuzzing/conformance rigs,
  milestones.
- [`CLAUDE.md`](CLAUDE.md) — contributor/agent workflow rules.
- [`PROGRESS.md`](PROGRESS.md) — per-session development log.
