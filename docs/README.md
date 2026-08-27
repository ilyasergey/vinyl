# Vinyl hardening notes

Notes from hardening Vinyl after its independent security audit
([issues #1–#12](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit)),
which falsified no theorem and still produced eleven findings. Numbered
notes record landed work in fix order; unnumbered notes are research
proposals.

## The findings

From the audit's tracking issue
([#12](https://github.com/ilyasergey/vinyl/issues/12)). None falsifies any
of the project's theorems: the audit exercised the round-trip capstones
(`Flac.decode_encode` and its checked/configurable variants,
`decodeReference_encode`) and the fast-path equivalence theorems
(`emitFast_eq_encode`, `decodeBytes_spec`) on the compiled binary, found
no input violating them within their stated scope, and confirmed the
axiom footprint is the standard `propext, Classical.choice, Quot.sound`.
Every finding lives in a layer the proofs do not reach.

| # | Finding | Severity | Class | Status |
|---|---------|----------|-------|--------|
| [#1](https://github.com/ilyasergey/vinyl/issues/1) | LPC predictor divergence → GMP abort | High | Decoder DoS | fixed ([01](01-robustness-theorems.md)) |
| [#2](https://github.com/ilyasergey/vinyl/issues/2) | Constant-subframe decompression bomb | High | Decoder DoS | fixed ([02](02-output-size-bounds.md)) |
| [#3](https://github.com/ilyasergey/vinyl/issues/3) | Unvalidated `totalSamples` → 1.1 TB allocation | Med-High | Decoder DoS | fixed ([03](03-untrusted-sizes.md)) |
| [#4](https://github.com/ilyasergey/vinyl/issues/4) | Sync-candidate / task storm | Medium | Decoder DoS | in progress |
| [#5](https://github.com/ilyasergey/vinyl/issues/5) | Unbounded wasted-bits count, saturating depth | Medium | Decoder DoS | open |
| [#6](https://github.com/ilyasergey/vinyl/issues/6) | Many tiny frames → non-tail recursion | Medium | Decoder DoS | open |
| [#7](https://github.com/ilyasergey/vinyl/issues/7) | Unguarded public encoder → silent wrong value | Medium | Correctness | open |
| [#8](https://github.com/ilyasergey/vinyl/issues/8) | `--encode-slow` huge channels + empty file | Medium | Encoder DoS | open |
| [#9](https://github.com/ilyasergey/vinyl/issues/9) | `toNat!` panic on bad numeric argument | Low-Med | CLI robustness | open |
| [#10](https://github.com/ilyasergey/vinyl/issues/10) | `-j` re-executes once per flag | Low | CLI robustness | open |
| [#11](https://github.com/ilyasergey/vinyl/issues/11) | `sampleRate = 0` emitted with audio | Low | Conformance | open |

See also [`PROGRESS.md`](../PROGRESS.md) (per-session log, sessions 17+)
and [`scripts/check.sh`](../scripts/check.sh) (the merge-gate lint).


- [01 — Robustness theorems](01-robustness-theorems.md): why a verified
  decoder was still killable; taxonomy of theorem kinds vs bug classes;
  the P1 fix pattern; checklist for new decoder paths.
- [02 — Output-size bounds](02-output-size-bounds.md): the P2
  decompression-bomb budget as a theorem (`Flac.decode_size_le`), and the
  bridging-equation technique that reused the existing proofs.
- [03 — Untrusted sizes](03-untrusted-sizes.md): the P3
  header-driven allocation — a fix no theorem could require, why the
  capacity cap is shaped the way it is, and what pins proof-invisible
  fixes.
- [Cost semantics](cost-semantics.md) *(research)*: a credit-charging
  cost monad for Lean to make resource bounds provable, motivated by
  P1/P3; theorem shapes, trusted residue, literature.

