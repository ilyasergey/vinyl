# Vinyl hardening notes

Notes from hardening Vinyl after its independent security audit
([issues #1–#12](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit)),
which falsified no theorem and still produced eleven findings. Numbered
notes record landed work in fix order; unnumbered notes are research
proposals.

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

See also [`PROGRESS.md`](../PROGRESS.md) (per-session log, sessions 17+)
and [`scripts/check.sh`](../scripts/check.sh) (the merge-gate lint).
