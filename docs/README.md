# Vinyl hardening notes

Notes from hardening Vinyl after its independent security audit
([issues #1–#12](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit)).
Numbered notes record the findings, one per fix, in fix order — a note is
marked **DRAFT** until its fix lands. Unnumbered notes are research
proposals the findings motivate.

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
| [#4](https://github.com/ilyasergey/vinyl/issues/4) | Sync-candidate / task storm | Medium | Decoder DoS | fixed ([04](04-speculative-work.md)) |
| [#5](https://github.com/ilyasergey/vinyl/issues/5) | Unbounded wasted-bits count, saturating depth | Medium | Decoder DoS | fixed ([05](05-saturating-arithmetic.md)) |
| [#6](https://github.com/ilyasergey/vinyl/issues/6) | Many tiny frames → non-tail recursion | Medium | Decoder DoS | open ([06](06-recursion-shape.md), draft) |
| [#7](https://github.com/ilyasergey/vinyl/issues/7) | Unguarded public encoder → silent wrong value | Medium | Correctness | open ([07](07-api-surface.md), draft) |
| [#8](https://github.com/ilyasergey/vinyl/issues/8) | `--encode-slow` huge channels + empty file | Medium | Encoder DoS | open |
| [#9](https://github.com/ilyasergey/vinyl/issues/9) | `toNat!` panic on bad numeric argument | Low-Med | CLI robustness | open |
| [#10](https://github.com/ilyasergey/vinyl/issues/10) | `-j` re-executes once per flag | Low | CLI robustness | open |
| [#11](https://github.com/ilyasergey/vinyl/issues/11) | `sampleRate = 0` emitted with audio | Low | Conformance | open |

## Incident notes

- [01 — Robustness theorems](01-robustness-theorems.md): the framework.
  Why a verified decoder was still killable; the taxonomy of theorem
  kinds vs bug classes; the P1 fix (wrap predictor restore to the bit
  depth, bounded on arbitrary input, identity on valid); checklist for
  new decoder paths.
- [02 — Output-size bounds](02-output-size-bounds.md): the P2
  decompression-bomb budget as a theorem (`Flac.decode_size_le`); why no
  cap separates bombs from encoded silence, so the constant is pinned by
  the encoder's provable per-frame minimum; the bridging-equation
  technique that reused the existing proofs.
- [03 — Untrusted sizes](03-untrusted-sizes.md): the P3 header-driven
  allocation — a fix no theorem could require, why the capacity cap is
  shaped the way it is, and what pins proof-invisible fixes.
- [04 — Speculative work](04-speculative-work.md): the P4 sync-candidate
  storm — resources spent guessing; why the parallel-path theorems are
  unconditional in the candidate array, and why speculation behind a
  self-validating boundary (the density bail and task cap) can be capped
  proof-free.
- [05 — Saturating arithmetic](05-saturating-arithmetic.md): the P5
  wasted-bits bomb — a functional bug wearing a DoS symptom: saturating
  `Nat` subtraction silently accepted streams the RFC rejects. The fix is
  theorem-bearing and lands in model and production identically; and
  because the offending field is unary-coded, *reading* it needed a cap
  too — a guard placed after an unbounded read fixes the accept-set and
  none of the cost.
- [06 — Recursion shape](06-recursion-shape.md) *(draft)*: the P6
  many-tiny-frames overflow — recursion depth equals frame count on the
  non-tail loops, plus an accidental quadratic; termination proofs live
  in a stack-free model, and tail-position is not even expressible.
- [07 — API surface](07-api-surface.md) *(draft)*: the P7 unguarded
  encoder — the only non-DoS finding: conditional theorems satisfied
  vacuously while the naturally-named unchecked entry point fabricates
  valid-looking streams for out-of-envelope audio; the fix is a
  namespace move, with the capstone name-pins following.

## Research notes

- [Cost semantics](cost-semantics.md): a credit-charging cost monad for
  Lean, making heap and time bounds provable for arbitrary input;
  motivated by P1/P3, with the two theorem shapes (pin + linear-budget
  sufficiency), the trusted residue, an adoption path, and literature.
- [Stack semantics](stack-semantics.md): making recursion depth provable,
  motivated by P6. Four routes — reify the stack into data (trampoline),
  a scoped depth charge in the cost monad, a syntactic tail certifier,
  verified stack-cost compilation — and the principle that an erased
  resource becomes specifiable once reified as a value.
- [API contracts](api-contracts.md): the coverage bug class, motivated by
  P7 — proven properties not attached to the names users call. The four
  rules (guard by default, natural names carry the strongest guarantee,
  an API-to-theorem map at the gate, subtype escalation) and how far the
  map can be mechanized with a `@[covered_by]` checker.

## See also

- [`PROGRESS.md`](../PROGRESS.md): per-session log; sessions 17+ cover
  the audit fixes.
- [`scripts/check.sh`](../scripts/check.sh): the merge gate enforcing the
  convention tier (proof hygiene, totality lint, pinned capstone names).
