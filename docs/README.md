# Vinyl hardening notes

Documentation growing out of the independent security audit of Vinyl
([issues #1–#11](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit),
tracking [issue #12](https://github.com/ilyasergey/vinyl/issues/12)),
which falsified none of the codec's theorems and still produced eleven
findings against the running program. The notes record what each fix
taught beyond the fix itself, so the lessons survive the sessions that
learned them.

Numbered notes record *landed* work, in the order the findings were fixed;
unnumbered notes are proposals and research directions. Suggested reading
order is 01, then 02, then the research note.

## [01 — Robustness theorems](01-robustness-theorems.md)

The framework the other notes hang off. Why a decoder can be proven
correct on all valid streams and total on all input, yet be killed by a
crafted file with no theorem falsified: round-trips quantify over the
encoder's image while attackers pick from all byte strings, and the
resources they exhaust are invisible to a denotational semantics. Gives
the taxonomy mapping theorem kinds to the bug classes they exclude
(round-trip correctness, value bounds, output-size bounds, stack shape,
termination, early validation), the P1 fix pattern (a bounding primitive
such as `wrapSInt`, one theorem bounding it on *arbitrary* input, one
making it invisible on valid input), the two-tier discipline separating
kernel-checked facts from lint-enforced conventions, and a pre-merge
checklist for new decoder paths.

## [02 — Output-size bounds](02-output-size-bounds.md)

How the decompression-bomb budget (P2) became the theorem
`Flac.decode_size_le`. Starts from an impossibility that shapes any fix:
no cap separates bombs from conformant streams, because a bomb is
byte-for-byte what silence legitimately compresses to. The budget constant
is therefore pinned by the encoder's provable per-frame minimum cost
(`encode_cost_le_budget`, tightening the block-size guards from 65535 to
4608 with every capstone intact). The reusable part is the proof
technique: each budgeted frame loop is a new function bridged to the old
one by a single equation (`budgeted = old.bind check`), so the
several-thousand-line equivalence stack is consumed as-is. Ends with the
recorded residuals (rejection cost, samples versus resident bytes) and
checklist additions.

## [Shallow cost semantics](shallow-cost-semantics.md) *(research note)*

The proposal for making resource consumption itself provable, motivated by
the two findings the logic cannot even state: capacity hints are
definitionally erased (P3), and totality does not bound bignum magnitude
(P1). Sketches a credit-charging cost monad over Lean with charged
allocation and bignum primitives, and the two theorem shapes that carry
the approach: a pin to the shipped pure decoder (all capstones transfer)
and linear-budget sufficiency for arbitrary input (the anti-DoS
specification). Replays P1 and P3 as unfillable proof holes, is explicit
about the trusted residue (charging completeness, adequacy constants,
reference-count uniqueness), lists the research questions Lean's runtime
makes concrete, and gives a staged adoption path plus the relevant
literature (CakeML's verified space cost semantics, separation-logic time
credits, RAML, Danielsson's cost monad, Perceus).

## Related material elsewhere in the repository

- [`PROGRESS.md`](../PROGRESS.md): the per-session log; sessions 17
  onward cover the audit fixes these notes come from.
- [`scripts/check.sh`](../scripts/check.sh): the merge gate enforcing the
  convention tier (proof hygiene, totality lint, pinned capstone names).
- The audit findings themselves:
  [issues #1–#12](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit).
