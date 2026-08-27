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

| # | Finding | Severity | Class | Tier | Research | Status |
|---|---------|----------|-------|------|----------|--------|
| [#1](https://github.com/ilyasergey/vinyl/issues/1) | LPC predictor divergence → GMP abort | High | Decoder DoS | T | [cost](cost-semantics.md) *(residue)* | fixed ([01](01-robustness-theorems.md)) |
| [#2](https://github.com/ilyasergey/vinyl/issues/2) | Constant-subframe decompression bomb | High | Decoder DoS | T | [cost](cost-semantics.md) *(residue)* | fixed ([02](02-output-size-bounds.md)) |
| [#3](https://github.com/ilyasergey/vinyl/issues/3) | Unvalidated `totalSamples` → 1.1 TB allocation | Med-High | Decoder DoS | C | [cost](cost-semantics.md) *(upgrade)* | fixed ([03](03-untrusted-sizes.md)) |
| [#4](https://github.com/ilyasergey/vinyl/issues/4) | Sync-candidate / task storm | Medium | Decoder DoS | C | [cost](cost-semantics.md) *(upgrade)* | fixed ([04](04-speculative-work.md)) |
| [#5](https://github.com/ilyasergey/vinyl/issues/5) | Unbounded wasted-bits count, saturating depth | Medium | Decoder DoS | T | [cost](cost-semantics.md) *(residue)*, [spec-val](spec-validation.md) *(class)* | fixed ([05](05-saturating-arithmetic.md)) |
| [#6](https://github.com/ilyasergey/vinyl/issues/6) | Many tiny frames → non-tail recursion | Medium | Decoder DoS | C | [stack](stack-semantics.md) *(upgrade)* | open ([06](06-recursion-shape.md), draft) |
| [#7](https://github.com/ilyasergey/vinyl/issues/7) | Unguarded public encoder → silent wrong value | Medium | Correctness | T | [api](api-contracts.md) *(class)* | open ([07](07-api-surface.md), draft) |
| [#8](https://github.com/ilyasergey/vinyl/issues/8) | `--encode-slow` huge channels + empty file | Medium | Encoder DoS | C | [cost](cost-semantics.md) *(upgrade)* | open ([08](08-late-guards.md), draft) |
| [#9](https://github.com/ilyasergey/vinyl/issues/9) | `toNat!` panic on bad numeric argument | Low-Med | CLI robustness | C | [api](api-contracts.md) *(class)* | open ([09](09-lint-surface.md), draft) |
| [#10](https://github.com/ilyasergey/vinyl/issues/10) | `-j` re-executes once per flag | Low | CLI robustness | C | [api](api-contracts.md) *(class)* | open ([10](10-prose-claims.md), draft) |
| [#11](https://github.com/ilyasergey/vinyl/issues/11) | `sampleRate = 0` emitted with audio | Low | Conformance | T | [spec-val](spec-validation.md) *(class)* | open ([11](11-spec-adequacy.md), draft) |

**Legend** — two orthogonal characterizations; see
[Formal-methods coverage](#formal-methods-coverage) below.

*Tier* — how the fix is secured today:

- **T** — theorem tier: secured by kernel-checked theorems using
  existing machinery; no new theory was needed.
- **C** — construction tier: enforced by code shape, lint, or test;
  the property is unstatable in the current semantics.

*Research* — which research note is relevant to the finding, and what
the proposed research would actually do for it:

- *upgrade* — make the property provable; today it rests only on code
  shape, lint, or tests.
- *residue* — the main property is already proven; the research would
  cover the informal part that is left (for example, how bounded values
  translate into bounded bytes).
- *class* — this particular bug needed no new theory to fix; the
  research is about keeping the same kind of bug from happening again.

## Formal-methods coverage

**What research would buy, per issue.** Four directions surfaced, each
with its own note:

- *Provable heap and time bounds* ([cost semantics](cost-semantics.md))
  would upgrade **#3** (the capacity hint becomes a charged allocation),
  **#4** (spawning and candidate gathering become charges the storm
  cannot pay), and **#8** (deciding a guard is charged in evaluation
  order, so guard-order bugs fail the budget proof). **#1**, **#2**, and
  **#5** were cost bugs too — the reason they rate tier **T** with only
  a *residue* role for research is that their fixes *reified the
  resource into a value* the current logic can bound: samples wrapped to
  their width (#1), output measured in sample count (#2), a read capped
  at `lim := b` (#5). The property each attack needed is excluded by
  theorem today; what remains for the cost model is only the
  value-to-bytes constant — that a 33-bit-bounded sample occupies O(1)
  memory, that `decode_size_le`'s sample count bounds resident bytes
  (02's recorded residual: a bomb still costs the budget in memory
  before its rejection) — and those value-bound theorems are precisely
  the lemmas the cost proofs would consume.
- *Provable stack depth* ([stack semantics](stack-semantics.md)) would
  upgrade **#6**: today the accumulator rewrite is pinned by equalities,
  but constant depth itself rests on syntax plus the compiler.
- *Mechanized name-to-theorem coverage*
  ([API contracts](api-contracts.md)) addresses **#7**'s class: a
  `@[covered_by]` checker makes "the natural name carries the strongest
  guarantee" a build failure instead of a review habit, and its
  perimeter corollaries absorb the lessons of **#9**/**#10**.
- *Validating the model against the standard*
  ([spec validation](spec-validation.md)) addresses **#11**'s class (and
  the accept-set half of **#5**): traceability matrix, must-reject
  corpora, referee triangulation, and an explicit accept-set predicate,
  so model-vs-RFC deviations surface at the gate instead of in audits.

**What formal methods cannot close, in principle.** No finding is beyond
formal methods entirely — each can be moved from *silent* to *checked*.
But two bindings at the edges are irreducibly informal, and several
findings bottom out in them. The *prose-to-formal binding*: no theorem
can certify that `WellFormed` means what RFC 9639's English means
(**#11**), or that a docstring's promise matches its author's intent
(**#10**) — formalization shrinks the text a human must compare, and
stops there. The *model-to-machine binding*: any cost, stack, or IO
model is adequate only up to trust in compiler, runtime, and hardware
(**#3**, **#4**, **#6**, **#8** even after the research lands); verified
compilation à la CakeML moves this boundary down to the hardware model,
never past it. Everything else about all eleven findings is, in
principle, theorem-shaped.

**What needed no new theory at all.** **#1**, **#2**, and **#5** are
fixed and theorem-secured today with machinery the project already had:
a bounding primitive plus an identity-on-valid lemma (#1), a budget
bridged to the old loops by one equation each (#2), an accept-set guard
carried through the existing simulation stack (#5). **#7** and **#11**
are the same kind — their drafts show existing theorems suffice (the
hypothesis-free checked capstone, and `some`-conditional guard
tightening) — pending their rounds. **#9** and **#10** need no theory
either, but in the opposite sense: after the fix there is nothing left
for a theorem to say about the instance; a total parser and a tested
re-exec loop are correct by construction. Their research role is *class*
only — the api-contracts perimeter rules prevent recurrence, they do not
(and need not) make anything provable.

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
- [08 — Late guards](08-late-guards.md) *(draft)*: the P8 encoder OOM —
  the rejecting check existed but ran on a data structure whose size the
  rejected parameter controls, built first; guard order as the encoder's
  version of validate-before-spending.
- [09 — Lint surface](09-lint-surface.md) *(draft)*: the P9 CLI panic —
  the shipped binary contains code outside the theorem surface *and*
  outside the merge gate's no-panic lint; the gate's scope must follow
  what the executables link.
- [10 — Prose claims](10-prose-claims.md) *(draft)*: the P10 `-j`
  re-exec growth — an `IO`-layer behavior specified only by a docstring,
  and the docstring was wrong; quantified behavioral claims need a
  checker (test or theorem) or a rewrite as description.
- [11 — Spec adequacy](11-spec-adequacy.md) *(draft)*: the P11
  `sampleRate = 0` emission — theorems correct about a model laxer than
  RFC 9639; guards tighten, `WellFormed` stays, and the deviation gets
  documented; only an external referee can see model-level gaps.

## Research notes

- [Cost semantics](cost-semantics.md): a credit-charging cost monad for
  Lean, making heap and time bounds provable for arbitrary input, with
  the two theorem shapes (pin + linear-budget sufficiency), the trusted
  residue, an adoption path, and literature. Related findings:
  - **#1** — the motivating example for value-dependent cost: bignum
    arithmetic charges by magnitude, so its budget proof consumes
    exactly the value-bound lemmas the fix introduced.
  - **#2** — the sample-count budget is proven; the recorded residual
    (a bomb still costs the budget in *memory* before rejection) is what
    a charged frame loop would bound.
  - **#3** — the motivating example for logic-invisible cost: a capacity
    hint is definitionally erased, and only a charged allocator can make
    a linear budget fail on it.
  - **#4** — charged `Task.spawn` and per-candidate charges would bound
    the speculative layer no correctness theorem mentions (§7).
  - **#5** — reading a unary field costs O(run) before any guard can see
    the value; the landed cap bounds this by construction, a charge
    would bound it by theorem.
  - **#8** — deciding a guard has a cost: the `Decidable` instance runs
    on data built first, so guard-order bugs fail a budget proof (§7).
- [Stack semantics](stack-semantics.md): making recursion depth provable.
  Four routes — reify the stack into data (trampoline), a scoped depth
  charge in the cost monad, a syntactic tail certifier, verified
  stack-cost compilation — and the principle that an erased resource
  becomes specifiable once reified as a value. Related findings:
  - **#6** — the motivating case: depth equals frame count on the
    non-tail loops, and tail-position is not even expressible in the
    logic.
  - **#5** — the reproducer overflowed the C stack *through the unary
    reader* before the guard could run; `Bits.readUnary`'s non-tail
    shape is inherited by the #6 round.
- [API contracts](api-contracts.md): the coverage bug class — proven
  properties not attached to the names users call. The four rules (guard
  by default, natural names carry the strongest guarantee, an
  API-to-theorem map at the gate, subtype escalation) and how far the
  map can be mechanized with a `@[covered_by]` checker. Related
  findings:
  - **#7** — the motivating case: the capstones cover a sibling of the
    naturally-named encoder, and out-of-envelope input round-trips to a
    different value silently.
  - **#9** — the perimeter corollary: the gate's no-panic jurisdiction
    must follow what the executables link, not where the proofs live.
  - **#10** — the other perimeter corollary: a quantified docstring
    claim is a contract with no checker; documentation must derive from
    checked artifacts or demote itself to description.
- [Spec validation](spec-validation.md): checking the model against
  RFC 9639 — the four accept/emit set relations and why the existing
  referees only tested the positive two; an RFC traceability matrix as a
  gate-checked artifact, must-reject corpora, referee triangulation, and
  an explicit accept-set predicate as the research goal. Related
  findings:
  - **#11** — the motivating case on the *emit* side: theorems correct
    about a `WellFormed` laxer than the RFC, so non-conformant files are
    emitted with every proof intact.
  - **#5** — the same gap on the *accept* side: the decoder accepted
    streams the RFC declares invalid, invisible to round-trips because
    both directions agree on the same lax model.

## See also

- [`PROGRESS.md`](../PROGRESS.md): per-session log; sessions 17+ cover
  the audit fixes.
- [`scripts/check.sh`](../scripts/check.sh): the merge gate enforcing the
  convention tier (proof hygiene, totality lint, pinned capstone names).
