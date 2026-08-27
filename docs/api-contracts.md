# API contracts: binding theorems to the names users call

*A research note, extracted from
[`07-api-surface.md`](07-api-surface.md) (audit finding P7, the unguarded
public encoder). The incident note records what happened and how it was
fixed; this note develops the methodology — how a verified library keeps
its guarantees attached to the identifiers people actually reach for, and
how much of that discipline can be mechanized.*

## The bug class: coverage

The taxonomy of [`01-robustness-theorems.md`](01-robustness-theorems.md)
asks, property by property, "is it proven?" P7 exposed an orthogonal
question: **is the proven property attached to what users touch?** Call
this a *coverage* bug. Every theorem in the library was true; the natural
name (`Stream.encode`, docstring "The encoder") pointed at a function the
theorems cover only under a hypothesis the caller was never asked to
hold, and out-of-envelope input round-tripped to a different value with
no signal. Nothing in a proof assistant polices this: "formally verified"
is a set of named theorems about specific functions, while users bind the
claim to whatever identifier is shortest. The gap between the two is API
design, and no kernel checks API design.

Coverage bugs are worth distinguishing from precondition bugs. The
precondition (`Audio.WellFormed`) was correct, decidable, documented, and
even runtime-checked — in a *sibling* function. What failed was the
binding: guarantee and name had parted ways.

## The discipline

Four rules, ordered by how much they cost the API author.

1. **Precondition-as-guard by default.** Every public entry point checks
   its precondition at runtime and returns `Option`/`Except`; `none` is
   the precondition's voice. The conditional theorem lives *behind* the
   guard, repackaged as a hypothesis-free statement about the guarded
   function — Vinyl's `decode_encodeChecked` ("any `some` result
   round-trips") is the model. Corollary: preconditions should be kept
   **decidable** as a matter of API design, not merely proof convenience;
   decidability is what makes the guard free to write and the
   hypothesis-free capstone possible.

2. **The natural name carries the strongest guarantee.** Unchecked
   variants have legitimate users — proofs, and callers who provably own
   the precondition — but they live in a namespace that says so
   (`Unchecked`, `Internal`), never on the shortest path. Two smells that
   this rule is violated: a docstring claiming more than any theorem that
   mentions the function by name, and a checked wrapper whose name is
   *longer* than its unchecked sibling (`encodeChecked` next to `encode`
   inverts the safe default — the convenient spelling should be the
   guarded one).

3. **Maintain an API-to-theorem map, and check it at the gate.** For each
   exported entry point: which theorem covers *this name* — not a
   sibling — and is it hypothesis-free? The map is finite, auditable, and
   exactly what a security reviewer reconstructs by hand (the P7 audit
   entry is that reconstruction). Vinyl's merge gate already pins that
   CLI branches call the functions the capstones are about; the same
   mechanism extends to the library surface.

4. **Escalate to types when values live long.** The stronger form makes
   the precondition unrepresentable: a subtype
   (`{a : Audio // a.WellFormed}`) with a smart constructor, so the check
   runs once and the type carries it thereafter — "parse, don't validate"
   [2]. Worth it when callers hold values across many calls; the `Option`
   guard is the lighter default. (The subtype also composes with rule 3:
   the theorem about the subtyped function is hypothesis-free by
   construction.)

## Mechanizing the map

Rule 3 is where research-grade leverage lives, because the map can be
made a checked artifact instead of a document. In increasing strength:

- **Gate greps** (available today): the convention tier. A block in
  `scripts/check.sh` lists each public name with the theorem covering it
  and fails when either side of a pair disappears — cheap, and already
  the house style for pinned capstone names.
- **An annotation checked by metaprogram.** An attribute, say
  `@[covered_by decode_encodeChecked]`, on every exported definition in
  the library root; an elaborator-level checker walks the public
  namespace and fails the build if an exported name lacks either a
  `covered_by` pointing at an existing theorem *whose statement mentions
  that name*, or an explicit `Unchecked`-namespace location. The
  statement-mentions check is the substance: it is what prevents the
  annotation from silently pointing at a sibling's theorem — the exact
  failure mode P7 embodies. All of this is ordinary Lean metaprogramming
  over the environment; nothing needs upstream support.
- **Derived documentation.** The same metaprogram emits the
  API-to-theorem map as a doc page, so the human-readable contract table
  and the checked one cannot drift apart.

The limit of mechanization is semantic: a checker can verify that *some*
theorem mentions the name and has no hypotheses, not that the theorem
says what the docstring promises. The residue — does `decode_encodeChecked`
mean "round-trips"? — stays with the reader, which is one more reason
theorem statements, not prose, should be the API reference of record.

## Relation to the resource notes

The resource notes ([`cost-semantics.md`](cost-semantics.md),
[`stack-semantics.md`](stack-semantics.md)) fight properties the logic
*cannot state*. Coverage is the opposite corner: everything is stateable
and already proven, and the entire failure is in presentation. That makes
it the cheapest class in the series to eliminate — no new semantics, no
instrumentation, one namespace move and a gate check — and the most
embarrassing to ship, since the fix was always one rename away.

## References

[1] B. Meyer. *Applying "Design by Contract".* IEEE Computer 25(10),
1992. (Preconditions as first-class API contracts; the guard/hypothesis
distinction in its original habitat.)

[2] A. King. *Parse, don't validate.* 2019.
(https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/ —
the subtype/smart-constructor escalation of rule 4.)

[3] E. Brady. *Type-Driven Development with Idris.* Manning, 2017.
(Making illegal states unrepresentable as a design method, the general
form of rule 4.)

Project-internal: [`07-api-surface.md`](07-api-surface.md) (the incident
and the landed fix), [`01-robustness-theorems.md`](01-robustness-theorems.md)
(the taxonomy this adds the coverage row to), `scripts/check.sh` (the
gate the checks extend), `Flac/Spec/Decode.lean`
(`decode_encodeChecked`, the hypothesis-free capstone shape rule 1
generalizes).
