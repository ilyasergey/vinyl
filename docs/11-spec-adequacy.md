# Spec adequacy: when the verified predicate is not the standard

> **DRAFT — the P11 fix has not landed.** `TODO(fix)` markers hold places
> for the landed details. The fix owner fills them, de-drafts, adds the
> README bullet, and flips finding #11's row.

Written after fixing audit finding P11
([issue #11](https://github.com/ilyasergey/vinyl/issues/11),
`sampleRate = 0` emitted with audio). The lowest-severity finding and the
one with the longest reach: it is the only entry in the series where the
theorems, the code, *and* the runtime behavior are all exactly as
designed — and the design is what deviates from RFC 9639. The proofs are
correct about a model that is laxer than the standard.

## The incident, in one paragraph

`Audio.WellFormed` bounds the sample rate only from above
(`sampleRate < 2^20`, the STREAMINFO field width), so `0` is admitted,
flows into the 20-bit field, and `vinyl --encode … 0` happily reports
"encoded 4000 samples @ 0 Hz". RFC 9639 §8.2 says the sample rate MUST
NOT be 0 when the file contains audio. The audit is honest about the
blast radius: libFLAC 1.4.2 accepts such a file, so interop damage is
limited; tooling that treats rate 0 as "unknown" or "non-audio" may
misbehave. The output is simply non-conformant, with every capstone
intact — including for the offending input, which round-trips perfectly.

## Why the proofs don't catch it

`WellFormed` is the codec's *own* predicate. The capstones prove
round-trip for everything it admits, faithfully including `sr = 0`; a
theorem cannot flag that its hypothesis is wrong about the world. This is
the classic spec-adequacy gap — "the verified spec is the model, not the
standard" — and it is [`05-saturating-arithmetic.md`](05-saturating-arithmetic.md)'s
accept-set observation reflected onto the *emit*-set: P5's decoder
accepted streams the RFC rejects, P11's encoder emits them. Both
deviations were invisible to every internal check because both sides of
the round-trip agree on the same laxer model; only an external referee —
the RFC text, other implementations, conformance corpora — can see them.

## The fix

Per the issue: require `numSamples = 0 ∨ 0 < sampleRate` in the CLI and
in `encodePcm16Fast`'s guard (rate 0 is defensible only for empty
content), *without* touching `Audio.WellFormed` — guards can tighten
freely under `some`-conditional theorems, so every capstone keeps its
statement. `TODO(fix)`: the landed guard and diff, whether the checked
encoders gained the same clause, a regression test (`--encode … 0` on
nonempty input must fail cleanly; empty input may keep rate 0), and
whether the round chose to also document the `WellFormed`-vs-RFC
deviation table (see below).

The alternative — tightening `WellFormed` itself — was rejected in the
issue's framing and is worth recording why: it would ripple hypotheses
through every capstone for a clause that only constrains *emission*
policy, not decodability. The predicate's job is "representable as a
FLAC stream"; the RFC's MUST is a conformance rule about files
containing audio. Keeping them distinct is correct layering — provided
the deviation is written down, which before this round it was not.

## Checklist addition

- For every MUST/MUST NOT in the governing spec: which clause of which
  predicate (or which guard) implements it — or which documented
  deviation covers it? An unmapped MUST is a P11 waiting to be found by
  someone else's audit.
- When a hypothesis predicate (`WellFormed`) and the standard disagree,
  fix the *guards* and document the predicate, unless decodability
  itself is at stake; hypotheses ripple, guards don't.
- Internal consistency proofs (round-trips) cannot detect model-level
  deviations by construction; budget for an external referee —
  conformance files, differential runs against another implementation —
  as part of the verification story, not as optional QA. How to organize
  the referees so this class cannot hide (traceability matrix,
  must-reject corpora, referee triangulation, an explicit accept-set
  predicate) is developed in [`spec-validation.md`](spec-validation.md).
