# Spec adequacy: when the verified predicate is not the standard

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

As the issue proposed: the clause `bytes.size = 0 ∨ 0 < sampleRate`
(rate 0 is defensible only for empty content) landed in the guard, *not*
in `Audio.WellFormed` — and it landed once, in the shared `Pcm16ShapeOk`
predicate the P8 round introduced
([`08-late-guards.md`](08-late-guards.md)), so both CLI entry points
(`encodePcm16Fast` and `encodePcm16Cfg`) tightened together. Guards can
tighten freely under `some`-conditional theorems, so every capstone keeps
its statement; the one hypothesis this adds to the two equality-shaped
lemmas is recorded in `08`.

Scope, stated honestly: the *sample-level* checked encoders
(`Flac.encode`, `encodeCheckedCfg`) test `WellFormed` and nothing more,
so a library caller who builds an `Audio` with audio at rate 0 still gets
a stream. That is the layering decision, made deliberately:
`WellFormed`'s job is "representable as a FLAC stream" — decodability,
which rate 0 does not threaten (the round-trip holds) — while the RFC's
MUST NOT is a conformance rule about *emission*. Tightening `WellFormed`
would ripple a hypothesis through every capstone to enforce an emission
policy; the byte-level entry points (the CLI, the only place a rate
parameter arrives as untrusted input) enforce it as a guard instead. The
deviation is now written down where coverage claims live —
`COVERAGE.md`'s "Known deviations from RFC MUSTs" — which before this
round it was not.

Reproducer: `vinyl --encode audio.pcm rate0.flac 4096 1 0` now fails
cleanly (`ENCODE ERROR`, rc 1); on an empty input, rate 0 still encodes.
Regression tests: the P11 checks in `encoderGuardTests`.

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
  as part of the verification story, not as optional QA.
