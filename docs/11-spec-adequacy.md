# Spec adequacy: when the verified predicate is not the standard

Written after audit finding P11
([issue #11](https://github.com/ilyasergey/vinyl/issues/11),
`sampleRate = 0` emitted with audio). The lowest-severity finding and the
one with the longest reach: at the time it was the only entry in the
series where the theorems, the code, *and* the runtime behavior were all
exactly as designed — and the design was what deviated from RFC 9639, so
the proofs were correct about a model laxer than the standard.

**Update (2026-09-11): the deviation is now closed, and the original fix
below was superseded.** `0 < a.sampleRate` was added to `Audio.WellFormed`
and a `0 < sr` guard to both `readStreamInfo` twins, so the model no
longer deviates on this point and the *decoder* now rejects rate 0 as
well — a fuller fix than the guard-only one first chosen. The ripple
through the capstones that the analysis below judged not worth paying
turned out to be tractable, following the `4 ≤ bps` change as a template
(both are STREAMINFO-field tightenings of the same shape). The analysis is
kept because the *lesson* — a verified predicate can be laxer than the
standard, and no internal round-trip check can see it — outlives the
instance, and because the reversal of the original decision is instructive
in its own right: "hypotheses ripple, so don't tighten them" is true only
until a template makes the ripple cheap.

## The incident, in one paragraph

*(As it stood before the closure above.)* `Audio.WellFormed` bounded the
sample rate only from above (`sampleRate < 2^20`, the STREAMINFO field
width), so `0` was admitted, flowed into the 20-bit field, and
`vinyl --encode … 0` happily reported "encoded 4000 samples @ 0 Hz".
RFC 9639 §8.2 says the sample rate MUST NOT be 0 when the file contains
audio. The audit is honest about the
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

It was fixed in two stages, and the second reversed the first's
architectural call.

**First — the guard-only fix.** The clause `bytes.size = 0 ∨ 0 < sampleRate`
landed in the shared `Pcm16ShapeOk` guard the P8 round introduced
([`08-late-guards.md`](08-late-guards.md)), so both CLI entry points
(`encodePcm16Fast`, `encodePcm16Cfg`) rejected rate 0 on nonempty input.
`Audio.WellFormed` was left admitting it, on the argument that
`WellFormed`'s job is decodability (which rate 0 does not threaten — the
round trip holds), that the RFC's MUST NOT is an *emission* rule, and that
tightening the hypothesis would ripple through every capstone.

**Second (2026-09-11) — the closure.** That argument was revisited and the
bound moved into the model after all: `0 < a.sampleRate` in
`Audio.WellFormed`, `Pcm16ShapeOk` tightened from the disjunction to an
unconditional `0 < sampleRate`, and — the part the guard-only fix never
reached — a `0 < sr` guard in **both `readStreamInfo` twins**, so the
*decoder* rejects a rate-0 stream from any source, not only ones this
encoder would have produced. The capstone ripple was real but tractable:
it followed the `4 ≤ bps` change exactly (STREAMINFO-field tightenings of
the same shape). `some`-conditional statements tolerate a tighter
hypothesis, and the hypothesis-free capstones extract `WellFormed` from a
successful encode, so they needed no change. IETF must-decode stays
61/61 — nothing valid is rejected. The deviation row in `COVERAGE.md` now
reads *no longer a deviation*.

Reproducer: `vinyl --encode audio.pcm rate0.flac 4096 1 0` fails cleanly
(`ENCODE ERROR`, rc 1), and a rate-0 stream now fails to *decode* as well.
Regression tests: the P11 checks in `encoderGuardTests`.

## Checklist addition

- For every MUST/MUST NOT in the governing spec: which clause of which
  predicate (or which guard) implements it — or which documented
  deviation covers it? An unmapped MUST is a P11 waiting to be found by
  someone else's audit.
- When a hypothesis predicate (`WellFormed`) and the standard disagree,
  fixing the *guards* and documenting the predicate is the cheap option —
  but it only constrains *emission*, never the decoder, and it leaves the
  model deviating. If a template exists for tightening the predicate (a
  prior field-bound change of the same shape, as `4 ≤ bps` was for
  `0 < sampleRate`), the capstone ripple is usually mechanical and worth
  paying, because tightening the predicate is the only option that also
  makes the decoder reject the non-conformant input. Hypotheses ripple;
  a worked template makes the ripple cheap.
- Internal consistency proofs (round-trips) cannot detect model-level
  deviations by construction; budget for an external referee —
  conformance files, differential runs against another implementation —
  as part of the verification story, not as optional QA.
