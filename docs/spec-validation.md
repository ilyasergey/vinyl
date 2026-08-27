# Spec validation: checking the model against the standard

*A research note, motivated by audit findings P5
([`05-saturating-arithmetic.md`](05-saturating-arithmetic.md)) and P11
([`11-spec-adequacy.md`](11-spec-adequacy.md)). The other research notes
fight properties the logic cannot state
([`cost-semantics.md`](cost-semantics.md),
[`stack-semantics.md`](stack-semantics.md)) or properties proven but not
attached to what users call ([`api-contracts.md`](api-contracts.md)).
This note takes the third gap: properties stated, proven, attached — and
**untrue about the world**, because the verified model deviates from
RFC 9639. No internal check can see this by construction; the question is
how to organize the external ones so it cannot hide.*

## The gap, and why the existing referees missed it

Vinyl is not naive about this: [`conformance/`](../conformance/README.md)
already runs differential rigs against libFLAC — every Vinyl stream must
pass `flac -t` and decode byte-identically under libFLAC, libFLAC-encoded
streams must decode identically under Vinyl, the RFC's companion corpus
([flac-test-files](https://github.com/ietf-wg-cellar/flac-test-files))
gates the merge, and a fuzz rig checks totality. Two audit findings got
through all of it. Seeing why requires splitting "conformant" into four
set relations, because encoder and decoder can each deviate in each
direction:

| Relation | Meaning | Checked by | Audit result |
|---|---|---|---|
| Vinyl-emit ⊆ RFC-valid | we emit only legal streams | `flac -t` in `smoke.sh` | **broke (P11)** — the referee is itself lax: libFLAC accepts rate-0 files |
| Vinyl-emit ⊆ Vinyl-accept | our own round-trip | the capstones (kernel) | holds |
| RFC-valid ⊆ Vinyl-accept | we decode all legal streams (in scope) | `ietf.sh` subset corpus | holds within scope |
| Vinyl-accept ⊆ RFC-valid | we reject illegal streams | **nothing** | **broke (P5)** — invalid wasted-bits streams accepted on every path |

The pattern: the existing rigs test the two *positive* directions
(things that must work), and both findings sat in the *negative*
directions (things that must be refused), where there was no rig at
all — plus a second-order gap, **referee laxness**: differential testing
can never catch a deviation the reference implementation also tolerates.
Internal proofs can't help because both sides of a round-trip agree on
the same model; the model itself is the defendant.

## Route 1: an RFC traceability matrix, as a checked artifact

The assurance-engineering answer (standard since DO-178C [4]):
enumerate every MUST / MUST NOT / SHALL in RFC 9639 and map each to its
implementation — a `WellFormed` clause, a decoder guard, a theorem, or an
explicitly documented deviation. Two properties make the matrix more
than paperwork here:

- Each row can name a **Lean declaration**, and the merge gate can check
  the declaration exists — the same grep-pinning `scripts/check.sh`
  already does for capstone names. A MUST whose row is empty is visible;
  today an unimplemented MUST is silent (P11's row would have been
  empty).
- The matrix is where deviations become *decisions*: P11's "rate 0 kept
  representable in `WellFormed`, forbidden by guard" is a fine design,
  recorded; before the audit it was an accident, unrecorded.

## Route 2: negative conformance corpora

Positive corpora (files that must decode) exist; the missing rig is
files that **must be rejected**, one per rejection-bearing matrix row —
a stream with `wasted ≥ b` (P5's reproducer is exactly this, and its
regression tests are the seed), a rate-0 file with audio, oversized
counts, reserved codes. The matrix generates the corpus systematically:
every MUST NOT that the decoder enforces gets a witness file, and the
gate asserts `vinyl --decode` refuses each. This is the external mirror
of the accept-set-shrinking fixes: P5-class bugs become red tests, not
audit findings.

## Route 3: referee triangulation

`flac -t` accepting rate-0 files is not a flaw in differential testing,
only in trusting one referee. Adding a second independent decoder
(ffmpeg's, at minimum) and *mining disagreements* — any file where
Vinyl, libFLAC, and ffmpeg do not unanimously agree is a finding for
someone — is the differential-testing tradition [2, 3] applied with the
codec as one voter among three. Version-pin the referees the way the
toolchain is pinned; a referee upgrade that changes a verdict is itself
signal.

## Route 4: make the model an explicit spec, then audit the spec

The deepest fix is to shrink what a human must compare against the RFC.
Today Vinyl's accept-set is *implicit* in decoder code (and its
theorems); the research move is to characterize it: a byte-level grammar
predicate `Conformant : ByteArray → Prop` with a two-sided theorem
`decode bytes = .ok a ↔ Conformant bytes ∧ …`. Then the traceability
matrix points at clauses of one readable predicate instead of 20k lines,
RFC review becomes a finite reading task, and accept-set changes (like
P5's) show up as diffs to a spec rather than behavior changes discovered
downstream. The honest limit stands: the RFC is prose, so the final
comparison is human — every route above only narrows what the human must
hold in mind at once.

## Adoption path for Vinyl

1. Start the deviation table now — it has two rows already (P5 fixed,
   P11 pending), and [`COVERAGE.md`](../COVERAGE.md) is its natural
   host or neighbour.
2. Wire a `must-reject/` corpus into `conformance/` seeded with the P5
   and P11 reproducers; grow it row-by-row from the matrix.
3. Add ffmpeg as a second referee in `smoke.sh`; report disagreements
   between referees even where Vinyl agrees with one of them.
4. The characterization theorem (Route 4) as the research contribution,
   in dialogue with the existing `decode_ok_iff_reference` — the
   accept-set transfer already proves production = model; what remains
   is model = readable grammar.

## References

[1] RFC 9639: *Free Lossless Audio Codec (FLAC).* (The standard the
model must answer to; §8.2 is P11's clause.)

[2] W. M. McKeeman. *Differential Testing for Software.* Digital
Technical Journal 10(1), 1998. (The methodology behind
`conformance/smoke.sh`, and Route 3's disagreement mining.)

[3] X. Yang, Y. Chen, E. Eide, J. Regehr. *Finding and Understanding
Bugs in C Compilers.* PLDI 2011. (CSmith — differential testing at
scale, including the referee-disagreement economics.)

[4] RTCA DO-178C: *Software Considerations in Airborne Systems and
Equipment Certification.* 2011. (Requirements traceability as a checked
deliverable — Route 1's pedigree.)

Project-internal: [`05-saturating-arithmetic.md`](05-saturating-arithmetic.md)
and [`11-spec-adequacy.md`](11-spec-adequacy.md) (the two incidents),
[`conformance/README.md`](../conformance/README.md) (the existing
referees), `COVERAGE.md` (corpus results), and
[`api-contracts.md`](api-contracts.md) (the same gate-pinning mechanism,
applied to names instead of MUSTs).
