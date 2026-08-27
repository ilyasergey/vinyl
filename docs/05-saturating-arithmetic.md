# Saturating arithmetic: when totality absorbs an invalid stream

> **DRAFT — the P5 fix has not landed.** Markers of the form `TODO(fix)`
> hold places for details of the landed change (guard placement, lemma
> diffs, test names, reproducer measurements). Structure and analysis are
> ready for review; the owner of the P5 round should fill, adjust, and
> de-draft this note in the docs commit that records the fix, and add the
> README bullet.

Written after fixing audit finding P5
([issue #5](https://github.com/ilyasergey/vinyl/issues/5), the
wasted-bits bomb). This note differs from its neighbours in kind. Notes
[`02`](02-output-size-bounds.md)–[`04`](04-speculative-work.md) record
resource bugs the logic could see only partially or not at all; P5's
resource symptom is a disguise. The root cause is **functional**: the
decoder's accept-set is larger than RFC 9639's, because a total,
saturating operation quietly gave meaning to a field value the spec
declares invalid. Unlike the capacity hint of `03` or the candidate cap of
`04`, the fix here is observable, theorem-bearing, and fully enforceable
in the logic — the rejection-completeness flavour of early validation from
[`01`](01-robustness-theorems.md)'s taxonomy.

## The incident, in one paragraph

Wasted bits (RFC 9639 §9.2.2) are a micro-optimization: when all samples
in a subframe share `w` trailing zero bits, the encoder stores them scaled
down at bit depth `b - w` and records `w` in the subframe header as a
unary run. The decoder reads the run (`k` zeros then a one, `w = k + 1`),
decodes at depth `b - w`, and shifts back up. Two absences stack: nothing
bounds `k` (a unary run can be as long as the file), and the reduced depth
is computed as `b - (k + 1)` in `Nat`, whose subtraction **saturates to
zero** instead of failing. The RFC declares `w ≥ b` invalid; Vinyl instead
decoded at depth 0 and then scaled by `2^w`. An 8 MB file with one
CONSTANT subframe and a `2^26`-bit unary run kills the reference decode
path (`--decode`) with an out-of-memory abort.

## Totality's own failure mode

The codebase's discipline is totality by construction: no `partial`, no
panicking indexing, total arithmetic. P5 is the tax on that discipline.
Total operations do not fail on malformed input; they *define behavior*
for it. Saturating `Nat` subtraction maps "the header claims more wasted
bits than the bit depth" to "decode at depth 0", a perfectly well-defined
semantics for a stream the spec rejects — and every proof stays green,
because nothing is wrong with any function. The same absorption pattern
sits behind other findings: `TODO(fix)`: cross-check phrasing — P11
(`sampleRate = 0` accepted) is the same disease with a milder symptom, and
each `Nat` subtraction, `getD`, `%`, `toNat`, or truncating conversion
applied to an attacker-controlled field is a candidate instance. Where
`01` said "totality is not a resource bound", this note adds the sharper
form: **totality converts validation failures into silent semantics unless
a rejection is written down explicitly.**

The audit's note that the fast paths return rc 0 on the reproducer is
luck, not design: with depth saturated to 0 the constant sample decodes to
0 and the scale-up is cheap there. The stream is invalid either way, and
was being accepted by every path.

## The fix

The guard the RFC implies: after reading the unary count `k`, reject the
subframe unless `k + 1 < b` (the wasted count `w = k + 1` must leave at
least one bit of depth; `w < b` is exactly the bound the encoder's own
validity certificate `SubCfg.Valid` already carries). Two properties make
this fix a pleasure rather than a chore:

- **It must land twice, identically.** `Subframe.read` (the list model)
  and `Decode.readSubframe` (the production bit reader) must gain the same
  branch, or the simulation theorem pinning them (`readSubframe_sim`, and
  through it `decode_ok_iff_reference`) breaks. The equivalence stack is
  not an obstacle here; it is the mechanism that guarantees the two
  decoders' accept-sets shrink in lockstep.
- **The round-trip pays nothing.** The encoder never emits `w ≥ b`:
  `SubCfg.Valid` requires `wasted < b`, `wastedDetect_lt` proves the
  detector respects it, and the written unary is `w - 1`, so the guard
  condition discharges from the existing hypothesis by arithmetic.
  `TODO(fix)`: confirm the actual proof diff — expected to be one new
  `if` in each reader, a matching branch in `readSubframe_sim`, and one
  `omega`-sized discharge in `Subframe.read_write`.

Unlike `03` and `04`, whose fixes no theorem could require, this change is
*visible* to the logic — the accept-set shrinks — so it is obligated to
move the proofs and does. Order matters at the site: the guard must run
before anything whose cost depends on `k` (in particular before
`shiftUp (k + 1)`, whose scale factor `2^(k+1)` is itself a `k`-bit
allocation); with the guard, `w ≤ 32` and every downstream cost is small.
`TODO(fix)`: confirm guard-before-shiftUp placement in both readers.

`TODO(fix)`: reproducer behavior after the fix (expected: clean
`DECODE ERROR` on all three modes, small peak RSS), regression test names,
and check counts.

## What this closes, and what it deliberately does not

Closed: the accept-set gap for wasted bits, on every decode path, with the
model and production decoders provably in agreement. A conformance lemma
is now *stateable* (any stream whose subframe declares `w ≥ b` decodes to
`none`) — `TODO(fix)`: state it if cheap, or record it as future work.

Not closed: the reference path's underlying appetite (it materializes the
input as `List Bool` by design; that is a cost property of the
specification-shaped decoder, in the convention tier, and the CLI's
production paths do not share it), and the general audit of other
saturating absorptions, which the checklist below turns into a review
habit rather than a one-off sweep.

## Checklist addition for new decoder paths

To the checklists of `01`–`04`, this incident adds:

- For every total operation applied to an attacker-controlled field
  (`Nat` subtraction, `getD`, `%`, `toNat`, truncation): does it define
  behavior for values the spec rejects? If so, where is the explicit
  rejection, and is there a theorem or a certificate clause (`Valid`-style)
  witnessing that valid streams never reach it?
- Does every validity guard run *before* any computation whose cost is a
  function of the guarded field?
- When an accept-set changes, does the change land identically in the
  model and production decoders, with the simulation theorem forcing the
  agreement?
