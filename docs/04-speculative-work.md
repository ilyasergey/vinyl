# Speculative work: when the optimizer is the attack surface

> **DRAFT — the P4 fix is in flight.** Markers of the form `TODO(fix)`
> hold places for details of the landed change (final shape, constants,
> lemma and test names, measurements). Structure and analysis are ready
> for review; the owner of the P4 round should fill, adjust, and de-draft
> this note in the same docs commit that records the fix, and add the
> README bullet.

Written after fixing audit finding P4
([issue #4](https://github.com/ilyasergey/vinyl/issues/4), the
sync-candidate storm). The previous notes covered resources spent
producing *output* ([`02-output-size-bounds.md`](02-output-size-bounds.md))
and resources reserved on a *header's word*
([`03-untrusted-sizes.md`](03-untrusted-sizes.md)). This finding is a
third shape: resources spent **guessing** — work an optimization layer
performs before any of it is known to be useful, in an amount the input's
byte *pattern* controls.

## The incident, in one paragraph

FLAC frames are self-contained but not indexed: nothing in the container
says where frame `n + 1` starts. The parallel decoder therefore guesses.
It scans the input for every offset that merely *looks* like a frame sync
code (`0xFF` then `0b111110xx`), collects each hit as a candidate, and
spawns speculative decode tasks for all of them up front (`syncScan`,
`syncCandidates`, `stepsPar`; two candidates per task). A file whose tail
is a run of `FF F8` pairs makes every second offset a candidate: a 64 MB
file yields ~32 million candidates and ~16 million task objects, all
allocated before a single candidate is parsed, and the process dies with
`std::bad_alloc`. Not one candidate was a real frame; the entire cost was
paid from guessing.

## Why the proofs don't catch it — and were designed not to

The sync scan is unverified *by design*, and that design is sound for
correctness. A candidate is only a hint: each speculative decode packages
the frame reader's own equation (`Step.ok : readFrameAt b0 d pos = some
(chs, next)`), the serial loop uses a step only when its position matches,
and `readFramesSteps_eq` collapses the whole parallel path to the serial
one **unconditionally in the candidate array**. Feed it garbage candidates
and the theorem still holds; a wrong guess costs work, never correctness.

That unconditionality is exactly the blind spot. Because the theorems
quantify over *any* candidate array, they can say nothing about its size,
and no correctness statement anywhere depends on how much was spent
producing or consuming it. This is the purest instance of the series'
theme: P1–P3 at least involved functions the proofs mention; the guessing
layer was deliberately placed outside the proof surface, and its workload
went with it. The audit's density observation makes it quantitative: real
frames cost some minimum number of bytes, so genuine sync positions have
bounded density, while the *pattern* `FF F8` has density 1/2 — a gap of
several orders of magnitude that nothing checked.

## The design that makes the fix free

The same property that hid the bug pays for the repair. Since steps are
hints validated by their own carried equations, **anything that only
removes candidates or steps cannot affect correctness** — a dropped step
just means the serial loop decodes that frame on the spot (under the
global output budget from `02`). So the guessing layer can be capped,
thinned, chunked, or abandoned for serial fallback freely, with zero proof
obligation: the same argument that let the P2 round cap speculative
precompute per chunk, applied one layer earlier at candidate gathering.

This is worth stating as the note's reusable lesson: *put speculation
behind a validation boundary that carries its own evidence, and every
resource policy on the speculative side becomes proof-free.* The converse
discipline is that such layers never get a theorem bounding their work, so
their budgets belong to the convention tier — enforced by construction,
guarded by lint and checklist, recorded here.

## The fix

`TODO(fix)` — replace with the landed shape. The suggested design from the
audit, for comparison with what landed:

- **Density cap.** A real frame needs at least `minFrameBytes` of input
  (cf. `frame_write_length_lb` from the P2 round: ≥ 80 + 8·ch bits), so
  more than `d.size / minFrameBytes`-ish candidates proves the file is
  lying about being frames. Past a multiple of that density, fall back to
  the serial loop, which is already the semantics the equations collapse
  to.
- **Task granularity.** Chunk speculative work by byte range rather than
  per candidate, so the number of task objects is bounded by input size
  over chunk size regardless of candidate density.

`TODO(fix)`: final constants and where they live; whether the cap is at
`syncCandidates` (gathering) or `stepsPar`/`byteStepsPar` (spawning) or
both; interaction with the P2 per-chunk precompute allowance; reproducer
behavior after the fix (rc, peak RSS, wall time, serial-fallback
threshold); regression test names; perf spot-check that real corpora do
not trip the density cap (they must not — density caps are only sound
when real data sits orders of magnitude below them).

## What is deliberately not proven

The cap carries no theorem, and none is possible in the current
semantics: like `03`'s capacity hint, candidate gathering affects only
execution cost, which the logic erases; unlike `03`, even the *result* it
feeds downstream is already unconditionally covered. The honest register
of this fix is the convention tier. The cost-semantics proposal
([`cost-semantics.md`](cost-semantics.md)) would change that: a charged
`Task.spawn` and per-candidate charge in `stepsPar` would make the linear
budget unprovable against the storm exactly as its §5 replays do for
P1/P3. `TODO(fix)`: link the landed cap from cost-semantics §7/§8 if the
peer note's example list is updated.

## Checklist addition for new decoder paths

To the checklists of `01`–`03`, this incident adds:

- If the path speculates, what bounds the *number* of speculative units —
  and is that bound a function of input size, not of how often an
  attacker-controlled pattern occurs?
- Is speculation behind a self-validating boundary (carried equations),
  so that thinning it is proof-free? If not, capping it will cost
  theorems.
- Does the density assumption behind any cap have provable slack against
  the format's own minimum-cost-per-unit (here: bytes per frame)?
