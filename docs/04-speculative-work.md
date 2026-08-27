# Speculative work: when the optimizer is the attack surface

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
`syncCandidates`, `stepsPar`; a fixed few candidates per task). A file
whose tail is a run of `FF F8` pairs makes every second offset a
candidate: a 64 MB file yields ~32 million candidates and ~16 million
task objects, all allocated before a single candidate is parsed, and the
process dies with `std::bad_alloc` (rc 134) after ~183 s. Not one
candidate was a real frame; the entire cost was paid from guessing.

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

Two independent caps landed, both in `Flac/Native/Decode.lean`, matching
the audit's two suggestions.

**Density bail, at gathering.** `minFrameBytes := 16` records that no
honestly framed stream carries a sync candidate denser than one per
16 bytes — a real frame is far larger (`frame_write_length_lb` gives
≥ `80 + 8·ch` bits, and that is before any subframe payload). Two places
act on it:

- `syncScan` caps each window's collected candidates at `(hi - lo) /
  minFrameBytes + 8` and stops scanning (`break`) once full, so no single
  window can allocate an array proportional to the attacker's pattern.
- `syncCandidates`, after gathering, discards the entire set —
  `if minFrameBytes * cands.size ≥ d.size then #[]` — when the density is
  impossible. An empty candidate array is not a special case downstream:
  the frame loop already decodes on the spot wherever no step is recorded,
  so `#[]` simply means "decode serially from `start`", and the first
  non-frame is rejected in O(1). The bail sits at `syncCandidates` rather
  than at each use, so both the sample path (`stepsPar`) and the byte path
  (`byteStepsPar`) inherit it from the one function they both call.

**Task-count cap, at spawning.** `maxStepTasks := 1024`, and
`stepChunkFor n := max stepChunkSize ((n + maxStepTasks - 1) /
maxStepTasks)` grows the per-task chunk so that `stepsPar` and
`byteStepsPar` spawn at most `maxStepTasks` task objects whatever the
candidate count. This is defense in depth: the density bail already
empties the pathological case, but the task cap bounds fan-out memory by
`input / chunk` for any input that *does* keep candidates, decoupling task
count from candidate count permanently. It composes cleanly with the P2
per-chunk precompute allowance (`chunkBudget`), which bounds the *output*
each surviving task may materialize; this bounds *how many* tasks there
are. Neither cap knows about the other.

The threshold has large provable slack. A frame at the smallest legal
block size still runs tens of bytes, so honest candidate density stays
well under 1/16; measured, a 1.47 MB sine gives 499 candidates against a
92 110 threshold (~185× headroom), and it decodes on the full parallel
path unchanged. The `FF F8` pattern sits at 1/2, four orders of magnitude
the other side of the line.

After the fix the audit's 64 MB storm returns a clean `DECODE ERROR` in
0.48 s at 246 MB peak RSS (from `std::bad_alloc` at ~4.1 GB after 183 s);
the 8 MB variant is instant at 32 MB. Regression tests (the P4 checks in
`bombTests`, `FlacTest/Cli.lean`): the density bail returns `#[]`,
both decoders reject the storm, honest audio keeps a nonempty candidate
set, and the task count stays `≤ maxStepTasks` for an arbitrarily large
candidate count.

## What is deliberately not proven

The cap carries no theorem, and none is possible in the current
semantics: like `03`'s capacity hint, candidate gathering affects only
execution cost, which the logic erases; unlike `03`, even the *result* it
feeds downstream is already unconditionally covered. The honest register
of this fix is the convention tier. The cost-semantics proposal
([`cost-semantics.md`](cost-semantics.md)) would change that: a charged
`Task.spawn` and a per-candidate charge in `stepsPar` would make a linear
budget unprovable against the storm exactly as its §5 replays do for
P1/P3, and the density bail is what would let the proof go through again —
the same shape as the P2 budget, one layer out.

There is also a concrete residual, worth stating plainly. The bail
discards the candidate set only *after* gathering it, and `syncScan`'s
per-window cap allows up to `d.size / minFrameBytes` candidates in total
(≈ input/16) before the discard. So peak memory on the attack is linear
in input, not O(1) — the 246 MB above is mostly the 64 MB input plus that
transient candidate array and its parallel-window pieces. A genuinely
constant-memory rejection would abort the scan the moment the first window
saturates, since one saturated window already proves the density is
impossible; that is a worthwhile tightening but changes `syncScan`'s
window-parallel structure, so it was left for when the constant matters.

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
