# Saturating arithmetic: when totality absorbs an invalid stream

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
path (`--decode`) with an abort.

## Totality's own failure mode

The codebase's discipline is totality by construction: no `partial`, no
panicking indexing, total arithmetic. P5 is the tax on that discipline.
Total operations do not fail on malformed input; they *define behavior*
for it. Saturating `Nat` subtraction maps "the header claims more wasted
bits than the bit depth" to "decode at depth 0", a perfectly well-defined
semantics for a stream the spec rejects — and every proof stays green,
because nothing is wrong with any function. The same absorption pattern
sits behind other findings: P11 (`sampleRate = 0` accepted, since closed
on both sides) is the same disease with a milder symptom, and each `Nat`
subtraction, `getD`, `%`,
`toNat`, or truncating conversion applied to an attacker-controlled field
is a candidate instance. Where `01` said "totality is not a resource
bound", this note adds the sharper form: **totality converts validation
failures into silent semantics unless a rejection is written down
explicitly.**

The audit's note that the fast paths return rc 0 on the reproducer is
luck, not design: with depth saturated to 0 the constant sample decodes to
0 and the scale-up is cheap there. The stream is invalid either way, and
was being accepted by every path — measurably so. On a 55-byte file
holding a single CONSTANT subframe with `w = b = 16`, every one of
`--decode`, `--decode-fast` and `--decode-pcm16` returned rc 0 before the
fix and rc 1 after it. That file, not the 8 MB bomb, is the finding.

## The fix

The guard the RFC implies: after reading the unary count `k`, reject the
subframe unless `k + 1 < b` (the wasted count `w = k + 1` must leave at
least one bit of depth; `w < b` is exactly the bound the encoder's own
validity certificate `SubCfg.Valid` already carries). Two properties make
this part a pleasure rather than a chore:

- **It must land twice, identically.** `Subframe.read` (the list model)
  and `Decode.readSubframe` (the production bit reader) gained the same
  branch, or the simulation theorem pinning them (`readSubframe_sim`, and
  through it `decode_ok_iff_reference`) would break. The equivalence stack
  is not an obstacle here; it is the mechanism that guarantees the two
  decoders' accept-sets shrink in lockstep. In the proof this cost one
  `by_cases hk : k + 1 < b` in `readSubframe_sim` and one in
  `posOK_readSubframe`, each with a two-line `none` branch.
- **The round-trip pays nothing.** The encoder never emits `w ≥ b`:
  `SubCfg.Valid` requires `wasted < b`, `wastedDetect_lt` proves the
  detector respects it, and the written unary is `w - 1`, so the guard
  condition discharges from the existing hypothesis by arithmetic. In
  `Subframe.read_write` the whole diff is one extra `if_pos hwlt` in a
  `rw` chain that was already there.

Unlike `03` and `04`, whose fixes no theorem could require, this change is
*visible* to the logic — the accept-set shrinks — so it is obligated to
move the proofs and does.

### The half the guard does not cover

The draft of this note predicted the fix would be "one new `if` in each
reader". That was wrong, and its own checklist is what caught it. The
question *does every validity guard run before any computation whose cost
is a function of the guarded field?* has an uncomfortable answer when the
guarded field is unary-coded: **reading the field is itself such a
computation.** `readUnary` walks one bit per zero, so a `2^26`-bit run
costs 64 M steps before any guard exists to look at `k`. Guarding after
the read fixes the accept-set and leaves the cost exactly where it was.

Measured, on the 8 MB reproducer, with the guard alone: `--decode` went
from one abort to a different abort — `Stack overflow detected` where the
pre-fix binary had died in `shiftUp`'s bignum map. Same rc 134, same
uselessness. The bomb had simply moved upstream of the fix.

So the count is now read through a capped reader,
`Bits.readUnaryUpTo lim` and its production mirror
`BitReader.readUnaryUpTo`, called with `lim := b`. A Rice residual's
unary run needs no such cap: it is bounded by the partition that encloses
it, and `readUnary` remains right there. A wasted-bits run has no
enclosing bound at all, which is the actual content of the issue title's
"unbounded". The cap is the structural expression of that difference.

What keeps this cheap in the proofs is a single characterization lemma:

```lean
theorem readUnaryUpTo_eq (lim : Nat) (s : BitStream) :
    readUnaryUpTo lim s
      = (readUnary s).bind (fun p => if p.1 < lim then some p else none)
```

The capped reader *is* the plain reader filtered by the cap, so every
existing `readUnary` lemma carries over by rewriting, and the round-trip
obligation reduces to `readUnaryUpTo_writeUnary`, which is
`readUnary_writeUnary` plus `q < lim`. On the production side the same
role is played by `readUnaryGo_sim_lt`: the existing `readUnaryGo_sim`
required *sufficient* fuel (`8 * d.size - pos ≤ fuel`), and the capped
reader deliberately supplies insufficient fuel, so the lemma is restated
with the fuel as a cap rather than a hypothesis —

```lean
readUnaryGo d q pos fuel
  = (Bits.readUnary ((bytesToBits d).drop pos)).bind
      (fun p => if p.1 < fuel then some (q + p.1, pos + p.1 + 1) else none)
```

— which subsumes the old lemma and makes `readUnaryUpTo_sim` fall out.
That is the general shape worth keeping: **when a cost bound narrows an
operation, state the narrowed operation as the old one composed with a
filter, and the proof debt stays at one lemma.**

The two halves are not redundant. The cap makes reading the field cost
O(b); the guard is what the RFC actually says, stated where a reader can
see it. `lim := b` (rather than `b - 1`, which would make the guard
provably dead) keeps them independent on purpose.

## Measurements

Reproducer: 8 388 661 bytes, one mono CONSTANT frame, blockSize 4096,
wasted flag set, `2^26`-bit unary run. (The audit's file used blockSize
65536 and reported an out-of-memory abort; at 4096 the stack goes first.
Same shape, whichever resource runs out first.)

| | `--decode` | `--decode-fast` | `--decode-pcm16` |
|---|---|---|---|
| before | rc 134, abort, 5.1 GB, 5.5 s | **rc 0**, 30 MB, 1.3 s | **rc 0**, 30 MB, 1.4 s |
| after | rc 1, `DECODE ERROR`, 4.0 GB, 5.6 s | rc 1, 13 MB, 0.01 s | rc 1, 13 MB, 0.01 s |

The two production paths are the interesting column: rejection is now
O(1) in the run length. The reference path's 4.0 GB is not amplification
by this input — a *legitimate* 8.5 MB file costs it 4.1 GB and 103 s,
because `Stream.decodeReference` materializes the whole input as
`List Bool` by design. Per input byte the bomb is now no more expensive
than music. See "what this deliberately does not close" below.

Regressions (6 new checks, 131 total): all three decoders reject a
`w = b` file and still accept `w = b - 1` (the largest count the RFC and
`SubCfg.Valid` both allow); both readers refuse a megabit unary run. That
last pair is non-vacuous — pre-fix, `Subframe.read` on the megabit run
returned `some`.

## What this closes, and what it deliberately does not

Closed: the accept-set gap for wasted bits, on every decode path, with the
model and production decoders provably in agreement; and the cost of
reading the count, now bounded by the bit depth on every path.

A conformance lemma is now *stateable* — any stream whose subframe
declares `w ≥ b` decodes to `none` — and left as future work. It is not
free: the interesting form quantifies over whole streams, so it wants the
frame-level accept-set characterization that `decode_ok_iff_reference`
gives between the two decoders but nothing yet gives against the RFC.

Not closed: the reference path's underlying appetite. It materializes the
input as `List Bool` by design; that is a cost property of the
specification-shaped decoder, in the convention tier, and the CLI's
production paths do not share it. Reject-or-accept, the reference path costs ~480 bytes of heap per input
byte — still true, and now documented as the specification path's cost:
the P6 round rerouted the CLI's `--decode` off it. `Bits.readUnary`'s
non-tail depth, which tracked the longest run it is *allowed* to read,
is closed by the same round's `readUnaryTR` swap. Both are
[`06`](06-recursion-shape.md)'s subject, not this one's.

Also not closed: the general audit of other saturating absorptions, which
the checklist below turns into a review habit rather than a one-off sweep.

## Checklist addition for new decoder paths

To the checklists of `01`–`04`, this incident adds:

- For every total operation applied to an attacker-controlled field
  (`Nat` subtraction, `getD`, `%`, `toNat`, truncation): does it define
  behavior for values the spec rejects? If so, where is the explicit
  rejection, and is there a theorem or a certificate clause (`Valid`-style)
  witnessing that valid streams never reach it?
- Does every validity guard run *before* any computation whose cost is a
  function of the guarded field — **including the read of the field
  itself**? A variable-length field (unary, UTF-8 coded number) needs its
  bound at the reader, not after it. If the field's own encoding is
  unbounded, the bound is part of the fix, not a follow-up.
- When a cost bound narrows an operation, can the narrowed version be
  characterized as the original composed with a filter? If so, state that
  lemma first; the rest of the proof debt disappears into it.
- When an accept-set changes, does the change land identically in the
  model and production decoders, with the simulation theorem forcing the
  agreement?
