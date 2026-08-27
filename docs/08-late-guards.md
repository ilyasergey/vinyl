# Late guards: validation after allocation, encoder edition

> **DRAFT — the P8 fix has not landed.** `TODO(fix)` markers hold places
> for the landed details. The fix owner fills them, de-drafts, adds the
> README bullet, and flips finding #8's row.

Written after fixing audit finding P8
([issue #8](https://github.com/ilyasergey/vinyl/issues/8), the
`--encode-slow` channel-count OOM). It is
[`03-untrusted-sizes.md`](03-untrusted-sizes.md)'s lesson — validate
before spending — replayed on the *encoder*, where the untrusted quantity
is a CLI parameter rather than a stream header, and with a twist: the
check that would have refused the input existed and ran. It just ran
second.

## The incident, in one paragraph

The slow encoder takes a channel count from the command line and
processes it in three stages: **(1)** a cheap sanity guard — `ch > 0`,
and the input's byte length must divide evenly into `ch` 16-bit
channels; **(2)** *build* the `Audio` value, by deinterleaving the input
bytes into `ch` per-channel sample lists; **(3)** check the built value
against `Audio.WellFormed`, whose clauses include the FLAC limit
`ch ≤ 8`. So the check that rejects an absurd channel count exists — but
it runs at stage 3, on a data structure whose *size is proportional to
that very channel count*, built at stage 2. The reproducer slips a
preposterous count past stage 1 using an **empty input file**: the
divisibility guard is `0 % (2·ch) = 0`, true for every `ch`, so
`--encode-slow empty.pcm out.flac 4096 4000000000` reaches stage 2,
where deinterleaving an empty input into 4 billion channels still
allocates one (empty) list per claimed channel — four billion cons
cells — and the process dies of OOM before the `ch ≤ 8` check ever
looks at anything. The fast path is immune only because it happens to
test `ch ≤ 8` inside its stage-1 guard; the two entry points disagree
about guard order, nothing more.

## Why the proofs don't catch it

`decodePcm16_encodePcm16Cfg` speaks only about the `some` branch, and it
is true: whenever the function answers, the answer round-trips. That a
`none` costs four billion allocations to produce is an
*evaluation-order* fact. In the model, `WellFormed` is a total predicate
on a value that simply exists; that deciding it at runtime requires the
value to be materialized first — and that construction is eager — is
below the logic's resolution, the same erasure
[`cost-semantics.md`](cost-semantics.md) §2 catalogues. The in-loop
discipline of [`01-robustness-theorems.md`](01-robustness-theorems.md)
("the check must run before the memory is spent") applies verbatim; P8
is that discipline violated by two lines being in the wrong order.

## The fix

Hoist `ch ≤ 8` into `encodePcm16Cfg`'s first guard, matching
`encodePcm16Fast`. The theorem is conditional on `some`, so a tighter
guard only moves inputs from "expensive `none`" to "cheap `none`" —
no proof moves, or at most one `if` restructuring in the round-trip
discharge. `TODO(fix)`: the landed diff, whether the guard was unified
with the fast path's (one shared guard function would prevent the two
entry points from disagreeing again), reproducer behavior, test names.

## Checklist addition

- Do all entry points that accept the same parameters run the same
  guards, in the same order? A slow/reference sibling with weaker or
  later guards is where this class lives.
- For each guard conjunct: what has already been *allocated* by the time
  it runs? Cheap conjuncts (numeric bounds) go first; conjuncts that
  need constructed data go last, and nothing bigger than the input may
  be constructed before the numeric ones pass.
- `x % 0`-style degeneracies: a modulus or divisibility guard is
  vacuously permissive on empty input; pair it with the bound it was
  standing in for.
