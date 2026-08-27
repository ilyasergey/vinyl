# Recursion shape: when the C stack is the resource

> **DRAFT — the P6 fix has not landed.** Markers of the form `TODO(fix)`
> hold places for details of the landed change (which loops were
> converted, bridging lemma names, test names, measurements). Structure
> and analysis are ready for review; the owner of the P6 round should
> fill, adjust, and de-draft this note in the docs commit that records
> the fix, and add the README bullet.

Written after fixing audit finding P6
([issue #6](https://github.com/ilyasergey/vinyl/issues/6), the
many-tiny-frames hang and stack overflow). The resource this time is
neither output ([`02`](02-output-size-bounds.md)) nor a reservation
([`03`](03-untrusted-sizes.md)) nor speculation
([`04`](04-speculative-work.md)): it is the **C call stack**, plus an
accidental quadratic. Both are properties of *how* the loops compute, not
of what they compute — the purest case so far of two functions the logic
considers interchangeable behaving asymptotically differently at runtime.

## The incident, in one paragraph

A FLAC frame can be as small as ~13 bytes, and frame count is
attacker-chosen: a ~900 KB file holds 70,000 valid tiny CONSTANT frames.
The frame loops on the reference and pcm16 paths have the shape

```
match readFrame … with
| some (chs, rest) => … (chs :: readFrames rest …)   -- cons AFTER the call
```

so each pending frame keeps a native stack frame alive: recursion depth
equals frame count, and enough frames overrun the default 8 MB stack
(SIGSEGV). Before that limit is even reached, the reference path churns:
it recomputes `List.length` per frame inside `skipBits`/`withConsumed`
(O(n²) over the stream) and materializes the entire input as a
`List Bool`. The reproducer never finishes on `--decode`, and higher
frame counts kill `--decode-pcm16` on the stack. `--decode-fast` is
unaffected: its byte-path loop (`readBytesSteps`) was already written in
accumulator form.

## Why the proofs don't catch it

Termination is proved by fuel: every loop consumes a `Nat` that strictly
decreases, in a model with no stack and no cost. Three separate erasures
stack up:

1. **"Terminates" is not "fits in 8 MB".** Fuel bounds the *number* of
   recursive calls, not the native frames simultaneously live. The
   difference between a tail call and a cons-after-return is precisely
   the difference the operational stack sees and the denotation does not.
2. **Tail-position is not even expressible.** `readFrames` in
   accumulator form and in cons-after-return form are provably equal
   functions — that equality is exactly what the fix will prove — so no
   theorem about either can distinguish them. Whether a syntactic tail
   call *compiles* to a jump is then the Lean compiler's decision,
   outside the logic entirely.
3. **Cost of auxiliary operations is invisible.** `List.length` per frame
   is a defined total function; nothing says it is O(n) each time, called
   n times.

This is the "stack shape" row of [`01`](01-robustness-theorems.md)'s
taxonomy, previously covered only by style. The existing merge-gate lint
bans `partial` — which guards *termination*, and is satisfied by every
one of the offending loops. Nothing guarded *depth*.

## The fix

Unlike `03` and `04`, this fix does touch proven functions: the frame
loops appear throughout the equivalence stack. And unlike `05`, it must
not change any observable value — same accept-set, same output, only the
computation's shape. That combination dictates the pattern, the same one
that carried the P2 budget
([`02`](02-output-size-bounds.md)): write the accumulator form as a new
function and pin it to the old one with a bridging equation, consuming
the existing lemma stack unchanged.

- **Loop conversion.** `readFrames` / `readFramesAt` / `readFramesSteps`
  and `recombine` move to accumulator (tail-recursive) form, as
  `readBytesSteps` already demonstrates; the bridging lemma has the shape
  `readFramesTR acc … = acc ++ readFrames …`. `TODO(fix)`: actual
  function and lemma names, and whether the top-level decoders swap
  wholesale or per path.
- **The quadratic.** The reference path carries the remaining length as a
  parameter instead of recomputing `List.length` per frame.
  `TODO(fix)`: where the length is threaded, and whether `withConsumed`
  changed shape or gained a counted variant with its own equation.
- **The `List Bool` appetite.** Materializing the input per-bit is the
  reference decoder's *purpose* — it is the specification-shaped path —
  so it stays; `TODO(fix)`: record whatever stance the round takes (keep
  `--decode` as the spec path with documented cost, or route the CLI's
  `--decode` through a verified-equal cheaper form). For scale: the P5
  round measured the reference path at roughly 480 bytes of heap per
  input byte.
- **Sites inherited from the P5 round.** `Bits.readUnary` is itself
  non-tail-recursive — discovered when P5's `2^26`-bit unary run
  overflowed the stack *through the reader* before any guard could see
  the count (see [`05-saturating-arithmetic.md`](05-saturating-arithmetic.md),
  "the half the guard does not cover"). P5 capped the one unbounded call
  site (`readUnaryUpTo`, `lim := b`), but Rice-residual unary runs on the
  list path still go through the uncapped reader, and a crafted partition
  can make a run as long as the remaining input: partition structure
  bounds the *value*'s cost in the budget, not the reader's recursion
  depth. `TODO(fix)`: convert `Bits.readUnary` to accumulator form (or
  record why its depth is acceptably bounded), and audit the other
  list-path bit readers for the same shape.

Note the division of labor: the equalities are real kernel-checked
theorems and the round-trip capstones flow through them untouched, yet
**none of them states the property being bought**. Constant stack depth
is delivered by the syntactic shape of the new definitions plus the
compiler's tail-call behavior — the convention tier again, now with a
proof-carrying escort.

`TODO(fix)`: reproducer behavior after the fix (expected: `--decode`
completes in seconds linearly, `--decode-pcm16` flat stack at any frame
count), regression test names and counts, perf spot-check that the
accumulator forms did not regress the fast path.

## What is deliberately not proven

That the compiled loops run in constant stack. The logic cannot state it
(erasure 2 above), so the guarantee rests on: definitions in syntactic
tail form, the Lean compiler's tail-call compilation, and the merge-gate
lint. `TODO(fix)`: if the lint gains a depth-shape check (e.g. grep for
cons-after-recursive-call patterns in decode paths, or a required
`-- tail` marker), record it here. A cost semantics with a stack-depth
charge ([`cost-semantics.md`](cost-semantics.md), §7 "Stack as a
resource") would make depth a theorem, with the compiler's tail-call
behavior as the residual adequacy assumption; the full design space —
that route, trampoline reification of the stack into data, a syntactic
tail certifier, and verified stack-cost compilation — is
[`stack-semantics.md`](stack-semantics.md).

## Checklist addition for new decoder paths

To the checklists of `01`–`05`, this incident adds:

- Is every loop whose iteration count the input controls in syntactic
  tail form (accumulator style)? "Fuel-bounded" answers termination, not
  depth.
- Does any per-iteration step call a function whose cost is proportional
  to the remaining input (`List.length`, slicing, re-scanning)? Carry the
  quantity instead.
- When converting a proven loop, pin the new form with a bridging
  equation rather than re-proving the stack (`readFramesB` in `02` and
  `TODO(fix)` here are the worked examples).
