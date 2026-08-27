# Recursion shape: when the C stack is the resource

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
   functions — that equality is exactly what the fix proves — so no
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
computation's shape. That combination dictated the pattern the draft of
this note predicted — accumulator forms pinned by bridging equations —
but the landed mechanism is better than swapping call sites:
**`@[csimp]`**. Each converted loop gets an accumulator (tail) sibling, a
bridging equation proved by induction, and a `@[csimp]` attribute on the
equation, which makes the Lean compiler emit the tail form wherever the
original is called — while every theorem, and every *statement*, keeps
reading the structural definition. Zero proof changes anywhere in
`Flac/Spec/`; the round-trip capstones flow through untouched because
nothing they mention changed. The equations use only
`propext, Quot.sound`.

- **Loop conversions landed** (each: `<name>Acc` accumulator + `<name>TR`
  wrapper + csimp equation `<name>_eq_<name>TR`):
  - `Stream.readFrames`, `Stream.readFramesB` — the reference frame
    loops. Bridging shape:
    `readFramesBAcc b0 acc budget fuel s = (readFramesB b0 budget fuel s).map (acc.reverse ++ ·)`.
  - `Decode.readFramesStepsB` — the shipped frame loop behind
    `decodeArrays`, i.e. `--decode-pcm16`, `--decode-fast`'s fallback,
    and (since this round) `--decode`. Verified in the generated IR: the
    old body had a non-tail self-call, the new `readFramesStepsBAcc`
    compiles to a `goto` loop with zero self-calls.
  - `Stream.recombine` — as a left fold over the reversed frame list
    (`recombine = foldr` by induction, then `List.foldl_reverse`); same
    output-linear work, no depth.
  - `Bits.readUnary` — the residue [`05`](05-saturating-arithmetic.md)
    left open: a Rice-residual run can be as long as the remaining input
    (the partition bounds the *value*, not the reader's depth).
    `readUnaryUpTo` stays recursive: its depth is bounded by `lim`, which
    its one caller instantiates with the bit depth (≤ 32).
  - *Not* converted: `Decode.readFrames` / `readFramesAt` /
    `readFramesSteps`, the intermediate forms of the parallel-path
    equivalence proof — no shipped entry point executes them
    (`decodeArrays` runs the budgeted loop), and converting proof-layer
    forms buys no runtime property.
- **The quadratic.** Not threaded away — the remaining-length parameter
  would have to flow through every reader `withConsumed` wraps, and the
  per-bit `List Bool` (~480 bytes of heap per input byte, measured in the
  P5 round) is the reference decoder's *purpose*: it is the
  specification-shaped path. The stance taken instead: **the CLI's
  `--decode` now decodes with `Flac.Decode.decodeOption`**, which
  `decodeOption_eq_reference` proves *pointwise equal* to
  `Stream.decodeReference` — same accept-set, same samples, at the
  production decoder's cost — and the reference decoder is no longer
  something the CLI runs on untrusted input. `scripts/check.sh`'s
  call-site pin and the `FlacTest/Capstones.lean` table moved in step.

Note the division of labor: the equalities are real kernel-checked
theorems and the round-trip capstones flow through them untouched, yet
**none of them states the property being bought**. Constant stack depth
is delivered by the syntactic shape of the new definitions plus the
compiler's tail-call behavior — the convention tier again, now with a
proof-carrying escort. The trusted residue is "Lean compiles self-tail
recursion to a jump, and applies csimp replacements", which the IR check
above spot-verified once.

**Reproducer behavior.** On a 3.1 MB file of 200,000 tiny CONSTANT
frames: `--decode` went from *still churning after 60 s* (killed) to
0.19 s; `--decode-pcm16` and `--decode-fast` round-trip it in ~0.15 s. A
7,000,000-frame file (117 MB) decodes via `--decode-pcm16` in 8.0 s, the
same wall time the old loop took where it survived — so the accumulator
forms cost nothing measurable. One platform honesty note: macOS runs the
Lean main function on a large (~1 GB) stack, so the *crash* needs ~8M
frames there (measured with a minimal probe); on a true 8 MB stack —
the audit's environment — depth-equals-frame-count died at the tens of
thousands of frames the reproducer packs. The IR-level check is the
platform-independent verification.

Regression tests: `recursionShapeTests` in `FlacTest/Cli.lean` — 100k
tiny frames round-trip through the production decoder, 500 frames through
the reference decoder, and a megabit unary run through `Bits.readUnary`.

## What is deliberately not proven

That the compiled loops run in constant stack. The logic cannot state it
(erasure 2 above), so the guarantee rests on: definitions in syntactic
tail form, the Lean compiler's tail-call compilation, and the merge gate —
which now grep-pins the five `@[csimp]` swap names, so a refactor cannot
silently drop one and revert a loop to stack-frame-per-frame. A real
syntactic tail *certifier* (elaborator-level, rejecting non-tail
recursion in decode paths at build time) remains the open mechanization,
and a cost semantics with a stack-depth charge
([`cost-semantics.md`](cost-semantics.md) §7 "Stack as a resource") would
make depth a theorem, with the compiler's tail-call behavior as the
residual adequacy assumption; the full design space — that route,
trampoline reification of the stack into data, the syntactic certifier,
and verified stack-cost compilation — is
[`stack-semantics.md`](stack-semantics.md).

## Checklist addition for new decoder paths

To the checklists of `01`–`05`, this incident adds:

- Is every loop whose iteration count the input controls in syntactic
  tail form (accumulator style)? "Fuel-bounded" answers termination, not
  depth.
- Does any per-iteration step call a function whose cost is proportional
  to the remaining input (`List.length`, slicing, re-scanning)? Carry the
  quantity instead — or, when the cost is the specification path's shape,
  route the shipped entry point through a proven-equal cheaper form.
- When converting a proven loop, pin the new form with a bridging
  equation rather than re-proving the stack — and prefer `@[csimp]` on
  the equation to editing call sites: theorems keep the structural form,
  the compiler gets the tail form, and no proof anywhere moves
  (`readFramesB_eq_readFramesBTR` is the worked example; `readFramesB` in
  [`02`](02-output-size-bounds.md) did the same job by hand).
