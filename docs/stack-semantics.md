# Stack semantics: making recursion depth provable

*A research note, companion to [`cost-semantics.md`](cost-semantics.md).
That note develops provable bounds for heap and time; this one takes the
resource that resists the same treatment hardest — the native call
stack — using audit finding P6
([issue #6](https://github.com/ilyasergey/vinyl/issues/6), the
many-tiny-frames stack overflow, recorded in
[`06-recursion-shape.md`](06-recursion-shape.md)) as the motivating case.*

## Why the stack is harder than the heap

For heap cost the obstacle is *erasure*: the logic sees values, not the
bytes spent building them, so a cost model must add the bytes back as
credits. The stack has a sharper obstacle: **the distinction that matters
is not merely uncounted but unstatable.** The two frame loops

```
readFrames s   = … (chs :: readFrames s')        -- cons after the call
readFramesTR a s = readFramesTR (a ++ chs) s'    -- accumulator, tail call
```

are provably equal functions — proving exactly that equality is how the
P6 fix keeps the capstones — so no proposition about either can separate
them. Whether a call occupies a native frame is decided by its *syntactic
position* and by the compiler's tail-call handling, two things the
denotation forgets by design. Any formal treatment has to smuggle the
distinction back in. There are four ways, ordered by how much they can be
adopted today.

## Route 1: reify the stack into data (by-construction spec)

Forbid raw recursion in input-driven loops. Provide one combinator, a
trampoline:

```lean
inductive Step (σ α : Type) | continue (s : σ) | done (a : α)

def loop (f : σ → Step σ α) : σ → Nat → Option α   -- fuel, self-tail-recursive
```

Constant stack is then a property of *one* definition, audited once;
every loop written through it inherits the property by construction,
because the combinator's vocabulary cannot express a non-tail call. A
computation that genuinely needs depth must carry an explicit stack
inside `σ` — heap data, visible to the logic, so a depth bound becomes an
ordinary theorem about a list's length, and the output-size budget of
[`02-output-size-bounds.md`](02-output-size-bounds.md) can price it.

This is the note's central principle, and it generalizes past stacks:
**an erased resource becomes specifiable the moment it is reified as a
value.** The trampoline is defunctionalized control (Reynolds [4]); the
accumulator loops the P6 fix introduces are its degenerate case with
`σ` = the accumulator. The trusted residue shrinks to "the one combinator
compiles to a jump."

## Route 2: a depth charge in the cost monad (theorem route)

Extend the shallow embedding of [`cost-semantics.md`](cost-semantics.md).
Stack differs from credits in shape: it is *scoped* — consumed on entry,
released on return — so the primitive is a bracket, not a `charge`:

```lean
def deeper : CostM α → CostM α   -- +1 depth inside, tracks the running max
```

Discipline: every recursive call not in tail position is wrapped. Then
`maxDepth (decodeC bytes) ≤ D` for arbitrary `bytes` is a plain theorem:
unprovable for the cons-after-return loop (depth grows with frame count —
the P6 bug becomes a proof hole, exactly like the P1/P3 replays in the
cost note), trivial for the accumulator form. The same monad's time
charges also catch P6's second half: pricing `List.length` linearly makes
the per-frame recomputation a quadratic total, which no linear budget
discharges.

The adequacy problem is sharper here than for heap: *where the wraps go*
is defined by what the compiler will turn into a jump, so the
instrumentation itself encodes a claim about the compiler. That coupling
is what makes this a research question rather than an afternoon's work.

## Route 3: a syntactic certifier (formal, not semantic)

Lean's metaprogramming can decide tail shape mechanically: an attribute
(say `@[tail_shape]`) whose elaborator walks the definition and fails on
any recursive occurrence in non-tail position. It proves nothing about
semantics, but it runs on every build, upgrades the convention tier from
"reviewers watch for it" to "elaboration rejects it", and pairs with the
documented compiler contract that self-tail-calls compile to jumps. This
is the cheapest mechanism that would have caught P6 at commit time, and
it fits the merge gate that already rejects `partial` and panicking
indexing.

## Route 4: a verified compiler with a stack cost semantics (gold standard)

End-to-end versions exist outside Lean: CakeML's verified space cost
semantics covers stack as well as heap [1], and Quantitative CompCert
proves stack-space bounds down to assembly [2]. There, "the compiled
decoder runs in N bytes of stack" is a theorem about the machine
artifact with no compiler trust left. Lean has no counterpart, and
building one is out of scope for a codec.

## Recommendation for Vinyl

Combine routes 1 and 3: land the P6 loops in accumulator/trampoline form
pinned to the old definitions by bridging equations (the
[`02`](02-output-size-bounds.md) pattern), and add the syntactic tail
checker to `scripts/check.sh` so the shape cannot regress silently.
Route 2 remains the research direction, tracked as "stack as a resource"
in [`cost-semantics.md`](cost-semantics.md) §7, with this note as its
worked-out design space.

## References

[1] A. Gómez-Londoño, J. Åman Pohjola, H. T. Syeda, M. O. Myreen,
Y. K. Tan. *Do You Have Space for Dessert? A Verified Space Cost
Semantics for CakeML Programs.* OOPSLA 2020. (Stack and heap, through a
verified compiler.)

[2] Q. Carbonneaux, J. Hoffmann, T. Ramananandro, Z. Shao. *End-to-End
Verification of Stack-Space Bounds for C Programs.* PLDI 2014.
(Quantitative CompCert.)

[3] N. A. Danielsson. *Lightweight Semiformal Time Complexity Analysis
for Purely Functional Data Structures.* POPL 2008. (The shallow cost
monad Route 2 extends.)

[4] J. C. Reynolds. *Definitional Interpreters for Higher-Order
Programming Languages.* ACM National Conference 1972. (Defunctionalization
— the idea behind reifying control as data.)

Project-internal: [`06-recursion-shape.md`](06-recursion-shape.md) (the
incident), [`cost-semantics.md`](cost-semantics.md) (the general
framework), [`01-robustness-theorems.md`](01-robustness-theorems.md)
(the "stack shape" taxonomy row this note develops).
