# Prose claims: the docstring as unchecked specification

Written after fixing audit finding P10
([issue #10](https://github.com/ilyasergey/vinyl/issues/10), the `-j`
re-exec growth). Low severity, high instructional value: in a project
where the central claims are kernel-checked, this bug hid behind the one
specification medium with no checker at all — a code comment. The
docstring said `withThreads` "recurses exactly once". It recursed once
*per flag*.

## The incident, in one paragraph

`-j N` / `--threads N` works by re-executing the binary with the thread
count set and the flag stripped — but `withThreads` stripped only **one**
leading flag before re-spawning on the rest, and each child blocks in
`child.wait`. So N leading thread flags created N nested OS processes,
each a full Lean runtime with its own task pool, all alive
simultaneously; wall time scaled linearly at ~1.5 ms per flag and
`ARG_MAX` admits on the order of 10⁵ of them. With a long-running inner
command, all N runtimes coexist. Not a crash — a quietly growing process
tree behind a comment asserting it cannot happen.

## Why the proofs don't catch it

Process spawning is `IO`: nothing in `Flac/Spec/` models it, no theorem
mentions `withThreads`, and the CLI sits outside the lint surface
([`09-lint-surface.md`](09-lint-surface.md)) besides. The only
specification this function ever had was its docstring, and the
docstring was wrong. That is the general observation worth the note:
the project's guarantee tiers (theorem / by-construction / lint) all
have *checkers*; prose has none, so prose is where stale claims survive
every build. A comment stating a behavioral property is a specification
with no enforcement — the same coverage question as
[`api-contracts.md`](api-contracts.md), one level down: there, names
promised more than the theorems; here, a sentence promises what nothing
checks at all.

## The fix

Both proposed mechanisms landed, belt and braces:

- **One pass.** `stripThreadFlags` consumes *every* leading `-j n` /
  `--threads n` / `--threads=n` before the single re-exec, the last count
  winning (which is what the strip-one-per-exec loop used to converge
  to). It is deliberately a pure function, so the property that matters —
  no leading flag survives a pass — is pinned by unit tests
  (`threadFlagTests`: single flag, mixed forms, forty stacked flags,
  idempotence, non-leading flags left alone).
- **The sentinel.** The spawned child carries `VINYL_THREADS_SET`, and
  `withThreads` refuses to re-exec when it is present — so however the
  argument parser evolves, one invocation spawns at most one child.

The docstring now describes the loop actually written. Measured with the
audit's own methodology (prepend N flag copies, time it): 120 stacked
flags cost the same ~12 ms as one, where before they cost ~1.5 ms each on
top.

## Checklist addition

- Any docstring making a *quantified behavioral claim* ("exactly once",
  "at most", "never") either points at the theorem/test that checks it,
  or is rewritten as description rather than promise.
- Flag-stripping loops: idempotence under repetition is the property to
  test — user input is a list, and "leading element" logic must be
  stated over runs, not single occurrences. Making the stripper a pure
  function is what makes that testable at all.
- `IO`-layer behavior (spawning, env, files) is testable even when it is
  not provable: a timing- or count-based regression test is the checker
  prose lacks.
