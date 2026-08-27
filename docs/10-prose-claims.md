# Prose claims: the docstring as unchecked specification

> **DRAFT — the P10 fix has not landed.** `TODO(fix)` markers hold places
> for the landed details. The fix owner fills them, de-drafts, adds the
> README bullet, and flips finding #10's row.

Written after fixing audit finding P10
([issue #10](https://github.com/ilyasergey/vinyl/issues/10), the `-j`
re-exec growth). Low severity, high instructional value: in a project
where the central claims are kernel-checked, this bug hid behind the one
specification medium with no checker at all — a code comment. The
docstring said `withThreads` "recurses exactly once". It recurses once
*per flag*.

## The incident, in one paragraph

`-j N` / `--threads N` works by re-executing the binary with the thread
count set and the flag stripped — but `withThreads` strips only **one**
leading flag before re-spawning on the rest, and each child blocks in
`child.wait`. So N leading thread flags create N nested OS processes,
each a full Lean runtime with its own task pool, all alive
simultaneously; wall time scales linearly at ~1.5 ms per flag and
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

Strip **all** leading `-j` / `--threads` / `--threads=` flags in one
pass before the single re-exec (or set a sentinel environment variable
and refuse to re-exec when present — belt and braces: the sentinel also
defends against flag forms a future parser adds), and correct the
docstring to describe the loop actually written. `TODO(fix)`: which of
the two mechanisms (or both) landed, the docstring's new wording, and a
regression test asserting flat wall time / single re-exec for stacked
flags (the audit's timing methodology, `yes -- '-j 2' | head -N`, is
directly reusable).

## Checklist addition

- Any docstring making a *quantified behavioral claim* ("exactly once",
  "at most", "never") either points at the theorem/test that checks it,
  or is rewritten as description rather than promise.
- Flag-stripping loops: idempotence under repetition is the property to
  test — user input is a list, and "leading element" logic must be
  stated over runs, not single occurrences.
- `IO`-layer behavior (spawning, env, files) is testable even when it is
  not provable: a timing- or count-based regression test is the checker
  prose lacks.
