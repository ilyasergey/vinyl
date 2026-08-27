# The lint surface: shipped code the gate never sees

> **DRAFT — the P9 fix has not landed.** `TODO(fix)` markers hold places
> for the landed details. The fix owner fills them, de-drafts, adds the
> README bullet, and flips finding #9's row.

Written after fixing audit finding P9
([issue #9](https://github.com/ilyasergey/vinyl/issues/9), the CLI
`toNat!` panic). The smallest finding in the series, and the one with the
clearest moral: every guarantee tier this project maintains — theorems,
totality-by-construction, merge-gate lint — is scoped to a set of files,
and the binary users run contains code outside all three.

## The incident, in one paragraph

`vinyl --encode audio.pcm out.flac abc 1` panics with a
`String.Slice.toNat! … Nat expected` backtrace, where a usage message and
exit 2 belong. Six call sites across the `--encode`/`--encode-slow`
arities parse numeric arguments with `toNat!`, the panicking variant —
while `withThreads`, in the same file, already parses its argument with
`toNat?` and errors cleanly. Not an attack in any meaningful sense; a
user typo produces a stack trace.

## Why the proofs don't catch it

The CLI lives in `FlacTest/Cli.lean` — the *test* package — which is
outside the theorem surface (no theorem mentions argument parsing, and
none should) and, more tellingly, outside `scripts/check.sh`'s totality
lint, which greps `Flac/` for panicking `!` indexing but not
`FlacTest/`. So the project's own no-panic discipline, mechanized and
enforced for the codec, stops at a directory boundary that the shipped
binary does not respect: `vinyl`'s `main` is `cliMain`. The audit's
row for this finding is, in effect, a map of where the gate's
jurisdiction ends. (That the production CLI lives in the test package at
all is the underlying smell — `TODO(fix)`: note if the round relocates
it.)

## The fix

Replace the six `toNat!` calls with `toNat?`, emitting the usage error
and exit 2 on `none`, exactly as `withThreads` already does — the
in-file precedent makes this a consistency fix, not a design decision.
Then move the boundary: extend the `scripts/check.sh` panic lint to
every module the `vinyl` executable links (`FlacTest/Cli.lean`
included), so the next `!` in CLI code fails the gate the way it would
in `Flac/`. `TODO(fix)`: landed diff, the lint extension's exact scope,
and a regression test invoking the CLI with garbage arguments and
asserting rc 2 with no panic.

## Checklist addition

- The gate's file scope must be derived from what the *shipped
  executables link*, not from which directory the proofs live in. Any
  code reachable from a `main` deserves at least the no-panic tier.
- When two call sites in one file parse the same kind of input two ways,
  the stricter one is the spec; unify on it.
