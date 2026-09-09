# The lint surface: shipped code the gate never sees

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
all is the underlying smell; the fix left it where it is — moving a
900-line module is a refactor, not a fix — and moved the *boundary*
instead, which is the part that was load-bearing.)

## The fix

The six `toNat!` sites now parse with `toNat?` and funnel `none` into a
shared `usageError` (message, usage text, exit 2) — the in-file precedent
`withThreads` set made this a consistency fix, not a design decision. Two
dead helpers that carried panicking indexing (`pcm16OfBytes` and a local
`deinterleave`, leftovers of an earlier CLI) were deleted rather than
grandfathered.

Then the boundary moved: `scripts/check.sh` now lints **every module the
lake executables link** (`FlacTest/Cli.lean`, `FlacTest/Capstones.lean`,
`FlacTest/Main.lean`, `Vinyl.lean`, `FlacTest.lean` — the list is kept in
step with the `[[lean_exe]]` roots in `lakefile.toml`) for the panicking
family: `!`-indexing, `get!`, `head!`/`tail!`, `toNat!`/`toInt!`, and
`panic!` itself. The next panicking call in CLI code fails the gate the
way it would in `Flac/`; that lint is also the regression guard — the
suite runs *inside* `cliMain`, so it cannot re-invoke the binary with
garbage arguments, and the by-hand check (`--encode … abc 1` → usage
message, rc 2, no backtrace) is recorded here instead.

## Checklist addition

- The gate's file scope must be derived from what the *shipped
  executables link*, not from which directory the proofs live in. Any
  code reachable from a `main` deserves at least the no-panic tier.
- When two call sites in one file parse the same kind of input two ways,
  the stricter one is the spec; unify on it.
