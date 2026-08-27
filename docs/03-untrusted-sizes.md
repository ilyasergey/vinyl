# Untrusted sizes: the allocation the logic cannot see

Written after fixing audit finding P3
([issue #3](https://github.com/ilyasergey/vinyl/issues/3), the
unvalidated-`totalSamples` allocation). Of the three resource findings
fixed so far this is the smallest diff and the most instructive one,
because it is the only fix that *no theorem in the development could have
required*: the buggy program and the fixed program are propositionally
equal.

## The incident, in one paragraph

`decodeBytes`, the shipped and benchmarked decode path, pre-sized its
output buffer as `2 · channels · totalSamples + 64` bytes, with
`totalSamples` taken verbatim from STREAMINFO's 36-bit field. That field
is attacker-controlled and is read before any audio frame is parsed, so a
42-byte file (a `fLaC` marker, one STREAMINFO block claiming 8 channels
and a maximal sample count, no frames at all) requests ~1.1 TB as the
decoder's first act. Whether that kills the process depends on the host:
under a virtual-memory ceiling (`ulimit -v`, a container's `memory.max`,
strict overcommit — typical production sandboxes) it aborts having
decoded nothing; on an unconstrained host with heuristic overcommit the
reservation is never touched and decode returns empty. Either way the
decoder briefly asked the operating system for a terabyte because a
42-byte input told it to.

## Why this bug is invisible to the proofs — permanently

P1 and P2 were at least *expressible* failures: the divergent predictor
and the decompression bomb are properties of the values the decoder
returns, and both fixes came with theorems (`fitsSInt_wrapSInt`,
`Flac.decode_size_le`). P3 is different in kind. In Lean,
`ByteArray.emptyWithCapacity n` is definitionally the empty array; `n` is
a reservation hint consumed by the runtime allocator and erased from the
logic. `emptyWithCapacity 64` and `emptyWithCapacity (2^40)` are the same
term up to `rfl`, so every theorem in `Flac/Spec/` holds of the buggy and
the fixed decoder with the identical proofs. Concretely: the fix below
changed no statement, no proof, and `lake build` replayed everything
untouched.

That is the disquieting part, and it should be said plainly: nothing in
the verified development enforces this fix or can prevent its
reintroduction. The guards that exist are the checklist in
[`01-robustness-theorems.md`](01-robustness-theorems.md), review, and the
regression tests; the proposal for making this class of bug a *proof
obligation* — a cost-instrumented decoder in which the unclamped
allocation makes a linear-budget theorem unprovable — is
[`cost-semantics.md`](cost-semantics.md), which uses exactly this line as
its motivating example. It is worth recording that its §5 replay, written
before this fix, derived the `min`-clamped allocation as the only form
under which the budget proof goes through; the fix that landed is that
form, arrived at by hand. The machinery would have forced it.

## The fix

```lean
def outCapacity (declared inputBytes : Nat) : Nat :=
  min declared (16 * inputBytes + 65536)
```

and `decodeBytes` passes its former expression through it. Properties
that pinned the constants:

- **Honest streams keep their exact pre-size.** For real audio, decoded
  PCM is at most a few times the compressed size; 16 input bytes of
  output per input byte covers every realistic ratio, so for honest files
  `min` selects the declared value and the benchmarked path allocates
  exactly once, as before.
- **The attack is neutralized, not special-cased.** The 42-byte file now
  requests ~66 KB. Any file claiming more output than 16× its own size is
  treated as what it statistically is: either lying or extremely
  silence-heavy, and in the second case the buffer simply grows by
  doubling — amortized linear, no correctness impact, on a stream shape
  that is rare and slow to produce anyway.
- **The P2 budget is deliberately *not* the cap.**
  `Stream.decodeBudget = 4096 · input + 65536` is a rejection threshold,
  the largest output the decoder will ever hand back; as an *allocation
  estimate* it is uselessly loose — a 1 MB file lying about
  `totalSamples` would still reserve 4 GB up front. A flat cap (the
  issue's `2^26` suggestion) was also rejected: it would cost large
  honest decodes their exact pre-sizing on the hot path. Estimating and
  bounding are different jobs; `16×` estimates, the budget bounds.

A survey (`grep` over `emptyWithCapacity` / `replicate` in
`Flac/Native/`) confirmed this was the only allocation sized by an
unvalidated header field: frame-level counts are bounded by the 16-bit
block-size field and covered cumulatively by the P2 budget, and every
other capacity is encoder-side or derived from already-decoded values.

## The conformance follow-up, deliberately not taken

The issue notes separately that a nonzero `totalSamples` could be
cross-checked against the decoded sample count, rejecting a mismatch.
That is a conformance improvement, not a DoS fix, and it changes the
decoder's accept-set — which means threading the check through the native
/ reference / parallel / byte equivalence stack and the capstones,
exactly the exercise P2 required
([`02-output-size-bounds.md`](02-output-size-bounds.md)); the bridging
technique there would apply verbatim. Left open until conformance work
prioritizes it; the P8 finding
([issue #8](https://github.com/ilyasergey/vinyl/issues/8)) also sits in
the early-validation row of the taxonomy and remains open.

## Checklist addition for new decoder paths

To the checklists in
[`01-robustness-theorems.md`](01-robustness-theorems.md) and
[`02-output-size-bounds.md`](02-output-size-bounds.md), this incident
adds:

- Does any allocation — including capacity *hints*, which no theorem
  sees — happen before the quantity it is sized by has been validated
  against the input?
- For every `emptyWithCapacity` / pre-size on an untrusted path: is the
  size derived from input-bounded quantities, and if it comes from a
  header field, what clamps it?
- When a fix is proof-invisible (allocation hints, evaluation order,
  in-place reuse), which non-proof artifact pins it: a regression test, a
  lint, a checklist entry? At least one must name it, or the next
  refactor silently undoes it.
