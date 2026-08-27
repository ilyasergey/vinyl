# The API surface: when the guarantee and the name part ways

> **DRAFT — the P7 fix has not landed.** Markers of the form `TODO(fix)`
> hold places for details of the landed change (final names, moved
> lemmas, tests). Structure and analysis are ready for review; the owner
> of the P7 round should fill, adjust, and de-draft this note in the docs
> commit that records the fix, add the README bullet, and flip finding
> #7's row.

Written after fixing audit finding P7
([issue #7](https://github.com/ilyasergey/vinyl/issues/7), the unguarded
public encoder). It is the only finding in the series that is not
denial-of-service: nothing crashes, nothing exhausts, the caller simply
receives **wrong data with no error signal**. It is also the only finding
where every fact needed to prevent it was already proven. The failure is
not in the theorems; it is in how the API presents them — which makes
this the note where the series' recurring warning ("the danger sits
wherever a convention can be mistaken for a kernel-checked fact",
[`01-robustness-theorems.md`](01-robustness-theorems.md)) stops being
abstract.

## The incident, in one paragraph

Every round-trip theorem is conditional on `Audio.WellFormed` (samples
fit the bit depth, 1–8 channels, sample rate < 2²⁰, …). The library
exports runtime-checked wrappers (`encodeChecked : Audio → Option
ByteArray` and friends) that test the precondition — and *also* exports
the raw `Stream.encode : EncoderCfg → Audio → ByteArray`, docstring "The
encoder", under the most natural name, with no guard. Being total, it
never refuses: audio violating a clause is encoded into a syntactically
perfect stream — valid CRCs, decodable — that denotes *different* audio.
A sample `2^(b-1)` is written mod `2^b` and decodes as `-2^(b-1)`; a
sample rate of 2²⁰ truncates in its 20-bit field and decodes as 0; nine
channels collide with the stereo-mode codes and decoding fails outright.
The `vinyl` CLI is immune (it validates every parameter before calling
in); only library callers are exposed.

## Why the proofs don't catch it

Nothing is falsified. Each misbehaving case violates a `WellFormed`
clause, so each theorem is satisfied vacuously — conditional theorems say
nothing off their hypothesis, which is the encoder-side mirror of the
decoder findings (there, inputs outside the *encoder's image*; here,
inputs outside the *theorem's hypothesis*). Two familiar mechanisms
combine:

1. **Totality absorbs, again.** As in
   [`05-saturating-arithmetic.md`](05-saturating-arithmetic.md), a total
   function converts "invalid input" into "well-defined behavior" — there
   a decoder accepting streams the RFC rejects, here an encoder
   fabricating plausible streams for audio the theorems exclude. Totality
   without an explicit rejection is a decision to give invalid inputs a
   meaning, and mod-wrapping bit fields is a meaning nobody chose.

2. **Guarantees attach to theorem statements; users bind them to
   identifiers.** "Formally verified codec" is, precisely, a set of named
   theorems about specific functions. A reader who finds `Stream.encode`
   has no signal — not in the type, not in the name — that the verified
   entry point is a differently-named sibling. The gap between what is
   proven and what a caller can reach in one obvious step is API design,
   and no kernel checks API design.

## The fix

The computation is untouched: `Stream.encode` is the correct reference
encoder *on its domain*, and the capstones need it to exist. What moves
is the surface:

- The unchecked pair (`Stream.encode`, `decodeReference`) relocates to an
  explicitly-marked home (`Unchecked` namespace or equivalent), with
  docstrings naming their precondition and the theorem that consumes
  them. `TODO(fix)`: final placement and whether `@[deprecated]` aliases
  remain for the old names.
- The public `encode` becomes the checked wrapper: `Audio → Option
  ByteArray`, where `none` is the precondition's voice. The
  hypothesis-free capstone shape already exists
  (`decode_encodeChecked`: any `some` result round-trips, no hypotheses)
  — the fix makes that the guarantee a caller cannot avoid holding.
- The capstone statements, the pinned-name greps in `scripts/check.sh`,
  and the CLI call-site pins reference these functions **by name**, so
  they move in step. `TODO(fix)`: the actual rename/lemma diff, and a
  test pinning that the public name is the guarded one.

Cheap proof work, but genuinely proof work — which is the point: this is
one of two findings (with P1) whose fix touches proven functions, yet the
change is entirely at the boundary between the theorems and their
audience.

## The methodology: keeping names and guarantees aligned

The reusable discipline, stated as rules for any verified library:

1. **Precondition-as-guard by default.** Public entry points check their
   preconditions at runtime and return `Option`/`Except`; the
   hypothesis-conditional theorem lives *behind* the guard, packaged as a
   hypothesis-free statement about the guarded function ("every `some`
   round-trips"). Decidability of `WellFormed` is what makes this free;
   keeping preconditions decidable is therefore an API decision, not just
   a proof convenience.
2. **The natural name goes to the guarded form.** Unchecked variants
   exist for proofs and for callers who own the precondition; they live
   in a namespace that says so (`Unchecked`, `Internal`), never as the
   shortest path. A docstring may not claim more than the theorem that
   mentions the function by name.
3. **An API-to-theorem map, checked at the gate.** For every exported
   entry point: which theorem covers *this name* (not a sibling), and is
   it hypothesis-free? `scripts/check.sh` already pins that the CLI
   branches call the functions the capstones are about; the same
   mechanism extends to the library surface — every public entry point is
   either capstone-covered or runtime-guarded, and the gate greps for it.
   `TODO(fix)`: record the check if the round adds it.
4. **Consider making the precondition unrepresentable.** The stronger
   form is a subtype (`{a : Audio // a.WellFormed}`) with a smart
   constructor, so the guard runs once and the type carries it — worth it
   when callers hold values across many calls; the `Option` guard is the
   lighter default.

The general statement of the class, for the taxonomy: a *coverage* bug.
Value bounds, size bounds, and stack shape asked "is the property
proven?"; this asks "is the proven property attached to what users
actually touch?" — a question about every exported name, answerable by
inspection, and worth a row in any audit of a verified artifact.

## Checklist addition for new entry points

- Does the natural, shortest-path name carry the strongest guarantee — or
  does it merely sit next to it?
- Is every precondition either checked at runtime (guard) or
  unrepresentable (subtype)? A hypothesis in a theorem is not a contract
  a caller can be assumed to have read.
- For each exported function: name the theorem about *it*. If the honest
  answer is "none, but its sibling…", the API is misdirecting.
