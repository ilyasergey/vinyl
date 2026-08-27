# The API surface: when the guarantee and the name part ways

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
exported runtime-checked wrappers (`encodeChecked : Audio → Option
ByteArray` and friends) that test the precondition — and *also* exported
the raw `Stream.encode : EncoderCfg → Audio → ByteArray`, docstring "The
encoder", under the most natural name, with no guard. Being total, it
never refuses: audio violating a clause is encoded into a syntactically
perfect stream — valid CRCs, decodable — that denotes *different* audio.
A sample `2^(b-1)` is written mod `2^b` and decodes as `-2^(b-1)`; a
sample rate of 2²⁰ truncates in its 20-bit field and decodes as 0; nine
channels collide with the stereo-mode codes and decoding fails outright.
The `vinyl` CLI is immune (it validates every parameter before calling
in); only library callers were exposed.

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

The computation is untouched: the reference encoder is correct *on its
domain*, and the capstones need it to exist. What moved is the surface:

- **The unchecked encoder relocated.** `Flac.Stream.encode` is now
  `Flac.Stream.Unchecked.encode`, and the raw default-configuration
  encoder that sat at the top level as `Flac.encode` is now
  `Flac.Unchecked.encode`. Both docstrings name the precondition, the
  theorems that consume them, and the off-domain mod-wrap behavior. No
  `@[deprecated]` aliases for the old unchecked names: the point is that
  the short spelling stops resolving to the unguarded function, and an
  alias would undo exactly that.
- **`decodeReference` did not move.** The issue proposed relocating the
  pair; only the encoder went. A decoder has no precondition a caller can
  violate — `decodeReference` is total, budgeted, and safe on arbitrary
  bytes — and its name already labels it the reference path. (What *did*
  change about it, in the P6 round: the CLI no longer executes it on
  untrusted input, for cost reasons — see
  [`06-recursion-shape.md`](06-recursion-shape.md).)
- **The public `encode` is the checked wrapper**: `Flac.encode : Audio →
  Option ByteArray`, where `none` is the precondition's voice.
  `encodeChecked` survives as a documented compatibility alias
  (`def encodeChecked := encode`). The capstone `decode_encode` is
  restated in the hypothesis-free shape — `encode a = some bytes →
  decode bytes = .ok a` — and the conditional statement survives as
  `decode_encode_unchecked`, about the relocated raw form.
  `decode_encode_cfg`, `decode_encodeChecked`, `emitFast_eq_encode`,
  `encodePcm16_eq` and `decodeReference_encode` keep their names,
  restated over `Unchecked.encode`.
- **The gate checks the binding.** `FlacTest/Capstones.lean` gained,
  besides the restated pins, a *type* pin:
  `example : Audio → Option ByteArray := Flac.encode` — the build fails
  if the shortest-path public encoder ever reverts to a form whose type
  does not refuse. Regression tests (`apiSurfaceTests`): the audit's
  three probes get `none` from `Flac.encode`, the unchecked form's
  mod-wrap of `2^15` to `-2^15` is pinned as the reason for the move, and
  a well-formed control round-trips.

Cheap proof work, but genuinely proof work — which is the point: this is
one of two findings (with P1) whose fix touches proven functions, yet the
change is entirely at the boundary between the theorems and their
audience.

## The methodology, in brief

The reusable discipline is developed in its own research note,
[`api-contracts.md`](api-contracts.md); the short form: this is a
*coverage* bug — earlier notes asked "is the property proven?", this one
asks "is the proven property attached to what users actually touch?" The
four rules: precondition-as-guard by default (with the
hypothesis-free-capstone packaging, and preconditions kept decidable as
an API decision); the natural, shortest-path name carries the strongest
guarantee, unchecked forms live in a namespace that says so; an
API-to-theorem map — which theorem covers *this name*, not a sibling —
checked at the merge gate (this round's mechanization: the type pin and
the restated capstone pins; the metaprogrammed `@[covered_by]` checker
remains the research direction); and escalation to a subtype
(`{a : Audio // a.WellFormed}`) when callers hold values across many
calls.

## Checklist addition for new entry points

- Does the natural, shortest-path name carry the strongest guarantee — or
  does it merely sit next to it?
- Is every precondition either checked at runtime (guard) or
  unrepresentable (subtype)? A hypothesis in a theorem is not a contract
  a caller can be assumed to have read.
- For each exported function: name the theorem about *it*. If the honest
  answer is "none, but its sibling…", the API is misdirecting.
