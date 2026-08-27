# Robustness theorems: what to prove so adversarial inputs cannot hurt us

Written after fixing audit finding P1 (issue #1, the LPC predictor
divergence). The fix itself is small; the reason the bug existed at all is
general and worth keeping, because every future decoder path can repeat it.

## The incident, in one paragraph

`Lpc.restoreA` reconstructed samples in exact ℤ: `x[n] = res[n] +
(Σ c·x[n-i]) >>> shift`. Nothing bounded the reconstructed magnitude, and
the reconstruction feeds back into itself. A crafted 8 KB stream (order 1,
coefficient `2^14-1`, shift 0) made samples grow as `16383^n`; within one
65535-sample block the bignums reached gigabytes and GMP aborted the
process with an uncatchable SIGABRT. Every decode mode was affected,
including the two verified ones.

## Why the proofs did not catch it

The project's central theorems are round-trips: `decode (encode a) = a`
for well-formed `a`. Three separate gaps let P1 through all of them.

1. **Round-trip theorems quantify over the encoder's image, not the
   decoder's domain.** The set of byte strings the decoder accepts is far
   larger than the set the encoder can emit. A divergent predictor never
   appears in an encoded stream, so no round-trip instance ever exercises
   one. A theorem of the form `∀ audio, P (decode (encode audio))` says
   nothing about `decode bytes` for arbitrary `bytes`.

2. **Totality is not a resource bound.** The codebase rules (no `partial`,
   no panicking indexing, fuel-bounded loops) guarantee every decode
   terminates with a well-defined value. `restoreA` was total: on the bomb
   input it returned a perfectly well-defined `Array Int` whose elements
   merely needed gigabytes to represent. Termination, totality, and even
   "returns the mathematically correct value" all hold while the process
   dies.

3. **The types carry no width invariant.** `Int` is arbitrary precision,
   so `Array Int` admits values no conformant fixed-width decoder could
   ever hold. Any invariant like "samples fit the declared bit depth" has
   to be stated and proven; it is not structural.

## The taxonomy: theorem kinds and the bug classes they exclude

For a decoder function such as `restoreA`, these are distinct obligations.
Each one, when missing, admits a distinct class of attack.

| Theorem kind | Shape | Bug class it prevents | Status in Vinyl |
|---|---|---|---|
| Round-trip correctness | `decode (encode a) = a` on well-formed `a` | wrong output on *valid* streams | proven (capstones) |
| Value boundedness | for *arbitrary* input, every intermediate and output value fits a fixed width | value blowup: bignum divergence, GMP abort (P1) | wrap by construction + `fitsSInt_wrapSInt`; end-to-end statement is future work |
| Output-size bound | `size (decode bytes) ≤ k · size bytes + c` | decompression bombs / amplification OOM (P2, P3) | not yet stated (issues #2, #3) |
| Stack shape | recursion is tail (or depth ≤ constant) for arbitrary input | stack overflow on many tiny frames (P6) | lint-enforced style, no theorem (issue #6) |
| Termination | fuel-bounded loops, no `partial` | infinite loops on crafted input | by construction |
| Early validation | header claims are checked against input size *before* any allocation proportional to them | huge up-front allocation from a tiny file (P3, P8) | not yet (issues #3, #8) |

The key discipline: for each theorem, ask **which set of inputs it
quantifies over**. "All well-formed audio" protects users of the encoder.
Only "all byte strings" protects users of the decoder, and the decoder is
the side that faces untrusted data.

A second discipline: resource-safety properties must hold **by
construction inside the loop**, not by a check after it. Validating the
output of `restoreA` after the fold would be too late; the memory is
already gone. The bound has to be maintained at every step of the
recurrence, which is also the only place a proof by induction can carry
it.

## The formal fix pattern used for P1

The fix is the pattern to reuse: make the production function compute what
a *fixed-width* implementation computes, then prove the fixed-width
behavior invisible on valid data.

1. **One bounding primitive.** `Flac.Bits.wrapSInt n x` reduces `x` to the
   `n`-bit two's-complement representative of its residue class mod `2^n`,
   which is exactly what register arithmetic in a conformant decoder does.
   Its in-range test comes first, so the hot path pays two comparisons and
   never divides.

2. **Two lemmas about it**, one per side of the trust boundary:
   - `fitsSInt_wrapSInt : FitsSInt n (wrapSInt n x)` for **arbitrary** `x`:
     the adversarial-input bound. This is the theorem kind that was
     missing.
   - `wrapSInt_eq_of_fits : FitsSInt n x → wrapSInt n x = x`: on the
     encoder's image the wrap is the identity, so correctness theorems
     survive.

3. **Placement follows the algebra of the recurrence.**
   - LPC (`Lpc.restoreA`): the wrap goes *inside* the loop, and the
     wrapped value is what enters the prediction history. The predictor
     uses an arithmetic shift, which does not commute with residues
     mod `2^b`, so wrapping late would compute something else, and the
     unwrapped feedback is precisely what diverges.
   - Fixed (`Fixed.restoreA`): the undifferencing chain is additions only,
     and addition commutes with residues mod `2^b`, so a single pointwise
     wrap of the final array computes exactly per-step wrapping, at the
     cost of one in-place pass. Intermediates stay polynomially bounded by
     input size, so deferring the wrap is safe there.

4. **Thread the identity hypothesis through the round-trip chain, sourced
   from what is already checked.** `restore_residual` (both predictors)
   gained the hypothesis "all samples fit `b` bits". It propagates:
   `readContent_writeContent` → `Subframe.read_write` (via
   `fitsSInt_shiftDown` for wasted bits) → `readChannels_spec` (via
   `side_fits`/`mid_fits` for the `b+1` stereo side channel) →
   `Frame.read_write` → `readFrames_writeFrames` →
   `decodeReference_encode`, where `Audio.WellFormed` supplies it. Nothing
   new is trusted: `WellFormed` was already the capstone hypothesis and is
   already decided at runtime by `encodeChecked`.

5. **A deliberate trade-off, recorded.** The alternative was to strengthen
   the runtime-checked `SubframeCfg.Valid` certificate to include "all
   samples fit". That makes validity self-contained but adds a per-sample
   scan to the encoder's per-frame certificate check (`safeChooser` runs
   it on the hot path). Threading the hypothesis instead costs the proofs
   a parameter and the encoder nothing. Measured decode cost of the wrap
   itself: about 2% single-threaded on a 32 MB synthetic probe, zero
   change to output bytes on valid streams.

## Checklist for any new decoder path

Before merging a function that consumes untrusted bits, answer for it:

- Which inputs do its theorems quantify over: the encoder's image, or all
  byte strings? What is proven for the latter?
- Is every arithmetic result it stores bounded by a width that follows
  from the format, for arbitrary input? Where exactly is that enforced,
  and is that point inside the loop?
- Is the memory it allocates bounded by a function of the *input* size,
  before believing any count read from a header?
- Is its recursion tail-position (or constant-depth) for arbitrary input?
- If it enforces a bound the format mandates (wrap, clamp, reject): is
  there a lemma that valid streams never hit it, so the round-trip
  proofs keep their statements?

## Future work this note anticipates

- An end-to-end boundedness theorem: every sample array `decodeArrays`
  returns has all elements `FitsSInt (bps + 2)` (subframe wrap at
  `b`/`b+1`, plus one bit of headroom through stereo reconstruction), for
  arbitrary input bytes. All local pieces now exist.
- Output-size and early-validation theorems for the amplification
  findings (issues #2, #3), which need a size-vs-input bound in the frame
  loop, not a value bound.
- Making resource consumption itself provable: value-level theorems bound
  what the decoder *returns*, never what it *spends* computing it (the
  capacity hint in P3 is definitionally invisible to the logic).
  `shallow-cost-semantics.md` develops this into a concrete proposal: a
  credit-charging cost monad over Lean, its two theorem shapes, and the
  research questions Vinyl makes concrete.
