# A shallowly-embedded cost semantics for Lean, motivated by Vinyl

*A research note. Companion to [`01-robustness-theorems.md`](01-robustness-theorems.md),
which classifies the theorem kinds this project does and does not have; this
note develops one row of that taxonomy — resource bounds — into a concrete
proposal. It is written for someone who did not participate in Vinyl's
development or in the audit that motivated it.*

## 1. Context: a verified codec that a 42-byte file can kill

Vinyl is a FLAC codec written in pure Lean 4. Its central results are
kernel-checked round-trip theorems (`decode (encode a) = a` for well-formed
`a`, over every encoder configuration), and its decode paths are total by
construction: no `partial`, no panicking indexing, fuel-bounded loops. An
independent audit ([issues #1–#11](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit),
tracking [issue #12](https://github.com/ilyasergey/vinyl/issues/12)) found no input
violating any theorem. It nevertheless found several inputs that kill the
process. Two of them frame this note:

- **P1 ([issue #1](https://github.com/ilyasergey/vinyl/issues/1)).** LPC
  decoding reconstructs samples by a feedback
  recurrence over arbitrary-precision `Int`. A crafted 8 KB stream made the
  reconstruction diverge geometrically (`sample[n] = 16383^n`); the bignums
  reached gigabytes within one block and GMP aborted the process. The
  function was total and returned a perfectly well-defined value; the value
  merely did not fit in physical memory.

- **P3 ([issue #3](https://github.com/ilyasergey/vinyl/issues/3)).** The
  fast decoder pre-sized its output buffer from the
  stream header's 36-bit `totalSamples` field, before parsing any audio.
  A 42-byte file claiming ~4·10⁹ samples requested ~1.1 TB as the
  decoder's first act. Under any memory ceiling (a container limit,
  `ulimit -v`) the process aborted having decoded nothing. (Since fixed —
  [`03-untrusted-sizes.md`](03-untrusted-sizes.md) — in exactly the
  clamped form §5 derives, a point taken up there.)

Neither is a functional-correctness bug. Both are *cost* bugs: the machine
resources consumed while computing a value, which Lean's logic does not
model. The question this note develops: what would it take to make such
properties **theorems**, so that the next P1 or P3 is a hole in a proof
rather than a finding in an audit?

## 2. The problem, precisely: cost is erased from the denotation

Lean's kernel reasons about the *values* programs denote. Everything about
how the compiled artifact computes those values — heap, stack, evaluation
order, allocator behavior — is outside the logical model. Vinyl runs into
this boundary in two distinct ways, worth separating because they need
different treatment.

**(a) Cost-only operations are definitionally invisible.** The P3
allocation is one line:

```lean
ByteArray.emptyWithCapacity (2 * si.channels * si.totalSamples + 64)
```

In Lean, `ByteArray.emptyWithCapacity n` is *definitionally equal* to the
empty array; `n` is a reservation hint consumed by the runtime allocator
and erased from the logic. `emptyWithCapacity 64` and
`emptyWithCapacity 10^12` are the same term up to `rfl`, so every theorem
holds of both with the identical proof. The fix (deriving the hint from the
validated input size instead of the untrusted header) is therefore
proof-free — and, by the same coin, *proof-invisible*. No specification
written against the current semantics can require it, because the logic
cannot distinguish the buggy program from the fixed one.

**(b) Cost can depend on values in ways totality does not bound.** The P1
recurrence is, in essence:

```lean
def restoreAux (cs : List Int) (shift : Nat) (hist : List Int) : List Int → List Int
  | [] => []
  | r :: res =>
    let x := r + predict cs shift hist   -- exact ℤ: no width, no wrap
    x :: restoreAux cs shift (x :: hist) res
```

Lean's `Int` is a GMP bignum: the space to *store* `x` and the time to
*multiply* by it grow with its magnitude. Totality gives termination and a
well-defined result; it says nothing about the size of intermediate values,
so "terminates" and "allocates gigabytes per sample" coexist. The eventual
fix wrapped each reconstructed sample to the stream's bit depth inside the
recurrence (`Flac.Bits.wrapSInt`, with `fitsSInt_wrapSInt` proving the
result always fits) — and note for later that this *value-boundedness*
lemma is precisely the fact any cost argument about this loop would need.

The pattern generalizes far beyond these two findings: reference-counted
in-place updates (`Array.push`/`Array.set` are O(1) when the array is
uniquely owned, full copies otherwise), thunk sharing, and stack shape are
all execution-level facts that propositionally equal programs can differ
on. Vinyl's performance work leans on several of them, currently
guaranteed by code shape and review, by nothing checked.

## 3. Why a *shallow* embedding is the right first tool here

Three ways cost can enter a formal development:

1. **Deep embedding + verified compilation.** Define an object language
   with an operational cost semantics, write the program in it, prove the
   bound, and compile with a compiler proven to preserve costs down to the
   machine. This is the gold standard and it exists: CakeML has a verified
   space cost semantics for its compiled programs [6], and CompCert has a
   verified stack-bound variant [7]. It is also a different project: Vinyl
   is 20k+ lines of Lean whose value is precisely that the *production*
   Lean code is the proven artifact. Lean has no cost-preserving verified
   compiler, and building one is not a codec project's job.

2. **External amortized analysis.** Type-system-based resource inference
   (AARA/RAML [8, 9]) derives bounds automatically, but for a different
   language, and without connecting to Vinyl's existing correctness proofs.

3. **Shallow embedding: a cost-instrumented monad inside Lean itself.**
   Write the decode path a second time in a monad that threads a credit
   budget; every resource-relevant primitive charges credits; running out
   is an observable failure. Cost becomes part of the *value* the function
   denotes, so resource bounds become ordinary propositions, provable by
   the same inductions as everything else, in the same file, against the
   same lemma library. This is a well-trodden idea — Danielsson's thunk
   monad [10], the Coq running-time monad [11], time credits in separation
   logic [3, 4, 5], Nipkow's timing functions in Isabelle [12] — but it
   has not been developed for Lean 4, whose runtime (Perceus-style
   reference counting with in-place reuse [13, 14], GMP integers) gives the
   adequacy question an unusual and interesting shape.

The decisive argument for the shallow route *in this project* is that
Vinyl already works this way. Its proof architecture is built on pinned
pairs: a fast production form and a slow specification form of the same
function, connected by an equality theorem (`readRiceSeqFast_eq`,
`emitFast_eq_encode`, `restoreA_toList`, …). A cost-instrumented decoder is
one more form of a function the project already maintains in two forms,
pinned by one more theorem. The methodology, the discipline, and the
review culture for "two forms + a bridge" already exist.

## 4. The embedding, sketched

Everything below is a sketch to convey shape, not compiled code.

```lean
/-- A computation paying for resources from a credit budget.
    `none` means the budget was exhausted (never a wrong answer). -/
def CostM (α : Type) := Nat → Option (α × Nat)

instance : Monad CostM where
  pure a := fun c => some (a, c)
  bind m f := fun c => match m c with
    | none => none
    | some (a, c') => f a c'

/-- Spend `k` credits. The only primitive that can fail. -/
def charge (k : Nat) : CostM Unit :=
  fun c => if k ≤ c then some ((), c - k) else none
```

Resource-relevant primitives get charged wrappers, and *only* the wrappers
are legal in instrumented code (a lint enforces this, §6):

```lean
/-- One credit ≈ one machine word of allocation. -/
def emptyWithCapacityC (n : Nat) : CostM (ByteArray) := do
  charge n                                -- a reservation is paid up front
  pure (ByteArray.emptyWithCapacity n)

def pushC (a : Array Int) (x : Int) : CostM (Array Int) := do
  charge 1                                -- amortized; see §7 on doubling
  pure (a.push x)

/-- Bignum cost is value-dependent: charge by limb count. -/
def limbs (x : Int) : Nat := x.natAbs.log2 / 64 + 1

def mulC (a b : Int) : CostM Int := do
  charge (limbs a + limbs b)
  pure (a * b)
```

Two theorem shapes then carry the whole approach.

**Faithfulness (the pin).** The instrumented decoder computes the shipped
one; budgets only decide *whether* it answers, never *what*:

```lean
theorem decodeBytesC_pin (bytes : ByteArray) (c c' : Nat) (r : ByteArray × Nat) :
    decodeBytesC bytes c = some (r, c') → Flac.Decode.decodeBytes bytes = some r
```

So every existing capstone transfers to the instrumented form for free,
and the *shipped binary remains the pure fast path* — the cost twin exists
for proving, exactly like the list-form specs do today.

**Sufficiency (the point).** A budget linear in the input is enough for
every input, valid or adversarial:

```lean
theorem decodeBytesC_linear (bytes : ByteArray) :
    ∀ c, K * bytes.size + C ≤ c →
      (decodeBytesC bytes c).isSome ↔ (Flac.Decode.decodeBytes bytes).isSome
```

This single statement is the anti-DoS specification: *no byte string can
make the decoder spend more than linearly many credits*. It is the
output-size theorems of `01-robustness-theorems.md` upgraded from "the result
is small" to "the computation was cheap".

## 5. How the two incidents die inside the proof

**P3, replayed.** The essence of the bug in four lines, instrumented:

```lean
def decodeToyC (bytes : ByteArray) : CostM (Array Int) := do
  let si ← readStreamInfoC bytes            -- untrusted 36-bit totalSamples
  let out ← emptyWithCapacityC (2 * si.channels * si.totalSamples + 64)
  decodeFramesC bytes out
```

Proving `decodeToyC_linear` reaches the `charge` inside
`emptyWithCapacityC` with the obligation

```
2 * si.channels * si.totalSamples + 64  ≤  K * bytes.size + C
```

and gets stuck, permanently: `totalSamples` is any 36-bit number read from
a 42-byte file, so no `K` and `C` exist. The theorem is only provable for

```lean
let out ← emptyWithCapacityC (min (2 * si.channels * si.totalSamples + 64)
                                  (k * bytes.size + 64))
```

— which is the fix. The audit finding has become an unfillable proof hole,
surfaced at development time, in the same workflow that surfaces
functional bugs. That is the entire thesis of the approach in one example.

This replay was written before the fix landed; the fix that later landed
(`Decode.outCapacity`, [`03-untrusted-sizes.md`](03-untrusted-sizes.md))
is the `min`-clamped form above with `k = 16` — chosen by hand and by
review, since without the instrumentation nothing forces it. The
prediction and the fix agreeing is mild evidence for the model; that
nothing but review *keeps* them agreeing is the argument for building
it.

**P1, replayed.** In the restore recurrence, each step's charge is
`limbs r + Σᵢ (limbs cᵢ + limbs histᵢ)` through `mulC`. On the unwrapped
recurrence, no bound on `limbs histᵢ` is available — the magnitude of a
reconstructed sample grows geometrically, its limb count linearly, and the
block's total cost quadratically, with no relation to input size; the
sufficiency proof is stuck. With the wrap in the loop, the lemma
`fitsSInt_wrapSInt : FitsSInt b (wrapSInt b x)` bounds every history entry
to one limb, the per-sample charge collapses to `O(order)`, and the linear
budget goes through. Two observations worth writing down:

- The value-boundedness theorem introduced by the functional P1 fix is
  *exactly* the lemma the cost proof consumes. Value bounds are the
  semantic core of cost bounds; the cost semantics adds the bookkeeping
  from bounded values to bounded credits. The taxonomy rows connect.
- The cost proof would have *forced* the P1 fix even if nobody had thought
  of the attack: you cannot bound the charges without bounding the values.
  This is the sense in which the embedding turns a class of unknown
  unknowns into proof obligations.

## 6. What stays trusted, and how to keep it small

A shallow embedding moves the trust boundary; it does not remove it. The
residue, explicitly:

1. **Charging completeness.** A `charge` that is missing makes the theorem
   silently weaker there. Discipline: instrumented code may allocate only
   through the charged wrappers, enforced by the merge gate the same way
   `scripts/check.sh` already enforces "no `partial`, no panicking
   indexing in decode paths" — grep-level lint over `Flac/Native/` and the
   instrumented namespace. Charging completeness then reduces to auditing
   the (small, fixed) wrapper file, analogous to auditing an axiom
   footprint.
2. **Adequacy of the constants.** "One credit per word", "limbs x" for GMP
   storage, "1 amortized per push": these assert facts about Lean's
   compiler and runtime that are unverified and will stay so until Lean
   has a cost-preserving verified compiler (CakeML shows what that takes
   [6]). The model still catches every *asymptotic* discrepancy — and P1,
   P2, P3 are all asymptotic amplification bugs, none about constants.
3. **Sharing.** `pushC`'s O(1) is true when the array is uniquely
   referenced (Lean's Perceus-style RC reuses it in place [13, 14]) and
   false when shared. Options, in increasing ambition: charge worst-case
   copies (sound, but makes Vinyl's genuinely-linear decoder look
   quadratic — useless); *assume* uniqueness at annotated points (trusted,
   matches how the code is actually written, lint-checkable at the FBIP
   style level); or bring uniqueness into the model itself, which is the
   genuinely open research end of this note (§7).

## 7. Research questions this project makes concrete

Vinyl is a good host for this line of work precisely because it is a real,
performance-tuned, already-verified codebase, so every idealization in a
cost model is immediately tested against code that cheats for speed.

- **Uniqueness in the model.** Lean's runtime performs destructive updates
  under RC-uniqueness [13, 14]; a cost semantics that cannot see sharing
  must either over- or under-approximate. Can a lightweight uniqueness
  discipline (a la Koka's FBIP, or borrowing annotations) be reflected
  into `CostM` obligations without rewriting the code in linear types?
- **Value-dependent charges.** Bignum charging couples the cost proof to
  value-bound invariants (`FitsSInt` here). Is there a systematic way to
  factor cost proofs through a "width discipline", so the value lemmas the
  functional proofs already need are the *only* extra input?
- **Amortization.** `Array.push` doubling wants banker's-method credits
  [3, 4]; blocks and partitions give the codec natural potential
  functions. How much of the classic amortized-analysis toolkit transfers
  to plain monadic Lean without separation logic?
- **Budget erasure.** The pin theorem lets the shipped path stay pure; can
  the instrumented form instead be compiled with credits erased (charge ≡
  id) so *one* definition serves both roles, with the erasure itself
  proven?
- **Stack as a resource.** P6
  ([issue #6](https://github.com/ilyasergey/vinyl/issues/6)) is a
  stack-depth bug; depth
  charging in the same monad would cover it, but Lean's compiler decides
  tail calls, which puts adequacy under pressure again. The design space
  (a scoped `deeper` bracket, trampoline reification, a syntactic tail
  certifier, verified stack-cost compilation) is worked out in
  [`stack-semantics.md`](stack-semantics.md).

## 8. A concrete starting path for Vinyl

1. ~~Land the value-level fixes for #2/#3 first~~ — done:
   [`02-output-size-bounds.md`](02-output-size-bounds.md) (the frame-loop
   budget and `Flac.decode_size_le`) and
   [`03-untrusted-sizes.md`](03-untrusted-sizes.md) (the capacity clamp).
   The value lemmas the cost proofs will consume exist
   (`frameCostTotal_le`, `encode_cost_le_budget`), and needed no new
   machinery.
2. Build `Flac/Cost/` : `CostM`, `charge`, charged wrappers for
   `ByteArray`/`Array` allocation and `Int` arithmetic; extend
   `scripts/check.sh` with the wrapper-only lint.
3. Instrument one leaf first — `Lpc.restoreA` is ideal: small, has the
   value-bound lemma ready, and is the P1 site. Prove its pin and a
   per-block linear budget from `fitsSInt_wrapSInt`.
4. Grow outward along the existing sim-proof chain (`readContent` →
   `readSubframe` → frame loop → `decodeBytes`), reusing its structure;
   state `decodeBytesC_linear` last.
5. Only then consider the research items of §7, each of which by that
   point has a concrete failing or trusted spot in the development to
   point at.

## References

[1] L. de Moura, S. Ullrich. *The Lean 4 Theorem Prover and Programming
Language.* CADE 2021. (The host system.)

[2] RFC 9639: *Free Lossless Audio Codec (FLAC).* §11 explicitly warns
about the decompression-amplification behavior behind P2/P3.

[3] R. Atkey. *Amortised Resource Analysis with Separation Logic.*
ESOP 2010 / LMCS 7(2), 2011. (Credits as ghost resources; the amortization
toolkit.)

[4] A. Charguéraud, F. Pottier. *Verifying the Correctness and Amortized
Complexity of a Union-Find Implementation in Separation Logic with Time
Credits.* J. Autom. Reasoning 62, 2019. (End-to-end credit-based
complexity proof for real code; CFML.)

[5] G. Mével, J.-H. Jourdan, F. Pottier. *Time Credits and Time Receipts
in Iris.* ESOP 2019. (Credits in a modern concurrent separation logic;
also lower bounds.)

[6] A. Gómez-Londoño, J. Åman Pohjola, H. T. Syeda, M. O. Myreen,
Y. K. Tan. *Do You Have Space for Dessert? A Verified Space Cost Semantics
for CakeML Programs.* OOPSLA 2020. (The existence proof for end-to-end
*space* bounds through a verified compiler — the deep-embedding gold
standard this note's shallow approach approximates.)

[7] Q. Carbonneaux, J. Hoffmann, T. Ramananandro, Z. Shao. *End-to-End
Verification of Stack-Space Bounds for C Programs.* PLDI 2014.
(Quantitative CompCert; the stack analogue.)

[8] M. Hofmann, S. Jost. *Static Prediction of Heap Space Usage for
First-Order Functional Programs.* POPL 2003. (Origin of automatic
amortized resource analysis.)

[9] J. Hoffmann, K. Aehlig, M. Hofmann. *Multivariate Amortized Resource
Analysis.* TOPLAS 34(3), 2012; and the RAML system (raml.co). (Automatic
inference — the contrast point to interactive proof.)

[10] N. A. Danielsson. *Lightweight Semiformal Time Complexity Analysis
for Purely Functional Data Structures.* POPL 2008. (The classic shallow
cost monad in dependent type theory; closest ancestor of §4.)

[11] J. McCarthy, B. Fetscher, M. New, D. Feltey, R. B. Findler. *A Coq
Library for Internal Verification of Running-Times.* FLOPS 2016. (A
monadic running-time library in Coq; design trade-offs for §4.)

[12] T. Nipkow, H. Brinkop. *Amortized Complexity Verified.* J. Autom.
Reasoning 62, 2019. (Isabelle/HOL timing-function style — the
non-monadic alternative.)

[13] S. Ullrich, L. de Moura. *Counting Immutable Beans: Reference
Counting Optimized for Purely Functional Programming.* IFL 2019. (Lean's
RC model; why in-place reuse exists and when.)

[14] A. Reinking, N. Xie, L. de Moura, D. Leijen. *Perceus: Garbage Free
Reference Counting with Reuse.* PLDI 2021. (The reuse discipline behind
§6's sharing problem, in Koka.)

[15] A. Guéneau, A. Charguéraud, F. Pottier. *A Fistful of Dollars:
Formalizing Asymptotic Complexity Claims via Deductive Program
Verification.* ESOP 2018. (How to state O(·) claims without constant
lies — relevant to phrasing `decodeBytesC_linear` honestly.)

Project-internal starting points: `docs/01-robustness-theorems.md` (the
taxonomy this note extends),
[issues #1–#12](https://github.com/ilyasergey/vinyl/issues?q=label%3Aaudit)
(the audit), `Flac/Spec/Bits.lean`
(`wrapSInt_eq_of_fits`, `fitsSInt_wrapSInt` — the value-bound lemmas §5
connects to), and `scripts/check.sh` (the merge-gate lint that §6 extends).
