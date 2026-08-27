# Output-size bounds: how the decompression-bomb budget was made a theorem

Written after fixing audit finding P2
([issue #2](https://github.com/ilyasergey/vinyl/issues/2), the
constant-subframe decompression bomb). The companion note
[`01-robustness-theorems.md`](01-robustness-theorems.md) classifies this
bug under "output-size bound: not yet stated"; this note records how that
row was filled in, because both the impossibility that shaped the fix and
the proof technique that made it cheap are reusable.

## The incident, in one paragraph

A CONSTANT subframe is FLAC's run-length shorthand: one stored value, and
the decoder materializes `blockSize` copies. Nothing related decoded
output to input size, so a conformant 105 KB stream of 3000 maximal
CONSTANT frames (65535 samples × 8 channels each, ~35 input bytes per
frame) asked the decoder for 1.57 billion samples: ~3.1 GB of PCM, over
12 GB as boxed sample arrays, and an out-of-memory abort. This is exactly
the amplification RFC 9639 §11 warns decoders about. Every theorem held
throughout: `decodeBytes_spec` proves the output bytes are *correct*,
never that there are *few* of them.

## The impossibility that shapes any fix

There is no cap that rejects bombs and accepts all conformant streams,
because **the bomb is what silence legitimately compresses to**. An hour
of 8-channel silence and a crafted bomb are byte-for-byte the same kind of
stream: maximal CONSTANT frames, amplification in the tens of thousands.
Any budget tight enough to stop one rejects the other.

So a bound must reject some conformant streams, and the real question
becomes: which side of the line does *our encoder's own output* fall on?
If any well-formed audio can be encoded into a stream the decoder now
rejects, the round-trip capstone `decode (encode a) = .ok a` is false, not
merely unproven. The fix is therefore two constants and two bounds that
must meet:

- **The budget.** The frame loop tracks cumulative decoded output at two
  budget units per sample (the PCM16 measure, used for every bit depth)
  and returns `none`, exactly like a corrupt stream, once a frame would
  push it past
  `Stream.decodeBudget bytes = decodeAmpl · bytes.size + decodeFloor`
  with `decodeAmpl = 4096` and `decodeFloor = 65536`.

- **The write side.** A frame costs at least `80 + 8·ch` bits to emit
  (`frame_write_length_lb`): 32 fixed header bits, a coded number (≥ 8),
  the explicit 16-bit block size, CRC-8, CRC-16, and at least one byte of
  subframe header per channel.

- **The decode side.** A frame costs at most `2·ch·blockSize` budget
  (`frameCostTotal_le`).

- **Where they meet.** `16·ch·bs ≤ 4096·(80 + 8·ch)` holds for every
  `ch ≤ 8` exactly when `bs ≤ 4608` (`encode_cost_le_budget`). So the
  configurable-block-size guards (`encodeCheckedCfg`, `encodePcm16Fast`,
  and the `decode_encode_cfg` hypothesis) tightened from 65535 to 4608,
  the default block size 4096 is unaffected, and every capstone keeps its
  statement with no new hypotheses.

The constant 4096 is not a tuning knob: it is pinned from below by the
encoder's provable worst case (encoded 8-channel silence at block size
4096 amplifies ~3800×) and pinned from above by wanting the smallest bound
the proofs allow. Changing it means redoing `encode_cost_le_budget`, and
the theorem will say whether the new value is sound.

## The proof pattern: one bridging equation per loop

The naive plan, threading a budget parameter through every frame loop and
re-proving the equivalence stack (native ↔ reference, serial ↔ parallel,
sample ↔ byte, several thousand lines), was never attempted. Instead each
budgeted loop is a *new* function proven equal to the old loop plus a
single cumulative check on a `some` result:

```
readFramesB b0 budget fuel s
  = (readFrames b0 fuel s).bind
      (fun frs => if frameCostTotal frs ≤ budget then some frs else none)
```

(`readFramesB_eq`, and likewise `readFramesStepsB_eq`,
`readFramesFastB_eq_At`, `readBytesStepsB_spec`.) The equation holds
because the loop's abort condition is monotone: if the total fits the
budget, no prefix ever trips the per-frame check; if it does not fit, the
loop dies at some frame and `none` equals `none` regardless of which
failure came first. One induction per loop, and every existing lemma about
the unbudgeted loops is consumed as-is. The top-level decoders swap in the
budgeted variants, and their proofs each gain one rewrite and one
`if_pos`.

This shape generalizes: any retrofitted runtime guard whose failure mode
is "reject the input" can be stated as `old.bind (check)` and bridged the
same way, leaving the verified pipeline untouched. It composes with the
in-loop-by-construction discipline from
[`01-robustness-theorems.md`](01-robustness-theorems.md): the *runtime
check* runs inside the loop (after the fold it would be too late, the
memory is spent), while the *proof* factors it out to the boundary.

One implementation detail made the byte path line up: `ByteStep` (the
parallel byte-emitting worker's result) carries its channel arrays only in
an erased proof field, so it gained a runtime `samples : Nat` with its own
equation `samples = (chs.map (·.size)).sum`. Both loops therefore charge
identical costs at every bit depth; charging the byte path by
`bytes.size` instead would diverge from the sample path whenever a sample
serializes to other than two bytes.

## Speculative work needs its own budget

The serial check alone does not fix the bomb, because the parallel decoder
materializes frames *before* the serial loop runs: `stepsPar` and
`byteStepsPar` decode every sync-scan candidate into steps. On the
reproducer that is the whole 12 GB, spent before any budget is consulted.

Each chunk of candidates now gets its own allowance,
`decodeAmpl ·` (the input bytes its candidates span), and stops
precomputing when a frame would exceed it. Consecutive chunks span
disjoint input, so the precompute's total output stays within
`decodeAmpl · d.size` overall. This cap is heuristic and carries **no
proof obligation**: steps are an optimization, each carries its own
equation, and a dropped step just means the serial loop decodes that frame
on the spot under the global budget. That is the same design that makes
the parallel decoder trustworthy in the first place, paying off again:
anything that only *removes* steps cannot affect correctness.

## What is now proven, and what is deliberately not

The theorem the audit observed was missing now exists, for arbitrary
bytes, decoder-side:

```
Flac.decode_size_le :
  decode bytes = .ok a →
  2 * (a.channels.map (·.length)).sum ≤ 4096 * bytes.size + 65536
```

(via `Stream.decodeReference_size_le` and the accept-set transfer). A
regression test decodes a generated bomb on every path and checks encoded
silence still round-trips; the CLI on the 105 KB reproducer prints a clean
`DECODE ERROR` where it previously aborted.

Known residual, recorded so it is not rediscovered:

- **Rejection is not free.** The budget is charged after each frame is
  materialized, so a bomb costs up to the budget in memory before the
  `none` (measured ~2–3 GB peak RSS on the 105 KB reproducer). The bound
  is linear in input size, which is the guarantee; the constant is
  `decodeAmpl` times allocator overhead. Charging from the frame header's
  declared `blockSize × channels` *before* `readContent` allocates would
  shrink the constant substantially, but changes what the bridging
  equations are stated over. Worth doing if the constant ever matters.

- **P3 is not this bug.** `decodeBytes` still pre-sizes its output buffer
  from the header's untrusted `totalSamples`
  ([issue #3](https://github.com/ilyasergey/vinyl/issues/3)); that is an
  early-validation fix, one line, and its invisibility to the logic is the
  motivating example of
  [`cost-semantics.md`](cost-semantics.md).

- **The budget bounds samples, not resident bytes.** What the process
  actually spends per admitted sample (boxed arrays, concatenation copies,
  GC lag) is a runtime fact outside the logic; making *that* provable is
  again the cost-semantics note's territory.

## Checklist addition for new decoder paths

To the checklist in [`01-robustness-theorems.md`](01-robustness-theorems.md),
this incident adds:

- If the path materializes output, which budget bounds it, and is the
  check reachable *before* the allocation that needs it?
- If the path speculates (parallel precompute, prefetch, lookahead), does
  the speculation observe a budget of its own, and is dropping speculative
  work provably harmless?
- If a new cap rejects inputs: what is the encoder's provable worst case
  against that cap, and which guard keeps the encoder inside it? The
  capstone must stay hypothesis-free at the shipped defaults.
