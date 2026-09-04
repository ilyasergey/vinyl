# Reference-decoder non-tail recursion (readRiceSeq / readSIntSeq / restoreAux) — REFERENCE decoder only (corrected)

**Status: reference-decoder residual readers hardened (2026-08-31) and its per-sample LPC
restore `Lpc.restoreAux` hardened (2026-09-02, found live by `fz_proven_pairs` — last section);
shipped decoder verified UNAFFECTED. Not a shipped-decoder bug.** An earlier draft of this note filed this as
a stack-overflow DoS in the shipped array decoder. Two independent IR audits corrected
that; this note records the accurate finding.

## What is actually true

`Flac.Rice.readRiceSeq` / `readSIntSeq` (`Flac/Native/Rice.lean`) build their result
list with a non-tail `x :: rec …` — one native stack frame per residual sample. These
readers are reached **only** by the reference decoder:

```
Stream.decodeReference  (the List-Bool model, CLI `--decode`)
  → readFrames → Frame.readChannels → Subframe.read
  → Rice.readResidual → readParts → readPart → readRiceSeq / readSIntSeq
```

The **shipped array decoder** — `decodeArrays`, hence `decodeBytes` and `decodePcm16A`
(the CLI `--decode-pcm16` path and the benchmarked fused decoder) — does **not** use
them. Its residual layer is `Flac.Decode.readRiceSeqScan` / `readSIntSeqGo` /
`readPartsA` (`Flac/Native/Decode.lean`), which is already tail-recursive.

**IR evidence.** In `.lake/build/ir/Flac/Native/Decode.c` the complete set of
`Flac.Rice` callees is `Method_ofCode`, `Method_paramBits`, `Method_escapeCode`,
`partSizes` — **zero** residual-reader calls. The `readRiceSeqTR` / `readSIntSeqTR`
twins appear only in `.lake/build/ir/Flac/Native/Rice.c`, called from `readPart` on the
reference path.

## Origin of the earlier misattribution

The gdb backtrace to `lp_vinyl_Flac_Rice_readRiceSeq` was genuine, but it came from the
`fz_decode_stack` prober while it was still configured to decode via `vm_decode_ref`
(the reference decoder). When the prober was retargeted to `vm_decode_pcm16` (the shipped
decoder) the attribution to `decodePcm16A` was carried over by mistake — but the shipped
decoder never enters `Flac.Rice.*`, so it was never the source of the overflow.

## The change that landed (kept)

Tail twins `readRiceSeqAcc`/`readRiceSeqTR`, `readSIntSeqAcc`/`readSIntSeqTR` (accumulate
reversed, reverse once) with `@[csimp]` swaps `readRiceSeq = readRiceSeqTR`,
`readSIntSeq = readSIntSeqTR`. The compiler emits the tail forms; the kernel checks the
value-equalities, so every theorem over `readRiceSeq`/`readSIntSeq` is unchanged. Both
proofs are sound (independently re-verified: correct base/step, no reversal or off-by-one,
BitStream threaded identically), no `sorry`, no new `axiom`. The swaps are pinned by name
in `scripts/check.sh`.

**Scope of the benefit.** This is a sound hardening of the reference decoder's two
residual loops. It does **not** by itself make `decodeReference` stack-flat — the
List-Bool model has other non-tail loops, which is why the fuzz rig bounds its input by
`VINYL_REF_MAX_BYTES = 8192` (`vinyl_checks.c`). And it changes the shipped decoder not
at all.

## Pin

`fz_decode_stack` forks a bounded-stack child (`tools/vinyl_decode_probe`) that builds a
deep stream with **libFLAC** (subset off, block size up to the legal maximum 65535) and
decodes it with `decodePcm16A` (the SHIPPED decoder) under a small `RLIMIT_STACK`. It
survives at every stack size across the full legal block-size range — including a
**bs=65535 frame at a 256 KB stack** — a genuine forward regression pin that the shipped
array decoder's residual/frame readers stay stack-flat. The emitter is libFLAC (outside
the Lean codec), so a decode signal is unambiguously the decoder. It does **not** cover
the two Rice twins above (they are on the reference path this prober does not touch). The
checked-Lean-encoder lane (bs ≤ 4608) remains available as `vinyl_decode_probe <...>
checked` for a Vinyl-encoded round-trip variant.

## Methodology note

The `@[csimp]` stack guarantee is *enumerative* — a missing swap is invisible to a gate
that only pins the swaps that exist — so a bounded-stack prober that catalogues the
ok→crash frontier is the right instrument. Here it produced a real, useful negative
result: the shipped decoder's residual layer is stack-flat, verified by both the IR and
the prober. The lesson recorded for the record is the attribution discipline: pin the
exact function the prober decodes, and read the IR to confirm which reader that path
actually calls before naming it in a finding.

## 2026-09-02 — `Lpc.restoreAux` (reference decoder), `repro-restoreAux-3343B.flac`

The 12 h campaign's `fz_proven_pairs` died with `Stack overflow detected. Aborting.` on this
3343-byte malformed input (sha256 `ea1838efd14b5af7b616794fd99deec36fd1566a47c5c56d2829cb9ca4b6550d`). gdb: ~3000 innermost frames in
`lp_vinyl_Flac_Lpc_restoreAux` — the List-Bool reference decoder's per-sample LPC restore,
non-tail, depth = the *declared* block size, so a malformed header can drive it 65535 deep
regardless of input size (the target's 4096 B cap does not bound the model). The PRODUCTION
decoder rejects the input cleanly (`measure_decode` decoded=0; CLI "not a decodable FLAC
stream"), so this is the reference-path class above, NOT a shipped bug. Fix: `restoreAuxTR`
`@[csimp]` twin in `Flac/Native/Lpc.lean` (value-equal; pinned in `scripts/check.sh`) — the
decode-side sibling of `residualAuxTR`. After it the input runs in 122 ms as a clean
`both_none` proven pair. Regression: `build/bin/fz_proven_pairs.fuzz fuzz/findings/decoder-stack-overflow-readriceseq/repro-restoreAux-3343B.flac`.
