import Flac.Native.Frame
import Flac.Native.Subframe
import Flac.Native.Rice
import Flac.Native.Emit
import Flac.Native.Encode
import Flac.Native.Decode
import Flac.Native.Codec

/-!
# Adversarial encoder choosers for the fuzz harness

Out of the proof surface (this file lives in `FlacTest/`, imports only
`Flac/Native/`, and defines no theorem). Each `@[export]`ed function is an
`EncoderCfg.chooser` (`List (List Int) → Frame.ChannelAsg`) that returns a
*valid* channel assignment the default heuristic chooser never emits, so the
encoder — and therefore the decoder, differentially — exercises the format
regions Vinyl otherwise leaves untested: LPC orders 9–32, mid/side
decorrelation, and high partition orders (`COVERAGE.md` claims 1–32 / all three
stereo modes / partition orders to 15, but the default chooser reaches almost
none of it).

Two safety properties make these usable in a fuzzer:

* **Every residual is ESCAPE-coded** (`Partition.escape 31`), i.e. stored at a
  fixed 31-bit width. There is no Rice unary run, so a hostile config can never
  blow the encoder up into a multi-gigabyte output the way a small Rice `k` on a
  large residual would.
* **`EncoderCfg.safeChooser` runs every output through `ChannelAsg.orVerbatim`**,
  which keeps the config only if it carries a `ChannelAsg.Valid` certificate and
  otherwise falls back to per-channel VERBATIM. So on any frame where the config
  is not valid (a short last frame, or a residual that does not fit 31 bits) the
  result is a bounded, correct VERBATIM frame — a no-op, never a crash.

The C harness (`fuzz/common/vinyl_gen.c`) installs one of these as `cfg.chooser`
via `lean_alloc_closure(fn, 1, 0)`.
-/

open Flac Flac.Frame Flac.Subframe Flac.Rice

/-- `2^po` partitions, each storing its residuals unencoded at 31 bits. Fixed
    width ⇒ the output size is bounded no matter how large the residuals get. -/
private def escResidual (po : Nat) : ResidualCfg :=
  { method := .rice4, po := po, choices := List.replicate (2 ^ po) (.escape 31) }

/-- An order-`n` LPC subframe whose only nonzero coefficient is the first
    (predict = the previous sample), so the residual is the first difference —
    small on correlated audio, and escape-coded so bounded regardless. Reaches
    the order-9..32 LPC decode path that Vinyl's own encoder never emits. -/
private def lpcSub (n : Nat) : SubCfg :=
  ⟨0, .lpc ((1 : Int) :: List.replicate (n - 1) (0 : Int)) 0 15 (escResidual 0)⟩

/-- Force an order-32 LPC subframe on every channel. -/
@[export vinyl_hostileLpc32]
def hostileLpc32 : List (List Int) → ChannelAsg := fun fr =>
  .independent (fr.map fun _ => lpcSub 32)

/-- Force mid/side stereo decorrelation (with an order-8 LPC subframe per
    decorrelated channel) on a 2-channel frame; independent LPC otherwise. -/
@[export vinyl_hostileStereo]
def hostileStereo : List (List Int) → ChannelAsg := fun fr =>
  match fr with
  | [_, _] => .midSide (lpcSub 8) (lpcSub 8)
  | _      => .independent (fr.map fun _ => lpcSub 8)

/-- Force a FIXED order-2 predictor with a high partition order (2^4 = 16
    partitions), exercising the high-partition-order residual decode path. -/
@[export vinyl_hostilePartition]
def hostilePartition : List (List Int) → ChannelAsg := fun fr =>
  .independent (fr.map fun _ => (⟨0, .fixed 2 (escResidual 4)⟩ : SubCfg))

/-- Force a FIXED order-1 predictor RICE-coded (NOT escape), with a LARGE Rice
    parameter (rice5 k=28). Unlike the escape-coded choosers above -- whose
    `Partition.Valid` requires `FitsSInt bits`, i.e. |r| < 2^30, so they can never
    emit a bound-violating residual -- a `.rice` partition imposes no
    residual-magnitude constraint. On large-swing 32-bit audio the first
    difference exceeds §9.2.7.3's |r| < 2^31 bound, reaching the residual-bound
    surface the escape choosers avoid. The large k is load-bearing: it keeps the
    UNARY quotient (`zigzag(r) >> k`) small (~32 bits/sample) so the emitted run
    stays bounded -- a small k would make `bitsToByteList` recurse over a
    multi-megabyte run and overflow the generator's own stack. -/
@[export vinyl_hostileFixed]
def hostileFixed : List (List Int) → ChannelAsg := fun fr =>
  .independent (fr.map fun _ =>
    (⟨0, .fixed 1 { method := .rice5, po := 0, choices := [.rice 28] }⟩ : SubCfg))

/-! ## Parameterized hostile choosers (Phase B3)

Captured-`Nat` variants of the fixed choosers above so the C harness can sweep
the parameter space (LPC order, partition order, RICE2 `k`, stereo mode) from
the free chooser slots. Each is exported at arity 2 and installed via
`lean_alloc_closure(fn, 2, 1)` with the captured `Nat` boxed into slot 0,
yielding the arity-1 `EncoderCfg.chooser` the encoder expects. `safeChooser` /
`ChannelAsg.orVerbatim` still gate every frame, so any parameter that yields an
invalid config falls back to a bounded VERBATIM frame. -/

/-- Like `hostileLpc32`, but with the LPC order supplied by the caller — sweeps
    the order-1..32 LPC decode path (e.g. the order-7 hole). -/
@[export vinyl_hostileLpcN]
def hostileLpcN (ord : Nat) : List (List Int) → ChannelAsg := fun fr =>
  .independent (fr.map fun _ => lpcSub ord)

/-- Like `hostilePartition`, but with the partition order supplied by the
    caller (`2 ^ po` escape-coded partitions). -/
@[export vinyl_hostilePartitionPO]
def hostilePartitionPO (po : Nat) : List (List Int) → ChannelAsg := fun fr =>
  .independent (fr.map fun _ => (⟨0, .fixed 2 (escResidual po)⟩ : SubCfg))

/-- Like `hostileFixed`, but with the RICE2 (`.rice5`) parameter supplied by the
    caller. Keep `k` large on wide-swing audio so the unary quotient stays
    bounded (see `hostileFixed`). -/
@[export vinyl_hostileRice2K]
def hostileRice2K (k : Nat) : List (List Int) → ChannelAsg := fun fr =>
  .independent (fr.map fun _ =>
    (⟨0, .fixed 1 { method := .rice5, po := 0, choices := [.rice k] }⟩ : SubCfg))

/-- Force a stereo decorrelation mode on a 2-channel frame: `0` independent,
    `1` left/side, `2` right/side, `3` mid/side (order-8 LPC per subframe).
    Any other mode, or a frame that is not exactly 2 channels, falls back to
    independent LPC. -/
@[export vinyl_hostileStereoMode]
def hostileStereoMode (m : Nat) : List (List Int) → ChannelAsg := fun fr =>
  match fr, m with
  | [_, _], 1 => .leftSide (lpcSub 8) (lpcSub 8)
  | [_, _], 2 => .rightSide (lpcSub 8) (lpcSub 8)
  | [_, _], 3 => .midSide (lpcSub 8) (lpcSub 8)
  | _, _      => .independent (fr.map fun _ => lpcSub 8)

/-- Deliberately emit an assignment that fails `ChannelAsg.Valid` — one more
    subframe config than there are channels — so the `Decidable (Valid …)` and
    `safeChooser`/`ChannelAsg.orVerbatim` reject arms run. The fallback keeps
    the frame a bounded, correct VERBATIM, so it is safe despite being invalid. -/
@[export vinyl_hostileInvalid]
def hostileInvalid : List (List Int) → ChannelAsg := fun fr =>
  .independent ((⟨0, .verbatim⟩ : SubCfg) :: fr.map fun _ => lpcSub 8)

/-- Re-export the SHIPPED fast encoder's chooser (out of the proof surface, in
    `FlacTest/`) so the C harness can build the exact `EncoderCfg` the
    `encodePcm16_eq` proven pair quantifies over: `Encode.encodePcm16` vs
    `Unchecked.encode ⟨bs, false, fastChooser 16⟩` (Phase 6G/7A). Exported
    uncurried: `vinyl_fastChooser(b, fr)`. -/
@[export vinyl_fastChooser]
def fuzzFastChooser (b : Nat) (fr : List (List Int)) : ChannelAsg :=
  Flac.Encode.fastChooser b fr

/-! ## Stable C entry-point names (Phase 7A)

The harness C used to `extern` the mangled `lp_vinyl_Flac_*` names directly, so a
Lean-internal rename broke the rig at link. These `@[export vinyl_*]` re-exports
give the fuzz harness a STABLE ABI (Lean emits both `vinyl_*` and `vinyl_*___boxed`
from each): a rename now touches only the one line below, and `check-symbols`
(llvm-nm) gates on these stable names. Out of the proof surface -- `FlacTest/`,
no theorem, `Flac/` untouched. -/

@[export vinyl_decode_bytes]     def fzDecodeBytes     := Flac.Decode.decodeBytes
@[export vinyl_decode_arrays]    def fzDecodeArrays    := Flac.Decode.decodeArrays
@[export vinyl_read_meta]        def fzReadMeta        := Flac.Decode.readMeta
@[export vinyl_decode_option]    def fzDecodeOption    := Flac.Decode.decodeOption
@[export vinyl_decode_pcm16a]    def fzDecodePcm16A    := Flac.decodePcm16A
@[export vinyl_decode_reference] def fzDecodeReference := Flac.Stream.decodeReference
@[export vinyl_pcm_bytes]        def fzPcmBytes        := Flac.Stream.pcmBytes
@[export vinyl_pcm_bytes_range]  def fzPcmBytesRange   := Flac.Stream.pcmBytesRange
@[export vinyl_encode]           def fzEncode          := Flac.encode
@[export vinyl_encode_pcm16_fast] def fzEncodePcm16Fast := Flac.encodePcm16Fast
@[export vinyl_encode_pcm16_cfg] def fzEncodePcm16Cfg  := Flac.encodePcm16Cfg
-- vlean_ prefix for these two: the harness already owns C API functions named
-- `vinyl_md5` / `vinyl_unchecked_encode` (vinyl_modes.h) with different signatures.
@[export vlean_unchecked_encode] def fzUncheckedEncode := Flac.Stream.Unchecked.encode
@[export vinyl_default_chooser]  def fzDefaultChooser  := Flac.Heuristics.defaultAsgChooser
@[export vlean_md5]              def fzMd5             := Flac.Md5.md5

-- A3e / C5: stable ABI for the emit writer and the pcm16 encode pipeline, so
-- `fz_encode_pcm16_eq.c` and `vinyl_gen.c` can drop the mangled `lp_vinyl_*`
-- names. Same arity/shape as the wrapped defs (emitFast: cfg, audio;
-- encodePcm16: blockSize, ch, sr, bytes; deinterleave: ch, samples;
-- pcm16OfByteList: bytes).
@[export vinyl_emit_fast]           def fzEmitFast        := Flac.Emit.emitFast
@[export vinyl_encode_pcm16]        def fzEncodePcm16     := Flac.Encode.encodePcm16
@[export vinyl_deinterleave]        def fzDeinterleave    := Flac.deinterleave
@[export vinyl_pcm16_of_byte_list]  def fzPcm16OfByteList := Flac.pcm16OfByteList
