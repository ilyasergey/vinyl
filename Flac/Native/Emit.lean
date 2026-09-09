import Flac.Native.Bits
import Flac.Native.Rice
import Flac.Native.Subframe
import Flac.Native.Lpc
import Flac.Native.Frame
import Flac.Native.Crc
import Flac.Native.Utf8Num
import Flac.Native.Stream

/-!
# The verified fast emitter — bit writer layer

`W` is a byte buffer plus a small bit accumulator (the low `n` bits of
`acc`, `n < 8` between pushes, MSB-first). Every primitive is proven in
`Flac.Spec.Emit` to *emit* exactly what the corresponding `List Bool`
model writer produces: `(f w).bits = w.bits ++ modelBits`. That is the
writer-side mirror of the reader simulation (`Flac.Spec.Reader`), and it
is what lets `Flac.Stream.Unchecked.encode` run on arrays and a `ByteArray` without
touching any theorem statement.

The accumulator is a `Nat` (scalar for our sizes): `acc < 2^n` is an
invariant, pushes are chunked to ≤ 32 bits, and all arithmetic uses the
GMP-free `p2` table and `>>>`/`&&&`.
-/

namespace Flac.Emit

open Flac.Bits (p2)

/-- The bit writer: completed bytes in `buf`, pending bits in the low
    `n` bits of `acc` (`n < 8`, `acc < 2^n` — `Flac.Spec.Emit.Inv`). -/
structure W where
  buf : ByteArray
  acc : Nat
  n : Nat

namespace W

def empty (cap : Nat) : W := ⟨ByteArray.emptyWithCapacity cap, 0, 0⟩

/-- Emit completed bytes out of the accumulator. -/
def flushGo (buf : ByteArray) (acc n : Nat) : ByteArray × Nat × Nat :=
  if _h : n < 8 then (buf, acc, n)
  else
    let hi := n - 8
    flushGo (buf.push (UInt8.ofNat (acc >>> hi))) (acc &&& (p2 hi - 1)) hi
termination_by n
decreasing_by omega

/-- Push the low `k` bits of `v`, MSB first (callers keep `k ≤ 32`;
    `v` is masked). -/
def push (w : W) (k v : Nat) : W :=
  let (buf, acc, n) := flushGo w.buf (w.acc * p2 k + (v &&& (p2 k - 1))) (w.n + k)
  ⟨buf, acc, n⟩

/-- Arbitrary-width big-endian push, chunked to keep the accumulator
    scalar. -/
def pushBits (w : W) (k v : Nat) : W :=
  if _h : k ≤ 32 then w.push k v
  else (w.pushBits (k - 32) (v >>> 32)).push 32 (v &&& 0xFFFFFFFF)
termination_by k
decreasing_by omega

/-- Unary code: `q` zero bits, then a one bit. -/
def pushUnary (w : W) (q : Nat) : W :=
  if _h : q < 32 then w.push (q + 1) 1
  else pushUnary (w.push 32 0) (q - 32)
termination_by q
decreasing_by omega

/-- `k`-bit two's complement (computes `Flac.Bits.writeSInt`). -/
def pushSInt (w : W) (k : Nat) (x : Int) : W :=
  w.pushBits k ((x + ((p2 k : Nat) : Int)).toNat &&& (p2 k - 1))

/-- Rice code with parameter `k` (computes `Flac.Rice.writeRice`). -/
def pushRice (w : W) (k : Nat) (x : Int) : W :=
  let u := Rice.zigzag x
  (w.pushUnary (u >>> k)).push k (u &&& (p2 k - 1))

/-! ## Sequences, partitions, residuals (mirroring the model writers) -/

/-- Fixed-width run over the segment `xs[start .. start+len)` (stopping
    at the array end, exactly like the model's `take`). -/
def pushSIntSeg (b : Nat) (xs : Array Int) : (start len : Nat) → W → W
  | _, 0, w => w
  | start, len + 1, w =>
    if start < xs.size then
      pushSIntSeg b xs (start + 1) len (w.pushSInt b (xs.getD start 0))
    else w

/-- Rice run over the segment `xs[start .. start+len)` (stopping at the
    array end). -/
def pushRiceSeg (k : Nat) (xs : Array Int) : (start len : Nat) → W → W
  | _, 0, w => w
  | start, len + 1, w =>
    if start < xs.size then
      pushRiceSeg k xs (start + 1) len (w.pushRice k (xs.getD start 0))
    else w

/-- Fixed-width run over a (short) list — LPC coefficients. -/
def pushSIntList (b : Nat) : List Int → W → W
  | [], w => w
  | x :: xs, w => pushSIntList b xs (w.pushSInt b x)

/-- The partitions of a coded residual, one `(choice, size)` pair at a
    time, walking `res` by index (computes
    `writeParts ∘ zip choices ∘ chunkBySizes`). -/
def pushParts (m : Rice.Method) (res : Array Int) :
    (choices : List Rice.Partition) → (sizes : List Nat) → (start : Nat) → W → W
  | [], _, _, w => w
  | _ :: _, [], _, w => w
  | ch :: choices, sz :: sizes, start, w =>
    let w' := match ch with
      | .rice k => pushRiceSeg k res start sz (w.push m.paramBits k)
      | .escape bits =>
        pushSIntSeg bits res start sz
          ((w.push m.paramBits m.escapeCode).push 5 bits)
    pushParts m res choices sizes (start + sz) w'

/-- A coded residual (computes `Rice.writeResidual`). -/
def pushResidual (bs ord : Nat) (cfg : Rice.ResidualCfg) (res : Array Int)
    (w : W) : W :=
  pushParts cfg.method res cfg.choices (Rice.partSizes bs cfg.po ord) 0
    ((w.push 2 cfg.method.code).push 4 cfg.po)

end W

/-! ## Predictor residuals over arrays (structural, for the proofs) -/

/-- First differences: `rem` of them starting at index `i`. -/
def diffGo (xs : Array Int) : (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    diffGo xs (i + 1) rem (out.push (xs.getD (i + 1) 0 - xs.getD i 0))

/-- `Fixed.diff1` over arrays. -/
def diffA (xs : Array Int) : Array Int :=
  diffGo xs 0 (xs.size - 1) (Array.emptyWithCapacity (xs.size - 1))

/-- `Fixed.residual` (the `ord`-th difference) over arrays. -/
def fixedResA : (ord : Nat) → Array Int → Array Int
  | 0, xs => xs
  | ord + 1, xs => diffA (fixedResA ord xs)

/-- LPC residuals: `rem` of them starting at index `i`, predicting from
    the array prefix (`Lpc.dotA` walks it most-recent-first). -/
def lpcResGo (cs : List Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo cs shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dotA cs xs (i - 1)) shift))

/-! ### Tap-specialised residual loops

One loop per coefficient count, so the specialisation is chosen **once per
subframe** by `lpcResA` and the taps are loop-invariant parameters that stay in
registers for the whole block. `Flac.Spec.Emit.lpcResGo{k}_eq` proves each is
`lpcResGo` at a fixed coefficient list. -/

def lpcResGo1 (c0 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo1 c0 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot1At xs c0 i) shift))

def lpcResGo2 (c0 c1 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo2 c0 c1 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot2At xs c0 c1 i) shift))

def lpcResGo3 (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo3 c0 c1 c2 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot3At xs c0 c1 c2 i) shift))

def lpcResGo4 (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo4 c0 c1 c2 c3 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot4At xs c0 c1 c2 c3 i) shift))

def lpcResGo5 (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo5 c0 c1 c2 c3 c4 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot5At xs c0 c1 c2 c3 c4 i) shift))

def lpcResGo6 (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot6At xs c0 c1 c2 c3 c4 c5 i) shift))

def lpcResGo7 (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot7At xs c0 c1 c2 c3 c4 c5 c6 i) shift))

def lpcResGo8 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot8At xs c0 c1 c2 c3 c4 c5 c6 c7 i) shift))

/-! ### The machine-word residual loops

`lpcResGo{k}` above are what the theorems read; what the encoder *runs* are
`lpcResGo{k}Fast` below, swapped in by `lpcResGo{k}_eq_fast` (`@[csimp]`).
Each is the same loop on `Int64`: taps and shift as machine words, the
`k` history samples carried in registers (`lpcResWin{k}`), `x - (Σ >>> shift)`
stored boxed. The taps are bounded by `2^15` once per subframe and each
sample by `2^30` as it enters the window, so every prediction sum is below
`2^53` and exact in a word (`Lpc.dot64_toInt_range`); a sample outside the
bound hands the rest of the block to the boxed loop (`lpcResGo{k}Slow`, a
copy so the swap cannot recurse into itself). -/

private theorem getD_lt (xs : Array Int) {i : Nat} (h : i < xs.size) : xs.getD i 0 = xs[i] := by
  simp [Array.getD, h]

/-- `lpcResGo1` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo1Slow (c0 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo1Slow c0 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot1At xs c0 i) shift))

/-- `lpcResGo1` with the last 1 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin1 (c0 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 : Int64) → Array Int → Array Int
  | _, 0, _, out => out
  | i, rem + 1, w0, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin1 c0 sh shift xs (i + 1) rem xi (out.push ((xi - p).toInt))
    else lpcResGo1Slow c0 shift xs i (rem + 1) out

def lpcResGo1Fast (c0 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 1 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 1) 0) = true then
    lpcResWin1 c0 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 1) 0).toInt64 out
  else lpcResGo1Slow c0 shift xs i rem out

/-- `lpcResGo2` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo2Slow (c0 c1 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo2Slow c0 c1 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot2At xs c0 c1 i) shift))

/-- `lpcResGo2` with the last 2 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin2 (c0 c1 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 : Int64) → Array Int → Array Int
  | _, 0, _, _, out => out
  | i, rem + 1, w0, w1, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w1 + c1.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin2 c0 c1 sh shift xs (i + 1) rem w1 xi (out.push ((xi - p).toInt))
    else lpcResGo2Slow c0 c1 shift xs i (rem + 1) out

def lpcResGo2Fast (c0 c1 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 2 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 2) 0) = true ∧
      Bits.small31 (xs.getD (i - 2 + 1) 0) = true then
    lpcResWin2 c0 c1 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 2) 0).toInt64 (xs.getD (i - 2 + 1) 0).toInt64 out
  else lpcResGo2Slow c0 c1 shift xs i rem out

/-- `lpcResGo3` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo3Slow (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo3Slow c0 c1 c2 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot3At xs c0 c1 c2 i) shift))

/-- `lpcResGo3` with the last 3 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin3 (c0 c1 c2 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 w2 : Int64) → Array Int → Array Int
  | _, 0, _, _, _, out => out
  | i, rem + 1, w0, w1, w2, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w2 + c1.toInt64 * w1 + c2.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin3 c0 c1 c2 sh shift xs (i + 1) rem w1 w2 xi (out.push ((xi - p).toInt))
    else lpcResGo3Slow c0 c1 c2 shift xs i (rem + 1) out

def lpcResGo3Fast (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 3 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1, c2], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 3) 0) = true ∧
      Bits.small31 (xs.getD (i - 3 + 1) 0) = true ∧
      Bits.small31 (xs.getD (i - 3 + 2) 0) = true then
    lpcResWin3 c0 c1 c2 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 3) 0).toInt64 (xs.getD (i - 3 + 1) 0).toInt64 (xs.getD (i - 3 + 2) 0).toInt64 out
  else lpcResGo3Slow c0 c1 c2 shift xs i rem out

/-- `lpcResGo4` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo4Slow (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo4Slow c0 c1 c2 c3 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot4At xs c0 c1 c2 c3 i) shift))

/-- `lpcResGo4` with the last 4 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin4 (c0 c1 c2 c3 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 w2 w3 : Int64) → Array Int → Array Int
  | _, 0, _, _, _, _, out => out
  | i, rem + 1, w0, w1, w2, w3, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w3 + c1.toInt64 * w2 + c2.toInt64 * w1 + c3.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin4 c0 c1 c2 c3 sh shift xs (i + 1) rem w1 w2 w3 xi (out.push ((xi - p).toInt))
    else lpcResGo4Slow c0 c1 c2 c3 shift xs i (rem + 1) out

def lpcResGo4Fast (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 4 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1, c2, c3], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 4) 0) = true ∧
      Bits.small31 (xs.getD (i - 4 + 1) 0) = true ∧
      Bits.small31 (xs.getD (i - 4 + 2) 0) = true ∧
      Bits.small31 (xs.getD (i - 4 + 3) 0) = true then
    lpcResWin4 c0 c1 c2 c3 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 4) 0).toInt64 (xs.getD (i - 4 + 1) 0).toInt64 (xs.getD (i - 4 + 2) 0).toInt64 (xs.getD (i - 4 + 3) 0).toInt64 out
  else lpcResGo4Slow c0 c1 c2 c3 shift xs i rem out

/-- `lpcResGo5` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo5Slow (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo5Slow c0 c1 c2 c3 c4 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot5At xs c0 c1 c2 c3 c4 i) shift))

/-- `lpcResGo5` with the last 5 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin5 (c0 c1 c2 c3 c4 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 w2 w3 w4 : Int64) → Array Int → Array Int
  | _, 0, _, _, _, _, _, out => out
  | i, rem + 1, w0, w1, w2, w3, w4, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w4 + c1.toInt64 * w3 + c2.toInt64 * w2 + c3.toInt64 * w1 + c4.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin5 c0 c1 c2 c3 c4 sh shift xs (i + 1) rem w1 w2 w3 w4 xi (out.push ((xi - p).toInt))
    else lpcResGo5Slow c0 c1 c2 c3 c4 shift xs i (rem + 1) out

def lpcResGo5Fast (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 5 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1, c2, c3, c4], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 5) 0) = true ∧
      Bits.small31 (xs.getD (i - 5 + 1) 0) = true ∧
      Bits.small31 (xs.getD (i - 5 + 2) 0) = true ∧
      Bits.small31 (xs.getD (i - 5 + 3) 0) = true ∧
      Bits.small31 (xs.getD (i - 5 + 4) 0) = true then
    lpcResWin5 c0 c1 c2 c3 c4 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 5) 0).toInt64 (xs.getD (i - 5 + 1) 0).toInt64 (xs.getD (i - 5 + 2) 0).toInt64 (xs.getD (i - 5 + 3) 0).toInt64 (xs.getD (i - 5 + 4) 0).toInt64 out
  else lpcResGo5Slow c0 c1 c2 c3 c4 shift xs i rem out

/-- `lpcResGo6` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo6Slow (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo6Slow c0 c1 c2 c3 c4 c5 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot6At xs c0 c1 c2 c3 c4 c5 i) shift))

/-- `lpcResGo6` with the last 6 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin6 (c0 c1 c2 c3 c4 c5 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 w2 w3 w4 w5 : Int64) → Array Int → Array Int
  | _, 0, _, _, _, _, _, _, out => out
  | i, rem + 1, w0, w1, w2, w3, w4, w5, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w5 + c1.toInt64 * w4 + c2.toInt64 * w3 + c3.toInt64 * w2 + c4.toInt64 * w1 + c5.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin6 c0 c1 c2 c3 c4 c5 sh shift xs (i + 1) rem w1 w2 w3 w4 w5 xi (out.push ((xi - p).toInt))
    else lpcResGo6Slow c0 c1 c2 c3 c4 c5 shift xs i (rem + 1) out

def lpcResGo6Fast (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 6 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1, c2, c3, c4, c5], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 6) 0) = true ∧
      Bits.small31 (xs.getD (i - 6 + 1) 0) = true ∧
      Bits.small31 (xs.getD (i - 6 + 2) 0) = true ∧
      Bits.small31 (xs.getD (i - 6 + 3) 0) = true ∧
      Bits.small31 (xs.getD (i - 6 + 4) 0) = true ∧
      Bits.small31 (xs.getD (i - 6 + 5) 0) = true then
    lpcResWin6 c0 c1 c2 c3 c4 c5 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 6) 0).toInt64 (xs.getD (i - 6 + 1) 0).toInt64 (xs.getD (i - 6 + 2) 0).toInt64 (xs.getD (i - 6 + 3) 0).toInt64 (xs.getD (i - 6 + 4) 0).toInt64 (xs.getD (i - 6 + 5) 0).toInt64 out
  else lpcResGo6Slow c0 c1 c2 c3 c4 c5 shift xs i rem out

/-- `lpcResGo7` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo7Slow (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo7Slow c0 c1 c2 c3 c4 c5 c6 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot7At xs c0 c1 c2 c3 c4 c5 c6 i) shift))

/-- `lpcResGo7` with the last 7 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin7 (c0 c1 c2 c3 c4 c5 c6 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 w2 w3 w4 w5 w6 : Int64) → Array Int → Array Int
  | _, 0, _, _, _, _, _, _, _, out => out
  | i, rem + 1, w0, w1, w2, w3, w4, w5, w6, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w6 + c1.toInt64 * w5 + c2.toInt64 * w4 + c3.toInt64 * w3 + c4.toInt64 * w2 + c5.toInt64 * w1 + c6.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin7 c0 c1 c2 c3 c4 c5 c6 sh shift xs (i + 1) rem w1 w2 w3 w4 w5 w6 xi (out.push ((xi - p).toInt))
    else lpcResGo7Slow c0 c1 c2 c3 c4 c5 c6 shift xs i (rem + 1) out

def lpcResGo7Fast (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 7 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1, c2, c3, c4, c5, c6], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 7) 0) = true ∧
      Bits.small31 (xs.getD (i - 7 + 1) 0) = true ∧
      Bits.small31 (xs.getD (i - 7 + 2) 0) = true ∧
      Bits.small31 (xs.getD (i - 7 + 3) 0) = true ∧
      Bits.small31 (xs.getD (i - 7 + 4) 0) = true ∧
      Bits.small31 (xs.getD (i - 7 + 5) 0) = true ∧
      Bits.small31 (xs.getD (i - 7 + 6) 0) = true then
    lpcResWin7 c0 c1 c2 c3 c4 c5 c6 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 7) 0).toInt64 (xs.getD (i - 7 + 1) 0).toInt64 (xs.getD (i - 7 + 2) 0).toInt64 (xs.getD (i - 7 + 3) 0).toInt64 (xs.getD (i - 7 + 4) 0).toInt64 (xs.getD (i - 7 + 5) 0).toInt64 (xs.getD (i - 7 + 6) 0).toInt64 out
  else lpcResGo7Slow c0 c1 c2 c3 c4 c5 c6 shift xs i rem out

/-- `lpcResGo8` verbatim: the swap's fallback must not be the swapped name. -/
def lpcResGo8Slow (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → Array Int → Array Int
  | _, 0, out => out
  | i, rem + 1, out =>
    lpcResGo8Slow c0 c1 c2 c3 c4 c5 c6 c7 shift xs (i + 1) rem
      (out.push (xs.getD i 0 - Flac.Bits.sar (Lpc.dot8At xs c0 c1 c2 c3 c4 c5 c6 c7 i) shift))

/-- `lpcResGo8` with the last 8 samples carried as machine words (oldest
    first) and the sample bound checked as each sample enters: one load and one
    conversion per sample, no separate guard pass. A sample outside `2^30`
    hands the rest of the block to the boxed loop. -/
def lpcResWin8 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (sh : Int64) (shift : Nat) (xs : Array Int) :
    (i rem : Nat) → (w0 w1 w2 w3 w4 w5 w6 w7 : Int64) → Array Int → Array Int
  | _, 0, _, _, _, _, _, _, _, _, out => out
  | i, rem + 1, w0, w1, w2, w3, w4, w5, w6, w7, out =>
    let x := xs.getD i 0
    if Bits.small31 x then
      let p := (c0.toInt64 * w7 + c1.toInt64 * w6 + c2.toInt64 * w5 + c3.toInt64 * w4 + c4.toInt64 * w3 + c5.toInt64 * w2 + c6.toInt64 * w1 + c7.toInt64 * w0) >>> sh
      let xi := x.toInt64
      lpcResWin8 c0 c1 c2 c3 c4 c5 c6 c7 sh shift xs (i + 1) rem w1 w2 w3 w4 w5 w6 w7 xi (out.push ((xi - p).toInt))
    else lpcResGo8Slow c0 c1 c2 c3 c4 c5 c6 c7 shift xs i (rem + 1) out

def lpcResGo8Fast (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int) (i rem : Nat)
    (out : Array Int) : Array Int :=
  if h : 8 ≤ i ∧ i + rem ≤ xs.size ∧ shift < 64 ∧ (∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7], Bits.FitsSInt 16 c) ∧
      Bits.small31 (xs.getD (i - 8) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 1) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 2) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 3) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 4) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 5) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 6) 0) = true ∧
      Bits.small31 (xs.getD (i - 8 + 7) 0) = true then
    lpcResWin8 c0 c1 c2 c3 c4 c5 c6 c7 (Int64.ofNat shift) shift xs i rem (xs.getD (i - 8) 0).toInt64 (xs.getD (i - 8 + 1) 0).toInt64 (xs.getD (i - 8 + 2) 0).toInt64 (xs.getD (i - 8 + 3) 0).toInt64 (xs.getD (i - 8 + 4) 0).toInt64 (xs.getD (i - 8 + 5) 0).toInt64 (xs.getD (i - 8 + 6) 0).toInt64 (xs.getD (i - 8 + 7) 0).toInt64 out
  else lpcResGo8Slow c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out

/-! #### The machine-word residual loops compute the boxed ones -/

theorem lpcResGo1Slow_eq (c0 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo1Slow c0 shift xs i rem out = lpcResGo1 c0 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo1Slow, lpcResGo1]
    exact ih _ _

theorem lpcResWin1_eq (c0 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 : Int64) (out : Array Int), 1 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 1) 0).toInt64 →
      Bits.small31 (xs.getD (i - 1) 0) = true →
      lpcResWin1 c0 (Int64.ofNat shift) shift xs i rem w0 out
        = lpcResGo1 c0 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 out hK hle hw0 hs0
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hs0
    have hi : m + 1 < xs.size := by omega
    simp only [lpcResWin1]
    by_cases hx : Bits.small31 (xs.getD (m + 1) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 1 + 1) ((xs.getD (m + 1) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 1 + 1 - 1 = m + 1 by omega])
        (by rw [show m + 1 + 1 - 1 = m + 1 by omega]; exact hx)]
      simp only [lpcResGo1]
      subst hw0
      have hstep : (((xs.getD (m + 1) 0).toInt64
            - (c0.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 1) 0 - Flac.Bits.sar (Lpc.dot1At xs c0 (m + 1)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0] (m + 1) (by omega) 0 := by
          rw [Lpc.dot64_unfold1 xs c0 (m + 1) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 1 ≤ j + [c0].length → j < m + 1 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m := by omega
          rcases hj' with rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0] (m + 1) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0] (m + 1) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0] (m + 1) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0] (m + 1) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0] (m + 1) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0] (m + 1) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0] (m + 1) (by omega) 0) shift).natAbs
            ≤ 1 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot1At]
        rw [dif_pos (show m + 1 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold1 xs c0 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo1Slow_eq c0 shift xs (rem + 1) (m + 1) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo1_eq_fast : @lpcResGo1 = @lpcResGo1Fast := by
  funext c0 shift xs i rem out
  unfold lpcResGo1Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0⟩ := h
    exact (lpcResWin1_eq c0 shift xs hsh hc rem i _ out hK hle
      rfl hs0).symm
  · exact (lpcResGo1Slow_eq c0 shift xs rem i out).symm

theorem lpcResGo2Slow_eq (c0 c1 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo2Slow c0 c1 shift xs i rem out = lpcResGo2 c0 c1 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo2Slow, lpcResGo2]
    exact ih _ _

theorem lpcResWin2_eq (c0 c1 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 : Int64) (out : Array Int), 2 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 2) 0).toInt64 →
      w1 = (xs.getD (i - 2 + 1) 0).toInt64 →
      Bits.small31 (xs.getD (i - 2) 0) = true →
      Bits.small31 (xs.getD (i - 2 + 1) 0) = true →
      lpcResWin2 c0 c1 (Int64.ofNat shift) shift xs i rem w0 w1 out
        = lpcResGo2 c0 c1 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 out hK hle hw0 hw1 hs0 hs1
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hs0 hs1
    have hi : m + 2 < xs.size := by omega
    simp only [lpcResWin2]
    by_cases hx : Bits.small31 (xs.getD (m + 2) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 2 + 1) w1 ((xs.getD (m + 2) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 2 + 1 - 2 = m + 1 by omega]; exact hw1) (by rw [show m + 2 + 1 - 2 + 1 = m + 2 by omega])
        (by rw [show m + 2 + 1 - 2 = m + 1 by omega]; exact hs1) (by rw [show m + 2 + 1 - 2 + 1 = m + 2 by omega]; exact hx)]
      simp only [lpcResGo2]
      subst hw0
      subst hw1
      have hstep : (((xs.getD (m + 2) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 1) 0).toInt64 + c1.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 2) 0 - Flac.Bits.sar (Lpc.dot2At xs c0 c1 (m + 2)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c1.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1] (m + 2) (by omega) 0 := by
          rw [Lpc.dot64_unfold2 xs c0 c1 (m + 2) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 2 ≤ j + [c0, c1].length → j < m + 2 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 := by omega
          rcases hj' with rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1] (m + 2) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1] (m + 2) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1] (m + 2) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1] (m + 2) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1] (m + 2) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1] (m + 2) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1] (m + 2) (by omega) 0) shift).natAbs
            ≤ 2 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot2At]
        rw [dif_pos (show m + 2 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold2 xs c0 c1 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo2Slow_eq c0 c1 shift xs (rem + 1) (m + 2) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo2_eq_fast : @lpcResGo2 = @lpcResGo2Fast := by
  funext c0 c1 shift xs i rem out
  unfold lpcResGo2Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1⟩ := h
    exact (lpcResWin2_eq c0 c1 shift xs hsh hc rem i _ _ out hK hle
      rfl rfl hs0 hs1).symm
  · exact (lpcResGo2Slow_eq c0 c1 shift xs rem i out).symm

theorem lpcResGo3Slow_eq (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo3Slow c0 c1 c2 shift xs i rem out = lpcResGo3 c0 c1 c2 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo3Slow, lpcResGo3]
    exact ih _ _

theorem lpcResWin3_eq (c0 c1 c2 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1, c2], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 w2 : Int64) (out : Array Int), 3 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 3) 0).toInt64 →
      w1 = (xs.getD (i - 3 + 1) 0).toInt64 →
      w2 = (xs.getD (i - 3 + 2) 0).toInt64 →
      Bits.small31 (xs.getD (i - 3) 0) = true →
      Bits.small31 (xs.getD (i - 3 + 1) 0) = true →
      Bits.small31 (xs.getD (i - 3 + 2) 0) = true →
      lpcResWin3 c0 c1 c2 (Int64.ofNat shift) shift xs i rem w0 w1 w2 out
        = lpcResGo3 c0 c1 c2 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 w2 out hK hle hw0 hw1 hw2 hs0 hs1 hs2
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 3 := ⟨i - 3, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hw2 hs0 hs1 hs2
    have hi : m + 3 < xs.size := by omega
    simp only [lpcResWin3]
    by_cases hx : Bits.small31 (xs.getD (m + 3) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 3 + 1) w1 w2 ((xs.getD (m + 3) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 3 + 1 - 3 = m + 1 by omega]; exact hw1) (by rw [show m + 3 + 1 - 3 + 1 = m + 2 by omega]; exact hw2) (by rw [show m + 3 + 1 - 3 + 2 = m + 3 by omega])
        (by rw [show m + 3 + 1 - 3 = m + 1 by omega]; exact hs1) (by rw [show m + 3 + 1 - 3 + 1 = m + 2 by omega]; exact hs2) (by rw [show m + 3 + 1 - 3 + 2 = m + 3 by omega]; exact hx)]
      simp only [lpcResGo3]
      subst hw0
      subst hw1
      subst hw2
      have hstep : (((xs.getD (m + 3) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 2) 0).toInt64 + c1.toInt64 * (xs.getD (m + 1) 0).toInt64 + c2.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 3) 0 - Flac.Bits.sar (Lpc.dot3At xs c0 c1 c2 (m + 3)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega), getD_lt xs (show m + 2 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 2]'(by omega)).toInt64 + c1.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c2.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1, c2] (m + 3) (by omega) 0 := by
          rw [Lpc.dot64_unfold3 xs c0 c1 c2 (m + 3) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 3 ≤ j + [c0, c1, c2].length → j < m + 3 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 := by omega
          rcases hj' with rfl | rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs2
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1, c2] (m + 3) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1, c2] (m + 3) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1, c2] (m + 3) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1, c2] (m + 3) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1, c2] (m + 3) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2] (m + 3) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2] (m + 3) (by omega) 0) shift).natAbs
            ≤ 3 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot3At]
        rw [dif_pos (show m + 3 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold3 xs c0 c1 c2 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo3Slow_eq c0 c1 c2 shift xs (rem + 1) (m + 3) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo3_eq_fast : @lpcResGo3 = @lpcResGo3Fast := by
  funext c0 c1 c2 shift xs i rem out
  unfold lpcResGo3Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1, hs2⟩ := h
    exact (lpcResWin3_eq c0 c1 c2 shift xs hsh hc rem i _ _ _ out hK hle
      rfl rfl rfl hs0 hs1 hs2).symm
  · exact (lpcResGo3Slow_eq c0 c1 c2 shift xs rem i out).symm

theorem lpcResGo4Slow_eq (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo4Slow c0 c1 c2 c3 shift xs i rem out = lpcResGo4 c0 c1 c2 c3 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo4Slow, lpcResGo4]
    exact ih _ _

theorem lpcResWin4_eq (c0 c1 c2 c3 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1, c2, c3], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 w2 w3 : Int64) (out : Array Int), 4 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 4) 0).toInt64 →
      w1 = (xs.getD (i - 4 + 1) 0).toInt64 →
      w2 = (xs.getD (i - 4 + 2) 0).toInt64 →
      w3 = (xs.getD (i - 4 + 3) 0).toInt64 →
      Bits.small31 (xs.getD (i - 4) 0) = true →
      Bits.small31 (xs.getD (i - 4 + 1) 0) = true →
      Bits.small31 (xs.getD (i - 4 + 2) 0) = true →
      Bits.small31 (xs.getD (i - 4 + 3) 0) = true →
      lpcResWin4 c0 c1 c2 c3 (Int64.ofNat shift) shift xs i rem w0 w1 w2 w3 out
        = lpcResGo4 c0 c1 c2 c3 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 w2 w3 out hK hle hw0 hw1 hw2 hw3 hs0 hs1 hs2 hs3
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 4 := ⟨i - 4, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hw2 hw3 hs0 hs1 hs2 hs3
    have hi : m + 4 < xs.size := by omega
    simp only [lpcResWin4]
    by_cases hx : Bits.small31 (xs.getD (m + 4) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 4 + 1) w1 w2 w3 ((xs.getD (m + 4) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 4 + 1 - 4 = m + 1 by omega]; exact hw1) (by rw [show m + 4 + 1 - 4 + 1 = m + 2 by omega]; exact hw2) (by rw [show m + 4 + 1 - 4 + 2 = m + 3 by omega]; exact hw3) (by rw [show m + 4 + 1 - 4 + 3 = m + 4 by omega])
        (by rw [show m + 4 + 1 - 4 = m + 1 by omega]; exact hs1) (by rw [show m + 4 + 1 - 4 + 1 = m + 2 by omega]; exact hs2) (by rw [show m + 4 + 1 - 4 + 2 = m + 3 by omega]; exact hs3) (by rw [show m + 4 + 1 - 4 + 3 = m + 4 by omega]; exact hx)]
      simp only [lpcResGo4]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      have hstep : (((xs.getD (m + 4) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 3) 0).toInt64 + c1.toInt64 * (xs.getD (m + 2) 0).toInt64 + c2.toInt64 * (xs.getD (m + 1) 0).toInt64 + c3.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 4) 0 - Flac.Bits.sar (Lpc.dot4At xs c0 c1 c2 c3 (m + 4)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega), getD_lt xs (show m + 2 < xs.size by omega), getD_lt xs (show m + 3 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 3]'(by omega)).toInt64 + c1.toInt64 * (xs[m + 2]'(by omega)).toInt64 + c2.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c3.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1, c2, c3] (m + 4) (by omega) 0 := by
          rw [Lpc.dot64_unfold4 xs c0 c1 c2 c3 (m + 4) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 4 ≤ j + [c0, c1, c2, c3].length → j < m + 4 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 ∨ j = m + 3 := by omega
          rcases hj' with rfl | rfl | rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs2
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs3
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1, c2, c3] (m + 4) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1, c2, c3] (m + 4) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1, c2, c3] (m + 4) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1, c2, c3] (m + 4) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1, c2, c3] (m + 4) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3] (m + 4) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3] (m + 4) (by omega) 0) shift).natAbs
            ≤ 4 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot4At]
        rw [dif_pos (show m + 4 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold4 xs c0 c1 c2 c3 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo4Slow_eq c0 c1 c2 c3 shift xs (rem + 1) (m + 4) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo4_eq_fast : @lpcResGo4 = @lpcResGo4Fast := by
  funext c0 c1 c2 c3 shift xs i rem out
  unfold lpcResGo4Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1, hs2, hs3⟩ := h
    exact (lpcResWin4_eq c0 c1 c2 c3 shift xs hsh hc rem i _ _ _ _ out hK hle
      rfl rfl rfl rfl hs0 hs1 hs2 hs3).symm
  · exact (lpcResGo4Slow_eq c0 c1 c2 c3 shift xs rem i out).symm

theorem lpcResGo5Slow_eq (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo5Slow c0 c1 c2 c3 c4 shift xs i rem out = lpcResGo5 c0 c1 c2 c3 c4 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo5Slow, lpcResGo5]
    exact ih _ _

theorem lpcResWin5_eq (c0 c1 c2 c3 c4 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1, c2, c3, c4], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 w2 w3 w4 : Int64) (out : Array Int), 5 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 5) 0).toInt64 →
      w1 = (xs.getD (i - 5 + 1) 0).toInt64 →
      w2 = (xs.getD (i - 5 + 2) 0).toInt64 →
      w3 = (xs.getD (i - 5 + 3) 0).toInt64 →
      w4 = (xs.getD (i - 5 + 4) 0).toInt64 →
      Bits.small31 (xs.getD (i - 5) 0) = true →
      Bits.small31 (xs.getD (i - 5 + 1) 0) = true →
      Bits.small31 (xs.getD (i - 5 + 2) 0) = true →
      Bits.small31 (xs.getD (i - 5 + 3) 0) = true →
      Bits.small31 (xs.getD (i - 5 + 4) 0) = true →
      lpcResWin5 c0 c1 c2 c3 c4 (Int64.ofNat shift) shift xs i rem w0 w1 w2 w3 w4 out
        = lpcResGo5 c0 c1 c2 c3 c4 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 w2 w3 w4 out hK hle hw0 hw1 hw2 hw3 hw4 hs0 hs1 hs2 hs3 hs4
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 5 := ⟨i - 5, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hw2 hw3 hw4 hs0 hs1 hs2 hs3 hs4
    have hi : m + 5 < xs.size := by omega
    simp only [lpcResWin5]
    by_cases hx : Bits.small31 (xs.getD (m + 5) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 5 + 1) w1 w2 w3 w4 ((xs.getD (m + 5) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 5 + 1 - 5 = m + 1 by omega]; exact hw1) (by rw [show m + 5 + 1 - 5 + 1 = m + 2 by omega]; exact hw2) (by rw [show m + 5 + 1 - 5 + 2 = m + 3 by omega]; exact hw3) (by rw [show m + 5 + 1 - 5 + 3 = m + 4 by omega]; exact hw4) (by rw [show m + 5 + 1 - 5 + 4 = m + 5 by omega])
        (by rw [show m + 5 + 1 - 5 = m + 1 by omega]; exact hs1) (by rw [show m + 5 + 1 - 5 + 1 = m + 2 by omega]; exact hs2) (by rw [show m + 5 + 1 - 5 + 2 = m + 3 by omega]; exact hs3) (by rw [show m + 5 + 1 - 5 + 3 = m + 4 by omega]; exact hs4) (by rw [show m + 5 + 1 - 5 + 4 = m + 5 by omega]; exact hx)]
      simp only [lpcResGo5]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      have hstep : (((xs.getD (m + 5) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 4) 0).toInt64 + c1.toInt64 * (xs.getD (m + 3) 0).toInt64 + c2.toInt64 * (xs.getD (m + 2) 0).toInt64 + c3.toInt64 * (xs.getD (m + 1) 0).toInt64 + c4.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 5) 0 - Flac.Bits.sar (Lpc.dot5At xs c0 c1 c2 c3 c4 (m + 5)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega), getD_lt xs (show m + 2 < xs.size by omega), getD_lt xs (show m + 3 < xs.size by omega), getD_lt xs (show m + 4 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 4]'(by omega)).toInt64 + c1.toInt64 * (xs[m + 3]'(by omega)).toInt64 + c2.toInt64 * (xs[m + 2]'(by omega)).toInt64 + c3.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c4.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0 := by
          rw [Lpc.dot64_unfold5 xs c0 c1 c2 c3 c4 (m + 5) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 5 ≤ j + [c0, c1, c2, c3, c4].length → j < m + 5 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 ∨ j = m + 3 ∨ j = m + 4 := by omega
          rcases hj' with rfl | rfl | rfl | rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs2
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs3
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs4
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4] (m + 5) (by omega) 0) shift).natAbs
            ≤ 5 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot5At]
        rw [dif_pos (show m + 5 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold5 xs c0 c1 c2 c3 c4 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo5Slow_eq c0 c1 c2 c3 c4 shift xs (rem + 1) (m + 5) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo5_eq_fast : @lpcResGo5 = @lpcResGo5Fast := by
  funext c0 c1 c2 c3 c4 shift xs i rem out
  unfold lpcResGo5Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1, hs2, hs3, hs4⟩ := h
    exact (lpcResWin5_eq c0 c1 c2 c3 c4 shift xs hsh hc rem i _ _ _ _ _ out hK hle
      rfl rfl rfl rfl rfl hs0 hs1 hs2 hs3 hs4).symm
  · exact (lpcResGo5Slow_eq c0 c1 c2 c3 c4 shift xs rem i out).symm

theorem lpcResGo6Slow_eq (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo6Slow c0 c1 c2 c3 c4 c5 shift xs i rem out = lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo6Slow, lpcResGo6]
    exact ih _ _

theorem lpcResWin6_eq (c0 c1 c2 c3 c4 c5 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 w2 w3 w4 w5 : Int64) (out : Array Int), 6 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 6) 0).toInt64 →
      w1 = (xs.getD (i - 6 + 1) 0).toInt64 →
      w2 = (xs.getD (i - 6 + 2) 0).toInt64 →
      w3 = (xs.getD (i - 6 + 3) 0).toInt64 →
      w4 = (xs.getD (i - 6 + 4) 0).toInt64 →
      w5 = (xs.getD (i - 6 + 5) 0).toInt64 →
      Bits.small31 (xs.getD (i - 6) 0) = true →
      Bits.small31 (xs.getD (i - 6 + 1) 0) = true →
      Bits.small31 (xs.getD (i - 6 + 2) 0) = true →
      Bits.small31 (xs.getD (i - 6 + 3) 0) = true →
      Bits.small31 (xs.getD (i - 6 + 4) 0) = true →
      Bits.small31 (xs.getD (i - 6 + 5) 0) = true →
      lpcResWin6 c0 c1 c2 c3 c4 c5 (Int64.ofNat shift) shift xs i rem w0 w1 w2 w3 w4 w5 out
        = lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 w2 w3 w4 w5 out hK hle hw0 hw1 hw2 hw3 hw4 hw5 hs0 hs1 hs2 hs3 hs4 hs5
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 6 := ⟨i - 6, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hw2 hw3 hw4 hw5 hs0 hs1 hs2 hs3 hs4 hs5
    have hi : m + 6 < xs.size := by omega
    simp only [lpcResWin6]
    by_cases hx : Bits.small31 (xs.getD (m + 6) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 6 + 1) w1 w2 w3 w4 w5 ((xs.getD (m + 6) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 6 + 1 - 6 = m + 1 by omega]; exact hw1) (by rw [show m + 6 + 1 - 6 + 1 = m + 2 by omega]; exact hw2) (by rw [show m + 6 + 1 - 6 + 2 = m + 3 by omega]; exact hw3) (by rw [show m + 6 + 1 - 6 + 3 = m + 4 by omega]; exact hw4) (by rw [show m + 6 + 1 - 6 + 4 = m + 5 by omega]; exact hw5) (by rw [show m + 6 + 1 - 6 + 5 = m + 6 by omega])
        (by rw [show m + 6 + 1 - 6 = m + 1 by omega]; exact hs1) (by rw [show m + 6 + 1 - 6 + 1 = m + 2 by omega]; exact hs2) (by rw [show m + 6 + 1 - 6 + 2 = m + 3 by omega]; exact hs3) (by rw [show m + 6 + 1 - 6 + 3 = m + 4 by omega]; exact hs4) (by rw [show m + 6 + 1 - 6 + 4 = m + 5 by omega]; exact hs5) (by rw [show m + 6 + 1 - 6 + 5 = m + 6 by omega]; exact hx)]
      simp only [lpcResGo6]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      have hstep : (((xs.getD (m + 6) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 5) 0).toInt64 + c1.toInt64 * (xs.getD (m + 4) 0).toInt64 + c2.toInt64 * (xs.getD (m + 3) 0).toInt64 + c3.toInt64 * (xs.getD (m + 2) 0).toInt64 + c4.toInt64 * (xs.getD (m + 1) 0).toInt64 + c5.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 6) 0 - Flac.Bits.sar (Lpc.dot6At xs c0 c1 c2 c3 c4 c5 (m + 6)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega), getD_lt xs (show m + 2 < xs.size by omega), getD_lt xs (show m + 3 < xs.size by omega), getD_lt xs (show m + 4 < xs.size by omega), getD_lt xs (show m + 5 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 5]'(by omega)).toInt64 + c1.toInt64 * (xs[m + 4]'(by omega)).toInt64 + c2.toInt64 * (xs[m + 3]'(by omega)).toInt64 + c3.toInt64 * (xs[m + 2]'(by omega)).toInt64 + c4.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c5.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0 := by
          rw [Lpc.dot64_unfold6 xs c0 c1 c2 c3 c4 c5 (m + 6) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 6 ≤ j + [c0, c1, c2, c3, c4, c5].length → j < m + 6 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 ∨ j = m + 3 ∨ j = m + 4 ∨ j = m + 5 := by omega
          rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs2
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs3
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs4
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs5
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5] (m + 6) (by omega) 0) shift).natAbs
            ≤ 6 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot6At]
        rw [dif_pos (show m + 6 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold6 xs c0 c1 c2 c3 c4 c5 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo6Slow_eq c0 c1 c2 c3 c4 c5 shift xs (rem + 1) (m + 6) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo6_eq_fast : @lpcResGo6 = @lpcResGo6Fast := by
  funext c0 c1 c2 c3 c4 c5 shift xs i rem out
  unfold lpcResGo6Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1, hs2, hs3, hs4, hs5⟩ := h
    exact (lpcResWin6_eq c0 c1 c2 c3 c4 c5 shift xs hsh hc rem i _ _ _ _ _ _ out hK hle
      rfl rfl rfl rfl rfl rfl hs0 hs1 hs2 hs3 hs4 hs5).symm
  · exact (lpcResGo6Slow_eq c0 c1 c2 c3 c4 c5 shift xs rem i out).symm

theorem lpcResGo7Slow_eq (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo7Slow c0 c1 c2 c3 c4 c5 c6 shift xs i rem out = lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo7Slow, lpcResGo7]
    exact ih _ _

theorem lpcResWin7_eq (c0 c1 c2 c3 c4 c5 c6 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 w2 w3 w4 w5 w6 : Int64) (out : Array Int), 7 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 7) 0).toInt64 →
      w1 = (xs.getD (i - 7 + 1) 0).toInt64 →
      w2 = (xs.getD (i - 7 + 2) 0).toInt64 →
      w3 = (xs.getD (i - 7 + 3) 0).toInt64 →
      w4 = (xs.getD (i - 7 + 4) 0).toInt64 →
      w5 = (xs.getD (i - 7 + 5) 0).toInt64 →
      w6 = (xs.getD (i - 7 + 6) 0).toInt64 →
      Bits.small31 (xs.getD (i - 7) 0) = true →
      Bits.small31 (xs.getD (i - 7 + 1) 0) = true →
      Bits.small31 (xs.getD (i - 7 + 2) 0) = true →
      Bits.small31 (xs.getD (i - 7 + 3) 0) = true →
      Bits.small31 (xs.getD (i - 7 + 4) 0) = true →
      Bits.small31 (xs.getD (i - 7 + 5) 0) = true →
      Bits.small31 (xs.getD (i - 7 + 6) 0) = true →
      lpcResWin7 c0 c1 c2 c3 c4 c5 c6 (Int64.ofNat shift) shift xs i rem w0 w1 w2 w3 w4 w5 w6 out
        = lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 w2 w3 w4 w5 w6 out hK hle hw0 hw1 hw2 hw3 hw4 hw5 hw6 hs0 hs1 hs2 hs3 hs4 hs5 hs6
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 7 := ⟨i - 7, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hs0 hs1 hs2 hs3 hs4 hs5 hs6
    have hi : m + 7 < xs.size := by omega
    simp only [lpcResWin7]
    by_cases hx : Bits.small31 (xs.getD (m + 7) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 7 + 1) w1 w2 w3 w4 w5 w6 ((xs.getD (m + 7) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 7 + 1 - 7 = m + 1 by omega]; exact hw1) (by rw [show m + 7 + 1 - 7 + 1 = m + 2 by omega]; exact hw2) (by rw [show m + 7 + 1 - 7 + 2 = m + 3 by omega]; exact hw3) (by rw [show m + 7 + 1 - 7 + 3 = m + 4 by omega]; exact hw4) (by rw [show m + 7 + 1 - 7 + 4 = m + 5 by omega]; exact hw5) (by rw [show m + 7 + 1 - 7 + 5 = m + 6 by omega]; exact hw6) (by rw [show m + 7 + 1 - 7 + 6 = m + 7 by omega])
        (by rw [show m + 7 + 1 - 7 = m + 1 by omega]; exact hs1) (by rw [show m + 7 + 1 - 7 + 1 = m + 2 by omega]; exact hs2) (by rw [show m + 7 + 1 - 7 + 2 = m + 3 by omega]; exact hs3) (by rw [show m + 7 + 1 - 7 + 3 = m + 4 by omega]; exact hs4) (by rw [show m + 7 + 1 - 7 + 4 = m + 5 by omega]; exact hs5) (by rw [show m + 7 + 1 - 7 + 5 = m + 6 by omega]; exact hs6) (by rw [show m + 7 + 1 - 7 + 6 = m + 7 by omega]; exact hx)]
      simp only [lpcResGo7]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      have hstep : (((xs.getD (m + 7) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 6) 0).toInt64 + c1.toInt64 * (xs.getD (m + 5) 0).toInt64 + c2.toInt64 * (xs.getD (m + 4) 0).toInt64 + c3.toInt64 * (xs.getD (m + 3) 0).toInt64 + c4.toInt64 * (xs.getD (m + 2) 0).toInt64 + c5.toInt64 * (xs.getD (m + 1) 0).toInt64 + c6.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 7) 0 - Flac.Bits.sar (Lpc.dot7At xs c0 c1 c2 c3 c4 c5 c6 (m + 7)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega), getD_lt xs (show m + 2 < xs.size by omega), getD_lt xs (show m + 3 < xs.size by omega), getD_lt xs (show m + 4 < xs.size by omega), getD_lt xs (show m + 5 < xs.size by omega), getD_lt xs (show m + 6 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 6]'(by omega)).toInt64 + c1.toInt64 * (xs[m + 5]'(by omega)).toInt64 + c2.toInt64 * (xs[m + 4]'(by omega)).toInt64 + c3.toInt64 * (xs[m + 3]'(by omega)).toInt64 + c4.toInt64 * (xs[m + 2]'(by omega)).toInt64 + c5.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c6.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0 := by
          rw [Lpc.dot64_unfold7 xs c0 c1 c2 c3 c4 c5 c6 (m + 7) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 7 ≤ j + [c0, c1, c2, c3, c4, c5, c6].length → j < m + 7 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 ∨ j = m + 3 ∨ j = m + 4 ∨ j = m + 5 ∨ j = m + 6 := by omega
          rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs2
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs3
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs4
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs5
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs6
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5, c6] (m + 7) (by omega) 0) shift).natAbs
            ≤ 7 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot7At]
        rw [dif_pos (show m + 7 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold7 xs c0 c1 c2 c3 c4 c5 c6 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo7Slow_eq c0 c1 c2 c3 c4 c5 c6 shift xs (rem + 1) (m + 7) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo7_eq_fast : @lpcResGo7 = @lpcResGo7Fast := by
  funext c0 c1 c2 c3 c4 c5 c6 shift xs i rem out
  unfold lpcResGo7Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1, hs2, hs3, hs4, hs5, hs6⟩ := h
    exact (lpcResWin7_eq c0 c1 c2 c3 c4 c5 c6 shift xs hsh hc rem i _ _ _ _ _ _ _ out hK hle
      rfl rfl rfl rfl rfl rfl rfl hs0 hs1 hs2 hs3 hs4 hs5 hs6).symm
  · exact (lpcResGo7Slow_eq c0 c1 c2 c3 c4 c5 c6 shift xs rem i out).symm

theorem lpcResGo8Slow_eq (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int) :
    ∀ (rem i : Nat) (out : Array Int),
      lpcResGo8Slow c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out = lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i out
    simp only [lpcResGo8Slow, lpcResGo8]
    exact ih _ _

theorem lpcResWin8_eq (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (shift : Nat) (xs : Array Int)
    (hsh : shift < 64) (hc : ∀ c ∈ [c0, c1, c2, c3, c4, c5, c6, c7], Bits.FitsSInt 16 c) :
    ∀ (rem i : Nat) (w0 w1 w2 w3 w4 w5 w6 w7 : Int64) (out : Array Int), 8 ≤ i → i + rem ≤ xs.size →
      w0 = (xs.getD (i - 8) 0).toInt64 →
      w1 = (xs.getD (i - 8 + 1) 0).toInt64 →
      w2 = (xs.getD (i - 8 + 2) 0).toInt64 →
      w3 = (xs.getD (i - 8 + 3) 0).toInt64 →
      w4 = (xs.getD (i - 8 + 4) 0).toInt64 →
      w5 = (xs.getD (i - 8 + 5) 0).toInt64 →
      w6 = (xs.getD (i - 8 + 6) 0).toInt64 →
      w7 = (xs.getD (i - 8 + 7) 0).toInt64 →
      Bits.small31 (xs.getD (i - 8) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 1) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 2) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 3) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 4) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 5) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 6) 0) = true →
      Bits.small31 (xs.getD (i - 8 + 7) 0) = true →
      lpcResWin8 c0 c1 c2 c3 c4 c5 c6 c7 (Int64.ofNat shift) shift xs i rem w0 w1 w2 w3 w4 w5 w6 w7 out
        = lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out := by
  have hsize : Int64.size = 2 ^ 64 := rfl
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro i w0 w1 w2 w3 w4 w5 w6 w7 out hK hle hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 8 := ⟨i - 8, by omega⟩
    simp only [Nat.add_sub_cancel] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
    have hi : m + 8 < xs.size := by omega
    simp only [lpcResWin8]
    by_cases hx : Bits.small31 (xs.getD (m + 8) 0) = true
    · rw [if_pos hx]
      rw [ih (m + 8 + 1) w1 w2 w3 w4 w5 w6 w7 ((xs.getD (m + 8) 0).toInt64) (out.push _) (by omega) (by omega)
        (by rw [show m + 8 + 1 - 8 = m + 1 by omega]; exact hw1) (by rw [show m + 8 + 1 - 8 + 1 = m + 2 by omega]; exact hw2) (by rw [show m + 8 + 1 - 8 + 2 = m + 3 by omega]; exact hw3) (by rw [show m + 8 + 1 - 8 + 3 = m + 4 by omega]; exact hw4) (by rw [show m + 8 + 1 - 8 + 4 = m + 5 by omega]; exact hw5) (by rw [show m + 8 + 1 - 8 + 5 = m + 6 by omega]; exact hw6) (by rw [show m + 8 + 1 - 8 + 6 = m + 7 by omega]; exact hw7) (by rw [show m + 8 + 1 - 8 + 7 = m + 8 by omega])
        (by rw [show m + 8 + 1 - 8 = m + 1 by omega]; exact hs1) (by rw [show m + 8 + 1 - 8 + 1 = m + 2 by omega]; exact hs2) (by rw [show m + 8 + 1 - 8 + 2 = m + 3 by omega]; exact hs3) (by rw [show m + 8 + 1 - 8 + 3 = m + 4 by omega]; exact hs4) (by rw [show m + 8 + 1 - 8 + 4 = m + 5 by omega]; exact hs5) (by rw [show m + 8 + 1 - 8 + 5 = m + 6 by omega]; exact hs6) (by rw [show m + 8 + 1 - 8 + 6 = m + 7 by omega]; exact hs7) (by rw [show m + 8 + 1 - 8 + 7 = m + 8 by omega]; exact hx)]
      simp only [lpcResGo8]
      subst hw0
      subst hw1
      subst hw2
      subst hw3
      subst hw4
      subst hw5
      subst hw6
      subst hw7
      have hstep : (((xs.getD (m + 8) 0).toInt64
            - (c0.toInt64 * (xs.getD (m + 7) 0).toInt64 + c1.toInt64 * (xs.getD (m + 6) 0).toInt64 + c2.toInt64 * (xs.getD (m + 5) 0).toInt64 + c3.toInt64 * (xs.getD (m + 4) 0).toInt64 + c4.toInt64 * (xs.getD (m + 3) 0).toInt64 + c5.toInt64 * (xs.getD (m + 2) 0).toInt64 + c6.toInt64 * (xs.getD (m + 1) 0).toInt64 + c7.toInt64 * (xs.getD (m) 0).toInt64) >>> Int64.ofNat shift).toInt)
          = xs.getD (m + 8) 0 - Flac.Bits.sar (Lpc.dot8At xs c0 c1 c2 c3 c4 c5 c6 c7 (m + 8)) shift := by
        rw [getD_lt xs hi, getD_lt xs (show m < xs.size by omega), getD_lt xs (show m + 1 < xs.size by omega), getD_lt xs (show m + 2 < xs.size by omega), getD_lt xs (show m + 3 < xs.size by omega), getD_lt xs (show m + 4 < xs.size by omega), getD_lt xs (show m + 5 < xs.size by omega), getD_lt xs (show m + 6 < xs.size by omega), getD_lt xs (show m + 7 < xs.size by omega)]
        have hd : c0.toInt64 * (xs[m + 7]'(by omega)).toInt64 + c1.toInt64 * (xs[m + 6]'(by omega)).toInt64 + c2.toInt64 * (xs[m + 5]'(by omega)).toInt64 + c3.toInt64 * (xs[m + 4]'(by omega)).toInt64 + c4.toInt64 * (xs[m + 3]'(by omega)).toInt64 + c5.toInt64 * (xs[m + 2]'(by omega)).toInt64 + c6.toInt64 * (xs[m + 1]'(by omega)).toInt64 + c7.toInt64 * (xs[m]'(by omega)).toInt64 = Lpc.dot64 xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0 := by
          rw [Lpc.dot64_unfold8 xs c0 c1 c2 c3 c4 c5 c6 c7 (m + 8) (by omega) (by omega) 0]
          simp only [Nat.add_sub_cancel, Int64.zero_add]
        rw [hd]
        have hwin34 : ∀ (j : Nat) (hj : j < xs.size), m + 8 ≤ j + [c0, c1, c2, c3, c4, c5, c6, c7].length → j < m + 8 →
            Bits.FitsSInt 34 xs[j] := by
          intro j hj h1 h2
          simp only [List.length_cons, List.length_nil] at h1
          have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 ∨ j = m + 3 ∨ j = m + 4 ∨ j = m + 5 ∨ j = m + 6 ∨ j = m + 7 := by omega
          rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · have := Bits.fitsSInt31_of_small31 hs0
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs1
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs2
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs3
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs4
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs5
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs6
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
          · have := Bits.fitsSInt31_of_small31 hs7
            rw [getD_lt xs (by omega)] at this
            exact Bits.fitsSInt_mono (by omega) this
        have hb := Lpc.dotAGo_bound_range xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0 hc hwin34
        simp only [Int.natAbs_zero, Nat.zero_add, List.length_cons, List.length_nil,
          Nat.reducePow, Nat.reduceMul] at hb
        have hdot : (Lpc.dot64 xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0).toInt
            = Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0 := by
          rw [Lpc.dot64_toInt_range xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0 hc hwin34]
          simp only [Int64.toInt_zero, Int.zero_add]
          apply Int.bmod_eq_of_le <;> omega
        have hp : (Lpc.dot64 xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0 >>> Int64.ofNat shift).toInt
            = Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0) shift := by
          rw [Bits.toInt_shiftRight_ofNat _ _ hsh, hdot, Bits.sar_eq_shiftRight]
        have hq : (Flac.Bits.sar (Lpc.dotAGo xs [c0, c1, c2, c3, c4, c5, c6, c7] (m + 8) (by omega) 0) shift).natAbs
            ≤ 8 * 2 ^ 48 := by
          rw [Bits.sar_eq_shiftRight, Int.shiftRight_eq_div_pow]
          exact Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hb
        have hxi := Bits.fitsSInt31_of_small31 hx
        rw [getD_lt xs hi] at hxi
        simp only [Bits.FitsSInt, Nat.reducePow] at hxi
        rw [Int64.toInt_sub, hp, Int.toInt64, Int64.toInt_ofInt, hsize, Int.bmod_sub_bmod]
        simp only [Lpc.dot8At]
        rw [dif_pos (show m + 8 ≤ xs.size by omega),
          ← Lpc.dotAGo_unfold8 xs c0 c1 c2 c3 c4 c5 c6 c7 m (by omega) 0]
        apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow, Nat.reduceMul] at hq ⊢ <;> omega
      rw [hstep]
    · rw [if_neg hx]
      exact lpcResGo8Slow_eq c0 c1 c2 c3 c4 c5 c6 c7 shift xs (rem + 1) (m + 8) out

/-- **The machine-word residual loop computes the boxed one.** -/
@[csimp] theorem lpcResGo8_eq_fast : @lpcResGo8 = @lpcResGo8Fast := by
  funext c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out
  unfold lpcResGo8Fast
  split
  · next h =>
    obtain ⟨hK, hle, hsh, hc, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := h
    exact (lpcResWin8_eq c0 c1 c2 c3 c4 c5 c6 c7 shift xs hsh hc rem i _ _ _ _ _ _ _ _ out hK hle
      rfl rfl rfl rfl rfl rfl rfl rfl hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7).symm
  · exact (lpcResGo8Slow_eq c0 c1 c2 c3 c4 c5 c6 c7 shift xs rem i out).symm

/-- `Lpc.residual` over arrays, dispatching the tap walk once per subframe. -/
def lpcResA (cs : List Int) (shift : Nat) (xs : Array Int) : Array Int :=
  let i := cs.length
  let rem := xs.size - cs.length
  let out := Array.emptyWithCapacity rem
  match cs with
  | [c0] => lpcResGo1 c0 shift xs i rem out
  | [c0, c1] => lpcResGo2 c0 c1 shift xs i rem out
  | [c0, c1, c2] => lpcResGo3 c0 c1 c2 shift xs i rem out
  | [c0, c1, c2, c3] => lpcResGo4 c0 c1 c2 c3 shift xs i rem out
  | [c0, c1, c2, c3, c4] => lpcResGo5 c0 c1 c2 c3 c4 shift xs i rem out
  | [c0, c1, c2, c3, c4, c5] => lpcResGo6 c0 c1 c2 c3 c4 c5 shift xs i rem out
  | [c0, c1, c2, c3, c4, c5, c6] =>
    lpcResGo7 c0 c1 c2 c3 c4 c5 c6 shift xs i rem out
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
    lpcResGo8 c0 c1 c2 c3 c4 c5 c6 c7 shift xs i rem out
  | cs' => lpcResGo cs' shift xs i rem out

namespace W

/-! ## Subframes -/

/-- Subframe content (computes `Subframe.writeContent`). -/
def pushContent (b : Nat) (cfg : Subframe.SubframeCfg) (xs : Array Int)
    (w : W) : W :=
  match cfg with
  | .constant => w.pushSInt b (xs.getD 0 0)
  | .verbatim => pushSIntSeg b xs 0 xs.size w
  | .fixed ord rcfg =>
    pushResidual xs.size ord rcfg (fixedResA ord xs)
      (pushSIntSeg b xs 0 ord w)
  | .lpc cs shift prec rcfg =>
    pushResidual xs.size cs.length rcfg (lpcResA cs shift xs)
      (pushSIntList prec cs
        (((pushSIntSeg b xs 0 cs.length w).push 4 (prec - 1)).pushSInt 5
          (shift : Int)))

/-- One subframe (computes `Subframe.write`). -/
def pushSubframe (b : Nat) (sc : Subframe.SubCfg) (xs : Array Int) (w : W) : W :=
  let scaled := if sc.wasted = 0 then xs
    else xs.map (Flac.Bits.shiftDown sc.wasted)
  pushContent (b - sc.wasted) sc.inner scaled
    (if sc.wasted = 0 then ((w.push 1 0).push 6 sc.inner.typeCode).push 1 0
     else (((w.push 1 0).push 6 sc.inner.typeCode).push 1 1).pushUnary
       (sc.wasted - 1))

/-- Continuation bytes of a coded number (computes
    `Utf8Num.writeConts`). -/
def pushConts (v : Nat) : (k : Nat) → W → W
  | 0, w => w
  | k + 1, w => pushConts v k (w.push 8 (0x80 + v / p2 (6 * k) % 64))

/-- Coded number (computes `Utf8Num.write`). -/
def pushUtf8 (v : Nat) (w : W) : W :=
  if v < p2 7 then w.push 8 v
  else if v < p2 11 then pushConts v 1 (w.push 8 (0xC0 + v / p2 6))
  else if v < p2 16 then pushConts v 2 (w.push 8 (0xE0 + v / p2 12))
  else if v < p2 21 then pushConts v 3 (w.push 8 (0xF0 + v / p2 18))
  else if v < p2 26 then pushConts v 4 (w.push 8 (0xF8 + v / p2 24))
  else if v < p2 31 then pushConts v 5 (w.push 8 (0xFC + v / p2 30))
  else pushConts v 6 (w.push 8 0xFE)

/-- Frame-header fields up to the CRC-8 (computes `Frame.headerCore`). -/
def pushHeaderCore (b : Nat) (strat : Bool) (num bs chCode : Nat) (w : W) : W :=
  (pushUtf8 num ((((((((w.push 14 0x3FFE).push 1 0).push 1
    (if strat then 1 else 0)).push 4 7).push 4 0).push 4 chCode).push 3
    (Frame.bpsCode b)).push 1 0)).push 16 (bs - 1)

/-- The subframe plan over arrays (mirrors `Frame.subframePlan`). -/
def planA (b : Nat) (asg : Frame.ChannelAsg) (chs : List (Array Int)) :
    List ((Nat × Subframe.SubCfg) × Array Int) :=
  match asg, chs with
  | .independent cfgs, chs => (cfgs.map ((b, ·))).zip chs
  | .leftSide c0 c1, [l, r] =>
    [((b, c0), l), ((b + 1, c1), Stereo.sideA l r)]
  | .rightSide c0 c1, [l, r] =>
    [((b + 1, c0), Stereo.sideA l r), ((b, c1), r)]
  | .midSide c0 c1, [l, r] =>
    [((b, c0), Stereo.midA l r), ((b + 1, c1), Stereo.sideA l r)]
  | _, _ => []

def pushPlan : List ((Nat × Subframe.SubCfg) × Array Int) → W → W
  | [], w => w
  | p :: ps, w => pushPlan ps (pushSubframe p.1.1 p.1.2 p.2 w)

/-- One frame: header, CRC-8, subframes, alignment, CRC-16, all CRCs
    computed over the emitter's own bytes (computes `Frame.write`;
    requires a byte-aligned writer, which frames always have). -/
def pushFrame (b : Nat) (strat : Bool) (num : Nat) (asg : Frame.ChannelAsg)
    (chs : List (Array Int)) (w : W) : W :=
  let start := w.buf.size
  let w1 := pushHeaderCore b strat num (chs.headD #[]).size
    (asg.code chs.length) w
  let w2 := w1.push 8 (Crc.crc8Range w1.buf start w1.buf.size).toNat
  let w3 := pushPlan (planA b asg chs) w2
  let w4 := w3.push ((8 - w3.n % 8) % 8) 0
  w4.push 16 (Crc.crc16Range w4.buf start w4.buf.size).toNat

/-! ## Streams -/

/-- The fixed-size STREAMINFO payload (computes `Stream.writeStreamInfo`). -/
def pushStreamInfo (bs sr ch b total md5 : Nat) (w : W) : W :=
  ((((((((w.push 16 bs).push 16 bs).push 24 0).push 24 0).push 20 sr).push 3
    (ch - 1)).push 5 (b - 1)).pushBits 36 total).pushBits 128 md5

/-- A sequence of already chunked frames. The model chooser stays on
    lists; only the samples handed to the emitter are materialized as
    arrays. -/
def pushFrames (b : Nat) (varBlk : Bool) (blockSize : Nat)
    (chooser : List (List Int) → Frame.ChannelAsg) :
    Nat → List (List (List Int)) → W → W
  | _, [], w => w
  | i, fr :: frs, w =>
    pushFrames b varBlk blockSize chooser (i + 1) frs
      (pushFrame b varBlk (if varBlk then i * blockSize else i)
        (chooser fr) (fr.map List.toArray) w)

/-- The byte-aligned marker + STREAMINFO prefix. -/
def pushStreamPrefix (cfg : Stream.EncoderCfg) (a : Stream.Audio) (w : W) : W :=
  let md5 := Stream.md5Nat (Md5.md5 (Stream.pcmBytes a.bps a.channels))
  let w1 := (((w.push 32 0x664C6143).push 1 1).push 7 0).push 24 34
  pushStreamInfo cfg.blockSize a.sampleRate a.channels.length a.bps
    a.numSamples md5 w1

/-- Marker, STREAMINFO, and all frames (computes `Stream.writeStream`). -/
def pushStream (cfg : Stream.EncoderCfg) (a : Stream.Audio) (w : W) : W :=
  pushFrames a.bps cfg.variableBlocking cfg.blockSize (cfg.safeChooser a.bps) 0
    (Stream.chunkChannels cfg.blockSize a.channels) (pushStreamPrefix cfg a w)

/-- Byte output of the verified emitter. -/
def encode (cfg : Stream.EncoderCfg) (a : Stream.Audio) : ByteArray :=
  (pushStream cfg a
    (empty (64 + 2 * a.channels.length * a.numSamples))).buf

end W

/-- Statically verified stream-emitter entry point. Its equality to the
    reference encoder is `Flac.Emit.emitFast_eq_encode`. -/
def emitFast (cfg : Stream.EncoderCfg) (a : Stream.Audio) : ByteArray :=
  W.encode cfg a

end Flac.Emit
