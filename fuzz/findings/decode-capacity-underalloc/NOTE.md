# `decodeBytes` output buffer pre-sized at 2 bytes/sample — 24/32-bit reallocs

**Status: CONFIRMATION of a known lead (engagement missed-lead #1) — NOT claimed as novel.**
Source review flagged that `--decode-fast`'s output pre-size hardcodes 16-bit width.
This entry records a dynamic reproduction at scale and the exact shortfall.

## What Vinyl does

`Flac.Decode.decodeBytes` pre-sizes its PCM output buffer with

```lean
ByteArray.emptyWithCapacity (outCapacity (2 * si.channels * si.totalSamples + 64) br.data.size)
  -- Native/Decode.lean:1114-1115 ; outCapacity = min declared (16*inputBytes + 65536)  (:1091)
```

The `2 *` in `declared` is 2 bytes/sample — correct only for bit depths ≤ 16. The
serialized output is `⌈bps/8⌉` bytes/sample: 3 at 24-bit, 4 at 32-bit. So on every
valid 24/32-bit decode with a truthful `totalSamples`, the initial buffer is short by
`(⌈bps/8⌉ − 2)/⌈bps/8⌉` of the final size and the `ByteArray` grows by doubling —
extra allocation + copies in exactly the least-exercised (non-16-bit) region.

This is **proof-invisible** by construction: the module's own docstring
(Decode.lean:1088-1090) notes `emptyWithCapacity n` is definitionally the empty
array, so the hint changes no decoded byte and no theorem — the same mechanism as
P3, but in the opposite direction (P3 clamped a 1.1 TB *over*-allocation down; this
is a silent *under*-allocation).

Detector: `fz_decode_capacity` recomputes the decoder's own pre-size from the parsed
STREAMINFO and file size and compares to the actual decoded output length. The 6h
`official` run reported **`decode_capacity_underalloc = 109,679`** (bps>16,
totalSamples>0), the depth class — distinct from the RFC-legal streaming case
(`total0 = 570`).

## Reproducer

`repro.flac` (8715 bytes). `sha256: 2af305beba3c0d122fcfd05193af1f59c921a3fcef948b51fb89ec81b5cda56c`

```sh
cd fuzz
FUZZ_STRICT=2 build/bin/fz_decode_capacity.fuzz -runs=1 findings/decode-capacity-underalloc/repro.flac
# [CAPACITY] decodeBytes pre-sizes 2 bytes/sample but bps=24 needs 3
#   ch=2 totalSamples=328 filesize=8715: capacity=1376 < output=36864 (short by 35488 B)
```

The engagement's own arithmetic on a large file: 24-bit short by ~52 MB, 32-bit by
~105 MB — the buffer reallocs its way up from the 16-bit hint each time.

## Reference behaviour

No referee involved — the decoded bytes are correct; only the allocation path is
wrong. This is a **capacity / performance** defect, not a correctness or interop
one, which is why no oracle that checks output *values* can see it and why it sat in
the non-16-bit region the corpora barely touched.

## Category

Capacity hint, saturating/fixed-width arithmetic (P8/P3 class). Fix is one token:

```lean
outCapacity (((si.bps + 7) / 8) * si.channels * si.totalSamples + 64) br.data.size
```

Proof-invisible, so it needs no theorem change — but it is a **T→C correction** in
spirit: a bound documented as safe is width-wrong off the 16-bit path.
