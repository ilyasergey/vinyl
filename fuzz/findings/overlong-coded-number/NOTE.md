# `readUtf8` accepts non-minimal (overlong) coded frame/sample numbers

**Status: FIXED (2026-08-31) — patch applied and verified.** `Utf8Num.contsFloor`
(the RFC 3629 minimality floor — `write`'s branch cutoffs `2^7,2^11,2^16,2^21,2^26,
2^31`) now gates `readContsMin`, and both reader twins (`Decode.readUtf8` fast path,
`Utf8Num.read` reference) reject a decoded value below the floor for its continuation
count. The change only SHRINKS the accept set, so it threads no hypothesis through the
capstones: `read_write`, `readUtf8_sim`, `readUtf8_pos8` and the frame round-trip go
through with the branch cutoff discharging the gate; `#print axioms` unchanged, `lake
build` / `flactest` (155) / `scripts/check.sh` all green. The detector `fz_overlong_utf8`
was flipped to a two-way regression pin: a 19 s run reports `minimal_accepted=2.79M`,
`overlong_rejected=686k`, `overlong_accepted=0 reject_bug=0 value_bug=0` — where a 15 s
run pre-fix reported ~1M `overlong_accepted`. History below.

**Original status: CONFIRMATION of a source-reviewed class (engagement appendix §3.7) — with a
new detector.** RFC 9639 §5 makes rejecting invalid data a MAY, so this is an
ACCEPT-SET / claim finding, not a decode nonconformance.

## What Vinyl does

FLAC frame and sample numbers are coded numbers in a UTF-8-like scheme.
`Flac.Decode.readUtf8` (Native/Decode.lean:36-49) dispatches on the leading byte's
class and `readConts` (:27-34) accumulates `acc*64 + (c-0x80)` per continuation byte
**with no minimality check**. So every value has multiple accepted encodings — 0 is
accepted as `00`, `C0 80`, `E0 80 80`, `F0 80 80 80`, … up to the 7-byte form.

RFC 9639 §9.1.5 defers coded-number handling to RFC 3629, under which overlong
sequences are ill-formed. Accepting them is the classic UTF-8 overlong-encoding class
with a known-bad security precedent (overlong sequences bypassing byte-level filters).
`COVERAGE.md`'s "reserved codes … rejected, as the RFC requires" is doubly wrong here:
the RFC requires no rejection, and Vinyl does not reject these.

Detector: `fz_overlong_utf8` — a constructive unit-differential. From each input it
derives a value V (<2³⁶) and a continuation count k, builds the k-continuation
encoding of V, and drives `readUtf8` on exactly those bytes. It asserts (robust,
would-abort) that the well-formed sequence is accepted, decodes to V, and consumes
k+1 bytes; then it counts `overlong_accepted` when k exceeds the minimal count.
A 15 s run: 3.3 M execs, ~1 M `overlong_accepted`, **`reject_bug=0 value_bug=0`** —
readUtf8 decodes overlong forms to the *correct* value, so the only issue is that it
accepts them.

## Reproducer

`repro.bin` — seeds value 0 with k=6 continuations (the 7-byte overlong form of 0).
`sha256: ae6b4439c027a318b6328f4c021a5724466ecb87a7c4efee12f1aa419ee82285`

```sh
cd fuzz
FUZZ_STRICT=2 build/bin/fz_overlong_utf8.fuzz -runs=1 findings/overlong-coded-number/repro.bin
# [OVERLONG CODED NUMBER ACCEPTED] readUtf8 decoded value 0 from a 7-byte
#   (k=6 continuation) encoding; the minimal form needs only k=0 (1 byte(s)).
```

## Reference behaviour

Self-contained (Vinyl's reader vs the minimality reference computed in the harness);
no external referee. The point is Vinyl-specific: a formally-verified decoder that
defers to RFC 3629 should reject overlong coded numbers, and its accept-set — the set
every theorem quantifies over — currently includes them.

## Category

Accept-set / spec-adequacy (the P5/§3.7 class). Fix is a minimality guard in
`readConts`/`readUtf8` (reject when the decoded value fits a shorter form), which only
*shrinks* the accept set and so ripples no hypothesis through the capstones. The
detector doubles as a two-way regression pin: adding the guard drops `overlong_accepted`
to 0 while `minimal_accepted` keeps passing.
