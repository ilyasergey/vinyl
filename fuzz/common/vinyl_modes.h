/* vinyl_modes.h — wrappers over the remaining Vinyl entry points used by
 * fz_decode_modes / fz_roundtrip:
 *
 *   vm_decode_pcm16  — Flac.decodePcm16A          (the CLI `--decode-pcm16`)
 *   vm_decode_ref    — Flac.Stream.decodeReference (the CLI `--decode`)
 *   vm_encode_fast   — Flac.encodePcm16Fast        (the CLI `--encode`)
 *   vm_encode_slow   — Flac.encodePcm16Cfg with
 *                      ⟨bs, false, Heuristics.defaultAsgChooser 16⟩
 *                                                  (the CLI `--encode-slow`)
 *
 * Declarations only; bodies live in vinyl_modes.c. (Ported from cfuzz's
 * header-only `static` vinyl_modes.h, whose single-TU trick existed only to
 * work around build.sh's fixed per-target object list -- the new Makefile
 * links whatever object list a target declares, so the split is trivial.)
 *
 * Conventions match vinyl_api.[ch]: decode wrappers return DEC_REJECT /
 * DEC_OK / DEC_SKIP, PCM is interleaved s16le in a wrapper-owned buffer
 * (one buffer PER WRAPPER so results from different modes never alias and
 * are directly memcmp-able), encode wrappers return 1 = accepted /
 * 0 = rejected. Non-16-bit streams are DEC_SKIP via the same readMeta
 * pre-check vinyl_decode_fast uses, so accept/reject/skip decisions are
 * comparable across all decode modes.
 */
#ifndef VINYL_MODES_H
#define VINYL_MODES_H

#include <stddef.h>
#include <stdint.h>

int vm_decode_pcm16(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len, int *bps, int *ch,
                    int *sr);
int vm_decode_ref(const uint8_t *in, size_t n, uint8_t **pcm, size_t *len, int *bps, int *ch,
                  int *sr);
int vm_encode_fast(const uint8_t *pcm, size_t n, size_t bs, size_t ch, size_t sr, uint8_t **out,
                   size_t *len);
int vm_encode_slow(const uint8_t *pcm, size_t n, size_t bs, size_t ch, size_t sr, uint8_t **out,
                   size_t *len);


/* --- folded in from vinyl_md5.h --- */
/* vinyl_md5.h -- thin wrapper over Flac.Md5.md5, Vinyl's hand-written,
 * proof-indexed, 64-round-unrolled MD5. Used by fz_md5 to differential it
 * against md5_ref. A wrong Vinyl MD5 makes `flac -t` reject Vinyl's output while
 * every round-trip theorem still holds -- a broken security-relevant primitive
 * in a verified codec, entirely outside the proof's scope. */


/* Runs Flac.Md5.md5(msg) and copies the 16-byte digest into out. Returns the
 * digest length the codec produced (16 on success; any other value is itself a
 * finding -- MD5 is always 16 bytes). */
size_t vinyl_md5(const uint8_t *msg, size_t len, uint8_t out[16]);

/* --- folded in from vinyl_unchecked_api.h --- */
/* vinyl_unchecked_api.h — the P7 surface: Flac.Stream.Unchecked.encode.
 *
 * P7 renamed the raw, precondition-free encoders under an `Unchecked` namespace
 * (docs/07). The checked encoders (encodePcm16Fast / encodeCheckedCfg) gate on
 * Pcm16ShapeOk + blockSize <= 4608; the unchecked one runs on any audio. This
 * wrapper builds a Stream.Audio from interleaved s16le PCM and drives
 * Stream.Unchecked.encode directly, so fz_unchecked_encode can:
 *   - confirm the raw path does not crash on out-of-envelope audio, and
 *   - assert it AGREES byte-for-byte with the checked encoder on the domain the
 *     checked encoder accepts (the P7 rename must not have changed behaviour). */


/* Encode interleaved s16le PCM through Stream.Unchecked.encode with
 * EncoderCfg <blockSize, false, defaultAsgChooser 16>. Returns 1 and fills
 * out/len on success (the raw encoder always produces bytes for well-shaped
 * geometry), 0 if the geometry is unusable (ch==0 or a partial frame). The
 * buffer is wrapper-owned, reused across calls. */
int vinyl_unchecked_encode(const uint8_t *pcm, size_t n, size_t bs, size_t ch, size_t sr,
                           uint8_t **out, size_t *len);

/* --- folded in from vinyl_parallel.h --- */
/* vinyl_parallel.h — determinism harness for Vinyl's parallel decode surface.
 *
 * The fortified codec swaps the compiled decode function via `@[csimp]` while
 * the kernel checks only a propositional equality (see docs/06-recursion-shape.md),
 * and `Flac.Decode.decodeBytes` dispatches to `byteStepsPar` on inputs above
 * `parThreshold` (1<<16). With a live task pool (LEAN_NUM_THREADS>1) those
 * decodes run genuinely concurrently, so decoding the SAME bytes repeatedly and
 * demanding byte-identical output is a direct test of the *binary*: a mismatch
 * across repeats is a Task-parallelism / runtime / miscompilation defect, not a
 * spec gap.
 *
 * This drives the public `decodeBytes` entry point (via vinyl_decode_fast), so
 * it needs no internal Lean symbol. Forced-serial / forced-parallel entry
 * points that call `readFramesFast` / `byteStepsPar` directly are a documented
 * extension, guarded on generated HAVE_* macros in vinyl_parallel.c. */


/* Decode `in`/`n` `repeat` times through vinyl_decode_fast. Returns the decode
 * code (DEC_OK / DEC_REJECT / DEC_SKIP) of the first decode. On DEC_OK, *pcm/
 * *len point to a module-owned snapshot of the first result and (*bps,*ch,*sr)
 * are its params; *stable is set to 1 if every subsequent decode produced
 * byte-identical output and the same accept decision, 0 otherwise. */
int vm_decode_stable(const uint8_t *in, size_t n, int repeat, uint8_t **pcm, size_t *len, int *bps,
                     int *ch, int *sr, int *stable);

/* FORCED-PARALLEL (A2): call byteStepsPar DIRECTLY, bypassing decodeBytes's
 * parThreshold gate AND its density bail (Decode.lean:711) -- coverage proved
 * the corpus never reaches the parallel internals through the public entry, so
 * seeding above parThreshold does not help; only a direct call does. Derives
 * (bps, ch, first-frame byte offset) from readMeta exactly as decodeBytes does,
 * builds `cands` via syncCandidates, then runs byteStepsPar `repeat` times under
 * the live pool and demands byte-identical concatenated frame output.
 *
 * *ran is set to 1 iff the parallel path actually executed (symbols present,
 * header parsed, AND byteStepsPar emitted a non-empty step array -- an empty
 * one means syncCandidates took the density bail and the parallel path never
 * engaged, so this exec must not be counted as parallel coverage). *stable to 1
 * iff every repeat produced identical bytes. When the codec does not export the
 * internal symbols, *ran stays 0 (feature unavailable) and the caller falls back
 * to the public-entry repeat. Determinism across repeats is the oracle: the
 * concatenated byteStepsPar bytes are NOT compared against the serial decode,
 * because a direct byteStepsPar invocation is not decodeBytes's internal one and
 * the two layouts are not directly comparable. */
void vm_force_par_stable(const uint8_t *in, size_t n, int repeat, int *ran, int *stable);

#endif /* VINYL_MODES_H */
