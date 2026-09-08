# Fuzzing statistics — reference baseline

A snapshot of a full-fleet campaign + coverage measurement, kept as a reference point
for future runs. Regenerate the numbers with:

```sh
python3 -m fleet run official 3600     # the campaign (writes runs/<ts>/SUMMARY.md)
scripts/ratchet.sh                      # distil grown corpus -> corpus/*/evolved/
make coverage                           # llvm-cov over Flac/Native (cov/report/latest/)
                                        #   prints the EFFECTIVE (honest-denominator) figure too
python3 cov/structural_zero.py --validate   # refresh the never-executable classifier; 0 contradictions expected
```

## 2026-09-08 — 72 h all-target campaign: `official` 66 h + `contract` 6 h (current reference)

| field | value |
|---|---|
| recorded | 2026-09-08 |
| runs | `runs/20260904_080449` (`official`, 237600 s) then `runs/20260907_020457` (`contract`, 21600 s) — all 27 targets |
| cores / jobs | 31 cores / 27 jobs, then 30 cores / 10 jobs |
| total executions | 7,474,221,966 (official) + 1,976,158,809 (contract) = **~9.45 B** |
| aggregate throughput | ~31,500 exec/s (official), ~91,500 exec/s (contract) |
| **crashes / OOMs** | **0 / 0** in both phases (watchdog SIGKILLs 0); no crash artifacts |
| findings | **none** — no new witness classes; the fatal `wide_sample_diff` class was never reached (`wide_sample_diff_oob_coded` = 0 too) |

First campaign on binaries carrying the reference-model `restoreAuxTR` twin, the global
reproducer cap and the `flac_reconstruct_oob_at` discriminator; none of the previous cycle's
rig failures recurred (run dir 3.6 GB after 66 h). Invariants held for the full duration:
proven pairs (`fz_proven_pairs` 11,925 execs, `peek_incoherent=0`), `emitFast == encode` and
`encodePcm16` byte-identical (`len_diff=0 byte_diff=0`), emit referee `all_agree=12506`,
both bounded-stack pins `overflow=0`, `16bit_violations=0`, `fz_float_exact`
`bps<=16_divergences=0`, and `fz_overlong_utf8`'s `Utf8Num.read (write n)` proven pair over
**9,854,566** round trips (`rt_bug=0`, `overlong_accepted=0`).

### Coverage — fleet union over `Flac/Native/*.c`

| metric | covered / total | % |
|---|---|---|
| **regions** | 6610 / 11132 | **59.4 %** |
| branches | 2833 / 4806 | 58.9 % |
| lines | 36498 / 63034 | 57.9 % |
| functions | 635 / 1549 | 41.0 % |
| **effective (genuine targets, `structural.txt`)** | **6610 / 7795** | **84.8 %** |

Dead-by-design 3337 regions (30.0 %); classifier `--validate`: 0 contradictions. Region
coverage is flat versus the 12 h run (+7 regions) — the frontier is the dead-by-design /
codec-knob / size-bound remainder documented in the 10 h entry, not corpus reach.

### Corpus

| set | files |
|---|---|
| committed seed archive (`corpus/seeds.tar.gz`) | 2616 seeds (unchanged) |
| `corpus/*/evolved/` after `scripts/ratchet.sh` on both runs | **42,192** (+8,738 this cycle) |

Largest distillate gains: `fz_decode_diff` +1502, `fz_decode_modes` +1348, `fz_samples_diff`
+934, `fz_decode_structured` +830, `fz_proven_pairs` +549, `fz_trailing_data` +499,
`fz_decode_capacity` +382, `fz_decode_par_eq` +372, `fz_unchecked_encode` +371,
`fz_self_consistent` +360, `fz_gen_roundtrip` +348, `fz_metamorphic` +288. Note the decode
targets that distilled +0 after the 10 h run grew substantially at 66 h: libFuzzer's
feature/edge signal keeps finding coverage-distinct inputs long after *region* coverage has
plateaued, so the evolved corpus is still worth carrying forward even when the headline does
not move.

## 2026-09-04 — 12 h all-target campaign: `official` 11 h + `contract` 1 h

| field | value |
|---|---|
| recorded | 2026-09-04 |
| runs | `runs/20260902_200441` (`official`, 39600 s) then `runs/20260903_070448` (`contract`, 3600 s) — all 27 targets |
| cores / jobs | 31 cores / 27 jobs, then 30 cores / 10 jobs |
| total executions | 1,113,066,823 (official) + 331,496,610 (contract) = ~1.44 B |
| aggregate throughput | ~28,100 exec/s (official), ~92,100 exec/s (contract) |
| **crashes / OOMs** | **0 / 0** in both phases (watchdog SIGKILLs 0) |
| findings | none new. One fatal `wide_sample_diff` abort in `official` = the documented `decode-sample-divergence-highbps` class (4th witness, `repro-1003B`), auto-classified by the stream-level discriminator built this cycle |

Invariants held across both phases: proven pairs (`fz_proven_pairs` 10,380 execs,
`peek_incoherent=0`), `emitFast == encode` and `encodePcm16` byte-identical, emit referee
`all_agree=9364`, both bounded-stack pins `overflow=0`, `16bit_violations=0`, and the new
`fz_overlong_utf8` `Utf8Num.read (write n)` proven pair over **4.11 M** round trips
(`rt_bug=0`, `overlong_accepted=0`).

Rig findings fixed and verified in this cycle (see `TODO.md` / `findings/`): the reference
model's `Lpc.restoreAux` stack overflow (`restoreAuxTR` `@[csimp]` twin; the previous, aborted
6.4 h run's `fz_proven_pairs` crash), the per-process reproducer cap that let `-fork` restarts
flood the disk (now a global 512/class cap — the 11 h run dir stayed at 2.7 GB vs 14 GB in
6.4 h before), and the bps 17–31 `wide_sample_diff` discriminator (`flac_reconstruct_oob_at`).

### Coverage — fleet union over `Flac/Native/*.c`

| metric | covered / total | % |
|---|---|---|
| **regions** | 6603 / 11132 | **59.3 %** |
| branches | 2828 / 4806 | 58.8 % |
| lines | 36454 / 63034 | 57.8 % |
| functions | 634 / 1549 | 40.9 % |
| **effective (genuine targets, `structural.txt`)** | **6603 / 7827** | **84.4 %** |

The denominator grew by 34 regions (the `restoreAuxAcc`/`restoreAuxTR` twin), so the
percentages are flat on a larger base; dead-by-design is 3305 regions (29.7 %). Classifier
`--validate`: 0 contradictions on this profile.

### Corpus

| set | files |
|---|---|
| committed seed archive (`corpus/seeds.tar.gz`) | 2616 seeds (unchanged) |
| `corpus/*/evolved/` after `scripts/ratchet.sh` on both runs | 33,454 (+2,433 this cycle) |

Largest distillate gains: `fz_trailing_data` +550, `fz_self_consistent` +423,
`fz_metamorphic` +404, `fz_streaminfo_contradict` +324, `fz_gen_roundtrip` +242,
`fz_residual_bound` +223, `fz_emit_conformance` +144, `fz_encode_pair` +111. The saturated
decode targets (`fz_decode_*`, `fz_crc`) distilled +0.

## 2026-09-02 — `official` campaign, 10 h

| field | value |
|---|---|
| recorded | 2026-09-02 |
| run | `runs/20260901_054549` (`official`, 36000 s / 10 h) |
| cores / jobs | 31 cores, 27 jobs (24 targets + 3 variants/AFL arm) |
| total executions | 1,108,806,068 (~1.11 B) |
| aggregate throughput | ~30,800 exec/s across the fleet |
| **crashes / OOMs** | **0 / 0** (watchdog SIGKILLs 0) |
| new findings | none (only known documented-class detectors + manufactured mutator/referee noise) |

### Coverage — fleet union over `Flac/Native/*.c` (honest llvm-cov denominator)

Measured after the two direct proven-pair lanes (`fz_proven_pairs` → `Flac.decode` +
`Stream.peekInfo`; `fz_overlong_utf8` → `Utf8Num.read`/`write`, see the anatomy section) and
the re-`ratchet`ed 10 h corpus.

| metric | covered / total | % |
|---|---|---|
| **regions** | 6599 / 11098 | **59.5 %** |
| branches | 2826 / 4792 | 59.0 % |
| lines | 36426 / 62851 | 58.0 % |
| functions | 633 / 1545 | 41.0 % |

Up from the pre-improvement 10 h measurement (regions 6528 / 58.8 %); `fz_proven_pairs`
alone rose 3031 → 3059 regions (+28, all new to the union — those two entrypoints reached
no target before). Top per-target region coverage (single-target, not union):
`fz_roundtrip` 47.3 %, `fz_metamorphic` 42.3 %, `fz_self_consistent` 40.1 %,
`fz_encode_referee` 35.6 %, `fz_residual_bound` 34.2 %, `fz_decode_modes` 32.3 %,
`fz_gen_roundtrip` 29.2 %, `fz_encode_diff` 28.9 %, `fz_proven_pairs`/`fz_unchecked_encode`
27.6 %. The fork+exec bounded-stack probers `fz_decode_stack` / `fz_encode_stack` read 0 %
by construction (the work runs in a forked child the parent's instrumentation does not see).

A per-cluster gpt-5.6-sol audit against the Lean source established that the uncovered ~41 %
is overwhelmingly **dead-by-design generated C**, not a corpus weakness: `@[inline]`-elided
standalone bodies (the 8 `Lpc.dotN` bodies alone = 203/330 missed Lpc.c regions, compiled
into `Emit.lpcResGoN`), `@[csimp]` pre-swap originals, the List-Bool reference lanes, and
derived-instance/`repr`/`Format`/boxed/splitter noise. The reachable encoder LPC orders 1–6
and all four stereo modes are already covered; `Encode.lpcFold7/8` + the multi-candidate
`Heuristics.lpcSearch` need a codec-side knob. See `TODO.md` Coverage.

### Coverage anatomy — what the uncovered 40.5 % IS (validated classifier, 2026-09-02)

`cov/structural_zero.py` classifies every `Flac/Native` C symbol by a whole-IR static
reachability analysis: the call graph over all emitted C (Flac + FlacTest), rooted at every
Lean symbol the fuzz harness references plus the module initializers, with closures followed
through their `___boxed` thunks and file-scope static closure objects. `--validate`
cross-checks it against the union profile: **0 contradictions** (no function with coverage is
tagged never-executable). `make coverage` prints the EFFECTIVE figure and writes
`cov/report/latest/structural.txt`.

| view | regions | % |
|---|---|---|
| raw llvm-cov headline | 6599 / 11098 | 59.5 % |
| dead-by-design — can never execute from any fuzz binary | 3305 (29.8 % of all) | — |
| **effective — over functions that are genuine targets** | **6599 / 7793** | **84.7 %** |

The 4499 missed regions, by cause:

| cause | missed | % of missed |
|---|---|---|
| `___boxed` / `___redArg` ABI thunks (unreferenced) | 1431 | 31.8 % |
| **live functions — the real frontier** | **1194** | **26.5 %** |
| unreachable (no call path from any fuzz entry point: unbudgeted / spec predecessors) | 528 | 11.7 % |
| `@[inline]`-elided standalone copies | 460 | 10.2 % |
| match / lambda closures (unreferenced) | 399 | 8.9 % |
| `@[csimp]` pre-swap originals | 320 | 7.1 % |
| derived instances / `repr` / `Format` | 163 | 3.6 % |
| module-init constants | 4 | 0.1 % |

The 1194 missed regions inside LIVE functions decompose at arm level (`llvm-cov show`):
~66 % refcount ownership + Lean constructor-reuse (`reuseFailAlloc` / `isShared`) arms —
memory-management alternatives, not input logic; ~1 % closed-constant fallbacks; ~33 % logic
arms, which are (a) **impossible by invariant** — `defaultChooser`'s `none, some` match arm
(`fixedSearch` is `none` only for an empty block while `lpcSearch` needs ≥16 samples),
`riceCfg`'s valid-by-construction clamp, `lpcResGoN` out-of-bounds tails, bignum quotient
paths; (b) **codec-knob** — `lpcFold7/8`, the `lpcCandidates=[est]` candidate loop,
`pushPartsR`'s RICE2 arm behind the `riceChoices` k≤14 clamp; or (c) **input-size-bound** —
`Emit.W.pushUtf8` / `Encode.BitWriter.pushUtf8` 4–6-byte frame indices need ≥2^16 frames.
"100 % of reachable code" is therefore bounded by (a)+(b)+(c). The corpus-reachable
remainder was closed by two direct proven-pair lanes:

- `fz_proven_pairs` → `Flac.decode` + `Stream.peekInfo` (+28 regions, above).
- `fz_overlong_utf8` → `Utf8Num.read (Utf8Num.write n) = some (n, [])` (Spec `read_write`,
  n < 2^36) across all seven width classes: `fz_overlong_utf8` 406 → 508 regions, Utf8Num.c in the
  union 79.3 → 89.3 % — the 4/5/6-byte writer arms no stream input can reach. 1.25 M round trips
  in a 15 s smoke, `rt_bug=0`.

### Corpus

| set | size | files |
|---|---|---|
| committed seed archive (`corpus/seeds.tar.gz`) | 9.8 MB | 2616 seeds (unchanged this run) |
| this run's grown corpus (pre-distillation, `runs/.../*/corpus`) | ~19 GB | — |
| new coverage-increasing seeds distilled into `corpus/*/evolved/` | — | ~31 k across 24 targets |

Largest evolved distillates (`scripts/ratchet.sh`): `fz_decode_structured` 3379,
`fz_samples_diff` 2666, `fz_trailing_data` 2595, `fz_gen_roundtrip` 2037,
`fz_self_consistent` 2003, `fz_decode_diff` 1938 — a far richer distillate than the 1 h run
(the 10 h campaign explored well beyond the committed seed set). The evolved corpus is
gitignored (regenerable from `make corpus` + a campaign + `scripts/ratchet.sh`).

### Environment

Lean `leanprover/lean4:v4.33.0`; referee libFLAC 1.4.2 (source-built) + ffmpeg libavcodec
(+ libFLAC 1.5.0 cross-version differential); clang-14 libFuzzer + AFL++; 32-core host
(31 used). Coverage on the `covfuzz` flavour (`-fprofile-instr-generate -fcoverage-mapping`).

## 2026-08-31 — `official` campaign, 1 h

| field | value |
|---|---|
| recorded | 2026-09-01 |
| run | `runs/20260831_233848` (`official`, 3600 s) |
| cores / jobs | 31 cores, 27 jobs (24 targets + 3 variants/AFL arm) |
| total executions | 127,639,772 (~127.6 M) |
| aggregate throughput | ~35,400 exec/s across the fleet |
| **crashes / OOMs** | **0 / 0** |
| new findings | none (only known documented-class detectors + manufactured mutator/referee noise) |

### Coverage — fleet union over `Flac/Native/*.c` (honest llvm-cov denominator)

| metric | covered / total | % |
|---|---|---|
| **regions** | 6450 / 11098 | **58.1 %** |
| branches | 2717 / 4792 | 56.7 % |
| lines | 35516 / 62851 | 56.5 % |
| functions | 628 / 1545 | 40.7 % |

Top per-target region coverage (single-target, not union):
`fz_roundtrip` 44.4 %, `fz_metamorphic` 41.7 %, `fz_self_consistent` 39.5 %,
`fz_encode_referee` 35.6 %, `fz_decode_modes` 30.7 %, `fz_residual_bound` 30.7 %,
`fz_encode_diff` 26.7 %, `fz_proven_pairs` 26.0 %. The fork+exec bounded-stack probers
`fz_decode_stack` / `fz_encode_stack` read 0 % by construction — the work runs in a forked
child that the parent's coverage instrumentation does not see.

The uncovered ~42 % of regions is dominated by unverified-by-design `Heuristics` search
branches (`lpcFold7/8`, the multi-candidate `lpcSearch` loop) that need a codec-side knob to
reach, and error/rejection arms that a corpus cannot all hit — see `TODO.md` Coverage.

### Corpus

| set | size | files |
|---|---|---|
| committed seed archive (`corpus/seeds.tar.gz`) | 9.8 MB | 2616 seeds |
| this run's grown corpus (pre-distillation, `runs/.../*/corpus`) | ~4.5 GB | — |
| new coverage-increasing seeds distilled into `corpus/*/evolved/` | — | 1587 |

Evolved additions this run (`scripts/ratchet.sh`): `fz_decode_par_eq` +984,
`fz_encode_referee` +566, `fz_crc` +30, `fz_encode_stack` +3, `fz_decode_stack` +2,
`fz_decode_diff` +1, `fz_decode_structured` +1. Every other target distilled +0 — the
committed seed set already reaches everything the 1 h run's grown corpus did (a mature,
coverage-saturated corpus). The evolved corpus is gitignored (regenerable).

### Environment

Lean `leanprover/lean4:v4.33.0`; referee libFLAC 1.4.2 (source-built) + ffmpeg libavcodec;
clang-14 libFuzzer + AFL++; 32-core host (31 used). Coverage on the `covfuzz` flavour
(`-fprofile-instr-generate -fcoverage-mapping`).
