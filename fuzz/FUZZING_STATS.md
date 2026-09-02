# Fuzzing statistics — reference baseline

A snapshot of a full-fleet campaign + coverage measurement, kept as a reference point
for future runs. Regenerate the numbers with:

```sh
python3 -m fleet run official 3600     # the campaign (writes runs/<ts>/SUMMARY.md)
scripts/ratchet.sh                      # distil grown corpus -> corpus/*/evolved/
make coverage                           # llvm-cov over Flac/Native (cov/report/latest/)
```

## 2026-09-02 — `official` campaign, 10 h (current reference)

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

Measured after the `fz_proven_pairs` shipped-entrypoint improvement (drives `Flac.decode`
+ `Stream.peekInfo`, previously undriven) and re-`ratchet`ed corpus.

| metric | covered / total | % |
|---|---|---|
| **regions** | 6586 / 11098 | **59.3 %** |
| branches | 2818 / 4792 | 58.8 % |
| lines | 36332 / 62851 | 57.8 % |
| functions | 632 / 1545 | 40.9 % |

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
