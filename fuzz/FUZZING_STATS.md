# Fuzzing statistics — reference baseline

A snapshot of a full-fleet campaign + coverage measurement, kept as a reference point
for future runs. Regenerate the numbers with:

```sh
python3 -m fleet run official 3600     # the campaign (writes runs/<ts>/SUMMARY.md)
scripts/ratchet.sh                      # distil grown corpus -> corpus/*/evolved/
make coverage                           # llvm-cov over Flac/Native (cov/report/latest/)
```

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
