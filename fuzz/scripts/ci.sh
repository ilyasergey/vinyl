#!/usr/bin/env bash
# Fuzz-rig CI: build both engines, prove the crown-jewel mutator, verify the
# corpus, and smoke every target. Deliberately SEPARATE from scripts/check.sh
# (the proof merge gate), which stays hermetic (no clang/afl/cmake/libFLAC dep).
# Run from fuzz/.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "== 1. build (both engines + tools) =="
make -j"$(nproc)" all

echo "== 2. required symbols present in the fortified codec =="
make check-symbols

echo "== 3. proven-equivalence twin map + encode-side TCB oracle guard =="
# E1: every proven-equivalent implementation side has a live C connector + >=1 driving
# target, AND -- crucially -- the reference writer (Unchecked.encode) and emitFast stay
# DISTINCT compiled callees in the IR. If a future `import Flac` pulled the
# Unchecked_encode->emitFast @[csimp] into FuzzGen's scope, the two @[export] wrappers
# would alias and fz_encode_pair would silently compare emitFast to itself forever.
python3 cov/twins.py

echo "== 4. crown-jewel mutator selftest (CRC vectors + generator/repair) =="
build/bin/mut_bench selftest

echo "== 5. mutator acceptance rate (expect ~25-27x; a drop means flac_struct.c regressed) =="
build/bin/mut_bench gen /tmp/ci_gen 200 0xC0FFEE >/dev/null
build/bin/mut_bench rate /tmp/ci_gen 20000 | tail -1

echo "== 6. config + corpus integrity =="
make validate
bash scripts/corpus_verify.sh

echo "== 7. smoke every target on libFuzzer =="
FUZZ_SMOKE_SECONDS="${FUZZ_SMOKE_SECONDS:-10}" make smoke

echo "== 8. honest per-target coverage (seeds-only) + baseline gate =="
# Build the coverage-instrumented siblings and replay the committed corpora through
# them (raw llvm-cov region/branch over Flac/Native/*.c). --seeds-only keeps the
# number reproducible (evolved/divergence corpora are not committed).
make --no-print-directory covfuzz
python3 cov/per_target.py --seeds-only
python3 cov/gate.py

echo "== 9. deterministic property sweeps (MD5 KAT/padding + Float-exact regression pin) =="
# The CI siblings of fz_md5 / fz_float_exact: fixed, coverage-flat surfaces that a
# campaign only wastes executions on. Each exits non-zero on a mismatch / an
# unexpected LPC divergence. $(BUILD) is absolute, so the target names are too.
make --no-print-directory "$PWD/build/bin/sweep_md5" "$PWD/build/bin/sweep_float_exact"
build/bin/sweep_md5
build/bin/sweep_float_exact

echo "== 10. standing conformance/coverage assertions =="
bash scripts/ci_assertions.sh

echo "CI: ALL GREEN"
