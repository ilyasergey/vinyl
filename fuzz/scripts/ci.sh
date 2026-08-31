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

echo "== 3. crown-jewel mutator selftest (CRC vectors + generator/repair) =="
build/bin/mut_bench selftest

echo "== 4. mutator acceptance rate (expect ~25-27x; a drop means flac_struct.c regressed) =="
build/bin/mut_bench gen /tmp/ci_gen 200 0xC0FFEE >/dev/null
build/bin/mut_bench rate /tmp/ci_gen 20000 | tail -1

echo "== 5. config + corpus integrity =="
make validate
bash scripts/corpus_verify.sh

echo "== 6. smoke every target on libFuzzer =="
FUZZ_SMOKE_SECONDS="${FUZZ_SMOKE_SECONDS:-10}" make smoke

echo "== 7. honest per-target coverage (seeds-only) + baseline gate =="
# Build the coverage-instrumented siblings and replay the committed corpora through
# them (raw llvm-cov region/branch over Flac/Native/*.c). --seeds-only keeps the
# number reproducible (evolved/divergence corpora are not committed).
make --no-print-directory covfuzz
python3 cov/per_target.py --seeds-only
python3 cov/gate.py

echo "== 8. deterministic property sweeps (MD5 KAT/padding + Float-exact regression pin) =="
# The CI siblings of fz_md5 / fz_float_exact: fixed, coverage-flat surfaces that a
# campaign only wastes executions on. Each exits non-zero on a mismatch / an
# unexpected LPC divergence. $(BUILD) is absolute, so the target names are too.
make --no-print-directory "$PWD/build/bin/sweep_md5" "$PWD/build/bin/sweep_float_exact"
build/bin/sweep_md5
build/bin/sweep_float_exact

echo "== 9. standing conformance/coverage assertions =="
bash scripts/ci_assertions.sh

echo "CI: ALL GREEN"
