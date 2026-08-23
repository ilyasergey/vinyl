#!/usr/bin/env bash
# Benchmark Vinyl vs libFLAC on the synthetic corpus.  Timing lives in one
# persistent Python process so timestamp-process startup is not charged to the
# command under test.  Set BENCH_RUNS to control repetitions (default: 5).
set -euo pipefail
cd "$(dirname "$0")/.."

BENCH=bench
CORPUS=$BENCH/corpus
RESULTS=$BENCH/results.csv

command -v flac >/dev/null || { echo "flac CLI required"; exit 1; }
[ -d "$CORPUS" ] || python3 $BENCH/gen_corpus.py "$CORPUS"
lake build flactest >/dev/null

python3 "$BENCH/run.py"
python3 $BENCH/plot.py "$RESULTS"
echo "wrote $RESULTS, compression.png, performance.png"
