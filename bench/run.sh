#!/usr/bin/env bash
# Benchmark Vinyl vs libFLAC on the synthetic corpus.  Timing lives in one
# persistent Python process so timestamp-process startup is not charged to the
# command under test.
#
# BENCH_RUNS      measured repetitions (default 5)
# BENCH_THREAD_SWEEP  thread counts to sweep (default 1,2,4,8, clamped to cores)
# BENCH_THREADS   caps the core count the sweep is clamped to
set -euo pipefail
cd "$(dirname "$0")/.."

BENCH=bench
CORPUS=$BENCH/corpus
RESULTS=$BENCH/results.csv

# Both harnesses pass `-j` to the encoder, which libFLAC gained in 1.5.0; an
# older CLI fails mid-run with "invalid option -- j" instead of here.
command -v flac >/dev/null || { echo "flac CLI required"; exit 1; }
flac --version | grep -qE 'flac 1\.[5-9]|flac [2-9]\.' || {
  echo "flac >= 1.5.0 required (this harness sweeps -j); found: $(flac --version)"; exit 1; }
[ -d "$CORPUS" ] || python3 $BENCH/gen_corpus.py "$CORPUS"
lake build flactest >/dev/null

python3 "$BENCH/run.py"
python3 $BENCH/plot.py "$RESULTS"
echo "wrote $RESULTS, summary.md, compression.png, performance.png, threads.png"
