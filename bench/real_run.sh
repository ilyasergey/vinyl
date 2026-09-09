#!/usr/bin/env bash
# Benchmark Vinyl vs libFLAC on the real-audio corpora.  Expects the corpora to
# be prepared already:
#
#   python3 bench/real_fetch.py --accept-ebu-terms      # EBU SQAM, 167.4 MiB
#   python3 bench/real_fetch.py --corpus librispeech    # LibriSpeech, 644.1 MiB
#
# BENCH_RUNS      measured repetitions (default 5)
# BENCH_THREAD_SWEEP  thread counts to sweep (default 1,2,4,8)
# BENCH_THREADS   caps the core count the sweep is clamped to (default: all cores)
# BENCH_SUITES    restrict to a comma-separated subset of suites
# BENCH_LIMIT     cap the unit count, for a smoke run
set -euo pipefail
cd "$(dirname "$0")/.."

BENCH=bench
RESULTS=$BENCH/real_results.csv

command -v flac >/dev/null || { echo "flac CLI required"; exit 1; }
flac --version | grep -qE 'flac 1\.[5-9]|flac [2-9]\.' || {
  echo "flac >= 1.5.0 required (this harness sweeps -j); found: $(flac --version)"; exit 1; }
[ -f "$BENCH/real_data/manifest.csv" ] || {
  echo "no prepared corpora — see bench/CORPORA.md"; exit 1; }

python3 $BENCH/real_units.py
lake build flactest >/dev/null
python3 $BENCH/real_run.py
python3 $BENCH/real_plot.py "$RESULTS"
echo "wrote $RESULTS, real_summary.md, real_compression.png, real_performance.png, real_threads.png"
