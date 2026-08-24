#!/usr/bin/env bash
# Benchmark Vinyl vs libFLAC on the real-audio corpora.  Expects the corpora to
# be prepared already:
#
#   python3 bench/real_fetch.py --accept-ebu-terms      # EBU SQAM, 167.4 MiB
#   python3 bench/real_fetch.py --corpus librispeech    # LibriSpeech, 644.1 MiB
#
# BENCH_RUNS controls measured repetitions (default 5), BENCH_THREADS the thread
# count both codecs are given for their multithreaded rows (default: all cores),
# BENCH_SUITES restricts to a comma-separated subset of suites.
set -euo pipefail
cd "$(dirname "$0")/.."

BENCH=bench
RESULTS=$BENCH/real_results.csv

command -v flac >/dev/null || { echo "flac CLI required"; exit 1; }
[ -f "$BENCH/real_data/manifest.csv" ] || {
  echo "no prepared corpora — see bench/CORPORA.md"; exit 1; }

python3 $BENCH/real_units.py
lake build flactest >/dev/null
python3 $BENCH/real_run.py
python3 $BENCH/real_plot.py "$RESULTS"
echo "wrote $RESULTS, real_compression.png, real_performance.png, real_summary.md"
