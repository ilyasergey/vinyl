#!/usr/bin/env bash
# Benchmark vinyl vs libFLAC on the synthetic corpus.
# Produces bench/results.csv: file,encoder,seconds,bytes,raw_bytes
# Every vinyl output is additionally verified with `flac -t`.
set -euo pipefail
cd "$(dirname "$0")/.."

BENCH=bench
CORPUS=$BENCH/corpus
OUT=$BENCH/out
RESULTS=$BENCH/results.csv
mkdir -p "$OUT"

command -v flac >/dev/null || { echo "flac CLI required"; exit 1; }
[ -d "$CORPUS" ] || python3 $BENCH/gen_corpus.py "$CORPUS"
lake build flactest >/dev/null

now() { python3 -c 'import time; print(time.perf_counter())'; }

echo "file,encoder,seconds,bytes,raw_bytes" > "$RESULTS"

for pcm in "$CORPUS"/*.pcm; do
  name=$(basename "$pcm" .pcm)
  ch=1
  case "$name" in *.2ch) ch=2; name=$(basename "$name" .2ch);; esac
  raw=$(stat -f%z "$pcm" 2>/dev/null || stat -c%s "$pcm")

  t0=$(now)
  .lake/build/bin/flactest --encode "$pcm" "$OUT/$name.vinyl.flac" 4096 $ch >/dev/null
  t1=$(now)
  flac -t -s "$OUT/$name.vinyl.flac"   # merge-gate: outputs must verify
  sz=$(stat -f%z "$OUT/$name.vinyl.flac" 2>/dev/null || stat -c%s "$OUT/$name.vinyl.flac")
  echo "$name,vinyl,$(python3 -c "print($t1-$t0)"),$sz,$raw" >> "$RESULTS"

  # decode timings on the vinyl-encoded file (outputs must round-trip)
  t0=$(now)
  .lake/build/bin/flactest --decode-fast "$OUT/$name.vinyl.flac" "$OUT/dec.raw" >/dev/null
  t1=$(now)
  cmp -s "$OUT/dec.raw" "$pcm"   # merge-gate: decoded bytes = input bytes
  echo "$name,vinyl decode,$(python3 -c "print($t1-$t0)"),$sz,$raw" >> "$RESULTS"
  t0=$(now)
  flac -d -s --force-raw-format --sign=signed --endian=little \
    -f -o "$OUT/dec2.raw" "$OUT/$name.vinyl.flac" 2>/dev/null
  t1=$(now)
  echo "$name,flac decode,$(python3 -c "print($t1-$t0)"),$sz,$raw" >> "$RESULTS"

  for lvl in 0 5 8; do
    t0=$(now)
    flac -$lvl --force-raw-format --sign=signed --endian=little --channels=$ch \
      --bps=16 --sample-rate=44100 -s -f -o "$OUT/$name.flac$lvl.flac" "$pcm" 2>/dev/null
    t1=$(now)
    sz=$(stat -f%z "$OUT/$name.flac$lvl.flac" 2>/dev/null || stat -c%s "$OUT/$name.flac$lvl.flac")
    echo "$name,flac -$lvl,$(python3 -c "print($t1-$t0)"),$sz,$raw" >> "$RESULTS"
  done
  echo "done: $name"
done

python3 $BENCH/plot.py "$RESULTS"
echo "wrote $RESULTS, compression.png, performance.png"
