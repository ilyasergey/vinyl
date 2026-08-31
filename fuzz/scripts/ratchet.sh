#!/usr/bin/env bash
# ratchet.sh -- distill a run's grown corpora (all variants + AFL queues) into the
# persistent, coverage-minimized corpus/<target>/evolved/ via each target's own
# .fuzz binary (Phase 3B per-target ratchet). Non-destructive: reads runs/, appends
# to evolved/. Run after a campaign to carry its coverage forward.
#
#   scripts/ratchet.sh [RUN_DIR]     # default: newest runs/*/
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1   # fuzz/
RUN="${1:-$(ls -dt runs/*/ 2>/dev/null | head -1)}"
[ -d "$RUN" ] || { echo "no run dir ($RUN)"; exit 1; }
RUN="${RUN%/}"
echo "ratchet: distilling $RUN -> corpus/<target>/evolved/"
mapfile -t TARGETS < <(ls targets/*.c | sed 's#.*/##; s#\.c$##')

for t in "${TARGETS[@]}"; do
  bin="build/bin/$t.fuzz"
  [ -x "$bin" ] || { echo "  SKIP $t (no $bin)"; continue; }
  # The AFL queue is merged in alongside the libFuzzer corpora below. `-merge=1`
  # coverage-minimizes ALL sources against the target's own instrumentation, so a
  # separate `afl-cmin` pass over the queue would be redundant -- this IS the
  # coverage-minimized cmin, just via the libFuzzer merger.
  srcs=()
  for d in "$RUN/$t"/corpus "$RUN/$t".*/corpus; do [ -d "$d" ] && srcs+=("$d"); done
  for q in "$RUN/$t"/afl/*/queue "$RUN/$t".*/afl/*/queue; do [ -d "$q" ] && srcs+=("$q"); done
  [ "${#srcs[@]}" -eq 0 ] && { echo "  SKIP $t (no grown corpus in run)"; continue; }
  dest="corpus/$t/evolved"; mkdir -p "$dest"
  before=$(find "$dest" -type f | wc -l)
  nice -n 15 "$bin" -merge=1 -merge_control_file="/tmp/ratchet_mcf_$t" \
      -max_len=4194304 -rss_limit_mb=8000 -detect_leaks=0 \
      "$dest" "${srcs[@]}" >/dev/null 2>&1
  after=$(find "$dest" -type f | wc -l)
  echo "  $t: |evolved| $before -> $after"
done
echo "ratchet done."
