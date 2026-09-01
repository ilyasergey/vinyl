#!/usr/bin/env bash
# Cross-version libFLAC accept-set differential: decode every file under the given corpus
# dirs (default: the decode corpora) with BOTH flac142_decode (1.4.2) and flac150_decode
# (1.5.0) -- same source, only the linked libFLAC differs -- and report every file whose
# accept/reject verdict differs between versions. This is the reproducible form of the
# "1 of N files" accept-set shift the 1.5.0 referee exists to make observable; each
# referee-derived counter in a campaign is only interpretable against a known libFLAC
# version, and this shows exactly which streams the version choice changes.
#
#   scripts/flac_version_diff.sh [dir ...]
#
# Requires build/bin/flac142_decode and build/bin/flac150_decode (scripts/build_flac150.sh).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

D142=build/bin/flac142_decode
D150=build/bin/flac150_decode
if [ ! -x "$D142" ] || [ ! -x "$D150" ]; then
  echo "missing $D142 / $D150 -- run scripts/build_flac150.sh first" >&2
  exit 2
fi

dirs=("$@")
[ ${#dirs[@]} -eq 0 ] && dirs=(corpus/decode corpus/fz_decode_diff corpus/fz_decode_capacity)

# The probes exit 0=accept, 1=reject, 2=read/usage error, and print the verdict word
# (accept / reject) on stdout -- so parse stdout, never the exit code (a reject's exit 1
# is legitimate, not a failure). Empty stdout (exit 2) becomes "err".
verdict() {
  local v
  v=$("$1" "$2" 2>/dev/null | awk 'NR==1{print $1}')
  printf '%s' "${v:-err}"
}

total=0 diffs=0
while IFS= read -r -d '' f; do
  total=$((total + 1))
  v142=$(verdict "$D142" "$f")
  v150=$(verdict "$D150" "$f")
  if [ "$v142" != "$v150" ]; then
    diffs=$((diffs + 1))
    echo "DIVERGE  1.4.2=$v142  1.5.0=$v150  $f"
  fi
done < <(find "${dirs[@]}" -type f -print0 2>/dev/null)

echo "checked $total files, $diffs cross-version accept-set divergence(s)"
