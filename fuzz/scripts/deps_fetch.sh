#!/usr/bin/env bash
# Fetch the pinned libFLAC source into the gitignored third_party/, and
# (optionally) the IETF conformance corpus into corpus/external/. Run from fuzz/.
#
#   scripts/deps_fetch.sh            # libFLAC 1.4.2
#   scripts/deps_fetch.sh --ietf     # + the IETF flac-test-files corpus
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

FLAC_TAG="${FLAC_TAG:-1.4.2}"
mkdir -p third_party corpus/external

if [ ! -d third_party/flac-src/include/FLAC ]; then
  echo "fetching libFLAC $FLAC_TAG -> third_party/flac-src"
  git clone --depth 1 --branch "$FLAC_TAG" https://github.com/xiph/flac third_party/flac-src
else
  echo "third_party/flac-src already present"
fi
# Warn (never fail) if a system flac disagrees with the source tag.
if command -v flac >/dev/null; then
  have="$(flac --version 2>/dev/null | awk '{print $2}')"
  [ "$have" = "$FLAC_TAG" ] || echo "note: system flac is $have, source tag is $FLAC_TAG"
fi

if [ "${1:-}" = "--ietf" ]; then
  if [ ! -d corpus/external/flac-test-files ]; then
    echo "fetching IETF flac-test-files -> corpus/external"
    git clone --depth 1 https://github.com/ietf-wg-cellar/flac-test-files \
      corpus/external/flac-test-files
  else
    echo "corpus/external/flac-test-files already present"
  fi
fi
echo "deps ready."
