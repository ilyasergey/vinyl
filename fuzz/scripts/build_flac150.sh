#!/usr/bin/env bash
# Fetch + build libFLAC 1.5.0 as a SEPARATE static referee (build/lib/libflac.plain150.a),
# alongside the pinned 1.4.2 the fleet links. 1.5.0 tightened the accept set (notably it
# rejects block size 65536, which 1.4.2 accepted), so a second-version referee makes those
# accept-set shifts observable instead of silently version-dependent. This does NOT replace
# the 1.4.2 referee -- to flip the whole fleet, re-fetch with FLAC_TAG=1.5.0 and rebuild.
#
#   scripts/build_flac150.sh            # -> build/lib/libflac.plain150.a + build/bin/flac150_decode
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

SRC=third_party/flac-src-150
if [ ! -d "$SRC/include/FLAC" ]; then
  echo "cloning libFLAC 1.5.0 -> $SRC"
  git clone --depth 1 --branch 1.5.0 https://github.com/xiph/flac "$SRC"
fi

echo "cmake configure + build libFLAC 1.5.0 (static, no programs)"
cmake -S "$SRC" -B build/flac-plain150 -DCMAKE_C_COMPILER=clang \
  -DCMAKE_C_FLAGS="-O1 -g" -DBUILD_SHARED_LIBS=OFF -DBUILD_PROGRAMS=OFF -DBUILD_EXAMPLES=OFF \
  -DBUILD_TESTING=OFF -DBUILD_DOCS=OFF -DWITH_OGG=OFF -DINSTALL_MANPAGES=OFF >/dev/null
cmake --build build/flac-plain150 --target FLAC -j "$(nproc)" >/dev/null
mkdir -p build/lib
cp build/flac-plain150/src/libFLAC/libFLAC.a build/lib/libflac.plain150.a
echo "built build/lib/libflac.plain150.a ($(strings build/lib/libflac.plain150.a | grep -m1 -oE 'reference libFLAC [0-9.]+'))"

echo "building build/bin/flac150_decode (1.5.0-linked accept/reject probe)"
clang -O1 -g -I"$SRC/include" -o build/bin/flac150_decode tools/flac150_decode.c build/lib/libflac.plain150.a -lm

# Same source linked against the pinned 1.4.2 referee -> an apples-to-apples cross-version
# differential (identical check logic, only the libFLAC version differs). Requires the
# 1.4.2 referee (make build/lib/libflac.plain.a) to exist.
if [ -f build/lib/libflac.plain.a ]; then
  echo "building build/bin/flac142_decode (1.4.2-linked, same logic)"
  clang -O1 -g -Ithird_party/flac-src/include -o build/bin/flac142_decode tools/flac150_decode.c \
    build/lib/libflac.plain.a -lm
fi
echo "done."
