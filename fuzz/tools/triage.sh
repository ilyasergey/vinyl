#!/usr/bin/env bash
# Triage a reproducer into a findings/ entry: replay it through the shipped CLI
# (the neutral, toolchain-free surface the client will reproduce with), record
# both codecs' verdicts via pcm_check, and scaffold a REPORT.md. Run from fuzz/.
#
#   tools/triage.sh <reproducer.flac> <NNN-slug> [decode|encode]
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

REPRO="${1:?usage: triage.sh <reproducer> <NNN-slug> [kind]}"
SLUG="${2:?need an NNN-slug, e.g. 001-decode-len-diff}"
DIR="findings/$SLUG"
mkdir -p "$DIR"
cp "$REPRO" "$DIR/repro.flac"

{
  echo "# Finding $SLUG"
  echo
  echo "- reproducer: \`repro.flac\` ($(stat -c%s "$REPRO") bytes)"
  echo "- codec rev: $(git -C .. rev-parse --short HEAD 2>/dev/null || echo unknown)"
  echo
  echo "## pcm_check (Vinyl vs libFLAC)"
  echo '```'
  ./build/bin/pcm_check "$REPRO" 2>&1 || true
  echo '```'
  echo
  echo "## shipped CLI replay"
  echo '```'
  # The shipped decoder is the `vinyl` executable (flactest is the test runner);
  # --decode-fast takes <in.flac> <out.pcm>.
  ( cd .. && lake exe vinyl --decode-fast "fuzz/$DIR/repro.flac" "fuzz/$DIR/repro.decoded.pcm" 2>&1 \
      && echo "decode OK -> repro.decoded.pcm" ) || \
    echo "(vinyl --decode-fast rejected/errored — expected for a reject reproducer)"
  echo '```'
  echo
  echo "## classification"
  echo "- bug_class: (L Lean-theorem | C construction | V validity | I interop | D DoS)"
  echo "- severity:"
  echo "- analysis:"
} > "$DIR/REPORT.md"

cat > "$DIR/repro.sh" <<EOF
#!/usr/bin/env bash
# Standalone reproduction for $SLUG.
set -e
cd "\$(dirname "\$0")/../.."
./build/bin/pcm_check "$DIR/repro.flac"
EOF
chmod +x "$DIR/repro.sh"
echo "scaffolded $DIR/{REPORT.md,repro.flac,repro.sh}"
