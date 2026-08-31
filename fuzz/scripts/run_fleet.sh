#!/usr/bin/env bash
# Thin wrapper over the Python fleet runner (mirrors bench/run.sh -> bench/run.py).
#
#   scripts/run_fleet.sh [config-name|path] [seconds]
#   scripts/run_fleet.sh default 1800
#   scripts/run_fleet.sh smoke 30
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 -m fleet run "$@"
