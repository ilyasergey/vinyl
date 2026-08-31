#!/usr/bin/env python3
"""CI coverage gate (Phase 1F). Compares the latest per-target run's fleet-union
native region coverage against a committed baseline and FAILS on regression.

The baseline (cov/baseline.json) is deliberately NOT committed until Phase 3D
(dict/value-profile) lands and changes the reachable set -- pinning a number
before then would bake in a soon-stale floor. Until it exists, this gate reports
the current number and passes (never invents a baseline).

Baseline is a FLOOR, never a target: a low number is a finding, not a failure, so
we gate only on *regression* below a previously-accepted floor.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SUMMARY = HERE / "report" / "latest" / "summary.json"
BASELINE = HERE / "baseline.json"


def main() -> int:
    if not SUMMARY.exists():
        print(f"GATE: no {SUMMARY} -- run `make coverage` first", file=sys.stderr)
        return 1
    s = json.loads(SUMMARY.read_text())
    union = s.get("targets", {}).get("__union__")
    if not union:
        print("GATE: summary has no fleet union (need >1 target)", file=sys.stderr)
        return 1
    cov, tot = union["regions_covered"], union["regions_total"]
    pct = 100.0 * cov / max(1, tot)
    print(f"GATE: fleet-union native region coverage = {cov}/{tot} ({pct:.2f}%)"
          f"{'  [seeds-only]' if s.get('seeds_only') else ''}")
    if not BASELINE.exists():
        print("GATE: no committed baseline yet (set cov/baseline.json after Phase 3D). PASS.")
        return 0
    base = json.loads(BASELINE.read_text())["regions_covered"]
    if cov < base:
        print(f"GATE FAIL: region coverage {cov} < baseline {base} (regression)", file=sys.stderr)
        return 1
    print(f"GATE: {cov} >= baseline {base}. PASS.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
