"""python3 -m fleet run|list|validate|smoke|status

Thin CLI over config/launch/report. Invoked from the fuzz/ directory (the
Makefile does exactly this); scripts/*.sh are thin wrappers over it.
"""

import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from . import launch
from .config import (BUILD_BIN, ConfigError, campaign_names, discover_targets, load_campaign,
                     validate_all)


def _cmd_list() -> int:
    from .config import TARGETS
    for name, t in discover_targets().items():
        print(f"{name}  [{t.bug_class}]  {t.input_kind}  {t.mutator}")
        print(f"    {t.summary}")
        print(f"    corpus  : {', '.join(TARGETS[name]['corpus'])}")
        if t.variants:
            print(f"    variants: {', '.join(['default', *t.variants])}")
    print(f"\ncampaigns: {', '.join(campaign_names()) or '(none)'}")
    return 0


def _cmd_smoke() -> int:
    """10s (FUZZ_SMOKE_SECONDS) per target on libFuzzer; non-zero exit = a
    spurious abort on the seed corpus, which fails the smoke."""
    from .config import CORPUS_DIR, resolve
    secs = int(os.environ.get("FUZZ_SMOKE_SECONDS", "10"))
    bad = 0
    for name, t in discover_targets().items():
        binary = BUILD_BIN / f"{name}.fuzz"
        if not binary.exists():
            print(f"SMOKE SKIP {name}: not built")
            continue
        cfg = resolve(t, "default")
        corpus = [str(CORPUS_DIR / c) for c in cfg["corpus"] if (CORPUS_DIR / c).is_dir()]
        env = dict(os.environ, FUZZ_MUTATOR=cfg["mutator"], FUZZ_DUMP_DIR="/tmp/fuzz_smoke_div")
        # libFuzzer writes newly discovered units into its FIRST corpus dir, so a
        # throwaway scratch dir goes first and the committed corpora follow as
        # read-only inputs -- otherwise every smoke run silently mutates the seeds.
        scratch = tempfile.mkdtemp(prefix=f"fuzz_smoke_{name}_")
        args = [str(binary), f"-max_total_time={secs}", f"-max_len={cfg['max_len']}",
                "-detect_leaks=0", f"-artifact_prefix={scratch}/", scratch, *corpus]
        r = subprocess.run(args, env=env, capture_output=True, text=True)
        ok = r.returncode == 0
        print(f"SMOKE {'OK  ' if ok else 'FAIL'} {name} (exit {r.returncode})")
        if ok:
            shutil.rmtree(scratch, ignore_errors=True)  # keep the scratch (and its
        else:                                            # crash-* reproducer) on FAIL
            bad += 1
            sys.stderr.write(r.stderr[-800:] + f"\n  reproducer + corpus kept in {scratch}\n")
    return 1 if bad else 0


def _cmd_status(run: str | None) -> int:
    runs = BUILD_BIN.parent.parent / "runs"
    target = Path(run) if run else max(runs.glob("*/"), default=None, key=os.path.getmtime)
    if not target or not (target / "status.json").exists():
        print("no status.json (no run yet?)", file=sys.stderr)
        return 1
    print((target / "status.json").read_text())
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    cmd, rest = argv[0], argv[1:]
    try:
        if cmd == "validate":
            return validate_all()
        if cmd == "list":
            return _cmd_list()
        if cmd == "smoke":
            return _cmd_smoke()
        if cmd == "status":
            return _cmd_status(rest[0] if rest else None)
        if cmd == "run":
            name = next((a for a in rest if not a.isdigit()), "default")
            secs = next((int(a) for a in rest if a.isdigit()), 0)
            meta, _ = load_campaign(name)  # validates + supplies default_seconds
            return launch.run_fleet(name, secs or meta["default_seconds"])
    except (ConfigError, FileNotFoundError) as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1
    print(f"unknown command: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
