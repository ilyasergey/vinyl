"""Preferred RSS bounding for the AFL arm: a real cgroup v2 memory limit.

libFuzzer children are already RSS-bounded by -rss_limit_mb (and -fork); only the
AFL arm (-m none) needs external bounding. A kernel memory cgroup enforces the
budget atomically -- no polling gap, no spawn race -- so it is preferred over the
`fleet.watchdog` poller, which stays as the fallback for hosts (like a plain
devcontainer) with no delegated cgroup or systemd user session.

We bound the RESIDENT set only, never the address space: RLIMIT_AS/RLIMIT_DATA
are forbidden here (Lean reserves a huge virtual arena per thread; an
address-space cap kills healthy runs). cgroup v2 `memory.max` (systemd
`MemoryMax`) caps physical memory, which is exactly the RSS budget we want.

`detect()` probes for a usable mechanism and returns "cgroupfs", "systemd-run",
or None. `wrap_cmd()` wraps an argv so the wrapped process runs under a memory
cgroup sized to rss_limit_mb, or returns argv unchanged when no mechanism exists.
"""

import os
import shutil
import subprocess
from pathlib import Path

_CGROUP_ROOT = Path("/sys/fs/cgroup")


def _v2_self_dir() -> Path | None:
    """The current process's cgroup v2 directory, or None if not on unified v2.

    /proc/self/cgroup lists a single `0::<path>` line under cgroup v2; any
    hierarchy-numbered lines mean a legacy/hybrid v1 layout we do not drive.
    """
    try:
        lines = Path("/proc/self/cgroup").read_text().splitlines()
    except OSError:
        return None
    for line in lines:
        parts = line.split(":", 2)
        if len(parts) == 3 and parts[0] == "0":
            return _CGROUP_ROOT / parts[2].lstrip("/")
    return None


def _detect_cgroupfs() -> bool:
    """True iff we can create a child cgroup and set `memory.max` on it.

    This requires a delegated, writable v2 subtree with the memory controller
    already available to children. We prove it by actually creating a throwaway
    child and writing its memory.max, then removing it -- a probe that lies less
    than reading flags does.
    """
    base = _v2_self_dir()
    if base is None or not base.is_dir():
        return False
    try:
        controllers = (base / "cgroup.controllers").read_text().split()
    except OSError:
        return False
    if "memory" not in controllers:
        return False
    probe = base / f"vinyl_fuzz_probe_{os.getpid()}"
    try:
        probe.mkdir()
    except OSError:
        return False
    ok = False
    try:
        (probe / "memory.max").write_text("67108864")  # 64 MiB, immediately removed
        ok = True
    except OSError:
        ok = False
    finally:
        try:
            probe.rmdir()
        except OSError:
            pass
    return ok


def _detect_systemd_run() -> bool:
    """True iff `systemd-run --user --scope` can actually start a transient unit."""
    if shutil.which("systemd-run") is None:
        return False
    try:
        r = subprocess.run(
            ["systemd-run", "--user", "--scope", "--quiet", "true"],
            capture_output=True, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return r.returncode == 0


def detect() -> str | None:
    """Return the preferred usable cgroup mechanism id, or None.

    A directly writable delegated cgroupfs subtree is preferred (no per-exec unit
    manager overhead); systemd-run --user --scope is the second choice. None means
    no kernel bounding is available and the watchdog fallback must be used.
    """
    if _detect_cgroupfs():
        return "cgroupfs"
    if _detect_systemd_run():
        return "systemd-run"
    return None


def wrap_cmd(argv: list[str], rss_limit_mb: int, mechanism: str | None) -> list[str]:
    """Wrap argv so the process runs under a memory cgroup of rss_limit_mb MB.

    Returns argv unchanged when no mechanism is available or the limit is <= 0.
    Never touches RLIMIT_AS: the cgroup caps physical RSS only, and swap is
    pinned to 0 so the RSS budget cannot be evaded by swapping.
    """
    if not mechanism or rss_limit_mb <= 0:
        return list(argv)

    if mechanism == "systemd-run":
        return [
            "systemd-run", "--user", "--scope", "--quiet",
            "-p", f"MemoryMax={rss_limit_mb}M",
            "-p", "MemorySwapMax=0",
            "--", *argv,
        ]

    if mechanism == "cgroupfs":
        base = _v2_self_dir()
        if base is None:
            return list(argv)
        limit = rss_limit_mb * 1024 * 1024
        # Create a fresh leaf cgroup named after the wrapping shell's own pid (so
        # concurrent jobs never collide), enroll the shell, size the limit, then
        # exec argv in place -- the exec inherits the cgroup membership.
        script = (
            f'cg="{base}/vinyl_fuzz_$$"; '
            f'mkdir -p "$cg" && '
            f'printf %s {limit} > "$cg/memory.max" && '
            f'printf %s 0 > "$cg/memory.swap.max" 2>/dev/null; '
            f'printf %s $$ > "$cg/cgroup.procs"; '
            f'exec "$@"'
        )
        return ["sh", "-c", script, "sh", *argv]

    return list(argv)


if __name__ == "__main__":
    print(detect())
