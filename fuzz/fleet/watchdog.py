"""Per-job process-tree RSS watchdog (the AFL-arm fallback for cgroup bounding).

NEVER RLIMIT_AS / RLIMIT_DATA / ulimit -v. Lean reserves a large *virtual* arena
per worker thread; an address-space cap tight enough to catch a decompression
bomb also kills healthy files with "failed to create thread" (a 4 GiB RLIMIT_AS
killed the IETF corpus's own predictor-overflow files, which decode in ~4 MiB
RSS, and produced a false positive earlier in this audit). We bound RESIDENT set
instead, by polling.

libFuzzer bounds itself with -rss_limit_mb, and `fleet.cgroup` bounds the AFL
arm via a real memory cgroup when one is available. This watchdog is the AFL
fallback for hosts with no delegated cgroup: it walks only each registered job's
process tree -- not all of /proc -- reading /proc/<pid>/statm field 2 (resident
pages).
"""

import os
import signal
import threading
import time
from pathlib import Path

_PAGE = os.sysconf("SC_PAGE_SIZE")

# A decode bomb can grow from a few MiB to tens of GiB in well under a second, so
# the poll interval must stay short enough to catch it before the host OOMs.
_POLL_SECONDS = 0.5

# Bound on freeze passes when tearing a tree down; a frozen (SIGSTOP-ed) parent
# cannot fork, so the pid set converges in one or two passes in practice.
_FREEZE_PASSES = 8


def _children(pid: int) -> list[int]:
    kids: list[int] = []
    task = Path(f"/proc/{pid}/task")
    try:
        for t in task.iterdir():
            cf = t / "children"
            try:
                kids += [int(x) for x in cf.read_text().split()]
            except OSError:
                pass
    except OSError:
        pass
    return kids


def _tree(pid: int) -> list[int]:
    seen, stack = [], [pid]
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.append(p)
        stack += _children(p)
    return seen


def _rss_mb(pid: int) -> int:
    try:
        with open(f"/proc/{pid}/statm") as f:
            return int(f.read().split()[1]) * _PAGE // (1024 * 1024)
    except (OSError, IndexError, ValueError):
        return 0


def _signal_tree(pid: int, sig: int) -> None:
    for p in _tree(pid):
        try:
            os.kill(p, sig)
        except OSError:
            pass


def _kill_tree(pid: int) -> None:
    """Tear the whole tree down without the spawn-between-walk-and-kill race.

    The naive walk-then-SIGKILL loses any child forked after we snapshot a
    parent's `children` list but before we kill that parent: once the parent
    dies the child reparents to init and drops out of the tree, so a re-walk
    never sees it. We first SIGSTOP every process in the tree -- a stopped
    process cannot fork, so the reachable pid set converges -- re-walking until
    no new pid appears, and only then SIGKILL the frozen set. Freezing keeps the
    children attached to their (still-alive, merely stopped) parents, so nothing
    reparents away before we reach it.
    """
    frozen: set[int] = set()
    for _ in range(_FREEZE_PASSES):
        fresh = [p for p in _tree(pid) if p not in frozen]
        if not fresh:
            break
        for p in fresh:
            try:
                os.kill(p, signal.SIGSTOP)
            except OSError:
                pass
            frozen.add(p)
    for p in frozen:
        try:
            os.kill(p, signal.SIGKILL)
        except OSError:
            pass


class Watchdog:
    """Polls registered (root_pid, rss_limit_mb, label, logfile) jobs and
    SIGKILLs a job whose whole process tree exceeds its resident budget."""

    def __init__(self):
        self._jobs: list[tuple[int, int, str, Path]] = []
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self.kills = 0
        self.peak: dict[str, int] = {}

    def register(self, pid: int, rss_limit_mb: int, label: str, logpath: Path):
        with self._lock:
            self._jobs.append((pid, rss_limit_mb, label, logpath))

    def start(self):
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()

    def _loop(self):
        while not self._stop.wait(_POLL_SECONDS):
            with self._lock:
                jobs = list(self._jobs)
            for pid, limit, label, logf in jobs:
                total = sum(_rss_mb(p) for p in _tree(pid))
                self.peak[label] = max(self.peak.get(label, 0), total)
                # C5: the budget is on the JOB, i.e. its whole process tree. A
                # decompression bomb spread across N worker threads/children can
                # sum far past `limit` while no single process exceeds it -- the
                # old per-process test never fired on exactly that case.
                if limit and total > limit:
                    _kill_tree(pid)
                    self.kills += 1
                    with open(logf, "a") as f:
                        f.write(f"[watchdog] {label} tree RSS {total}MB > {limit}MB -- SIGKILL "
                                f"@{time.strftime('%H:%M:%S')}\n")
