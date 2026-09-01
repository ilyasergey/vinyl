"""Run directory, corpus composition, process launch, and RSS discipline.

Each job runs in runs/<ts>/<label>/ with its own composed corpus, artifacts,
and FUZZ_DUMP_DIR. AFL instances of one target share ONE -o root so -M/-S sync
works. RSS is bounded by -rss_limit_mb (libFuzzer) or the process-tree watchdog
(AFL); never RLIMIT_AS.
"""

import hashlib
import os
import shutil
import signal
import subprocess
import time
from pathlib import Path

from . import cgroup, report
from .config import CORPUS_DIR, FLEET_TOML, FUZZ_ROOT, Job, load_campaign
from .watchdog import Watchdog


def _compose_corpus(job: Job, dest: Path) -> tuple[int, int]:
    """Copy every declared corpus dir into `dest` with content-hash names, so a
    basename collision across sources can never silently drop a seed. Returns
    (files, duplicate_contents)."""
    dest.mkdir(parents=True, exist_ok=True)
    seen: set[str] = set()
    n = dup = 0
    # Committed seed dirs PLUS this target's distilled evolved corpus (Phase 3B
    # ratchet): campaigns start from the coverage-minimized product of prior runs,
    # so the 1.83B-exec investment carries forward instead of restarting from seeds.
    evolved = CORPUS_DIR / job.target / "evolved"
    sources = [CORPUS_DIR / e for e in job.corpus] + ([evolved] if evolved.is_dir() else [])
    for src in sources:
        if not src.is_dir():
            continue
        for f in src.iterdir():
            if not f.is_file():
                continue
            data = f.read_bytes()
            h = hashlib.sha256(data).hexdigest()[:16]
            if h in seen:
                dup += 1
                continue
            seen.add(h)
            (dest / f"{h}_{f.name}").write_bytes(data)
            n += 1
    if n == 0:
        # A3: config._validate_corpus already proved this bundle non-empty, so a
        # zero here means the tree changed under us -- fail, do NOT invent a
        # single `fLaC` seed and let the campaign look healthy on 4 bytes.
        raise FileNotFoundError(f"{dest}: composed corpus is empty ({list(job.corpus)})")
    return n, dup


def _libfuzzer_cmd(job: Job, wd: Path, seconds: int) -> tuple[list[str], dict]:
    # A strict campaign (FUZZ_STRICT set) WANTS aborts to surface via exit code, so
    # it keeps crash-stopping; a normal campaign uses -fork + -ignore_* and relies on
    # the post-run crash-* gate instead.
    strict = job.env.get("FUZZ_STRICT", "0") not in ("0", "", None)
    args = [str(job.binary), f"-rss_limit_mb={job.rss_limit_mb}", f"-timeout={job.timeout}",
            "-detect_leaks=0", "-print_final_stats=1", f"-max_len={job.max_len}",
            # -fork replaces the old `-workers=N -jobs=1000000000` respawn hack. Each
            # fork child is a fresh fork+exec that re-runs main -> lean_init_task_manager
            # (so the Lean runtime is cleanly re-initialised per child), and the parent
            # emits ONE coherent cumulative stat stream -- no exec/s inflation, no OOM
            # restart churn. A child that abort()s is respawned within -max_total_time.
            f"-fork={job.workers}",
            f"-artifact_prefix={wd}/artifacts/"]
    if not strict:
        # Benign OOM/timeout/abort must not tear down the whole fork mid-campaign; the
        # post-run gate (report.py / CI) FAILS on any crash-* artifact instead. smoke
        # and the strict campaign omit these and keep exit-code detection.
        args += ["-ignore_ooms=1", "-ignore_timeouts=1", "-ignore_crashes=1"]
    # FLAC decode is gated on magic-value equality tests; a FLAC dictionary + value
    # profile jump the gate. Scoped to flac_stream ONLY -- a FLAC dict pollutes RAW
    # parameter blocks and is useless on packed PCM (Phase 3D).
    if job.input_kind == "flac_stream":
        dict_path = FUZZ_ROOT / "config" / "flac.dict"
        if dict_path.exists():
            args.append(f"-dict={dict_path}")
        args += ["-use_value_profile=1", "-entropic=1"]
    if seconds > 0:
        args.append(f"-max_total_time={seconds}")
    args.append(str(wd / "corpus"))
    env = dict(os.environ)
    env.update(job.env)
    env.setdefault("LEAN_NUM_THREADS", "1")
    env["FUZZ_MUTATOR"] = job.mutator
    env["FUZZ_DUMP_DIR"] = str(wd / "divergences")
    return args, env


def _afl_cmd(job: Job, wd: Path, afl_out: Path, instance: str, seconds: int) -> tuple[list[str], dict]:
    args = ["afl-fuzz", "-i", str(wd / "corpus"), "-o", str(afl_out), "-m", "none",
            "-t", str(job.timeout * 1000), "-G", str(job.max_len)]
    args += (["-M", "main"] if instance == "main" else ["-S", instance])
    if job.input_kind == "flac_stream":
        # FLAC dictionary on the flac_stream AFL arm only (Phase 3D), same scoping as
        # libFuzzer's -dict.
        dict_path = FUZZ_ROOT / "config" / "flac.dict"
        if dict_path.exists():
            args += ["-x", str(dict_path)]
        # CMPLog / RedQueen `-c` sibling if it was built (`make cmplog`) -- solves the
        # non-CRC magic values (sync / block-size / sample-rate / bps codes, STREAMINFO
        # fields). Additive over the CRC mutator + dict (Phase 3E-afl).
        cmplog = FUZZ_ROOT / "build" / "bin" / f"{job.target}.cmplog"
        if cmplog.exists():
            args += ["-c", str(cmplog)]
    args += ["--", str(job.binary)]  # no @@: in-memory persistent harness
    env = dict(os.environ)
    env.update(job.env)
    env.setdefault("LEAN_NUM_THREADS", "1")
    env["AFL_MAP_SIZE"] = str(job.mapsize or 0)
    env["AFL_SKIP_CPUFREQ"] = "1"
    env["AFL_AUTORESUME"] = "1"
    env["AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES"] = "1"
    env["FUZZ_DUMP_DIR"] = str(wd / "divergences")
    _afl_mut = {"crc": "afl_mutator.so", "pcm": "pcm_mutator.so"}.get(job.mutator)
    if _afl_mut:
        env["AFL_CUSTOM_MUTATOR_LIBRARY"] = str(FUZZ_ROOT / "build" / "lib" / _afl_mut)
    return args, env


def run_fleet(campaign: str, seconds: int, run_root: Path | None = None) -> int:
    meta, jobs = load_campaign(campaign)
    # A job whose binary is not built is a broken config, not something to skip
    # past -- an operator asked for it. Fail before creating a run dir.
    missing = sorted({j.binary.name for j in jobs if not j.binary.exists()})
    if missing:
        raise FileNotFoundError(f"campaign {campaign}: binaries not built: {', '.join(missing)} "
                                f"(run `make` in {FUZZ_ROOT})")
    ts = time.strftime("%Y%m%d_%H%M%S")
    root = run_root or (FUZZ_ROOT / "runs" / ts)
    root.mkdir(parents=True, exist_ok=True)
    shutil.copy(FLEET_TOML, root / "fleet.snapshot.toml")
    report.write_build_info(root)

    wd_watch = Watchdog()
    procs: list[tuple[Job, str, subprocess.Popen, Path]] = []

    # Phase 3C: prefer a cgroup v2 RSS bound for the AFL arm (libFuzzer children are
    # already bounded by -rss_limit_mb + -fork). detect() returns None in this
    # devcontainer (no delegation) -> wrap_cmd is a passthrough and the watchdog
    # remains the fallback. NEVER RLIMIT_AS.
    cg_mech = cgroup.detect()
    print(f"fleet {ts}: {len(jobs)} job(s), {seconds}s budget -> {root} "
          f"(cgroup: {cg_mech or 'none, watchdog fallback'})")
    for job in jobs:
        # libFuzzer parallelizes inside one process (-workers); AFL uses one
        # -M/-S instance per process.
        for inst in (["main"] if job.engine == "libfuzzer" else
                     ["main"] + [f"sec{i}" for i in range(2, job.instances + 1)]):
            label = job.label if inst == "main" else f"{job.label}.{inst}"
            wd = root / label
            (wd / "artifacts").mkdir(parents=True, exist_ok=True)
            (wd / "divergences").mkdir(parents=True, exist_ok=True)
            files, dup = _compose_corpus(job, wd / "corpus")
            logf = root / f"{label}.log"
            if job.engine == "libfuzzer":
                args, env = _libfuzzer_cmd(job, wd, seconds)
            else:
                afl_out = root / job.label / "afl"  # ONE -o per target for -M/-S sync
                afl_out.mkdir(parents=True, exist_ok=True)
                args, env = _afl_cmd(job, wd, afl_out, inst, seconds)
                # Wrap in a cgroup RSS bound when available (no-op passthrough if not).
                args = cgroup.wrap_cmd(args, job.rss_limit_mb, cg_mech)
            with open(logf, "w") as lf:
                lf.write(f"# {label}: composed {files} seeds ({dup} dup contents deduped)\n")
                lf.write(f"# cmd: {' '.join(args)}\n\n")
                lf.flush()
                p = subprocess.Popen(args, cwd=wd, env=env, stdout=lf, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            procs.append((job, label, p, logf))
            if job.engine == "afl":
                wd_watch.register(p.pid, job.rss_limit_mb, label, root / f"{label}.watchdog.log")
            print(f"  {label} [{job.engine}] pid={p.pid} corpus={files}(+{dup}dup) log={logf.name}")

    wd_watch.start()
    t0 = time.time()
    report.live_loop(root, procs, seconds)  # blocks for the budget, tails logs
    wd_watch.stop()
    elapsed = max(1.0, time.time() - t0)

    # AFL does not self-terminate on -max_total_time; stop the whole group.
    for _job, _label, p, _lf in procs:
        if p.poll() is None:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGINT)
            except OSError:
                pass
    time.sleep(2)
    for _job, _label, p, _lf in procs:
        if p.poll() is None:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except OSError:
                pass

    zero = report.write_summary(root, procs, wd_watch, elapsed)
    print(f"fleet done -> {root}  (SUMMARY.md, BASELINE.md, status.json)")
    if zero:
        # Phase 2A: a job with no parseable exec count. With -fork the cumulative
        # `#N` line only appears at a job boundary, so a SLOW target (e.g.
        # fz_decode_modes at max_len=131072 over a large evolved corpus) can be
        # triage-bound for the whole budget and emit none -- it still initialised
        # (banner) and did not crash. So this is a WARNING, not a campaign failure:
        # a genuinely broken harness is caught by the crash-* post-run gate and by
        # `make smoke`'s exit-code detection. Surfaced loudly so it is never missed.
        print(f"WARNING: {len(zero)} job(s) produced no parseable exec count "
              f"(slow/triage-bound under -fork, or a dead harness -- check the log): "
              f"{', '.join(zero)}")
    return 0
