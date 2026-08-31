"""Live status + SUMMARY.md / BASELINE.md.

Parses libFuzzer stderr (#N ... cov: X ft: Y exec/s: Z rss: R) and AFL
fuzzer_stats, renders a periodic table, and on exit writes SUMMARY.md (execs,
cov, artifacts + divergences by class, watchdog kills) and BASELINE.md (exec/s,
peak cov, peak RSS per label -- the regression reference: a change that halves
exec/s becomes visible instead of folklore).
"""

import json
import re
import subprocess
import time
from pathlib import Path

# libFuzzer stat parsing that tolerates BOTH the plain line
#   `#12345 NEW cov: 900 ft: ... rss: 76Mb`
# and the -fork parent line (no word after `#N:`, exec/s without a colon, NO rss):
#   `#3: cov: 6132 ft: 30666 corp: .. exec/s 292 oom/timeout/crash: 0/0/0 time: 60s job: 3`
# The `#N` counter is CUMULATIVE, so the run total is the MAX seen (never a sum of
# per-worker maxes -- that was the old exec/s+exec inflation, bug 4). exec/s is
# COMPUTED as execs/elapsed_wall, never scraped.
_HASH = re.compile(r"^#(\d+)[:\s]", re.M)
_FINAL = re.compile(r"number_of_executed_units:\s*(\d+)")   # -print_final_stats: authoritative
_COV = re.compile(r"\bcov:\s*(\d+)")
_RSS = re.compile(r"\brss:\s*(\d+)")
# A target's substantive per-run counters are printed as `[tag] key=value ...`
# on stderr (captured in the job/worker logs); this is what actually needs to
# reach SUMMARY.md, not just the libFuzzer exec/cov line.
_TAG = re.compile(r"^\[[a-z0-9_-]+\] .*", re.M)


def write_build_info(root: Path):
    repo = root.parent.parent.parent  # fuzz/runs/<ts> -> repo
    info = {}
    try:
        info["git_rev"] = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"],
                                                   text=True).strip()
    except Exception:
        info["git_rev"] = "unknown"
    tc = repo / "lean-toolchain"
    info["lean_toolchain"] = tc.read_text().strip() if tc.exists() else "unknown"
    # F2: the reference version every differential result came from. The rig LINKS
    # libFLAC built from third_party/flac-src, so the source tree's declared version
    # is authoritative (not whatever `flac` happens to be on PATH). State it so a
    # 1.4.2 result is never silently read as a 1.5.0 one.
    info["libflac_src"] = _libflac_src_version(repo)
    try:
        info["flac_cli"] = subprocess.check_output(["flac", "--version"], text=True).strip()
    except Exception:
        info["flac_cli"] = "unknown"
    (root / "build.info").write_text(json.dumps(info, indent=2))


def _libflac_src_version(repo: Path) -> str:
    """Version from the libFLAC source tree the rig actually compiles and links
    (third_party/flac-src, else ../reference/flac-src), read from its CMake
    project() line -- the same tree mk/toolchain.mk feeds to FLAC_BUILD."""
    for cml in (repo / "fuzz" / "third_party" / "flac-src" / "CMakeLists.txt",
                repo.parent / "reference" / "flac-src" / "CMakeLists.txt"):
        try:
            m = re.search(r"project\(FLAC\s+VERSION\s+([0-9.]+)", cml.read_text())
            if m:
                return m.group(1)
        except OSError:
            continue
    return "unknown"


def _parse_libfuzzer(log: Path, wd: Path, elapsed: float) -> dict:
    """-fork runs one process writing one log with a CUMULATIVE `#N` counter; the
    authoritative final total is `-print_final_stats`' number_of_executed_units.
    exec/s is COMPUTED (execs/elapsed_wall), never scraped -- scraping and summing
    per-worker exec/s inflated md5 to ~962k/s vs a true ~18k/s. cov is the engine's
    internal PC count (NOT source coverage -- see cov/per_target.py for that)."""
    execs = cov = rss = 0
    for lp in [log] + sorted(wd.glob("fuzz-*.log")):
        try:
            txt = lp.read_text(errors="replace")
        except OSError:
            continue
        finals = [int(x) for x in _FINAL.findall(txt)]
        hashes = [int(x) for x in _HASH.findall(txt)]
        e = max(finals) if finals else (max(hashes) if hashes else 0)
        execs = max(execs, e)  # #N cumulative -> MAX across any logs, never a sum
        covs = _COV.findall(txt)
        rsss = _RSS.findall(txt)
        if covs:
            cov = max(cov, max(int(x) for x in covs))
        if rsss:
            rss = max(rss, max(int(x) for x in rsss))
    if not execs and not cov:
        return {}
    return {"execs": execs, "cov": cov, "cov_unit": "pc",
            "exec_s": int(execs / elapsed) if elapsed > 0 else 0, "rss": rss}


def _parse_afl(afl_dir: Path, instance: str) -> dict:
    stats = afl_dir / instance / "fuzzer_stats"
    if not stats.exists():
        return {}
    d = {}
    for line in stats.read_text().splitlines():
        if ":" in line:
            k, _, v = line.partition(":")
            d[k.strip()] = v.strip()
    def _finite_int(v) -> int:
        try:
            f = float(v)
            return int(f) if f == f and f not in (float("inf"), float("-inf")) else 0
        except (ValueError, TypeError):
            return 0
    def _finite_float(v) -> float:
        try:
            f = float(v)
            return f if f == f and f not in (float("inf"), float("-inf")) else 0.0
        except (ValueError, TypeError):
            return 0.0
    # AFL's cov is bitmap_cvg PERCENT (a float, e.g. 5.32) -- a DIFFERENT unit from
    # libFuzzer's PC count. Keep the decimals and label the unit so the two are never
    # silently mixed in one column (bug 2: int(...rstrip('%')) truncated 5.32->5).
    return {"execs": _finite_int(d.get("execs_done", 0)),
            "cov": _finite_float(d.get("bitmap_cvg", "0").rstrip("%")), "cov_unit": "bitmap%",
            "exec_s": _finite_int(d.get("execs_per_sec", 0)),
            "crashes": _finite_int(d.get("saved_crashes", 0))}


def _report_line(log: Path, wd: Path) -> str:
    """The newest `[tag] key=value ...` target-report line across the job log and
    any -jobs worker logs -- the substantive counters (out_of_contract, analyzed,
    sr0_with_audio, fused/fallback, ...) that would otherwise never leave the log."""
    best = ""
    for lp in [log] + sorted(wd.glob("fuzz-*.log")):
        try:
            hits = _TAG.findall(lp.read_text(errors="replace"))
        except OSError:
            continue
        if hits:
            best = hits[-1].strip()
    return best


def _bucket_counters(div: Path) -> dict:
    """Sum witness-config bucket OCCURRENCES across every per-pid counters-*.json
    (Phase 2D). -fork gives each child its own file; this sums them, which the old
    stderr scrape (last line only) could not. These are occurrence counts, NOT bug
    counts -- one defect spans many buckets."""
    totals: dict[str, int] = {}
    for cf in div.glob("counters-*.json"):
        try:
            doc = json.loads(cf.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        for cls, rec in doc.get("buckets", {}).items():
            totals[cls] = totals.get(cls, 0) + int(rec.get("occurrences", 0))
    return totals


def _dump_counts(wd: Path) -> dict:
    out = {}
    div = wd / "divergences"
    if div.is_dir():
        # Authoritative per-class counts come from the summed counters.json
        # occurrences; fall back to counting dumped witness files for any class
        # that has a dump dir but no counter (older runs).
        out.update(_bucket_counters(div))
        for cls in div.iterdir():
            if cls.is_dir() and cls.name not in out:
                out[cls.name] = sum(1 for _ in cls.iterdir())
    arts = wd / "artifacts"
    if arts.is_dir():
        # Split by artifact class: only crash-* is a real crash (SEGV/abort). oom-*
        # and timeout-* are the Lean-runtime cumulative-RSS high-water / slow-input
        # class -- benign and self-restarting, verified non-reproducible per input --
        # so lumping them into "crashes" (as this did) manufactures false findings.
        names = [f.name for f in arts.iterdir()]
        crash = sum(1 for n in names if n.startswith("crash"))
        oom = sum(1 for n in names if n.startswith("oom"))
        tmo = sum(1 for n in names if n.startswith("timeout"))
        if crash:
            out["artifacts"] = crash
        if oom:
            out["oom"] = oom
        if tmo:
            out["timeout"] = tmo
    return out


def _row(job, label, log, root, elapsed: float) -> dict:
    if job.engine == "libfuzzer":
        s = _parse_libfuzzer(log, root / label, elapsed)
    else:
        inst = "main" if label == job.label else label.rsplit(".", 1)[1]
        s = _parse_afl(root / job.label / "afl", inst)
    # AFL parallelizes by -M/-S instances; libFuzzer by -workers. Only AFL
    # should report the instance count.
    s.update({"label": label, "engine": job.engine,
              "workers": job.instances if job.engine == "afl" else job.workers,
              "report_line": _report_line(log, root / label)})
    s.update(_dump_counts(root / label))
    return s


# Keys in a row that are run STATS, not divergence-class dump counts.
_STAT_KEYS = {"execs", "cov", "cov_unit", "exec_s", "rss", "label", "engine", "workers",
              "crashes", "artifacts", "oom", "timeout", "report_line"}


def _div_total(r: dict) -> int:
    return sum(v for k, v in r.items() if k not in _STAT_KEYS)


def _fmt_cov(r: dict) -> str:
    """Engine-INTERNAL coverage with its unit -- libFuzzer PC count (`pc`) vs AFL
    bitmap coverage (`%`). Not source coverage (see cov/per_target.py). Labelling the
    unit stops the two from being read as one comparable number."""
    unit = r.get("cov_unit", "")
    v = r.get("cov", 0)
    if unit == "bitmap%":
        return f"{v:.2f}%"
    if unit == "pc":
        return f"{int(v)}pc"
    return str(v)


def live_loop(root: Path, procs, seconds: int):
    start = time.time()
    while True:
        elapsed = time.time() - start
        rows = [_row(job, label, log, root, elapsed) for job, label, _p, log in procs]
        (root / "status.json").write_text(json.dumps(
            {"elapsed": int(elapsed), "budget": seconds, "jobs": rows}, indent=2))
        print(f"\n[{int(elapsed):>5}s/{seconds}s] "
              f"{'label':<28} {'eng':<4} {'w':>2} {'exec/s':>8} {'cov':>7} "
              f"{'crash':>5} {'oom':>4} {'divs':>5}")
        for r in rows:
            print(f"        {r['label']:<28} {r.get('engine',''):<4} {r.get('workers',0):>2} "
                  f"{r.get('exec_s',0):>8} {r.get('cov',0):>7} "
                  f"{r.get('crashes', r.get('artifacts',0)):>5} {r.get('oom',0):>4} "
                  f"{_div_total(r):>5}")
        alive = any(p.poll() is None for _j, _l, p, _lf in procs)
        if elapsed >= seconds or (seconds > 0 and not alive):
            break
        time.sleep(min(5, max(1, seconds - elapsed)))


def write_summary(root: Path, procs, watchdog, elapsed: float) -> list[str]:
    rows = [_row(job, label, log, root, elapsed) for job, label, _p, log in procs]
    prov = {}
    try:
        prov = json.loads((root / "build.info").read_text())
    except Exception:
        prov = {}
    lines = [f"# Fuzz campaign SUMMARY — {root.name}", "",
             f"- reference: libFLAC {prov.get('libflac_src', '?')} (src) / "
             f"{prov.get('flac_cli', '?')} + ffmpeg libavcodec; "
             f"lean {prov.get('lean_toolchain', '?')}",
             f"- watchdog SIGKILLs: {watchdog.kills}", ""]
    # Every divergence class ANY target dumped this run, so a newer class
    # (wide_output_contract, trailing_reject, par_vs_serial, ...) is never hidden
    # behind three hard-coded columns (bug 3).
    classes = sorted({k for r in rows for k in r if k not in _STAT_KEYS})
    head = ["label", "engine", "workers", "execs", "exec/s", "cov", "crashes", "oom", "timeout",
            *classes]
    lines.append("| " + " | ".join(head) + " |")
    lines.append("|" + "---|" * len(head))
    for r in rows:
        cells = [r["label"], r.get("engine", ""), str(r.get("workers", 0)), str(r.get("execs", 0)),
                 str(r.get("exec_s", 0)), _fmt_cov(r),
                 str(r.get("crashes", r.get("artifacts", 0))),
                 str(r.get("oom", 0)), str(r.get("timeout", 0)), *(str(r.get(c, 0)) for c in classes)]
        lines.append("| " + " | ".join(cells) + " |")

    lines += ["", "_exec/s = execs/elapsed (wall); cov is ENGINE-INTERNAL "
              "(pc=libFuzzer PCs, %=AFL bitmap), NOT source coverage -- see "
              "`make coverage` / cov/per_target.py for region/branch over Flac/Native._"]

    # The substantive per-target counters (the `[tag] key=value` report lines):
    # occurrence RATES, not just the deduped dump-file counts above. Without this a
    # green campaign hides "analyzed=0", "out_of_contract=3", "hdr_clash 40%", etc.
    tagged = [r for r in rows if r.get("report_line")]
    if tagged:
        lines += ["", "## Per-target counters (last report line)", ""]
        for r in tagged:
            lines.append(f"- `{r['label']}`: {r['report_line']}")
    (root / "SUMMARY.md").write_text("\n".join(lines) + "\n")

    base = [f"# BASELINE — {root.name}", "",
            "Regression reference: exec/s and peak RSS per label. A later change",
            "that halves exec/s or blows RSS is visible against this.", "",
            "| label | exec/s | cov | peak_rss_mb |", "|---|---|---|---|"]
    for r in rows:
        base.append(f"| {r['label']} | {r.get('exec_s',0)} | {_fmt_cov(r)} "
                    f"| {watchdog.peak.get(r['label'], r.get('rss',0))} |")
    (root / "BASELINE.md").write_text("\n".join(base) + "\n")

    # Phase 2A: a job that executed 0 inputs is a broken harness/config (crash on
    # the first seed, bad binary) -- surface it so the caller FAILs. But -fork emits
    # its cumulative `#N:` count only at job boundaries, so a SHORT run can legitimately
    # show 0 before the first job completes; only assert this once the run has had real
    # time (a genuine dead harness stays 0 for the whole 1800s campaign) and the target
    # left no witness-config occurrences either (which would prove it did execute).
    return [r["label"] for r in rows
            if r.get("engine") in ("libfuzzer", "afl") and int(r.get("execs", 0)) == 0
            and elapsed > 120 and _div_total(r) == 0]
