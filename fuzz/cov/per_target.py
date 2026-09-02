#!/usr/bin/env python3
"""Per-target source-based coverage for the Vinyl fuzz fleet (Phase 1).

Replays each target's corpus through its coverage-instrumented SIBLING binary
(build/bin/<t>.covfuzz -- a real libFuzzer binary built with -fprofile-instr-generate
-fcoverage-mapping, so instrumentation-changed codegen is measured on a sibling of
the exact target, not on a separate hand-written driver), merges the profile with
llvm-profdata, and reports region+branch coverage.

HEADLINE metric = raw `llvm-cov report` region/branch total over
.lake/build/ir/Flac/Native/*.c, exactly as the tool prints it -- NO curated
denominator, NO dead-code subtraction. Anyone reproduces it in one command; that
is the whole point after the old 213/888 bespoke-denominator problem.

Products (cov/report/<stamp>/):
  <t>.native.txt      per-target region/branch over Flac/Native/*.c
  html/<t>/           per-target HTML with branch counts ("where is it stuck")
  <t>.harness.txt     SECOND report scoped TO fuzz/common|targets (which oracle
                      branches never fire -- is the fuzzer stuck in the codec or
                      in its own machinery?)
  union.native.txt    fleet-union region/branch (all targets' profiles merged)
  contribution.txt    regions a target covers that the union-of-others does not
                      ("is this job earning its cores"; fz_md5/fz_float_exact ~0)
  aborts.txt          per target, the corpus chunks that abort/OOM the binary
                      (a deliverable the old rig could not produce)
  structural.txt      the union re-read through cov/structural_zero.json: how many
                      regions belong to functions that can never execute (ABI thunks,
                      csimp pre-swap, inline-elided, closures, derived instances,
                      module init) and the EFFECTIVE coverage over the live remainder

Coverage comes from .covfuzz binaries ONLY. Divergence verdicts NEVER do.

Usage:
  python3 cov/per_target.py                 # all targets, configured+evolved corpora
  python3 cov/per_target.py fz_decode_diff  # one target
  python3 cov/per_target.py --contribution  # + the contribution matrix (slower)
  python3 cov/per_target.py --delta         # + seed->evolved region delta per target
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fleet import config as C  # noqa: E402

FUZZ = C.FUZZ_ROOT
BUILD_BIN = C.BUILD_BIN
IR_NATIVE = C.FUZZ_ROOT.parent / ".lake" / "build" / "ir" / "Flac" / "Native"
CHUNK = 200          # symlink files per replay chunk (survive an aborting unit)
MAX_LEN = 4194304    # 4 MiB: do not truncate the 157 KB IETF vector or larger seeds
RSS_MB = 8000        # a decode bomb must not OOM the host; the replay is not a cgroup job


def tool(name: str) -> str:
    exe = shutil.which(name)
    if not exe:
        sys.exit(f"error: {name} not on PATH (llvm-14 tools needed; version must match clang-14)")
    return exe


def native_sources() -> list[str]:
    """The unadjusted denominator: every Native/*.c file, exactly as on disk."""
    files = sorted(str(p) for p in IR_NATIVE.glob("*.c"))
    if not files:
        sys.exit(f"error: no Native IR under {IR_NATIVE} -- run `lake build` / `make lean-ir`")
    return files


def harness_sources() -> list[str]:
    return sorted(str(p) for p in (FUZZ / "common").glob("*.c")) + \
           sorted(str(p) for p in (FUZZ / "targets").glob("*.c"))


# A class dir can hold hundreds of thousands of near-duplicate reproducers (the
# pre-Phase-2C uncapped dumps: one class hit 517k files in a single run). Replaying
# them all costs hours and adds ~0 unique coverage, so the divergence contribution
# is SAMPLED: at most DIV_PER_CLASS files per class dir (scandir + early break, so a
# 500k-file dir is never fully listed) and DIV_CAP files total per target.
DIV_PER_CLASS = 40
DIV_CAP = 1200


def divergence_sample(t: C.Target) -> list[Path]:
    """A bounded, cheap sample of dumped divergences (coverage-interesting inputs the
    live corpus does not retain). Every file in a class is near-identical for coverage,
    so a small per-class sample captures its coverage without walking the whole dir."""
    if t.input_kind != "flac_stream":
        return []
    out: list[Path] = []
    import os
    for cls_dir in sorted((FUZZ / "runs").glob(f"*/{t.name}*/divergences/*")):
        if not cls_dir.is_dir():
            continue
        taken = 0
        try:
            with os.scandir(cls_dir) as it:
                for e in it:
                    if e.is_file(follow_symlinks=False):
                        out.append(Path(e.path))
                        taken += 1
                        if taken >= DIV_PER_CLASS:
                            break  # early break: never list a 500k-file class dir
        except OSError:
            continue
        if len(out) >= DIV_CAP:
            break
    return out[:DIV_CAP]


def replay_dirs(t: C.Target, seeds_only: bool = False) -> list[Path]:
    """Corpus DIRS to replay in full: the configured corpus, the distilled evolved
    corpus, and -- for FLAC-stream decoders -- the must-reject seeds, filed findings,
    and AFL queues. Dumped divergences are NOT here (they can be millions of
    near-duplicate files); a bounded sample is added separately via divergence_sample().
    seeds_only restricts to the committed configured corpus (a deterministic,
    reproducible number for the CI gate; evolved/divergences are not committed)."""
    cfg = C.resolve(t, "default")
    dirs: list[Path] = []
    for entry in cfg["corpus"]:
        d = C.CORPUS_DIR / entry
        if d.is_dir():
            dirs.append(d)
    if seeds_only:
        return dirs
    evolved = C.CORPUS_DIR / t.name / "evolved"
    if evolved.is_dir():
        dirs.append(evolved)
    if t.input_kind == "flac_stream":
        mr = C.CORPUS_DIR / "decode" / "must_reject"
        if mr.is_dir():
            dirs.append(mr)
        for label_glob in (t.name, f"{t.name}.*"):
            for q in (FUZZ / "runs").glob(f"*/{label_glob}/afl/*/queue"):
                dirs.append(q)
        fd = FUZZ / "findings"
        if fd.is_dir():
            dirs.append(fd)
    return dirs


def gather_files(dirs: list[Path]) -> list[Path]:
    seen: set[bytes] = set()  # dedupe by content hash is overkill here; dedupe by path
    files: list[Path] = []
    for d in dirs:
        for p in d.rglob("*"):
            if p.is_file() and p.stat().st_size > 0:
                key = p.resolve().as_posix().encode()
                if key not in seen:
                    seen.add(key)
                    files.append(p)
    return files


def _replay_to_profraw(bin_: Path, label: str, files: list[Path], profdir: Path,
                       extra_env: dict[str, str] | None = None) -> list[str]:
    """Chunked symlink replay: ~CHUNK files per process, each chunk its own profraw
    written into `profdir` (NOT merged here). A chunk whose binary aborts loses only
    that chunk (13 oracle sites abort even at FUZZ_STRICT=0); its files are recorded
    in the returned `aborts`. `extra_env` (a variant's `env`) is merged over the base
    replay env so VM_FORCE_PAR=1 / LEAN_NUM_THREADS=4 / VM_REENC_LANE actually take
    effect and the par-forced/edge lanes get measured (A4a)."""
    profdir.mkdir(parents=True, exist_ok=True)
    work = profdir / "_work"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir()
    aborts: list[str] = []
    env = dict(os.environ, LEAN_NUM_THREADS="1", FUZZ_STRICT="0")
    if extra_env:
        env.update({k: str(v) for k, v in extra_env.items()})
    for ci, start in enumerate(range(0, len(files), CHUNK)):
        chunk = files[start:start + CHUNK]
        cdir = work / f"c{ci:04d}"
        cdir.mkdir()
        for i, f in enumerate(chunk):
            try:
                (cdir / f"{i:04d}_{f.name}"[:200]).symlink_to(f.resolve())
            except OSError:
                pass
        env["LLVM_PROFILE_FILE"] = str(profdir / f"c{ci:04d}-%p.profraw")
        r = subprocess.run([str(bin_), "-runs=0", f"-max_len={MAX_LEN}",
                            f"-rss_limit_mb={RSS_MB}", "-detect_leaks=0", str(cdir)],
                           env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if r.returncode != 0:
            aborts.append(f"{label} chunk c{ci:04d} rc={r.returncode}: "
                          + ", ".join(f.as_posix() for f in chunk[:8])
                          + (" ..." if len(chunk) > 8 else ""))
    shutil.rmtree(work, ignore_errors=True)
    return aborts


def replay(target: str, files: list[Path], out: Path, bin_name: str | None = None) -> tuple[Path, list[str]]:
    """Single-lane replay (default env) -> (merged_profdata, aborts). Kept for the
    seeds-only CI path and the seed->evolved delta. `target` is the profile label;
    `bin_name` (default = target) selects the binary."""
    bin_ = BUILD_BIN / f"{bin_name or target}.covfuzz"
    if not bin_.exists():
        sys.exit(f"error: {bin_} missing -- run `make covfuzz`")
    profdir = out / "profraw" / target
    if profdir.exists():
        shutil.rmtree(profdir)
    aborts = _replay_to_profraw(bin_, target, files, profdir)
    raws = sorted(profdir.glob("*.profraw"))
    if not raws:
        return (Path(), aborts)
    pd = out / f"{target}.profdata"
    subprocess.run([tool("llvm-profdata"), "merge", "-sparse", *map(str, raws), "-o", str(pd)],
                   check=True)
    shutil.rmtree(profdir, ignore_errors=True)
    return (pd, aborts)


def replay_target(t: C.Target, out: Path, seeds_only: bool = False) -> tuple[Path, list[str], int]:
    """A4a variant-merged coverage. For the FULL corpus, replay EVERY variant
    (`default` + each named variant) through THAT variant's resolved `env`, then
    merge all variants' `.profraw` into ONE profdata so the per-target report
    reflects the whole campaign shape -- the par-forced/edge/small lanes are
    measured and the `vm_force_par_stable` false zero disappears. `--seeds-only`
    stays default-variant-only (unchanged, reproducible CI number). The bounded
    divergence sample and target-level extras (evolved/must_reject/AFL/findings)
    ride the `default` lane only, so the existing divergence sampling is preserved
    and not re-run per variant. Returns (profdata, aborts, files_replayed)."""
    n = t.name
    if seeds_only:
        files = gather_files(replay_dirs(t, seeds_only=True))
        pd, aborts = replay(n, files, out)
        return (pd, aborts, len(files))
    bin_ = BUILD_BIN / f"{n}.covfuzz"
    if not bin_.exists():
        sys.exit(f"error: {bin_} missing -- run `make covfuzz`")
    profbase = out / "profraw" / n
    if profbase.exists():
        shutil.rmtree(profbase)
    aborts: list[str] = []
    total = 0
    for v in ("default", *t.variants):
        cfg = C.resolve(t, v)
        if v == "default":
            files = gather_files(replay_dirs(t, seeds_only=False)) + divergence_sample(t)
        else:
            dirs = [C.CORPUS_DIR / e for e in cfg["corpus"] if (C.CORPUS_DIR / e).is_dir()]
            files = gather_files(dirs)
        if not files:
            continue
        total += len(files)
        aborts += _replay_to_profraw(bin_, f"{n}.{v}", files, profbase / v, cfg["env"])
    raws = sorted(profbase.rglob("*.profraw"))
    if not raws:
        return (Path(), aborts, total)
    pd = out / f"{n}.profdata"
    subprocess.run([tool("llvm-profdata"), "merge", "-sparse", *map(str, raws), "-o", str(pd)],
                   check=True)
    shutil.rmtree(profbase, ignore_errors=True)
    return (pd, aborts, total)


def region_pct(export_json: dict) -> tuple[int, int]:
    """(covered_regions, total_regions) from an llvm-cov export doc."""
    tot = export_json["data"][0]["totals"]["regions"]
    return (tot["covered"], tot["count"])


def cov_report(bin_: Path, pd: Path, sources: list[str], dest: Path) -> None:
    txt = subprocess.run([tool("llvm-cov"), "report", str(bin_), f"-instr-profile={pd}", *sources],
                         check=True, capture_output=True, text=True).stdout
    dest.write_text(txt)


def cov_export(bin_: Path, pd: Path, sources: list[str]) -> dict:
    js = subprocess.run([tool("llvm-cov"), "export", str(bin_), f"-instr-profile={pd}",
                         "--format=text", *sources],
                        check=True, capture_output=True, text=True).stdout
    return json.loads(js)


def cov_html(bin_: Path, pd: Path, sources: list[str], outdir: Path) -> None:
    subprocess.run([tool("llvm-cov"), "show", str(bin_), f"-instr-profile={pd}",
                    "-format=html", "-show-branches=count", "-show-line-counts-or-regions",
                    f"-output-dir={outdir}", *sources],
                   check=True, stdout=subprocess.DEVNULL)


def structural_summary(rep: Path, union: Path, native: list[str], out: Path) -> None:
    """Honest-denominator view of the union: attribute every Native function's regions to
    its cov/structural_zero.json tag. Functions tagged anything but `has-standalone-body`
    can NEVER execute their standalone body (ABI thunks, csimp pre-swap originals,
    @[inline]-elided copies, match closures, derived instances, module init), so they are
    excluded from BOTH numerator and denominator of the `effective` figure. Uses
    `llvm-cov report -show-functions` per file, whose rows reconcile exactly to the
    file TOTALs (the per-function `export` does not). Writes structural.txt."""
    sz = FUZZ / "cov" / "structural_zero.json"
    if not sz.exists():
        return
    tags = {k: v.get("tag", "has-standalone-body")
            for k, v in json.loads(sz.read_text()).get("functions", {}).items()}
    tot = miss = dead_tot = dead_miss = 0
    by_tag: dict[str, list[int]] = {}
    for src in native:
        rep_txt = subprocess.run([tool("llvm-cov"), "report", str(rep), f"-instr-profile={union}", src,
                                  "-show-functions"], capture_output=True, text=True).stdout
        for line in rep_txt.splitlines():
            p = line.split()
            if len(p) < 4 or not p[1].isdigit() or p[0] == "TOTAL":
                continue
            name = p[0].split(":", 1)[-1]
            n, m = int(p[1]), int(p[2])
            tag = tags.get(name, "has-standalone-body")
            tot += n
            miss += m
            b = by_tag.setdefault(tag, [0, 0])
            b[0] += n
            b[1] += m
            if tag != "has-standalone-body":
                dead_tot += n
                dead_miss += m
    if not tot:
        return
    live_tot, live_cov = tot - dead_tot, (tot - miss) - (dead_tot - dead_miss)
    lines = [f"# Structural (honest-denominator) view of the fleet union over Flac/Native/*.c",
             f"# raw:       {tot - miss}/{tot} regions covered = {100 * (tot - miss) / tot:.1f}%  (the llvm-cov headline)",
             f"# dead-by-design (structural_zero tag != has-standalone-body): {dead_tot} regions "
             f"({dead_miss} missed) = {100 * dead_tot / tot:.1f}% of all regions, can never execute",
             f"# effective: {live_cov}/{live_tot} = {100 * live_cov / max(1, live_tot):.1f}%  "
             f"(coverage of functions that ARE genuine coverage targets)", "",
             f"{'tag':22s} {'regions':>8s} {'missed':>7s} {'% of missed':>11s}"]
    for tag, (n, m) in sorted(by_tag.items(), key=lambda kv: -kv[1][1]):
        lines.append(f"{tag:22s} {n:8d} {m:7d} {100 * m / max(1, miss):10.1f}%")
    (out / "structural.txt").write_text("\n".join(lines) + "\n")
    print(f"{'EFFECTIVE (live fns)':28s} {live_cov:>7d}/{live_tot:<7d}{100 * live_cov / max(1, live_tot):5.1f}%  "
          f"(dead-by-design excluded: {dead_tot} regions; see structural.txt)")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("targets", nargs="*", help="targets to measure (default: all)")
    ap.add_argument("--contribution", action="store_true",
                    help="also compute each target's unique region contribution")
    ap.add_argument("--delta", action="store_true",
                    help="also compute seed->evolved region delta per target")
    ap.add_argument("--seeds-only", action="store_true",
                    help="replay only committed configured corpora (reproducible CI number)")
    ap.add_argument("--outdir", default=None)
    args = ap.parse_args()

    all_targets = C.discover_targets()
    names = args.targets or sorted(all_targets)
    for n in names:
        if n not in all_targets:
            sys.exit(f"error: unknown target {n!r}")

    out = Path(args.outdir) if args.outdir else FUZZ / "cov" / "report" / "latest"
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    native = native_sources()
    harness = harness_sources()

    profdata: dict[str, Path] = {}
    all_aborts: list[str] = []
    summary: dict[str, dict] = {}
    print(f"# Per-target coverage over {len(native)} Native/*.c files (raw llvm-cov denominator)"
          f"{'  [seeds-only]' if args.seeds_only else ''}\n")
    print(f"{'target':28s} {'regions':>16s} {'branches':>16s}")
    for n in names:
        t = all_targets[n]
        bin_ = BUILD_BIN / f"{n}.covfuzz"
        pd, aborts, _ = replay_target(t, out, seeds_only=args.seeds_only)
        all_aborts += aborts
        if not pd:
            print(f"{n:28s} {'(no profile)':>16s}")
            continue
        profdata[n] = pd
        cov_report(bin_, pd, native, out / f"{n}.native.txt")
        cov_report(bin_, pd, harness, out / f"{n}.harness.txt")
        cov_html(bin_, pd, native, out / "html" / n)
        ex = cov_export(bin_, pd, native)
        rc, rt = region_pct(ex)
        bt = ex["data"][0]["totals"]["branches"]
        summary[n] = dict(regions_covered=rc, regions_total=rt,
                          branches_covered=bt["covered"], branches_total=bt["count"])
        print(f"{n:28s} {rc:>7d}/{rt:<7d}{100*rc/rt:5.1f}% "
              f"{bt['covered']:>7d}/{bt['count']:<7d}{100*bt['covered']/max(1,bt['count']):5.1f}%")

    # ---- fleet union: merge every target's profdata, report over Native with all objects.
    if len(profdata) > 1:
        union = out / "union.profdata"
        subprocess.run([tool("llvm-profdata"), "merge", "-sparse",
                        *map(str, profdata.values()), "-o", str(union)], check=True)
        # Every .covfuzz binary links the IDENTICAL libvinyl.covfuzz.a, so the Native
        # functions have the same name+coverage-mapping hash in all of them and the
        # merged (summed) counts apply through ANY single object. Using one object
        # (not -object per target) avoids the harness-symbol hash-mismatch error that
        # multi-object reporting raises when the differing target/harness records meet.
        rep = BUILD_BIN / f"{list(profdata)[0]}.covfuzz"
        txt = subprocess.run([tool("llvm-cov"), "report", str(rep), f"-instr-profile={union}", *native],
                             check=True, capture_output=True, text=True).stdout
        (out / "union.native.txt").write_text(txt)
        ex = cov_export(rep, union, native)
        rc, rt = region_pct(ex)
        summary["__union__"] = dict(regions_covered=rc, regions_total=rt)
        print(f"\n{'FLEET UNION':28s} {rc:>7d}/{rt:<7d}{100*rc/rt:5.1f}%  (headline native region coverage)")
        structural_summary(rep, union, native, out)

    (out / "summary.json").write_text(json.dumps(
        dict(seeds_only=args.seeds_only, targets=summary), indent=2))

    # ---- contribution: regions a target covers that the union-of-all-OTHERS does not.
    # "Is this job earning its cores?" fz_md5 / fz_float_exact are predicted ~0.
    if args.contribution and len(profdata) > 1:
        rep = BUILD_BIN / f"{list(profdata)[0]}.covfuzz"

        def covered_of(pds: list[Path]) -> int:
            m = out / "_contrib.profdata"
            subprocess.run([tool("llvm-profdata"), "merge", "-sparse", *map(str, pds), "-o", str(m)],
                           check=True)
            return region_pct(cov_export(rep, m, native))[0]

        total = covered_of(list(profdata.values()))
        rows = []
        for n in profdata:
            others = [pd for k, pd in profdata.items() if k != n]
            rows.append((n, total - covered_of(others)))
        rows.sort(key=lambda r: -r[1])
        body = f"# unique region contribution vs union-of-others (fleet total covered = {total})\n"
        body += "".join(f"  {n:28s} +{u}\n" for n, u in rows)
        (out / "contribution.txt").write_text(body)
        print("\n# contribution (unique regions vs union-of-others)")
        for n, u in rows:
            print(f"  {n:28s} +{u}")

    # ---- delta: did fuzzing buy coverage? committed seeds vs seeds+evolved, per target.
    if args.delta:
        print("\n# seed->evolved region delta (committed seeds vs +evolved)")
        rows = []
        for n in names:
            if n not in profdata:
                continue
            t = all_targets[n]
            seed_dirs = [C.CORPUS_DIR / e for e in C.resolve(t, "default")["corpus"]
                         if (C.CORPUS_DIR / e).is_dir()]
            seed_files = gather_files(seed_dirs)
            spd, _ = replay(f"{n}__seed", seed_files, out, bin_name=n)
            grown = region_pct(cov_export(BUILD_BIN / f"{n}.covfuzz", profdata[n], native))[0]
            seed = region_pct(cov_export(BUILD_BIN / f"{n}.covfuzz", spd, native))[0] if spd else 0
            rows.append((n, seed, grown))
            print(f"  {n:28s} seed {seed:>5d} -> grown {grown:>5d}  (+{grown - seed})")
        (out / "delta.txt").write_text(
            "# committed-seed vs seed+evolved covered regions over Native\n"
            + "".join(f"  {n:28s} {s} -> {g}  (+{g - s})\n" for n, s, g in rows))

    if all_aborts:
        (out / "aborts.txt").write_text("\n".join(all_aborts) + "\n")
        print(f"\n{len(all_aborts)} corpus chunk(s) aborted/OOMed a binary -- see {out/'aborts.txt'}")

    print(f"\nreports in {out}/  (html/<t>/index.html for branch-count drilldown)")
    print("headline = union.native.txt TOTAL region% ; harness = <t>.harness.txt")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
