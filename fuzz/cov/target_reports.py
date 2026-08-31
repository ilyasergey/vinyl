#!/usr/bin/env python3
"""Rich per-fuzzer coverage reports, one directory per target (for analysis +
brainstorming how to raise each fuzzer's coverage).

For every target it replays that target's corpus through its `.covfuzz` binary and
writes to  cov/report/targets/<target>/ :

  coverage.txt   llvm-cov region/branch report over Flac/Native/*.c (per file)
  html/          llvm-cov source view with per-branch execution counts -- open
                 html/index.html to SEE which lines/branches are never hit
  uncovered.txt  the actionable worklist: every Native function ranked by how
                 many regions this fuzzer leaves UNCOVERED (biggest first), so
                 "generate inputs that reach these" is obvious
  harness.txt    coverage of fuzz/common|targets -- which oracle branches fire
  INFO.md        headline numbers + the corpus replayed + how to read it

By default it replays the FULL corpus (committed seeds + evolved + this target's
dumped divergences/findings) so the report reflects what the fuzzer actually
achieves. Use --seeds-only for the fast, reproducible committed-corpus number.

Usage:
  python3 cov/target_reports.py                    # all targets, full corpus
  python3 cov/target_reports.py fz_decode_diff     # one target
  python3 cov/target_reports.py --seeds-only       # committed corpus only (fast)
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import per_target as P  # reuse the validated replay + llvm-cov plumbing

C = P.C


def module_of(path: str) -> str:
    p = path.replace("\\", "/")
    return p.split("/ir/", 1)[1] if "/ir/" in p else p


def demangle(sym: str) -> str:
    s = sym
    if s.startswith("lp_vinyl_"):
        s = s[len("lp_vinyl_"):]
    return s


def load_structural_tags() -> dict[str, str]:
    """E2: optional {symbol -> tag} lookup from cov/structural_zero.json so a zero
    row can be annotated `inline-elided | csimp-superseded | boxed-wrapper` and a
    known-false zero is never re-chased. No-crash if the json is absent/stale."""
    p = Path(__file__).resolve().parent / "structural_zero.json"
    if not p.exists():
        return {}
    try:
        doc = json.loads(p.read_text())
    except (json.JSONDecodeError, OSError):
        return {}
    fns = doc.get("functions", {})
    return {k: v.get("tag") for k, v in fns.items()
            if isinstance(v, dict) and v.get("tag")}


def uncovered_worklist(export_doc: dict, dest: Path, tags: dict[str, str] | None = None) -> tuple[int, int]:
    """Rank Native functions by UNCOVERED region count (biggest first). Returns
    (covered_regions, total_regions). Rows are annotated with their structural-zero
    tag (E2) when present."""
    tags = tags or {}
    doc = export_doc["data"][0]
    rows = []
    tot_cov = tot = 0
    for f in doc.get("functions", []):
        regions = f.get("regions", [])
        if not regions:
            continue
        # region tuple: [l0,c0,l1,c1, exec_count, file_id, expanded_id, kind]
        cov = sum(1 for r in regions if r[4] > 0)
        n = len(regions)
        tot_cov += cov
        tot += n
        rows.append((n - cov, n, cov, module_of(f["filenames"][0]) if f.get("filenames") else "?",
                     f["name"]))
    rows.sort(reverse=True)
    lines = ["# Uncovered-region worklist for this fuzzer (Native only).",
             "# columns: UNCOVERED  covered/total  module  function  [structural-zero tag]",
             "# functions this fuzzer never enters (UNCOVERED == total) are the first",
             "# candidates -- craft/seed inputs that reach them to raise coverage.",
             "# a [tag] (from cov/structural_zero.json) marks a codegen/csimp false",
             "# zero -- inline-elided / csimp-superseded / boxed-wrapper: NOT a corpus gap.", ""]
    for unc, n, cov, mod, name in rows:
        if unc == 0:
            continue
        flag = "  <-- never entered" if cov == 0 else ""
        tag = tags.get(name) or tags.get(demangle(name))
        tagstr = f"  [{tag}]" if tag else ""
        lines.append(f"{unc:5d}  {cov:4d}/{n:<4d}  {mod:28s} {demangle(name)}{flag}{tagstr}")
    dest.write_text("\n".join(lines) + "\n")
    return tot_cov, tot


def process_target(n, t, native, harness, root, work, seeds_only, tags) -> str:
    """Replay one target's corpus and write its report dir. Independent of every
    other target (own work subdir + own output dir), so this runs in parallel.
    The full-corpus replay is variant-merged (A4a); --seeds-only stays fast."""
    bin_ = P.BUILD_BIN / f"{n}.covfuzz"
    if not bin_.exists():
        return f"{n:26s} (no .covfuzz -- run make covfuzz)"
    pd, aborts, nfiles = P.replay_target(t, work, seeds_only=seeds_only)
    if not pd:
        return f"{n:26s} (no profile)"
    dest = root / n
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    P.cov_report(bin_, pd, native, dest / "coverage.txt")     # Native region/branch, per file
    P.cov_report(bin_, pd, harness, dest / "harness.txt")     # fuzz/common|targets
    P.cov_html(bin_, pd, native, dest / "html")               # source view w/ branch counts
    ex = P.cov_export(bin_, pd, native)
    uncovered_worklist(ex, dest / "uncovered.txt", tags)      # per-function ranking
    cov, tot = P.region_pct(ex)                               # llvm-cov totals -> matches coverage.txt
    bt = ex["data"][0]["totals"]["branches"]
    pct = 100 * cov / max(1, tot)
    (dest / "INFO.md").write_text(
        f"# {n} coverage report\n\n"
        f"- **region coverage over Flac/Native/*.c: {cov}/{tot} = {pct:.1f}%**\n"
        f"- branch coverage: {bt['covered']}/{bt['count']} = "
        f"{100*bt['covered']/max(1,bt['count']):.1f}%\n"
        f"- input_kind: {t.input_kind};  corpus replayed: "
        f"{'committed seeds only (default variant)' if seeds_only else 'committed + evolved + divergences/findings, ALL variants merged (A4a)'}\n"
        f"- files replayed: {nfiles}"
        + (f";  {len(aborts)} corpus chunk(s) aborted/OOMed a binary (see below)" if aborts else "")
        + "\n\n"
        "## how to read\n"
        "- `html/index.html` -- source view; red = never executed, per-branch counts show which\n"
        "  side of each condition the fuzzer never takes.\n"
        "- `uncovered.txt` -- functions ranked by uncovered regions; the `<-- never entered`\n"
        "  ones are the highest-leverage targets for new seeds/mutations.\n"
        "- `harness.txt` -- coverage of the oracle/harness itself (is the fuzzer stuck in the\n"
        "  codec or in its own machinery?).\n"
        + ("\n## corpus chunks that aborted this binary\n" + "\n".join(aborts) if aborts else ""))
    return f"{n:26s} {pct:8.1f}%  {dest.relative_to(P.FUZZ)}/"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("targets", nargs="*")
    ap.add_argument("--seeds-only", action="store_true")
    ap.add_argument("-j", "--jobs", type=int, default=0,
                    help="parallel targets (default: min(8, cpu/4))")
    args = ap.parse_args()

    all_t = C.discover_targets()
    names = args.targets or sorted(all_t)
    for n in names:
        if n not in all_t:
            sys.exit(f"unknown target {n!r}")

    native = P.native_sources()
    harness = P.harness_sources()
    tags = load_structural_tags()
    root = P.FUZZ / "cov" / "report" / "targets"
    work = P.FUZZ / "cov" / "report" / "_work"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    # Each replay already fans out into chunk subprocesses, so keep the per-target
    # parallelism moderate to avoid oversubscribing the box.
    W = args.jobs or min(8, max(2, (os.cpu_count() or 4) // 4))

    print(f"# Per-fuzzer reports -> {root}/<target>/   "
          f"({'seeds-only' if args.seeds_only else 'FULL corpus'}, {W} parallel)\n")
    print(f"{'target':26s} {'region%':>9s}  reports")
    with ThreadPoolExecutor(max_workers=W) as ex:
        futs = {ex.submit(process_target, n, all_t[n], native, harness, root, work,
                          args.seeds_only, tags): n for n in names}
        for fut in as_completed(futs):
            print(fut.result(), flush=True)
    shutil.rmtree(work, ignore_errors=True)
    print(f"\nAll per-fuzzer reports under {root.relative_to(P.FUZZ)}/  "
          f"(each dir: coverage.txt, html/, uncovered.txt, harness.txt, INFO.md)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
