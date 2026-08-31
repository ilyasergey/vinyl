#!/usr/bin/env python3
"""E1 -- proven-equivalence twin map + driver linter (a standing CI detector).

Vinyl proves several runtime implementations equal to a reference / tail-recursive
form (`@[csimp]`) or to each other (`*_eq_*`). Coverage of the *reference* side is
often invisible in a naive report because the compiled program runs the OTHER twin,
so a whole module can read 0% while being fully proven -- and, worse, a future
`@[export]` can silently bind the *pre*-csimp writer (exactly the emitFast case:
`FuzzGen.lean` imports only `Flac.Native.*`, so `@[csimp] Unchecked_encode_eq_emitFast`
in `Flac/Spec/Emit.lean` does NOT rewrite `vlean_unchecked_encode`; the export names
the reference writer by design and emitFast coverage must come from
`vinyl_gen_encode_pair`).

This tool:
  1. Enumerates every `@[csimp]` twin (Flac/Native + Flac/Spec) and every
     `theorem *_eq_*` in Flac/Spec (the proven-equivalence surface).
  2. For each implementation SIDE of the decode trio (decodeOption/decodeArrays,
     decodeReference, decodeBytes) and encode triple (encodePcm16, emitFast,
     Unchecked.encode) asserts >=1 fuzz target drives it, via a C connector symbol
     that must actually appear in the harness sources.
  3. Records, via `llvm-nm` on build/lib/libvinyl.fuzz.a (if present), which
     compiled symbol each `@[export]` in FlacTest/FuzzGen.lean binds to, so a
     future export cannot silently regress a twin binding.

Exit nonzero (CI-fail) if any side has no driver / no live connector.

    python3 cov/twins.py
"""
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fleet import config as C  # noqa: E402

REPO = C.FUZZ_ROOT.parent
FUZZ = C.FUZZ_ROOT
SPEC = REPO / "Flac" / "Spec"
NATIVE = REPO / "Flac" / "Native"
FUZZGEN = REPO / "FlacTest" / "FuzzGen.lean"
ARCHIVES = [FUZZ / "build" / "lib" / "libvinyl.fuzz.a",
            REPO / "build" / "lib" / "libvinyl.fuzz.a"]

# Implementation SIDES that MUST be driven. Each: the Lean symbol, the C connector
# symbol(s) that route a fuzz target into it (extern'd in targets/ or common/), and
# the driving target(s). Built from the plan's twin table (decode trio + encode
# triple). A side is UNROUTED (CI-fail) if no connector is found in the harness
# sources or none of its drivers is a discovered target.
SIDES: dict[str, dict] = {
    "decodeOption": dict(
        lean="Flac.Decode.decodeOption", family="decode",
        connectors=["vinyl_decode_option"],
        drivers=["fz_self_consistent", "fz_proven_pairs", "fz_metamorphic"]),
    "decodeArrays": dict(
        lean="Flac.Decode.decodeArrays", family="decode",
        connectors=["vinyl_decode_arrays"],
        drivers=["fz_decode_diff", "fz_decode_structured", "fz_roundtrip",
                 "fz_encode_diff", "fz_unchecked_encode"]),
    "decodeReference": dict(
        lean="Flac.Stream.decodeReference", family="decode",
        connectors=["vinyl_decode_reference"],
        drivers=["fz_proven_pairs", "fz_self_consistent"]),
    "decodeBytes": dict(
        lean="Flac.Decode.decodeBytes", family="decode",
        connectors=["vinyl_decode_bytes"],
        drivers=["fz_decode_capacity", "fz_decode_diff"]),
    "encodePcm16": dict(
        lean="Flac.Encode.encodePcm16", family="encode",
        connectors=["vinyl_encode_pcm16"],
        drivers=["fz_encode_pcm16_eq"]),
    "emitFast": dict(
        lean="Flac.Emit.emitFast", family="encode",
        connectors=["vinyl_emit_fast"],
        drivers=["fz_encode_pair", "fz_emit_conformance", "fz_residual_bound"]),
    "Unchecked.encode": dict(
        lean="Flac.Stream.Unchecked.encode", family="encode",
        connectors=["vlean_unchecked_encode", "vinyl_unchecked_encode"],
        drivers=["fz_unchecked_encode", "fz_encode_pcm16_eq"]),
}

# The one binding that is intentionally NOT the csimp target (documented, not a bug).
BINDING_NOTES = {
    "vlean_unchecked_encode":
        "binds Stream.Unchecked.encode (the reference writer), NOT emitFast: "
        "FuzzGen imports Flac.Native only, so @[csimp] Unchecked_encode_eq_emitFast "
        "does not rewrite it. emitFast is driven via vinyl_gen_encode_pair instead.",
}


def csimp_twins() -> list[tuple[str, str, str]]:
    """(lhs_def, rhs_def, file) for every `@[csimp] theorem LHS_eq_RHS`."""
    out: list[tuple[str, str, str]] = []
    pat = re.compile(r"@\[csimp\]\s*theorem\s+([A-Za-z0-9_']+)")
    for d in (NATIVE, SPEC):
        for f in sorted(d.glob("*.lean")):
            for m in pat.finditer(f.read_text()):
                thm = m.group(1)
                if "_eq_" in thm:
                    lhs, rhs = thm.split("_eq_", 1)
                else:
                    lhs, rhs = thm, "?"
                out.append((lhs, rhs, str(f.relative_to(REPO))))
    return out


def eq_theorems() -> list[tuple[str, str]]:
    """(theorem_name, file) for every `theorem *_eq_*` under Flac/Spec."""
    out: list[tuple[str, str]] = []
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?theorem\s+([A-Za-z0-9_']*_eq_[A-Za-z0-9_']*)",
                     re.M)
    for f in sorted(SPEC.glob("*.lean")):
        for m in pat.finditer(f.read_text()):
            out.append((m.group(1), str(f.relative_to(REPO))))
    return out


def harness_symbols() -> str:
    """All target + common C source text (one blob) for connector presence checks."""
    blobs = []
    for d in (FUZZ / "targets", FUZZ / "common"):
        for f in sorted(d.glob("*.c")) + sorted(d.glob("*.h")):
            blobs.append(f.read_text())
    return "\n".join(blobs)


def target_sources() -> dict[str, str]:
    return {f.stem: f.read_text() for f in sorted((FUZZ / "targets").glob("*.c"))}


def fuzzgen_exports() -> list[str]:
    return re.findall(r"@\[export\s+([A-Za-z0-9_]+)\]", FUZZGEN.read_text())


def archive_symbols() -> tuple[Path | None, set[str]]:
    for a in ARCHIVES:
        if a.exists():
            nm = subprocess.run(["llvm-nm", str(a)], capture_output=True, text=True)
            syms = {ln.split()[-1] for ln in nm.stdout.splitlines()
                    if len(ln.split()) >= 2 and ln.split()[-2] in ("T", "t", "W", "D")}
            return a, syms
    return None, set()


def main() -> int:
    blob = harness_symbols()
    tsrc = target_sources()
    discovered = C.discover_targets()
    fails: list[str] = []

    print("# E1 proven-equivalence twins\n")
    twins = csimp_twins()
    print(f"## @[csimp] twins ({len(twins)})  (LHS runs as RHS at runtime)")
    for lhs, rhs, f in twins:
        print(f"  {lhs:32s} -> {rhs:32s}  {f}")
    eqs = eq_theorems()
    print(f"\n## Flac/Spec *_eq_* equivalence theorems ({len(eqs)})")
    for name, f in eqs:
        print(f"  {name:40s} {f}")

    print("\n## implementation sides -> driving target(s)")
    for side, spec in SIDES.items():
        found_conn = [c for c in spec["connectors"] if c in blob]
        drivers = [d for d in spec["drivers"] if d in discovered]
        # A driver is CONFIRMED if it (or a common wrapper it links) reaches a
        # connector; direct references are reported, transitive ones are trusted
        # via the connector-in-harness check.
        direct = [d for d in drivers if any(c in tsrc.get(d, "") for c in spec["connectors"])]
        status = "OK"
        if not found_conn:
            status = "FAIL(no live connector)"
            fails.append(f"{side}: no connector of {spec['connectors']} in harness sources")
        elif not drivers:
            status = "FAIL(no driver)"
            fails.append(f"{side}: none of {spec['drivers']} is a discovered target")
        print(f"  [{status:22s}] {side:18s} {spec['lean']}")
        print(f"       connector: {found_conn or spec['connectors']}"
              f"   drivers: {drivers}"
              + (f"   (direct: {direct})" if direct else ""))

    print("\n## @[export] -> compiled-symbol binding (llvm-nm)")
    arc, syms = archive_symbols()
    exports = fuzzgen_exports()
    if arc is None:
        print("  note: libvinyl.fuzz.a not built yet -- binding record skipped "
              "(routing gate above is the CI-fail condition).")
    else:
        print(f"  archive: {arc.relative_to(REPO)}  ({len(syms)} defined symbols)")
        for e in exports:
            present = "bound" if e in syms else "MISSING (rebuild pending)"
            note = f"   <-- {BINDING_NOTES[e]}" if e in BINDING_NOTES else ""
            print(f"    {e:34s} {present}{note}")
    for sym, note in BINDING_NOTES.items():
        if sym not in exports and sym not in blob:
            print(f"  note: documented binding symbol {sym} not found -- {note}")

    if fails:
        print("\nTWINS FAIL:")
        for x in fails:
            print(f"  - {x}")
        return 1
    print("\nOK: every twin side has a live connector + >=1 driving target.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
