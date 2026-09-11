#!/usr/bin/env python3
"""E1 -- proven-equivalence twin map + driver linter (a standing CI detector).

Vinyl proves several runtime implementations equal to a reference / tail-recursive
form (`@[csimp]`) or to each other (`*_eq_*`). Coverage of the *reference* side is
often invisible in a naive report because the compiled program runs the OTHER twin,
so a whole module can read 0% while being fully proven -- and, worse, a future
`@[export]` can silently bind the *post*-csimp writer (exactly the emitFast case:
`vlean_unchecked_encode` must name the reference writer, so it lives in
`FlacTest/FuzzRef.lean`, which imports `Flac.Native.Stream` alone and therefore
never sees `@[csimp] Unchecked_encode_eq_emitFast` from `Flac/Spec/Emit.lean`.
It used to live in `FuzzGen.lean`, and did alias once `Flac/Native/Codec.lean`
started importing that swap for the shipped entry points. emitFast coverage comes
from `vinyl_gen_encode_pair`).

This tool:
  1. Enumerates every `@[csimp]` twin (Flac/Native + Flac/Spec) and every
     `theorem *_eq_*` in Flac/Spec (the proven-equivalence surface).
  2. For each implementation SIDE of the decode trio (decodeOption/decodeArrays,
     decodeReference, decodeBytes) and encode triple (encodePcm16, emitFast,
     Unchecked.encode) asserts >=1 fuzz target drives it, via a C connector symbol
     that must actually appear in the harness sources.
  3. Records, via `llvm-nm` on build/lib/libvinyl.fuzz.a (if present), which
     compiled symbol each `@[export]` in FlacTest/Fuzz*.lean binds to, so a
     future export cannot silently regress a twin binding.
  4. Parses the compiled IR (.lake/build/ir/FlacTest/Fuzz*.c) and, for each
     twin PAIR whose two sides are BOTH exported to C (only pair #13,
     Unchecked.encode vs emitFast), asserts the two `@[export]` wrappers tail-call
     DISTINCT `lp_vinyl_*` callees. This is the encode-side TCB oracle guard: if a
     future import pulled `@[csimp] Unchecked_encode_eq_emitFast` into the
     exporting module's scope, the reference writer would silently alias to
     emitFast, `fz_encode_pair` would compare emitFast to itself, and every green
     run would be a false negative. That has happened once already.

Exit nonzero (CI-fail) if any side has no driver / no live connector, or if a
must-be-distinct twin pair aliases to a single compiled callee.

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
# The harness exports are spread across FlacTest modules, not one file: an export
# whose callee must NOT be rewritten by a `@[csimp]` has to live in a module that
# does not import the swap, so `vlean_unchecked_encode` sits in FuzzRef.lean while
# the rest are in FuzzGen.lean. Scan the directory, not a single file, or moving an
# export to fix an aliasing failure looks like the export disappearing.
FUZZGEN_SRCS = sorted((REPO / "FlacTest").glob("Fuzz*.lean"))
FUZZGEN_IRS = sorted((REPO / ".lake" / "build" / "ir" / "FlacTest").glob("Fuzz*.c"))
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
        "FuzzRef.lean imports Flac.Native.Stream alone, so @[csimp] Unchecked_encode_eq_emitFast "
        "does not rewrite it. emitFast is driven via vinyl_gen_encode_pair instead.",
}

# @[export] wrapper PAIRS that MUST compile to DISTINCT lp_vinyl_* callees -- the
# encode-side TCB oracle guard. Of the csimp twins only pair #13 (Unchecked.encode
# vs emitFast) has BOTH sides exported to C, so it is the only pair a compiled-IR
# disjointness check can (and must) police: the proven-pair targets fz_encode_pair /
# fz_unchecked_encode are meaningful ONLY because the reference writer and emitFast
# are two DISTINCT compiled programs. FuzzGen imports Flac.Native.* only, so
# @[csimp] Unchecked_encode_eq_emitFast (Flac/Spec/Emit.lean) is out of scope and the
# exports do not alias. Should someone `import Flac` FuzzGen -- or move that csimp
# into a Native module -- both wrappers would tail-call lp_vinyl_Flac_Emit_W_encode,
# the target would compare emitFast to itself, and every green run would be a silent
# false negative that no build/nm/routing gate can see. Each entry:
# (export_a, expected_callee_a, export_b, expected_callee_b, why).
DISTINCT_EXPORT_PAIRS: list[tuple[str, str, str, str, str]] = [
    ("vlean_unchecked_encode", "lp_vinyl_Flac_Stream_Unchecked_encode",
     "vinyl_emit_fast", "lp_vinyl_Flac_Emit_W_encode",
     "pair #13: reference writer vs emitFast -- both reachable from C; aliasing "
     "makes fz_encode_pair/fz_unchecked_encode compare emitFast to itself forever."),
]


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
    out: list[str] = []
    for src in FUZZGEN_SRCS:
        out += re.findall(r"@\[export\s+([A-Za-z0-9_]+)\]", src.read_text())
    return out


def fuzzgen_ir_callees() -> dict[str, set[str]]:
    """{function -> set of lp_vinyl_* callees} from the compiled FlacTest/Fuzz*.c IR.

    Each `@[export]` becomes a `LEAN_EXPORT lean_object* NAME(...){ ... }` DEFINITION
    (the bare `);` forward declarations at the top of the file carry no body and are
    skipped) whose tiny body tail-calls the one lp_vinyl_* mangled symbol the export
    actually binds. The body is delimited by brace matching so the callee set is exact
    regardless of the wrapper's shape. Returns {} if the IR has not been built.
    """
    if not FUZZGEN_IRS:
        return {}
    text = "\n".join(p.read_text() for p in FUZZGEN_IRS)
    header = re.compile(r"^LEAN_EXPORT\s+lean_object\*\s+([A-Za-z0-9_]+)\s*\([^;{]*\)\s*\{",
                        re.M)
    callee = re.compile(r"\blp_vinyl_[A-Za-z0-9_]+")
    out: dict[str, set[str]] = {}
    for m in header.finditer(text):
        brace = m.end() - 1  # position of the body's opening '{'
        depth = 0
        i = brace
        while i < len(text):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        out[m.group(1)] = set(callee.findall(text[brace + 1:i]))
    return out


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

    print("\n## @[export] wrapper callee-disjointness (IR: .lake/.../FlacTest/Fuzz*.c)")
    callees = fuzzgen_ir_callees()
    if not callees:
        # Both callers (scripts/check.sh and fuzz/scripts/ci.sh) build before this
        # runs, so the FlacTest/Fuzz*.c IR is present whenever the check is meant to
        # mean anything. An absent IR here is not a benign "not built yet" -- silently
        # skipping the disjointness gate is exactly the blind spot that once let the
        # reference writer alias to emitFast. Fail rather than skip.
        msg = ("FlacTest/Fuzz*.c IR absent -- callee-disjointness gate could not run; "
               "run `lake build` before this check")
        print(f"  FAIL(no IR): {msg}")
        fails.append(msg)
    else:
        for exp_a, want_a, exp_b, want_b, why in DISTINCT_EXPORT_PAIRS:
            ca, cb = callees.get(exp_a), callees.get(exp_b)
            if ca is None or cb is None:
                missing = [e for e, c in ((exp_a, ca), (exp_b, cb)) if c is None]
                status = "FAIL(wrapper absent)"
                fails.append(f"{exp_a} vs {exp_b}: export wrapper(s) {missing} "
                             "not defined in the FlacTest/Fuzz*.c IR")
            elif ca & cb:
                status = "FAIL(ALIASED)"
                fails.append(f"{exp_a} vs {exp_b}: both wrappers tail-call {sorted(ca & cb)} "
                             "-- the reference writer has silently aliased to emitFast. "
                             + why)
            elif want_a not in ca or want_b not in cb:
                bad = [f"{e}->{sorted(c)} (want {w})"
                       for e, c, w in ((exp_a, ca, want_a), (exp_b, cb, want_b))
                       if w not in c]
                status = "FAIL(unexpected callee)"
                fails.append(f"{exp_a} vs {exp_b}: {bad} -- twin binding changed; "
                             "review before trusting the proven-pair oracle. " + why)
            else:
                status = "OK"
            print(f"  [{status:22s}] {exp_a} -> {sorted(ca or [])}")
            print(f"       {' ':24s} {exp_b} -> {sorted(cb or [])}")

    if fails:
        print("\nTWINS FAIL:")
        for x in fails:
            print(f"  - {x}")
        return 1
    print("\nOK: every twin side has a live connector + >=1 driving target.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
