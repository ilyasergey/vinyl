#!/usr/bin/env python3
"""E2 -- one-time static classifier of Native codegen "structural zeros".

Several `Flac/Native/*.c` functions can NEVER show coverage no matter the corpus,
because the compiled program does not run their standalone body:

  inline-elided     the Lean source def is `@[inline]`, so it is inlined at every
                    call site and its own emitted body is dead.
  csimp-superseded  a `@[csimp] X_eq_XTR` theorem replaces `X` with its tail-
                    recursive twin at runtime, so `X`'s own body never runs.
  boxed-wrapper     a `___boxed` / `___redArg` ABI thunk, exercised only through
                    its unboxed sibling.
  match-closure     a `_match__N` / `_splitter` / `_lam_N` / `_spec__N` / `_closed_`
                    codegen closure -- an internal artifact of a match/lambda, not a
                    source-level function.
  derived-instance  a derived `ctorIdx` / `ofNat` / `DecidableEq` / `Repr` / `Format` /
                    `ToString` / `Inhabited` / `BEq` / `Hashable` instance body -- never
                    called by the codec at runtime (debug/printing plumbing).
  module-init       an `_init_*` / `initialize_*` module-initialization constant.
  unreachable       no call path from ANY fuzz-harness entry point (every Lean symbol the
                    C under fuzz/common|targets|tools|engine references, i.e. the
                    `vinyl_*` @[export] wrappers and direct `lp_vinyl_*` externs) or from
                    a module initializer, through the whole-IR call graph (Flac + FlacTest,
                    closures included via their `___boxed` thunks). A never-entered spec /
                    unbudgeted predecessor with no runtime caller. NOT fuzz-coverable.
  has-standalone-body   everything else -- a genuine coverage target.

`--validate` cross-checks the classification against cov/report/latest/union.profdata:
a function that HAS coverage but is tagged unreachable/csimp-superseded/inline-elided is
a contradiction and is printed (the analysis, not the coverage, would be wrong).

The csimp match is NAMESPACE-AWARE: the theorem's enclosing `namespace` stack is
tracked while scanning, so `Flac.Bits.readUnary_eq_readUnaryTR` supersedes exactly
`lp_vinyl_Flac_Bits_readUnary` and not the unrelated `Flac.Bits.BitReader.readUnary`
(a bare-suffix match used to mis-tag that unused predecessor as csimp-superseded).

It grep-classifies every function symbol defined in `.lake/build/ir/Flac/Native/*.c`
against the source `.lean` attributes and the C name patterns, and writes
`fuzz/cov/structural_zero.json`. `target_reports.py` reads that file to annotate the
`uncovered.txt` rows, so a false zero is never re-chased.

    python3 cov/structural_zero.py [--validate]
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fleet import config as C  # noqa: E402

REPO = C.FUZZ_ROOT.parent
IR_NATIVE = REPO / ".lake" / "build" / "ir" / "Flac" / "Native"
NATIVE = REPO / "Flac" / "Native"
SPEC = REPO / "Flac" / "Spec"
OUT = C.FUZZ_ROOT / "cov" / "structural_zero.json"

_INLINE = re.compile(r"@\[[^\]]*inline[^\]]*\]\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                     r"def\s+([A-Za-z0-9_']+)")
_CSIMP = re.compile(r"@\[csimp\]\s*theorem\s+([A-Za-z0-9_']+)")
_NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)")
_NS_END = re.compile(r"^\s*end\s+([A-Za-z0-9_.']+)")
_CSIMP_LHS = re.compile(r"@([A-Za-z0-9_.']+)\s*=")  # the stated `@LHS = @RHS`
_CLOSURE = re.compile(r"(_match__\d|_splitter|_lam_\d|_elam_\d|___lam|___elam|_spec__\d|_closed_)")
_DERIVED = re.compile(r"(ctorIdx|ctorElim|toCtorIdx|_ofNat$|_ofNat_|decEq|DecidableEq|instRepr|_repr|Repr|"
                      r"Format|joinSep|List_repr|toString|instToString|instInhabited|instBEq|_beq$|Hashable)")


def inline_defs(module: str) -> set[str]:
    f = NATIVE / f"{module}.lean"
    if not f.exists():
        return set()
    return set(_INLINE.findall(f.read_text()))


def csimp_superseded() -> set[str]:
    """Mangled fully-qualified LHS names of every `@[csimp] LHS_eq_RHS` theorem (the
    superseded original), e.g. `Flac_Bits_readUnary`. The enclosing `namespace` stack
    is tracked so the match is exact, never a bare short-name suffix."""
    out: set[str] = set()
    for d in (NATIVE, SPEC):
        for f in d.glob("*.lean"):
            ns: list[str] = []
            lines = f.read_text().splitlines()
            for i, line in enumerate(lines):
                if m := _NS_OPEN.match(line):
                    ns.append(m.group(1))
                elif m := _NS_END.match(line):
                    if ns and ns[-1] == m.group(1):
                        ns.pop()
                elif "@[csimp]" in line:
                    # the theorem head + statement may span the next few lines
                    tail = " ".join(lines[i:i + 4])
                    if not (m := _CSIMP.search(tail)):
                        continue
                    # Prefer the STATED `@LHS = ...` (may be fully qualified, e.g.
                    # `@Flac.Stream.Unchecked.encode`); fall back to the name's `X_eq_Y` prefix.
                    if lm := _CSIMP_LHS.search(tail):
                        lhs = lm.group(1)
                    elif "_eq_" in m.group(1):
                        lhs = m.group(1).split("_eq_", 1)[0]
                    else:
                        continue
                    if "." not in lhs and ns:  # short name -> qualify with the enclosing namespace
                        lhs = ".".join(ns) + "." + lhs
                    out.add(lhs.replace(".", "_"))
    return out


_SYM = re.compile(r"\b((?:lp_vinyl|l|_init|initialize|vinyl|vlean)_[A-Za-z0-9_]+)\b")
IR_ROOT = REPO / ".lake" / "build" / "ir"
HARNESS_DIRS = [C.FUZZ_ROOT / d for d in ("common", "targets", "tools", "engine")]


_STR = re.compile(r'"(?:[^"\\]|\\.)*"')
_KEYWORDS = {"if", "else", "for", "while", "switch", "do", "return", "sizeof"}


def scan_file(cfile: Path) -> tuple[list[tuple[str, list[str]]], dict[str, set[str]]]:
    """(functions, file_scope_inits) for a Lean-emitted C file.
    functions: (symbol, body lines) for every function DEFINED. Lean's C is unindented --
    nested `{`/`}` sit at column 0 like the function's own -- so the body is delimited by
    brace DEPTH (string literals stripped first), never by indentation. A definition is a
    depth-0 line ending in `{` whose token before `(` is a non-keyword identifier;
    prototypes end in `;` and are skipped.
    file_scope_inits: global -> {symbols in its static initializer}. Capture-free closures
    are emitted as `static const lean_closure_object X___closed__N_value = {.. .m_fun =
    (void*)X___lam__0___boxed ..}` + `X___closed__N = &X___closed__N_value` -- references
    that live OUTSIDE any function and must still count as edges."""
    out: list[tuple[str, list[str]]] = []
    inits: dict[str, set[str]] = {}
    depth = 0
    cur: str | None = None
    body: list[str] = []
    for raw in cfile.read_text().splitlines():
        line = _STR.sub('""', raw)
        # `extern "C" {` / `#ifdef` wrappers bracket the whole file: not function scope.
        if line.startswith("#") or line.startswith("extern"):
            continue
        if depth == 0:
            s_ = line.rstrip()
            if s_.endswith("{") and "(" in s_:
                head = s_[:s_.index("(")].split()
                name = head[-1].lstrip("*") if head else ""
                if name and name not in _KEYWORDS and re.fullmatch(r"[A-Za-z_]\w*", name):
                    cur, body = name, []
            elif "=" in s_ and s_.endswith(";"):
                lhs, rhs = s_.split("=", 1)
                defined = _SYM.findall(lhs)
                if defined:
                    inits.setdefault(defined[-1], set()).update(_SYM.findall(rhs))
            depth = max(0, depth + line.count("{") - line.count("}"))
            continue
        depth += line.count("{") - line.count("}")
        if depth <= 0:
            depth = 0
            if cur is not None:
                out.append((cur, body))
            cur, body = None, []
        elif cur is not None:
            body.append(line)
    return out, inits


def scan_functions(cfile: Path) -> list[tuple[str, list[str]]]:
    return scan_file(cfile)[0]


def call_graph() -> dict[str, set[str]]:
    """caller -> {referenced Lean symbols} over every IR .c file (Flac + FlacTest). A
    reference is any Lean-shaped identifier inside the function body -- direct calls,
    `lean_alloc_closure((void*)X___boxed, ...)` closure captures, and `_init_*` constant
    initializers alike. Prototypes (file scope) are not references."""
    g: dict[str, set[str]] = {}
    for cf in sorted(IR_ROOT.rglob("*.c")):
        fns, inits = scan_file(cf)
        for name, body in fns:
            refs = g.setdefault(name, set())
            for line in body:
                refs.update(sym for sym in _SYM.findall(line) if sym != name)
        for glob, refs in inits.items():  # static closure objects and their aliases
            g.setdefault(glob, set()).update(r for r in refs if r != glob)
    # A closed term (e.g. a capture-free lambda) lives in a static global `X___closed__N`
    # built by `_init_X___closed__N()`; code references the GLOBAL, so route that
    # reference to its builder -- the builder is what captures the lambda's `___boxed`.
    for refs in g.values():
        for r in [r for r in refs if r not in g and "_init_" + r in g]:
            refs.add("_init_" + r)
    return g


def harness_roots() -> set[str]:
    roots: set[str] = set()
    for d in HARNESS_DIRS:
        for f in list(d.glob("*.c")) + list(d.glob("*.h")):
            roots.update(_SYM.findall(f.read_text()))
    return roots


def reachable_symbols() -> set[str]:
    """Closure of the IR call graph from the fuzz-harness roots + module initializers."""
    g = call_graph()
    todo = {s_ for s_ in g if s_.startswith("initialize_")} | harness_roots()
    seen: set[str] = set()
    while todo:
        s_ = todo.pop()
        if s_ in seen:
            continue
        seen.add(s_)
        todo |= g.get(s_, set()) - seen
    return seen


def c_definitions(cfile: Path) -> list[str]:
    """Function symbols with a standalone body in a Lean-emitted C file (depth-aware; a
    prototype is not a definition). `_init_*` closed-term initializers are kept and tagged
    module-init unless reachable."""
    return [name for name, _ in scan_functions(cfile)]


def classify(name: str, inl: set[str], csimp: set[str], reach: set[str] | None = None) -> str:
    # Ground truth first: if any fuzz entry point can reach this symbol, its standalone
    # body is a genuine coverage target -- even for @[inline] defs (the compiler does not
    # inline every call site: BitReader.accBytes/scanOne execute standalone), csimp
    # originals kept alive as forwarders by an @[export] wrapper, or ___boxed thunks that
    # are real closure entry points. The tags below only explain WHY an UNREACHABLE
    # symbol can never execute.
    if reach is not None and name in reach:
        return "has-standalone-body"
    if "___boxed" in name or "___redArg" in name:
        return "boxed-wrapper"
    # csimp: `q` is namespace-qualified (`Flac_Bits_readUnary`); accept the plain symbol
    # or a `__private_..._0__`-prefixed one, never a bare short-name suffix.
    if any(name == "lp_vinyl_" + q or name.endswith("__" + q) for q in csimp):
        return "csimp-superseded"
    if any(name == d or name.endswith("_" + d) for d in inl):
        return "inline-elided"
    if name.startswith("_init_") or name.startswith("initialize_"):
        return "module-init"
    if _CLOSURE.search(name):
        return "match-closure"
    if _DERIVED.search(name):
        return "derived-instance"
    return "unreachable" if reach is not None else "has-standalone-body"


def validate(functions: dict[str, dict]) -> int:
    """Contradiction check: a function WITH coverage tagged as never-executable (any
    tag other than has-standalone-body claims the body can never run)."""
    import shutil
    import subprocess
    union = C.FUZZ_ROOT / "cov" / "report" / "latest" / "union.profdata"
    bins = sorted(C.BUILD_BIN.glob("*.covfuzz"))
    cov = shutil.which("llvm-cov")
    if not (union.exists() and bins and cov):
        print("validate: need cov/report/latest/union.profdata + a .covfuzz binary + llvm-cov")
        return 0
    bad = []
    for cf in sorted(IR_NATIVE.glob("*.c")):
        rep = subprocess.run([cov, "report", str(bins[0]), f"-instr-profile={union}", str(cf),
                              "-show-functions"], capture_output=True, text=True).stdout
        for line in rep.splitlines():
            p = line.split()
            if len(p) < 4 or not p[1].isdigit() or p[0] == "TOTAL":
                continue
            name, regs, miss = p[0].split(":", 1)[-1], int(p[1]), int(p[2])
            tag = functions.get(name, {}).get("tag")
            if regs > miss and tag != "has-standalone-body":
                bad.append(f"  {name}  tag={tag}  covered={regs - miss}/{regs}")
    print(f"\nvalidate: {len(bad)} contradiction(s) (covered function tagged never-executable)")
    for b in bad:
        print(b)
    return 1 if bad else 0


def main() -> int:
    do_validate = "--validate" in sys.argv
    cfiles = sorted(IR_NATIVE.glob("*.c"))
    if not cfiles:
        sys.exit(f"error: no Native IR under {IR_NATIVE} -- run `lake build` / `make lean-ir`")
    csimp = csimp_superseded()
    reach = reachable_symbols()
    functions: dict[str, dict] = {}
    counts: dict[str, int] = {}
    for cf in cfiles:
        module = cf.stem
        inl = inline_defs(module)
        for name in c_definitions(cf):
            tag = classify(name, inl, csimp, reach)
            functions[name] = {"module": f"Flac/Native/{cf.name}", "tag": tag}
            counts[tag] = counts.get(tag, 0) + 1
    doc = {
        "generated_by": "cov/structural_zero.py",
        "source": ".lake/build/ir/Flac/Native/*.c",
        "note": "false-zero classifier; a tagged function cannot show coverage regardless of corpus",
        "counts": counts,
        "functions": dict(sorted(functions.items())),
    }
    OUT.write_text(json.dumps(doc, indent=2) + "\n")
    print(f"# structural-zero classification over {len(cfiles)} Native/*.c "
          f"({len(functions)} function symbols)\n")
    for tag in ("inline-elided", "csimp-superseded", "boxed-wrapper", "match-closure",
                "derived-instance", "module-init", "unreachable", "has-standalone-body"):
        print(f"  {tag:22s} {counts.get(tag, 0)}")
    print(f"\nwrote {OUT.relative_to(REPO)}")
    return validate(functions) if do_validate else 0


if __name__ == "__main__":
    raise SystemExit(main())
