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
  has-standalone-body   everything else -- a genuine coverage target.

It grep-classifies every function symbol defined in `.lake/build/ir/Flac/Native/*.c`
against the source `.lean` attributes and the C name patterns, and writes
`fuzz/cov/structural_zero.json`. `target_reports.py` reads that file to annotate the
`uncovered.txt` rows, so a false zero is never re-chased.

    python3 cov/structural_zero.py
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


def inline_defs(module: str) -> set[str]:
    f = NATIVE / f"{module}.lean"
    if not f.exists():
        return set()
    return set(_INLINE.findall(f.read_text()))


def csimp_superseded() -> set[str]:
    """LHS def names of every `@[csimp] LHS_eq_RHS` (the superseded original)."""
    out: set[str] = set()
    for d in (NATIVE, SPEC):
        for f in d.glob("*.lean"):
            for thm in _CSIMP.findall(f.read_text()):
                if "_eq_" in thm:
                    out.add(thm.split("_eq_", 1)[0])
    return out


def c_definitions(cfile: Path) -> list[str]:
    """Function symbols with a standalone body in a Lean-emitted C file: a line
    ending in `{` and carrying `NAME(`; the token right before the first `(` is the
    symbol. Declarations (prototypes) end in `;` and are skipped."""
    syms: list[str] = []
    for line in cfile.read_text().splitlines():
        s = line.rstrip()
        if not s.endswith("{") or "(" not in s:
            continue
        head = s[:s.index("(")].split()
        if not head:
            continue
        name = head[-1].lstrip("*")
        if not name or not re.fullmatch(r"[A-Za-z_]\w*", name) or name.startswith("_init_"):
            continue
        syms.append(name)
    return syms


def classify(name: str, inl: set[str], csimp: set[str]) -> str:
    if "___boxed" in name or "___redArg" in name:
        return "boxed-wrapper"
    if any(name == d or name.endswith("_" + d) for d in csimp):
        return "csimp-superseded"
    if any(name == d or name.endswith("_" + d) for d in inl):
        return "inline-elided"
    return "has-standalone-body"


def main() -> int:
    cfiles = sorted(IR_NATIVE.glob("*.c"))
    if not cfiles:
        sys.exit(f"error: no Native IR under {IR_NATIVE} -- run `lake build` / `make lean-ir`")
    csimp = csimp_superseded()
    functions: dict[str, dict] = {}
    counts: dict[str, int] = {}
    for cf in cfiles:
        module = cf.stem
        inl = inline_defs(module)
        for name in c_definitions(cf):
            tag = classify(name, inl, csimp)
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
    for tag in ("inline-elided", "csimp-superseded", "boxed-wrapper", "has-standalone-body"):
        print(f"  {tag:22s} {counts.get(tag, 0)}")
    print(f"\nwrote {OUT.relative_to(REPO)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
