#!/usr/bin/env python3
"""Check that every declaration the kernel generators emit is present verbatim
in the module it was generated into.

The per-order kernels and their proofs are templates instantiated for each order
(`gen_restore_window.py` orders 1-12 into `Flac/Native/Lpc.lean`,
`gen_residual_window.py` orders 1-8 into `Flac/Native/Emit.lean`). Nothing
regenerates them at build time, so without a check the templates drift from the
code and the next order added by hand reintroduces exactly the index-arithmetic
class of error the templates exist to prevent.

Whole-file equality is not the property to check: the modules group all the
definitions first and all the proofs after, while a template emits one order's
definition and proof together, and each module holds much else besides. The
property that does hold, and that this script enforces, is **per-declaration
containment**: split the emitted text into top-level declarations and require
each to appear verbatim in the target module.

Exit status 0 if every declaration is present, 1 otherwise.
"""
import importlib.util
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]

# (generator, target module, orders)
JOBS = [
    ("gen_restore_window.py", "Flac/Native/Lpc.lean", range(1, 13)),
    ("gen_residual_window.py", "Flac/Native/Emit.lean", range(1, 9)),
]


def load(path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def declarations(text: str) -> list[str]:
    """Split generated Lean into top-level declarations (doc comment attached)."""
    out: list[str] = []
    cur: list[str] = []
    for line in text.split("\n"):
        opens = re.match(r"(/--|@\[|private theorem |theorem |def |/-!)", line)
        continues = cur and (cur[-1].rstrip().endswith(("-/", "in")) or re.match(r"(/--|@\[)", cur[-1]))
        if opens and cur and not continues:
            out.append("\n".join(cur).strip())
            cur = []
        cur.append(line)
    out.append("\n".join(cur).strip())
    return [d for d in out if d]


def main() -> int:
    missing = 0
    for gen_name, target, orders in JOBS:
        gen = load(pathlib.Path(__file__).parent / gen_name)
        src = (ROOT / target).read_text()
        for k in orders:
            emitted = gen.gen(k)
            # a generator returns either one block or (definitions, proofs)
            parts = emitted if isinstance(emitted, tuple) else (emitted,)
            for decl in [d for part in parts for d in declarations(part)]:
                if decl not in src:
                    missing += 1
                    head = decl.split("\n")[0][:90]
                    print(f"FAIL: {gen_name} order {k} emits a declaration absent from {target}:\n"
                          f"      {head}")
    if missing:
        print(f"FAIL: {missing} generated declaration(s) not present verbatim; "
              f"regenerate or update the template")
        return 1
    print("ok: every generated declaration is present verbatim")
    return 0


if __name__ == "__main__":
    sys.exit(main())
