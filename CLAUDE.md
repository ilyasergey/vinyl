# Vinyl — agent working conventions

A formally verified FLAC codec in pure Lean 4. The complete technical plan is
in `PLAN.md` — read it before writing code. This file holds the *workflow*
rules every session must follow.

## Toolchain / build

- Lean `leanprover/lean4:v4.33.0` (pinned in `lean-toolchain`). No external
  dependencies: core Lean + its bundled `Std` only. No mathlib in `Flac/Native/`
  ever; mathlib is not a dependency at all for now.
- Build: `lake build`. Run tests: `lake exe flactest` (must print `ALL TESTS
  PASSED` and exit 0).

## Non-negotiable rules (from PLAN.md §8)

- **No `sorry` and no new `axiom` ever reaches `master`.** A stuck proof
  becomes a minimized statement recorded in `PROGRESS.md` (and an issue once a
  remote exists), not a hole.
- **Decoder totality by construction**: no `partial def`, no panicking (`!`)
  indexing anywhere in decode paths in `Flac/Native/`.
- `Flac/Spec/` contains theorems only; keep one file per lemma cluster.
- Heuristics (`Flac/Native/Heuristics.lean`) are unverified *by design*; only
  output-format lemmas may depend on them.
- Where PLAN.md and RFC 9639 disagree, the RFC wins — then fix PLAN.md.

## Progress logging & commits

- **Every session appends a dated entry to `PROGRESS.md`**: what was
  attempted, what landed, what is blocked (with exact lemma names), and what
  the next step is.
- **Commit regularly** — after each self-contained unit (a module + its
  proofs + its tests), not one giant commit per session. Commit messages:
  short imperative subject, body says which milestone (M0–M7) it advances.
- Never commit with a broken `lake build` or failing `lake exe flactest`.

## Layout map (see PLAN.md §3 for the full tree)

- `Flac/Native/` — executable production code, including the reference
  decoder/model (`Stream.decodeReference`) that the proofs are phrased over.
- `Flac/Spec/` — all theorems; no `sorry`, no axioms.
- `FlacTest/` — unit + golden tests wired into `lake exe flactest`.
- `conformance/`, `fuzz/`, `bench/` — differential rigs and benchmarks,
  driven by shell/Python against the built binary; outside the trusted base.
- `PROGRESS.md` — per-session log, one entry per session.
