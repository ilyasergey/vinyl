# Kernel generators

The per-order machine-word kernels and their proofs are written once as a
template and emitted for every order the decoder and encoder specialise:

- `gen_restore_window.py K…` → `restoreWin{K}` / `restoreRoll{K}` and
  `restoreRoll{K}_eq_fold` in `Flac/Native/Lpc.lean` (orders 1–12).
- `gen_residual_window.py` (`gen(K, slow_def, slow_eq)`) → `lpcResWin{K}` /
  `lpcResGo{K}Fast` and `lpcResGo{K}_eq_fast` in `Flac/Native/Emit.lean`
  (orders 1–8).

The per-order proofs differ only in index arithmetic, which is the one class of
error writing them by hand reliably produces. The emitted text is pasted into
the modules rather than generated at build time, so `check_gen.py` — run by
`scripts/check.sh` — requires every declaration a generator emits to appear
verbatim in its target module. Change a template and the modules must follow,
or the gate fails.
