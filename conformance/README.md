# Differential testing against libFLAC

The theorems prove the encoder and decoder agree with *each other*;
interoperability with the rest of the world is established by testing
against libFLAC (the `flac` CLI, developed against 1.5.0; any ≥ 1.4
works). Three rigs live in this directory, one more in `scripts/`:

- [`smoke.sh`](smoke.sh) — both directions on synthetic signals
  (PLAN.md §6 rigs 1–2): every Vinyl stream must pass `flac -t`
  (CRC-8/16 + MD5) and decode byte-identically with libFLAC;
  libFLAC-encoded streams must decode byte-identically with Vinyl.
- [`ietf.sh`](ietf.sh) — the RFC 9639 companion test-file corpus
  ([flac-test-files](https://github.com/ietf-wg-cellar/flac-test-files));
  usage: `conformance/ietf.sh <path-to-flac-test-files>`. The
  must-decode `subset/` set is a merge gate; results are summarized in
  [`COVERAGE.md`](../COVERAGE.md).
- [`fuzz.sh`](fuzz.sh) — PLAN.md §6 rigs 3–5, `fuzz.sh [iterations]`
  (default 200): random bytes and truncations must never crash or hang
  the decoder (totality); bit-flipped valid streams must be cleanly
  rejected or decoded, with CRCs catching most corruptions; and random
  audio must round-trip byte-identically through the *compiled* checked
  encoder/decoder — the theorem guarantees the functions agree, so this
  rig tests the trusted base (compiler + runtime).
- [`../scripts/check.sh`](../scripts/check.sh) — the ratchet: full
  build, **zero `sorry`/`axiom`**, grep-pinned capstone theorems
  present, decoder-totality lint (no `partial`, no panicking indexing),
  unit suite.

## Checking one file by hand

The same cross-check the rigs automate, on a single file — see the
"Cross-checking against libFLAC" section of the
[top-level README](../README.md) for a copy-paste walkthrough.
