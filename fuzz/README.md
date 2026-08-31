# `fuzz/` — differential fuzzing for Vinyl

A two-engine (libFuzzer + AFL++) fuzzing subsystem that
compiles Vinyl's Lean-generated C into one instrumented process and compares it
against **two independent reference decoders** — libFLAC 1.4.2 and ffmpeg's
libavcodec — plus theorem-on-the-binary checks. It is a **different tier** from
the proof merge gate (`../scripts/check.sh`), which stays hermetic — this tier
needs clang/AFL/cmake/libFLAC/ffmpeg and is skippable.

Everything the codec proves is a statement about *functions*. This subsystem
tests the *binary* and the *interop*: the compiled C against the theorems, Vinyl
against the libFLAC **and** ffmpeg references (a two-referee differential that
tells "Vinyl is the outlier" apart from "the two referees disagree"), and Vinyl's
output against a strict `flac -t`.

## Dependencies

The devcontainer provisions everything via `.devcontainer/setup.sh`. **Without
Docker**, on Debian 12 / Ubuntu 22.04+:

```
sudo apt-get install -y \
  clang llvm afl++ cmake pkg-config build-essential xxd time \
  flac libflac-dev \
  ffmpeg libavcodec-dev libavformat-dev libavutil-dev libswresample-dev
```

What each is for: **clang** carries libFuzzer in its compiler-rt; **afl++** is
the second engine; **flac libflac-dev** is the primary reference decoder + the
`flac`/`metaflac` CLIs; **ffmpeg + libav*-dev** is the second independent
reference decoder (its libavcodec decodes the 12/20/24-bit depths the `flac` CLI
can't emit as raw, which is why it matters for any-depth coverage); **cmake**
builds the instrumented libFLAC flavours.

Lean 4 is not an apt package:

- **Lean 4** (`leanprover/lean4:v4.33.0`, pinned by `../lean-toolchain`) via
  elan: `curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh`.

The ffmpeg **dev libraries** are a hard build requirement (like libFLAC's): the
3-way `fz_samples_diff` links libavcodec, so `make` fails fast at
`mk/toolchain.mk` with a clear message if they are absent. The `flac`/`ffmpeg`
**CLIs** are used at corpus-gen time (`scripts/corpus_gen.sh --hires`, which
skips its 20-bit seed only if the IETF clone is missing).

## Build

```
scripts/deps_fetch.sh          # libFLAC 1.4.2 into third_party/ (or reuse ../reference/flac-src)
scripts/deps_fetch.sh --ietf   # + the IETF flac-test-files corpus -> corpus/external (optional, network)
make corpus                    # unpack the committed seed archive (corpus/seeds.tar.gz) -> per-target dirs
make -j$(nproc)                # lake build, IR, libFLAC, every target x fuzz+afl, the mutator .so, tools
make covfuzz                   # coverage-instrumented sibling of every target (also built by `make coverage`)
make ubsan                     # opt-in scoped-UBSan sibling (harness C only)
make cmplog                    # opt-in AFL CMPLog/RedQueen `-c` sibling (flac_stream magic values)
```

Two engines, five flavours: every target builds as `.fuzz` (libFuzzer) and
`.afl` (AFL++) under `make all`, plus a coverage-instrumented `.covfuzz` sibling
(`make covfuzz`, driven by `make coverage`). Two more are opt-in: `.ubsan` (a
scoped UBSan sibling over the hand-written harness C only — never the wrapping
Lean IR or libFLAC) and `.cmplog` (AFL's `-c` RedQueen operand logger for the
non-CRC magic values). honggfuzz is gone — libFuzzer + AFL++ are the only engines.

`make` is two-phase: it runs `lake build` and emits the symbol map, then
re-invokes itself so the IR glob sees a populated tree — a fresh checkout builds
in one `make`.

The curated seed corpus ships as a **single archive** (`corpus/seeds.tar.gz`,
tracked in git); the extracted per-target seed dirs are gitignored to keep the
tree free of thousands of small files. `make corpus` unpacks it (once per clone);
`scripts/corpus_gen.sh --all` regenerates every seed from scratch and
`make corpus-pack` rebuilds the archive deterministically. `corpus/MANIFEST.toml`
carries the per-seed sha256 + provenance (`scripts/corpus_verify.sh`).

## Run

```
make list        # every target: bug class, input kind, mutator, corpus, variants
make validate    # every FUZZ_TARGET macro parses + matches its run config; campaigns resolve
make check       # toolchain + check-symbols + validate + mut_bench selftest
make smoke       # 10s per target (FUZZ_SMOKE_SECONDS); non-zero on a spurious abort
make coverage    # HONEST per-target coverage: replay each target's corpus through its
                 #   .covfuzz sibling, raw llvm-cov region/branch over Flac/Native/*.c
                 #   (python3 cov/per_target.py --contribution --delta for the breakdown)

python3 -m fleet run default 1800      # the broad campaign (config/fleet.toml)
python3 -m fleet run official 7200     # the full-fleet run: all 22 targets, one+ worker each
python3 -m fleet run contract 1800     # the encode / output-contract surface (G1, emit-set, STREAMINFO)
python3 -m fleet run modes-deep 3600   # deep dive on the parallel decode surface
python3 -m fleet run strict 120        # regression pins at FUZZ_STRICT=2 over the curated corpora
```

A campaign writes `runs/<ts>/` with per-job isolation (`corpus/`, `artifacts/`,
`divergences/<class>/`), a live table, and `SUMMARY.md`/`BASELINE.md` on exit.
Divergences are catalogued as **witness-config buckets** (`common/buckets.c`):
each is a SHA-256 content-addressed reproducer with an uncapped occurrence count,
summed across `-fork` children via per-pid `counters.json`, and reported as
`witness_configs` — never "bug counts" (one defect spans many buckets). The
report is honest by construction: `exec/s = execs/elapsed_wall` (not the sum of
per-worker rates), and the `cov` column is engine-INTERNAL — labelled `pc`
(libFuzzer PCs) or `%` (AFL bitmap), NOT source coverage (that is `make coverage`).

## The fuzzers

Bug class: **L** = the binary contradicts a kernel-checked theorem (highest
value); **V** = a decode/encode divergence vs the reference or a validity failure;
**C** = a construction-secured / emit-set surface (the checked/unchecked encoder
and RFC conformance of the bytes Vinyl emits). Every `abort()` names the theorem
or property it contradicts.

| target | class | what it checks | oracle / reference |
|--------|-------|----------------|--------------------|
| **fz_decode_structured** | V | Vinyl vs libFLAC decode over the **deep-decoder space** — the CRC-repairing structured mutator gets ~12× more (mut_bench rate) libFLAC-accepted mutants past the frame CRC, reaching Rice/LPC/stereo/wasted paths | libFLAC 1.4.2 (`oracle.c`); 16-bit |
| **fz_decode_diff** | V | Vinyl vs libFLAC decode over the **malformed-header space** (plain mutation / AFL havoc) | libFLAC 1.4.2 (`oracle.c`); 16-bit |
| **fz_decode_modes** | L | the three proven-equal decode entry points (`decodeBytes`/`decodePcm16A`/`decodeReference`) must agree, and `decodeBytes` must be deterministic across repeats under a live task pool — the P6 `@[csimp]` surface. `par-forced` calls `byteStepsPar` directly. Each lane's abort cites its EXACT composition (fast↔pcm16: `decodeBytes_spec`+`pcm16FastA_eq_range`+`decodePcm16A_eq`; fast↔ref: +`decodeOption_eq_reference`+`pcmBytesA_eq`), never the samples theorem for a byte comparison | on-binary; per-lane composition |
| **fz_samples_diff** | V | **any-depth (4–32 bit) THREE-WAY** sample differential: Vinyl `decodeArrays` vs libFLAC **and** ffmpeg native planes — closes the 16-bit blind spot via referee triangulation. Aborts only when Vinyl contradicts a libFLAC+ffmpeg *consensus*; a referee split or a bignum sample is catalogued, not aborted. Also carries the **output-contract** detector (a reconstruction escaping `FitsSInt(bps)`, libFLAC-corroborated → `wide_output_contract`) and an in-band **resident-set** instrument (`resource_amplification`: a decode whose RSS dwarfs its input) | libFLAC + ffmpeg native planes (`wide_diff.c`) |
| **fz_proven_pairs** | L | executes **both sides** of `decodeOption == decodeReference` on the binary — a divergence is necessarily a compiler/runtime/`@[csimp]` defect (the standing TCB oracle) | on-binary; `decodeOption_eq_reference` |
| **fz_self_consistent** | L | the decoder **output contract**, any depth: rectangular planes + channel/bps/rate bounds (garbage-independent → abort), samples-fit-bps (garbage-in tolerated → measured), and WellFormed↔`Flac.encode` agreement. Plus **cross-mode agreement** (input ≤8192 B): `decodeOption` vs `decodeReference` (deep `audio_eq`), and vs `decodeBytes`↔`pcmBytes` (16-bit) — `selfcon_mode_disagree`, `reference-small` variant, `FUZZ_STRICT>=1` aborts | referee-free (`vinyl_checks.c`) |
| **fz_metamorphic** | L | `decode(encode(decode x)) == decode(x)` on the binary — `Flac.decode_encode` applied to the decoder's own output. Optional `reenc-pcm16` / `reenc-emit` variants (env `VM_REENC_LANE`) re-encode via `Encode.encodePcm16Fast` / `Emit.emitFast` so the shipped **fast** encoders are exercised, not only `Flac.encode` | referee-free; `decode_encode` |
| **fz_md5** | V | Vinyl's hand-written `Flac.Md5.md5` vs an **independent RFC 1321** reference, sweeping the ≡54–63 mod 64 padding boundaries every exec | `md5_ref.c` |
| **fz_roundtrip** | L | `encode → decode` capstones on the binary (fast + slow encoders), and fast-vs-slow accept-set agreement in the shared checked domain | on-binary; `decodePcm16_encodePcm16Fast/Cfg` |
| **fz_encode_diff** | V | Vinyl encode vs libFLAC encode, each round-tripped through the other decoder; Vinyl output libFLAC can't read = corrupted-output finding | libFLAC 1.4.2 |
| **fz_encode_validity** | V | Vinyl's own output must pass a strict `flac -t` equivalent: MD5 checking ON + STREAMINFO↔frame consistency (RFC 9639 §9.1) + decoded PCM == input | libFLAC MD5 (`flac_api.c`) |
| **fz_unchecked_encode** | C | `Stream.Unchecked.encode` (P7) must equal the checked encoder on its domain, and not footgun (its out-of-envelope output must decode back) | on-binary |
| **fz_trailing_data** | V | reject-where-referees-accept on **ordinary files**: valid stream + trailing bytes (128-byte ID3v1) or frame-boundary truncation. Vinyl returns none where libFLAC/ffmpeg recover the audio. Also an **ID3v2 prefix** before `fLaC` (Vinyl requires the marker at byte 0 — `trailing_id3v2_prefix`). Catalogue; `FUZZ_STRICT>=2` aborts on ID3v1 | Vinyl vs libFLAC + ffmpeg |
| **fz_gen_roundtrip** | V | **G1** any-depth (1–32) round-trip on Vinyl's OWN proven writer (`Stream.Unchecked.encode`) through the 3-way oracle — the encode-side force-multiplier. An **adversarial `EncoderCfg` chooser** (`../FlacTest/FuzzGen.lean`, escape-coded so output stays bounded) forces LPC orders 9–32, mid/side decorrelation and high partition orders the default chooser never emits; correlated populations (ramp/walk/sine) give real residuals. `set_md5_checking` on the output validates Vinyl's STREAMINFO MD5 convention above 16-bit (`gen_md5_mismatch`). Also emits the stereo out-of-range witness and the Unchecked self-decode check (`gen_self_decode_fail`) | Vinyl vs libFLAC + ffmpeg (`vinyl_gen.c` + `FuzzGen.lean`) |
| **fz_streaminfo_contradict** | L | deliberate STREAMINFO/frame contradictions (STREAMINFO carries no CRC): **sr=0 with audio** (RFC 9639 §9.1.7 MUST NOT), differing channel count, and a reported bps that does not bound the samples. Referee-free; catalogue + `FUZZ_STRICT>=2` abort | referee-free (`fz_streaminfo_contradict.c`) |
| **fz_emit_conformance** | C | RFC clauses on Vinyl's **emitted** bytes (not a decoder's tolerance) over G1 at every depth: frame sample-rate/bit-depth code 0 (subset §7), STREAMINFO block/bps bounds (§8.2 / Table 3, catches bps 1–3). Runs the checker on **`Emit.emitFast`** output too (`vinyl_gen_encode_pair`) — the shipped fast writer, not only the reference writer. A standing emit-set gate | conformance (`flac_struct.c` walk) |
| **fz_residual_bound** | C | residual magnitude bound `\|r\|<2^31 ∧ r≠−2^31` (RFC 9639 §9.2.7.3) on G1 mono single-frame output, recomputed from decoded samples (no Rice decode → sound). The correlated G1 populations + adversarial chooser give it real FIXED/LPC residuals to analyse (uniform noise → VERBATIM → nothing to bound). Analyses **`Emit.emitFast`** output (`vinyl_gen_encode_pair`) so the fast writer is bound-checked. 16-bit self-check must stay 0 | emit-set (`flac_residual.c`) |
| **fz_encode_pair** | L | the **encoder proven pair**: `Emit.emitFast` == `Stream.Unchecked.encode` (`emitFast_eq_encode`) over G1 at every depth 1–32 and every chooser — the encode-side analogue of `fz_proven_pairs`, and the standing pin on the encode `@[csimp]` that routes the shipped slow encoder through `emitFast`. A byte divergence is a compiler/runtime defect no round-trip or referee oracle can see; aborts unconditionally | on-binary; `emitFast_eq_encode` |
| **fz_encode_pcm16_eq** | L | the **shipped 16-bit encoder proven pair**: `Encode.encodePcm16` == `Stream.Unchecked.encode ⟨bs,false,fastChooser 16⟩` (`encodePcm16_eq`) on the same packed PCM — the largest missing proven pair, pinning the whole `encodePcm16` path (deinterleave + `fastChooser 16`) byte-for-byte against the Unchecked writer. A byte/length divergence is a compiler/runtime/`@[csimp]` defect; aborts unconditionally. PCM bounded to 16 KB (overflow-free) | on-binary; `encodePcm16_eq` |
| **fz_decode_capacity** | C | `decodeBytes` pre-sizes its PCM output at **2 bytes/sample** (16-bit); at bps>16 (needs `⌈bps/8⌉`) every valid fast decode with a correct `totalSamples` under-allocates and reallocs. Recomputes the decoder's own `outCapacity` from STREAMINFO vs the actual output length; the depth class (bps>16, `total>0`), the RFC-legal streaming `total=0` case and 16-bit `totalSamples` lies are counted apart. Catalogue; `FUZZ_STRICT>=2` aborts | capacity invariant (source-derived) |
| **fz_float_exact** | C | the encoder's Float (=`double`) LPC search is documented "every value well inside 2^53"; at 24/32-bit the autocorrelation lag sums exceed it, so `double` is inexact and the quantized LPC vector can diverge from exact arithmetic (round-trip still holds — a search/claim defect no decoder oracle sees). Vinyl `autocorrF`/`levinson`/`quantizeCoefs` vs an **exact `__int128` + long-double** recompute, gated by a long-double control so only autocorr-attributable divergences flag; the 16-bit self-test (`div16`) must stay 0. Catalogue; `FUZZ_STRICT>=1` aborts | exact-int / long-double model (`fz_float_exact.c`) |
| **fz_overlong_utf8** | C | frame/sample **coded numbers** are read by `readUtf8`→`readConts` (no minimality check), so non-minimal (overlong) encodings are accepted — the RFC 3629 overlong class (§9.1.5). A constructive unit-differential: build the k-continuation encoding of a value V and drive `readUtf8`, asserting accept + correct value + correct consumed length (a mis-decode aborts), then count `overlong_accepted` when k exceeds the minimal form. Two-way regression pin (a minimality guard drops it to 0, `minimal_accepted` still passes). Catalogue; `FUZZ_STRICT>=2` aborts | minimality reference (`fz_overlong_utf8.c`) |

## How to add a new fuzzer

1. **Write `targets/fz_foo.c`** — one `LLVMFuzzerTestOneInput(const uint8_t*, size_t)`
   plus one `FUZZ_TARGET(...)` declaring identity:
   ```c
   FUZZ_TARGET(.name = "fz_foo",
               .summary = "one line shown in `make list` and the banner",
               .input_kind = FUZZ_INPUT_FLAC_STREAM,   // FLAC_STREAM | PACKED_PCM | RAW
               .default_mutator = FUZZ_MUT_CRC,        // CRC (flac only) | PLAIN
               .needs_vinyl = 1, .report = report)
   ```
   The macro is the single source of truth for identity — there is **no sidecar
   file**. Reuse the shared FFI wrappers (`common/vinyl_*.h`, `common/flac_api.h`,
   `common/oracle.h`); do not inline Lean extern calls.
2. **Add one row to `TARGETS` in `fleet/config.py`** — its corpus and any
   `max_len`/`rss_limit_mb`/`bug_class`/`variants` override. Corpus is a list of
   subdirs under `corpus/`.
3. **Add a job to `config/fleet.toml`** if you want it in a campaign.
4. `make && make validate && make smoke` — the glob build discovers the new
   `.c` with zero makefile edits; validate confirms the macro parses and matches
   the registry; smoke runs it 10s.

If it calls a *new* codec entry point, add a stable `@[export vinyl_*]` wrapper in
`../FlacTest/FuzzGen.lean` (the harness links stable names, **not** mangled
`lp_vinyl_Flac_*`) and list it in `REQUIRED_SYMS` (`mk/lean.mk`) — `check-symbols`
then catches a Lean-internal rename before the link, and `cov/twins.py` records
which compiled twin the export binds to.

## Tools

```
build/bin/mut_bench rate corpus/decode/gen 20000   # CRC-aware/plain accept ratio (~12x)
build/bin/mut_bench selftest                        # CRC vectors + generator N/N via libFLAC
build/bin/mut_bench gen corpus/decode/gen 400       # 16-bit CRC-correct decode seeds (the multi-depth
                                                    #   decode/wide seeds are committed data)
build/bin/measure_decode corpus/decode/gen          # decode: bytes->samples amplification, peak RSS
build/bin/measure_encode                             # encode: blockSize task-storm sweep + RSS/time
build/bin/measure_encode 65536                       # pinned slow-path encode (for the stack probe)
tools/stack_probe.sh                                 # encoder stack threshold vs input (ulimit -s sweep)
build/bin/pcm_check <a.flac>                         # eyeball one reproducer through the codec
tools/shrink.py <repro.flac> -- vinyl --decode-fast @@ /tmp/o   # structure-aware minimizer
tools/thread_probes.sh                               # CLI thread-flag footguns (NOTE-classified)
conformance/mustreject.py                            # RFC-invalid verdict table (vinyl x 3 vs flac -t)
python3 cov/per_target.py                            # honest per-target + fleet-union region/branch over Flac/Native/*.c
python3 cov/per_target.py --contribution --delta     # unique-region contribution + seed->evolved delta per target
python3 cov/target_reports.py                        # per-target report dirs (coverage.txt/html/uncovered.txt); FULL corpus is
                                                    #   VARIANT-MERGED (every variant's env applied, profraws merged); --seeds-only = fast CI number
python3 cov/gate.py                                  # CI coverage regression floor (seeds-only, reproducible)
python3 cov/twins.py                                 # E1: every proven-equivalent twin side has >=1 driving target + nm symbol->twin binding (CI gate)
python3 cov/structural_zero.py                       # E2: classify inline/csimp/boxed false-zeros -> cov/structural_zero.json (annotates uncovered.txt)
python3 cov/lint.py                                  # E3/E4/E5: size-threshold audit + input_kind<->corpus + seed-structure/comment-wiring lints
build/bin/gen_g1_flac corpus/decode/g1_hostile       # materialize the G1 hostile-chooser space (LPC/partition/RICE2/stereo/invalid) as committed FLAC seeds
build/bin/mk_reject corpus/decode/must_reject        # CRC-8-repaired single-field-violation reject microseeds (reserved codes, block 65536, sr=0, min-block, type-127)
scripts/corpus_gen.sh --all                          # regenerate every corpus (see sources.toml)
scripts/corpus_verify.sh                             # MANIFEST sha256 + 4MB size gate (ci.sh)
scripts/ci_assertions.sh                             # standing gates: corpus flac -t + encode float-search reached
```

## Five load-bearing invariants (don't "simplify" these)

- **Link order** (`mk/flags.mk`): the fuzzer runtime must precede `libvinyl`, or
  crt1's `main` resolves to a Lean `main` and the binary isn't a fuzzer.
- **RSS is bounded by RESIDENT set, never `RLIMIT_AS`/`ulimit -v`**
  (`fleet/watchdog.py`): Lean reserves a huge virtual arena per thread.
- **`common/flac_struct.c` is the CRC mutator/walker, kept verbatim**: do not
  touch its unary order, `frame_end_bit`, padding zeroing, or contractive-LPC rule.
- **`vinyl_init()` calls `lean_init_task_manager()`**: without it every
  `Task.spawn` runs inline and the parallel surface goes untested.
- **ffmpeg planes are normalized `>> (32 − bps)` before comparison**
  (`wide_diff.c`): libavcodec LEFT-justifies >16-bit samples into int32, while
  libFLAC and Vinyl are right-aligned. Drop the shift and every 20/24/32-bit
  sample looks 2⁸–2¹⁶× off and the 3-way oracle false-aborts. The 3-way abort
  is also gated on a libFLAC+ffmpeg *consensus* for the same reason — ffmpeg
  alone disagreeing is a referee split, not a Vinyl defect.

The FFI wrappers are verbose because Lean's `lean_inc`/`lean_dec` convention is;
the many "catalogue, don't abort" branches are the garbage-in discipline
(`Bits.lean` sanctions out-of-range decoded samples), not hedging.

## KNOWN LIMITATIONS (honest)

- **The three-way differential reaches the encode side only through G1.**
  `fz_samples_diff` runs Vinyl vs libFLAC vs ffmpeg on *decode*; `fz_gen_roundtrip`
  extends the same 3-way oracle to Vinyl's *own emitted* bytes (encode →
  decode-3-way), so the ffmpeg referee now sees the encoder — but only for streams
  G1 generates. Byte-for-byte emit-set conformance is still checked structurally
  (`fz_emit_conformance`) and against libFLAC `flac -t` (`fz_encode_validity`),
  not against ffmpeg. Note ffmpeg's demuxer accepts far more than libFLAC, so most
  referee splits are "ffmpeg-only-accepts" and are catalogued
  (`wide_ref_disagree` / `wide_ref_only`), never aborted.
- 12/20-bit reference material comes from the IETF corpus (`--hires`): ffmpeg's
  *encoder* clamps `-bits_per_raw_sample` to 16/24 and the `flac` CLI to 8/16/24/32,
  so 20-bit exists only as a decode seed, not a generated one.
- The legacy `fz_decode_{diff,structured,modes}` still gate to 16-bit (they now
  run the 16-bit `decode/wide16` subset so they don't waste execs on seeds they
  skip); any-depth coverage is `fz_samples_diff` + `fz_gen_roundtrip` + the
  output-contract/proven-pair/metamorphic oracles + the `--hires` seeds.
- `fz_decode_modes` `par-forced` checks `byteStepsPar` **determinism** across
  repeats, not correctness against the serial path: a direct `byteStepsPar`
  invocation is not `decodeBytes`'s internal one, so a byte comparison against the
  serial decode would manufacture false divergences (measured), and is not done.
- The committed `corpus/decode/wide` holds valid streams at depths {8,12,16,24}
  with FIXED subframes; the LPC/stereo/wasted archetypes come from the 16-bit
  `flac_generate` (`flac_struct.c`, driven by `mut_bench gen`) and, for the
  otherwise-unreachable LPC 9–32 / decorrelation / high-partition regions, from
  the **adversarial choosers** on G1 (`FlacTest/FuzzGen.lean`). Those choosers are
  parameterized (`hostileLpcN` / `hostilePartitionPO` / `hostileRice2K` /
  `hostileStereoMode` / `hostileInvalid`) and **materialized as committed FLAC**
  (`corpus/decode/g1_hostile`, via `gen_g1_flac`) so the `flac_stream` decode
  targets can consume them directly. The encode-side hostile RICE2/partition are
  bounded (k∈{18,24,28,30}, PO∈{4,5,6,8}) — a small-k RICE2 on adversarial high-bps
  residuals is a Rice unary-output explosion (OOM), and small-k / very-high-PO
  decode coverage is a decode-only concern, reached via crafted seeds, not by
  forcing the encoder.
- **Every referee verdict is a libFLAC 1.4.2 number.** The differential targets and
  witness-config counters (`wide_ref_disagree`, `decode_capacity_underalloc`, …) were
  produced against libFLAC 1.4.2; 1.5.0 changed behaviour (it *rejects* RFC-forbidden
  block size 65536, which 1.4.2 accepted). Any referee-facing counter must be
  version-qualified or re-run against a 1.5.0 build before it is quoted — see
  `../FUZZING-TODO.md` #1; `fleet/report.py` records the linked libFLAC version per run.
- **Open codec findings are DOCUMENTED, not fixed here.** The `Flac/` codec is off-limits
  to this subsystem (only `@[export]` additions in `../FlacTest/FuzzGen.lean`). The rig
  carries deterministic **regression pins** for the open findings (sample-rate-0,
  overlong coded numbers, channel truncation, `decodeBytes` under-allocation, block size
  65536, STREAMINFO min/maxBlock) — see `findings/`; the detectors fire under
  `FUZZ_STRICT` and are ready to become strict gates once a fix lands.

## Layout

```
Makefile mk/*          two-phase glob build (toolchain, flags, lean, build, tools, cov)
common/                30 files: FFI wrappers, oracles, the CRC mutator, the FUZZ_TARGET contract
  fuzz_main.c/fuzz_target.h   init/report driver + the target contract + run-time knobs + FUZZ_MAX_SAMPLES cap
  fuzz_data.h                C99 front-consuming cursor for param carving (fuzz_data_* accessors)
  vinyl_api,vinyl_modes       Vinyl decode/encode FFI (decode-fast, pcm16, ref, encode, parallel, md5)
  vinyl_checks               referee-free checks: self-consistency (+ channel coherence), proven pair, metamorphic
  vinyl_gen                  G1: drive Stream.Unchecked.encode at any depth + correlated populations +
                             the adversarial chooser select (shim in ../FlacTest/FuzzGen.lean)
  flac_api                   libFLAC decode + encode + strict flac -t validator
  wide_diff                  any-depth 3-way Vinyl-vs-libFLAC-vs-ffmpeg sample differential + output-contract
                             detector + libFLAC MD5-convention verify
  flac_residual              recompute residuals from decoded samples for the emit-set bound (no Rice decode)
  flac_bits.c/.h             the ONE FLAC bit layer: CRC-8/16, bit reader/writer, STREAMINFO offsets
                             (Phase 4 dedup — tools/flac_repair, shrink.py and mustreject.py all drive it)
  rng.h                      the ONE xorshift64 + splitmix seed used across the harness
  buckets.c/.h               witness-config bucketing: SHA-256 reproducers, uncapped occurrences, counters.json
  oracle                     the decode-diff oracle + reproducer dump (delegates to buckets)
  flac_struct                the CRC-repairing structured mutator/walker (verbatim, frozen; mut_bench selftest)
  ffi_util.h / md5_ref       shared FFI helpers (grow / mk_ba / nat_small) + independent RFC 1321 MD5
  pack.h                     the packed-PCM encode-input unpacker
  pcm_mutator.c              packed-PCM / G1-param structured mutator (authored; NOT yet wired into the engines)
targets/ fz_*.c        22 drop-in targets, discovered by glob (no sidecars)
engine/                mutator policy + libFuzzer/AFL adapters (runtime FUZZ_MUTATOR select)
fleet/                 python runner: config (target registry + campaigns), launch, watchdog, report, cgroup
cov/                   HONEST coverage: per_target.py replays each .covfuzz sibling (raw llvm-cov region/branch
                       over Flac/Native/*.c) + fleet-union; target_reports.py writes per-target report dirs
                       (FULL corpus is VARIANT-MERGED); gate.py (CI floor); twins.py (E1 equivalence-twin map),
                       structural_zero.py (E2 inline/csimp/boxed false-zero classifier), lint.py (E3 threshold
                       audit / E4 input_kind<->corpus / E5 seed-structure + comment<->wiring)
tools/                 gen_g1_flac (G1 hostile choosers -> FLAC seeds), mk_reject (CRC-repaired reject microseeds),
                       shrinker, resource meters (measure_decode/encode), stack_probe, thread probes
config/fleet.toml      the one fleet config: default / official / modes-deep / contract / strict campaigns
corpus/                seeds. decode/: hires (non-16-bit + LPC-13-32 + IETF 20-bit), wide16 (16-bit subset),
                       gen_params (G1 RAW params + overlong selectors), g1_hostile (materialized hostile-chooser
                       FLAC: LPC/partition/RICE2/stereo/invalid), must_reject (single-field reject microseeds +
                       ID3v2 prefix), parallel16 (pcm16-parallel), large16/large24_32 (>64 KiB, crosses
                       parThreshold; par_window_noise.flac >1 MiB crosses syncWindow), pairs_small (<=2 KiB).
                       encode/: gen, edge, shapes (deterministic FIXED/LPC/wasted/variance PCM). + sources.toml
                       (regen recipes) + MANIFEST.toml (sha256 + gate)
conformance/           must-reject verdict table
findings/              reproduced real bugs, each NOTE labelled NOVEL or CONFIRMATION + minimized repro
```
