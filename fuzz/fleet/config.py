"""Targets and campaigns -> validated Job objects.

Target IDENTITY (name, summary, input_kind, mutator) is read from the
`FUZZ_TARGET(...)` macro in each `targets/*.c` -- the same declaration the binary
uses for its own banner, so there is one source of truth and no sidecar to drift.
Fleet-side run config (corpus, max_len, rss, variants) lives in the TARGETS table
below; campaign composition lives in `config/fleet.toml`. This module turns both
into frozen Job objects and validates everything up front.
"""
import re
import sys
import tomllib
from dataclasses import dataclass, replace
from pathlib import Path

FUZZ_ROOT = Path(__file__).resolve().parent.parent
TARGETS_DIR = FUZZ_ROOT / "targets"
BUILD_BIN = FUZZ_ROOT / "build" / "bin"
CORPUS_DIR = FUZZ_ROOT / "corpus"
FLEET_TOML = FUZZ_ROOT / "config" / "fleet.toml"

_KIND = {"FLAC_STREAM": "flac_stream", "PACKED_PCM": "packed_pcm", "RAW": "raw"}
_MUT = {"CRC": "crc", "PLAIN": "plain", "PCM": "pcm"}

# Fleet-side run config per target. Identity comes from the .c macro; this adds
# only knobs the fleet needs. Omitted keys take the DEFAULTS. `variants` are
# named env/knob overrides a campaign job can select.
DEFAULTS = dict(engines=("libfuzzer", "afl"), timeout=25, rss_limit_mb=3000,
                max_len=16384, env={"LEAN_NUM_THREADS": "1"})
# engine -> built-binary suffix.
_ENGINE_SUFFIX = {"libfuzzer": "fuzz", "afl": "afl"}
# decode/blocksizes, decode/multichan, decode/metablocks: libFLAC-encoded 16-bit
# seeds carrying header block-size codes 1-15, channel-assignment codes 2-7, and
# every metadata block type -- structurally unreachable from Vinyl's own writer
# (which only emits block-size code 7 / sample-rate code 0 / <=2ch decorrelation).
# These are 8-15 KB, so they feed the FAST decode lane only. decode/ref_small is
# the <=8 KB (1-2 frame) subset of the same shapes, so it ALSO reaches the
# fz_decode_modes REFERENCE lane (VM_REF_MAX_INPUT=8192, a stack-safety bound) --
# driving decodeReference / Frame.readChannels / resolveBlockSize / Stereo.c on the
# non-canonical block sizes and 3-8 channel geometries.
_DECODE = ("decode/gen", "decode/wide", "decode/regress",
           "decode/blocksizes", "decode/multichan", "decode/metablocks", "decode/ref_small")
# The 16-bit-GATED decode differentials (fz_decode_diff/structured/modes) DEC_SKIP
# every non-16-bit stream after a full readMeta + whole-input alloc, so they get
# the 16-bit SUBSET of wide (decode/wide16) instead of the full multi-depth bundle
# -- ~3/4 of wide is non-16-bit, wasted on them (F3). corpus_gen.sh --wide carves
# wide16 from wide, so it never drifts.
_DECODE16 = ("decode/gen", "decode/wide16", "decode/regress",
             "decode/blocksizes", "decode/multichan", "decode/metablocks", "decode/ref_small")
# The any-depth oracles (3-way samples diff, self-consistency, metamorphic) also
# get the external non-16-bit / LPC-13-32 seeds; the 16-bit-gated targets would
# only SKIP them, and the small-max_len proven-pairs target does not want the
# 157 KB IETF seed, so hires is scoped to the targets that exercise it.
# decode/multichan_hi adds 24-bit 3-8ch + explicit-sample-rate seeds (gen_multichan
# is 16-bit only), so the any-depth oracles get high-depth channel-assignment /
# explicit-SR coverage the 16-bit-gated targets would only SKIP.
_DECODE_ANY = (*_DECODE, "decode/hires", "decode/multichan_hi")
# 6C: the IETF flac-test-files conformance corpus (deps_fetch.sh --ietf). subset +
# uncommon are libFLAC/ffmpeg-produced streams across depths/rates Vinyl's own
# encoder never emits -- the 12/20-bit files close COVERAGE.md's unverified "decoded
# too" claim via fz_samples_diff's ffmpeg referee. Added only to the any-depth
# decoders; the 6E sample cap bounds any large IETF file.
_IETF = ("external/flac-test-files/subset", "external/flac-test-files/uncommon")
_DECODE_ANY_IETF = (*_DECODE_ANY, *_IETF)
_PAR = {"LEAN_NUM_THREADS": "4"}
# P0.1: the sample-aware PCM mutator (common/pcm_mutator.c) reshapes the raw
# fuzzer bytes of a packed-PCM encode input into correlated/boundary-shaped audio,
# so choosePlanF reaches FIXED/LPC/wasted/mid-side instead of near-always VERBATIM.
# libFuzzer-only: the AFL arm selects its mutator .so via AFL_CUSTOM_MUTATOR_LIBRARY
# (fleet/launch.py), which only wires the crc mutator today.
_PCM_VARIANT = {"pcm": dict(mutator="pcm", engines=("libfuzzer",))}
TARGETS: dict[str, dict] = {
    # RAW G1 targets: the "pcm" variant selects the G1-param field mutator
    # (pcm_mutate_g1_param) so the gen_params header is walked field-aware instead of
    # by plain byte havoc -- drives chooser/depth/blocking transitions deliberately.
    "fz_gen_roundtrip":     dict(bug_class="V", max_len=64,
                                 corpus=("decode/gen_params",), variants=dict(_PCM_VARIANT)),
    "fz_emit_conformance":  dict(bug_class="C", max_len=64,
                                 corpus=("decode/gen_params",)),
    "fz_residual_bound":    dict(bug_class="C", max_len=64, corpus=("decode/gen_params",),
                                 variants=dict(_PCM_VARIANT)),
    # CRC primitive differential: Flac.Crc.crc8/crc16 vs the independent C clone.
    # Any bytes exercise it; reuse the md5 arbitrary-byte seeds.
    "fz_crc":               dict(bug_class="V", max_len=8192, corpus=("md5",)),
    # Decode-side stack prober (regression pin, expected green): forks a bounded-stack
    # child that builds a deep stream with libFLAC (flac_encode, subset off, bs up to the
    # legal max 65535) and decodes it via the shipped decodePcm16A (tail array forms
    # readRiceSeqScan/readSIntSeqGo/readPartsA). A witness = a future non-tail regression
    # in the shipped decode path. RAW 4-byte geometry; work is in the forked child -> libFuzzer only.
    "fz_decode_stack":      dict(bug_class="C", engines=("libfuzzer",), max_len=64,
                                 timeout=30, corpus=("encode/stack_seeds",)),
    # decodeBytes_spec ON THE BINARY in the PARALLEL region (>= parThreshold=65536):
    # fused decodeBytes == pcmBytesRange(decodeArrays), byte-for-byte. The byte lane in
    # fz_self_consistent is coupled to the reference lane's 8 KB stack cap so it never
    # runs above parThreshold; this drops the reference lane and runs uncapped. serial
    # (1 thread) and par (N threads) run the SAME oracle -> a deterministic-but-wrong
    # parallel stitch is caught.
    "fz_decode_par_eq":     dict(bug_class="L", max_len=262144,
                                 corpus=(*_DECODE_ANY, "decode/parallel16",
                                         "decode/large16", "decode/large24_32"),
                                 variants={"serial": {},
                                           "par": dict(env={"LEAN_NUM_THREADS": "4"})}),
    # Encoder proven pair Emit.emitFast == Stream.Unchecked.encode at ARBITRARY depth
    # -- the encode-side analogue of fz_proven_pairs, over the non-16-bit region.
    "fz_encode_pair":       dict(bug_class="L", max_len=64,
                                 corpus=("decode/gen_params",)),
    # decodeBytes output pre-size uses 2 bytes/sample (16-bit) -> 24/32-bit reallocs;
    # needs the non-16-bit hires seeds to reach the depth region it flags.
    "fz_decode_capacity":   dict(bug_class="C",
                                 corpus=(*_DECODE_ANY, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"large": dict(max_len=262144,
                                     corpus=(*_DECODE_ANY, "decode/g1_hostile", "decode/must_reject",
                                             "decode/large16", "decode/large24_32"))}),
    # Float LPC search vs exact/long-double recompute: at 24/32-bit the autocorr
    # exceeds 2^53 and the quantized coefficients can diverge (PHASE2 F5b). max_len
    # admits a full 4608-sample 32-bit input (3 header + 4 bytes/sample).
    "fz_float_exact":       dict(bug_class="C", max_len=18448, corpus=("decode/float_seeds",)),
    # readUtf8 accepts non-minimal (overlong) coded frame numbers -- a constructive
    # unit-differential over value x continuation-count; RAW seeds just diversify (V,k).
    "fz_overlong_utf8":     dict(bug_class="C", max_len=64, corpus=("decode/gen_params",)),
    "fz_decode_diff":       dict(bug_class="V",
                                 corpus=(*_DECODE16, "decode/g1_hostile16", "decode/must_reject"),
                                 variants={"large": dict(max_len=131072,
                                     corpus=(*_DECODE16, "decode/g1_hostile16", "decode/must_reject",
                                             "decode/large16")),
                                           "par-window": dict(max_len=1572864,
                                     corpus=("decode/large16",))}),
    "fz_decode_structured": dict(bug_class="V",
                                 corpus=(*_DECODE16, "decode/g1_hostile16", "decode/must_reject"),
                                 variants={"havoc": dict(mutator="plain"),
                                           "large": dict(max_len=131072,
                                     corpus=(*_DECODE16, "decode/g1_hostile16", "decode/must_reject",
                                             "decode/large16"))}),
    "fz_decode_modes":      dict(bug_class="L", max_len=131072,
                                 corpus=(*_DECODE16, "decode/parallel16", "decode/g1_hostile16",
                                         "decode/must_reject"),
                                 variants={"serial": {},
                                           # 6F: max_len=8192 keeps every input at/under
                                           # VM_REF_MAX_INPUT so the fast<->ref lane -- the ONLY
                                           # route through decodeReference and 5 modules of model
                                           # code -- runs on EVERY input at thousands/s. At the
                                           # default 131072 that lane was skipped on nearly every
                                           # input (9/s). serial/par/par-forced still exceed
                                           # parThreshold=65536 to reach the parallel branch.
                                           "small": dict(max_len=8192),
                                           # par exercises byteStepsPar determinism. A hostile
                                           # ~64-131 KB input drives the parallel scanner into
                                           # atomic-refcount contention that is SUPER-LINEAR in thread
                                           # count (~66 CPU-s / 17 s at 4 threads x VM_REPEAT=3), so it
                                           # timed out under full-fleet load and burned the worker.
                                           # It is content- not size-driven, so a max_len cap does not
                                           # help; the lever is thread count. 2 threads still runs the
                                           # parallel branch (Task.spawn / byteStepsPar) and its
                                           # determinism check, at ~7 s for the worst witness -- no
                                           # timeout. par-forced keeps the 4-thread coverage (bounded
                                           # max_len=65600). Eliminates the timeout waste.
                                           "par": dict(env={"LEAN_NUM_THREADS": "2", "VM_REPEAT": "2"}),
                                           # VM_REPEAT 5->3 and an explicit >=60s timeout so the
                                           # benign par-forced timeouts are not swallowed by
                                           # -ignore_timeouts (independent of the fork decision).
                                           "par-forced": dict(max_len=65600, timeout=60,
                                               env={**_PAR, "VM_FORCE_PAR": "1", "VM_REPEAT": "3"})}),
    "fz_encode_diff":       dict(bug_class="V", max_len=65544, corpus=("encode/gen", "encode/shapes"),
                                 variants=dict(_PCM_VARIANT)),
    "fz_encode_validity":   dict(bug_class="V", max_len=65544, corpus=("encode/gen", "encode/shapes"),
                                 variants={"edge": dict(corpus=("encode/gen", "encode/edge")),
                                           **_PCM_VARIANT}),
    # md5 is ~100x faster than the other targets (~21k exec/s), so it is the only
    # one that reaches the Lean-runtime allocator's RSS high-water (~850 B/exec
    # retained, NOT a harness leak -- vinyl_md5 is lean_dec-correct) within a run:
    # at ~3.7M execs peak_rss crosses 3 GB and libFuzzer dumps a false `oom-*`
    # (the offending input reproduces in 0 ms). The -fork parent then respawns the
    # child (RSS resets) -- the intended -fork respawn. A higher limit just makes the
    # recycle rarer; 8 GB on a 125 GB box keeps md5 running ~4x longer between respawns.
    "fz_md5":               dict(bug_class="V", max_len=4096, rss_limit_mb=8000, corpus=("md5",)),
    "fz_metamorphic":       dict(bug_class="L",
                                 corpus=(*_DECODE_ANY_IETF, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"reenc-pcm16": dict(env={"VM_REENC_LANE": "pcm16-fast"}),
                                           "reenc-emit": dict(env={"VM_REENC_LANE": "emit"}),
                                           "large": dict(max_len=131072,
                                     corpus=(*_DECODE_ANY_IETF, "decode/g1_hostile",
                                             "decode/must_reject", "decode/large16"))}),
    # + a max_len=2048 high-throughput sibling (6F): the small-input route through
    #   the model-code decodeReference pair, at ~84/s vs the 4096 default.
    "fz_proven_pairs":      dict(bug_class="L", max_len=4096,
                                 corpus=(*_DECODE, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"small": dict(max_len=2048,
                                                         corpus=("decode/pairs_small",))}),
    # C04 FIXED (2026-08-31): the per-sample AND per-frame encode loops
    # (bitsToByteList/pcm16OfByteList/deinterleaveN, then writeFrames/chunkChannels)
    # are now tail-recursive via @[csimp], so encoding large audio no longer
    # overflows the default 8 MB stack (the only residual is a sub-512 KB
    # writeRiceSeq case, bounded by partition size <=4608, unreachable at 8 MB).
    # The 16 KB cap that existed to avoid crash-looping on the KNOWN overflow is
    # lifted to 65 KB so the round-trip is exercised on large audio too.
    "fz_roundtrip":         dict(bug_class="L", max_len=65536, corpus=("encode/gen", "encode/shapes"),
                                 variants=dict(_PCM_VARIANT)),
    # ffmpeg+libFLAC EMIT-side referee: Vinyl's production-encoder (fast + checked) bytes
    # run through the 3-way decode consensus (wide_diff). Catches an encoder that emits a
    # stream the independent references decode differently. Shares the checked-encode corpus.
    # max_len is capped below fz_roundtrip's 65536: each exec runs two Vinyl encodes (the
    # checked one is a full heuristic search) plus libFLAC/ffmpeg decodes, so smaller inputs
    # buy throughput -- multi-frame shapes are still well within 16 KB.
    "fz_encode_referee":    dict(bug_class="V", max_len=16384, corpus=("encode/gen", "encode/shapes"),
                                 variants=dict(_PCM_VARIANT)),
    # 6G: the encodePcm16_eq proven pair (Encode.encodePcm16 == Unchecked.encode with
    # fastChooser 16). Cap lifted with C04 fixed (see fz_roundtrip).
    "fz_encode_pcm16_eq":   dict(bug_class="L", max_len=65536, corpus=("encode/gen", "encode/edge", "encode/shapes"),
                                 variants=dict(_PCM_VARIANT)),
    "fz_samples_diff":      dict(bug_class="V",
                                 corpus=(*_DECODE_ANY_IETF, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"large": dict(max_len=131072,
                                     corpus=(*_DECODE_ANY_IETF, "decode/g1_hostile",
                                             "decode/must_reject", "decode/large16"))}),
    "fz_self_consistent":   dict(bug_class="L",
                                 corpus=(*_DECODE_ANY_IETF, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"reference-small": dict(max_len=8192)}),
    # + decode/hires so the bps-contradiction probe has bases whose FRAMES carry
    # an EXPLICIT depth code (libFLAC/ffmpeg output); on a Vinyl-image base the
    # frame depth code is 0 ("from STREAMINFO") and rewriting STREAMINFO bps stays
    # coherent, so that probe needs the external-encoder seeds to fire.
    "fz_streaminfo_contradict": dict(bug_class="L",
                                 corpus=(*_DECODE, "decode/hires", "decode/g1_hostile",
                                         "decode/must_reject"),
                                 variants={"large": dict(max_len=131072,
                                     corpus=(*_DECODE, "decode/hires", "decode/g1_hostile",
                                             "decode/must_reject", "decode/large16"))}),
    # + the noncanonical-grammar decode dirs (block-size codes 1-15, channel codes
    # 2-7 / stereo 8-10, sample-rate codes 12-14, every metadata block type): all
    # already committed, ~180 direct Decode.resolveBlockSize/skipSampleRate/readFields/
    # readChannels regions this decode-only target otherwise never sees.
    "fz_trailing_data":     dict(bug_class="V",
                                 corpus=("decode/gen", "decode/hires", "decode/g1_hostile",
                                         "decode/must_reject", "decode/blocksizes", "decode/multichan",
                                         "decode/metablocks", "decode/ref_small"),
                                 variants={"large": dict(max_len=131072,
                                     corpus=("decode/gen", "decode/hires", "decode/g1_hostile",
                                             "decode/must_reject", "decode/blocksizes", "decode/multichan",
                                             "decode/metablocks", "decode/ref_small", "decode/large16"))}),
    # C04 FIXED (2026-08-31): the encode non-tail recursion is retired, so the
    # 16 KB cap that avoided crash-looping on the overflow is lifted to 65 KB;
    # Unchecked.encode of large audio is now overflow-free at the default stack.
    "fz_unchecked_encode":  dict(bug_class="C", max_len=65536, corpus=("encode/gen", "encode/edge", "encode/shapes")),
    # C04: autonomous rediscovery of the encoder non-tail-recursion stack overflow
    # (findings/encoder-stack-overflow-CONFIRMED). Forks a bounded-stack child that
    # runs the SLOW encoder until Stream.writeFrames/chunkChannels (still un-swapped
    # per-frame recursion) overflow. RAW 5-byte geometry selectors (channels,
    # blockSize, samples, stackKB); the real work is in the forked child, so AFL's
    # persistent coverage adds nothing -- libFuzzer only. Catalogue-by-default;
    # FUZZ_STRICT>=1 escalates an overflow to a hard abort. timeout=30 covers the
    # child's fork+exec + 8 s watchdog alarm.
    "fz_encode_stack":      dict(bug_class="C", engines=("libfuzzer",), max_len=64,
                                 timeout=30, corpus=("encode/stack_seeds",)),
}


class ConfigError(Exception):
    pass


@dataclass(frozen=True)
class Target:
    name: str
    summary: str
    input_kind: str
    mutator: str
    bug_class: str
    variants: dict


@dataclass(frozen=True)
class Job:
    target: str
    label: str
    engine: str
    workers: int
    instances: int
    max_len: int
    timeout: int
    rss_limit_mb: int
    mutator: str
    corpus: tuple[str, ...]
    env: dict[str, str]
    binary: Path
    mapsize: int | None
    # input_kind (flac_stream / packed_pcm / raw) decides where format-specific
    # tooling applies: the FLAC dictionary + value-profile are scoped to
    # flac_stream only (a FLAC dict pollutes RAW parameter blocks, Phase 3D).
    input_kind: str = "raw"


def _parse_macro(src: str, field: str, pattern: str) -> str:
    m = re.search(rf"\.{field}\s*=\s*{pattern}", src)
    if not m:
        raise ConfigError(f"FUZZ_TARGET: could not read .{field}")
    return m.group(1)


def discover_targets() -> dict[str, Target]:
    """Read every targets/*.c FUZZ_TARGET macro; cross-check against TARGETS."""
    out: dict[str, Target] = {}
    for c in sorted(TARGETS_DIR.glob("*.c")):
        src = c.read_text()
        name = _parse_macro(src, "name", r'"([^"]+)"')
        if name != c.stem:
            raise ConfigError(f"{c.name}: FUZZ_TARGET name {name!r} != basename")
        if name not in TARGETS:
            raise ConfigError(f"{name}: no run config in fleet/config.py TARGETS")
        out[name] = Target(
            name=name, summary=_parse_macro(src, "summary", r'"([^"]+)"'),
            input_kind=_KIND[_parse_macro(src, "input_kind", r"FUZZ_INPUT_(\w+)")],
            mutator=_MUT[_parse_macro(src, "default_mutator", r"FUZZ_MUT_(\w+)")],
            bug_class=TARGETS[name].get("bug_class", "?"),
            variants=TARGETS[name].get("variants", {}))
    stray = set(TARGETS) - set(out)
    if stray:
        raise ConfigError(f"TARGETS has entries with no targets/*.c: {sorted(stray)}")
    return out


def resolve(t: Target, variant: str) -> dict:
    """DEFAULTS + target run config + variant override (env merges, else replace)."""
    rc = TARGETS[t.name]
    if variant not in ("default", *t.variants):
        raise ConfigError(f"{t.name}: unknown variant {variant!r}")
    cfg = {**DEFAULTS, "mutator": t.mutator, **{k: v for k, v in rc.items() if k != "variants"}}
    cfg["env"] = dict(DEFAULTS["env"])
    if variant != "default":
        for k, v in t.variants[variant].items():
            if k == "env":
                cfg["env"].update(v)
            else:
                cfg[k] = v
    return cfg


def make_job(t: Target, variant: str, engine: str, workers: int, instances: int,
             require_binaries: bool = True) -> Job:
    cfg = resolve(t, variant)
    if engine not in cfg["engines"]:
        raise ConfigError(f"{t.name}: engine {engine!r} not in {cfg['engines']}")
    label = t.name if variant == "default" else f"{t.name}.{variant}"
    binary = BUILD_BIN / f"{t.name}.{_ENGINE_SUFFIX[engine]}"
    corpus = tuple(cfg["corpus"])
    _validate_corpus(label, corpus)
    mapsize = None
    # The AFL map size is a BUILD artifact. `make validate` resolves campaigns on
    # a possibly-unbuilt tree, so it must not require the .mapsize file to exist;
    # only an actual run (require_binaries) does.
    if engine == "afl" and require_binaries:
        # AFL's real map size is probed at link time; a missing/too-small value
        # fails rather than silently falling back to AFL's 64 KiB default.
        ms = BUILD_BIN / f"{t.name}.afl.mapsize"
        if not ms.exists():
            raise ConfigError(f"{label}: {ms.name} absent -- build {t.name}.afl first")
        mapsize = int(ms.read_text().strip())
        if mapsize < 65536:
            raise ConfigError(f"{label}: AFL_MAP_SIZE={mapsize} < 65536")
    return Job(target=t.name, label=label, engine=engine, workers=int(workers),
               instances=int(instances), max_len=int(cfg["max_len"]), timeout=int(cfg["timeout"]),
               rss_limit_mb=int(cfg["rss_limit_mb"]), mutator=cfg["mutator"], corpus=corpus,
               env={k: str(v) for k, v in cfg["env"].items()}, binary=binary, mapsize=mapsize,
               input_kind=t.input_kind)


def _validate_corpus(label: str, corpus: tuple[str, ...]) -> None:
    """Every declared dir must exist and the bundle must hold at least one seed."""
    if not corpus:
        raise ConfigError(f"{label}: no corpus declared")
    total = 0
    for entry in corpus:
        d = CORPUS_DIR / entry
        if not d.is_dir():
            raise ConfigError(f"{label}: corpus dir {entry!r} does not exist")
        total += sum(1 for f in d.iterdir() if f.is_file())
    if total == 0:
        raise ConfigError(f"{label}: corpus {list(corpus)} resolves to 0 seed files")


def job_cores(j: Job) -> int:
    """A job's core footprint is its process/thread count times the Lean thread
    pool it spins up -- a workers=6 job with LEAN_NUM_THREADS=4 pins 24 cores, not
    6. libFuzzer parallelizes by -workers, AFL by -M/-S instances."""
    procs = j.instances if j.engine == "afl" else j.workers
    return procs * max(1, int(j.env.get("LEAN_NUM_THREADS", "1")))


def load_campaign(name: str, require_binaries: bool = True) -> tuple[dict, list[Job]]:
    """Resolve one [campaign.<name>] from config/fleet.toml into (meta, [Job])."""
    with open(FLEET_TOML, "rb") as f:
        doc = tomllib.load(f)
    camp = doc.get("campaign", {}).get(name)
    if camp is None:
        have = ", ".join(doc.get("campaign", {})) or "-"
        raise ConfigError(f"no campaign {name!r} in {FLEET_TOML.name} (have: {have})")
    targets = discover_targets()
    meta = {"budget_cores": int(camp.get("budget_cores", 24)),
            "default_seconds": int(camp.get("default_seconds", 1800))}
    # Campaign-level env applied to every job (e.g. FUZZ_STRICT=2 for a strict
    # regression campaign that escalates the catalogue-by-default detectors).
    camp_env = {k: str(v) for k, v in camp.get("env", {}).items()}
    jobs: list[Job] = []
    for s in camp.get("job", []):
        tname = s.get("target")
        if tname not in targets:
            raise ConfigError(f"campaign {name}: unknown target {tname!r}")
        job = make_job(targets[tname], s.get("variant", "default"),
                       s.get("engine", "libfuzzer"), s.get("workers", 1), s.get("instances", 1),
                       require_binaries=require_binaries)
        if camp_env:
            job = replace(job, env={**job.env, **camp_env})
        if "corpus" in s:  # per-job corpus override (e.g. curated regress set for strict)
            corpus = tuple(s["corpus"])
            _validate_corpus(job.label, corpus)
            job = replace(job, corpus=corpus)
        jobs.append(job)
    used = sum(job_cores(j) for j in jobs)
    if used > meta["budget_cores"]:
        raise ConfigError(f"campaign {name}: {used} cores > budget_cores {meta['budget_cores']}")
    return meta, jobs


def campaign_names() -> list[str]:
    with open(FLEET_TOML, "rb") as f:
        return sorted(tomllib.load(f).get("campaign", {}))


def validate_all() -> int:
    """`make validate`: macros parse, TARGETS match, every campaign resolves."""
    try:
        targets = discover_targets()
        print(f"OK: {len(targets)} targets, macros parsed, run config matched.")
        for name in campaign_names():
            meta, jobs = load_campaign(name, require_binaries=False)
            print(f"OK: campaign {name}: {len(jobs)} jobs "
                  f"({sum(job_cores(j) for j in jobs)}/{meta['budget_cores']} cores)")
    except ConfigError as e:
        print(f"VALIDATE FAIL: {e}", file=sys.stderr)
        return 1
    return 0
