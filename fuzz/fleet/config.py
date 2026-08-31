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
_MUT = {"CRC": "crc", "PLAIN": "plain"}

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
# All <=24 KB so they also feed fz_decode_modes' reference lane (VM_REF_MAX_INPUT=24576).
_DECODE = ("decode/gen", "decode/wide", "decode/regress",
           "decode/blocksizes", "decode/multichan", "decode/metablocks")
# The 16-bit-GATED decode differentials (fz_decode_diff/structured/modes) DEC_SKIP
# every non-16-bit stream after a full readMeta + whole-input alloc, so they get
# the 16-bit SUBSET of wide (decode/wide16) instead of the full multi-depth bundle
# -- ~3/4 of wide is non-16-bit, wasted on them (F3). corpus_gen.sh --wide carves
# wide16 from wide, so it never drifts.
_DECODE16 = ("decode/gen", "decode/wide16", "decode/regress",
             "decode/blocksizes", "decode/multichan", "decode/metablocks")
# The any-depth oracles (3-way samples diff, self-consistency, metamorphic) also
# get the external non-16-bit / LPC-13-32 seeds; the 16-bit-gated targets would
# only SKIP them, and the small-max_len proven-pairs target does not want the
# 157 KB IETF seed, so hires is scoped to the targets that exercise it.
_DECODE_ANY = (*_DECODE, "decode/hires")
# 6C: the IETF flac-test-files conformance corpus (deps_fetch.sh --ietf). subset +
# uncommon are libFLAC/ffmpeg-produced streams across depths/rates Vinyl's own
# encoder never emits -- the 12/20-bit files close COVERAGE.md's unverified "decoded
# too" claim via fz_samples_diff's ffmpeg referee. Added only to the any-depth
# decoders; the 6E sample cap bounds any large IETF file.
_IETF = ("external/flac-test-files/subset", "external/flac-test-files/uncommon")
_DECODE_ANY_IETF = (*_DECODE_ANY, *_IETF)
_PAR = {"LEAN_NUM_THREADS": "4"}
TARGETS: dict[str, dict] = {
    "fz_gen_roundtrip":     dict(bug_class="V", max_len=64,
                                 corpus=("decode/gen_params",)),
    "fz_emit_conformance":  dict(bug_class="C", max_len=64,
                                 corpus=("decode/gen_params",)),
    "fz_residual_bound":    dict(bug_class="C", max_len=64, corpus=("decode/gen_params",)),
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
    "fz_float_exact":       dict(bug_class="C", max_len=18448, corpus=("decode/gen_params",)),
    # readUtf8 accepts non-minimal (overlong) coded frame numbers -- a constructive
    # unit-differential over value x continuation-count; RAW seeds just diversify (V,k).
    "fz_overlong_utf8":     dict(bug_class="C", max_len=64, corpus=("decode/gen_params",)),
    "fz_decode_diff":       dict(bug_class="V",
                                 corpus=(*_DECODE16, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"large": dict(max_len=131072,
                                     corpus=(*_DECODE16, "decode/g1_hostile", "decode/must_reject",
                                             "decode/large16")),
                                           "par-window": dict(max_len=1572864,
                                     corpus=("decode/large16",))}),
    "fz_decode_structured": dict(bug_class="V",
                                 corpus=(*_DECODE16, "decode/g1_hostile", "decode/must_reject"),
                                 variants={"havoc": dict(mutator="plain"),
                                           "large": dict(max_len=131072,
                                     corpus=(*_DECODE16, "decode/g1_hostile", "decode/must_reject",
                                             "decode/large16"))}),
    "fz_decode_modes":      dict(bug_class="L", max_len=131072,
                                 corpus=(*_DECODE16, "decode/parallel16", "decode/g1_hostile",
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
                                           "par": dict(env={**_PAR, "VM_REPEAT": "3"}),
                                           # VM_REPEAT 5->3 and an explicit >=60s timeout so the
                                           # benign par-forced timeouts are not swallowed by
                                           # -ignore_timeouts (independent of the fork decision).
                                           "par-forced": dict(max_len=65600, timeout=60,
                                               env={**_PAR, "VM_FORCE_PAR": "1", "VM_REPEAT": "3"})}),
    "fz_encode_diff":       dict(bug_class="V", max_len=65544, corpus=("encode/gen", "encode/shapes")),
    "fz_encode_validity":   dict(bug_class="V", max_len=65544, corpus=("encode/gen", "encode/shapes"),
                                 variants={"edge": dict(corpus=("encode/gen", "encode/edge"))}),
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
    # max_len at the 16384 default (not 65536): encoding ~32k samples overflows the
    # Lean stack in bitsToByteList (findings/encoder-stack-overflow-CONFIRMED), which
    # would crash-loop this round-trip target on the KNOWN bug. 16 KB PCM is verified
    # overflow-free and still exercises the full round-trip; large-audio encode is
    # untestable here anyway (that IS the overflow).
    "fz_roundtrip":         dict(bug_class="L", corpus=("encode/gen", "encode/shapes")),
    # 6G: the encodePcm16_eq proven pair (Encode.encodePcm16 == Unchecked.encode with
    # fastChooser 16). 16 KB max_len keeps PCM overflow-free (like fz_roundtrip).
    "fz_encode_pcm16_eq":   dict(bug_class="L", corpus=("encode/gen", "encode/edge", "encode/shapes")),
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
    "fz_trailing_data":     dict(bug_class="V",
                                 corpus=("decode/gen", "decode/hires", "decode/g1_hostile",
                                         "decode/must_reject"),
                                 variants={"large": dict(max_len=131072,
                                     corpus=("decode/gen", "decode/hires", "decode/g1_hostile",
                                             "decode/must_reject", "decode/large16"))}),
    # max_len at the 16384 default (not 65536): Unchecked.encode of ~32k samples
    # overflows the Lean stack in bitsToByteList (findings/encoder-stack-overflow-
    # CONFIRMED). 16 KB PCM is verified overflow-free; the >4608 block-size region
    # this target targets comes from the header bytes, not the PCM length, so the
    # out-of-envelope path is still fully reached.
    "fz_unchecked_encode":  dict(bug_class="C", corpus=("encode/gen", "encode/edge")),
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
