#!/usr/bin/env python3
"""Standing corpus/threshold/seed CI detectors (E3, E4, E5).

  E3  --thresholds : enumerate every codec + harness magic size constant and report
                     whether a config.py variant/seed crosses it, or emit a
                     "needs crossing variant or unsafe-note" warning.
  E4  --corpus     : per target, check each corpus dir's format matches the target's
                     input_kind (flac_stream => fLaC-led; packed_pcm/raw => not), and
                     note the RAW consumed-layout vs max_len.
  E5  --seeds      : verify a sample of committed seeds' structure matches their
                     filename/intent (order-N LPC files, stale-CRC reject seeds) AND
                     that corpus_gen.sh comments asserting a seed feeds a target match
                     what config.py actually wires (the pcm16-parallel stale-comment
                     class).

With no flag it runs all three. Exits nonzero if any hard FAIL is found (a format
mismatch or a comment-vs-config wiring contradiction); softer findings print as WARN.

    python3 cov/lint.py [--thresholds|--corpus|--seeds]
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fleet import config as C  # noqa: E402

REPO = C.FUZZ_ROOT.parent
FUZZ = C.FUZZ_ROOT
NATIVE = REPO / "Flac" / "Native"
COMMON = FUZZ / "common"
TARGETS_C = FUZZ / "targets"
CORPUS_GEN = FUZZ / "scripts" / "corpus_gen.sh"


class Report:
    def __init__(self) -> None:
        self.fail = 0
        self.warn = 0

    def ok(self, msg: str) -> None:
        print(f"  OK    {msg}")

    def note(self, msg: str) -> None:
        print(f"  note  {msg}")

    def warned(self, msg: str) -> None:
        self.warn += 1
        print(f"  WARN  {msg}")

    def failed(self, msg: str) -> None:
        self.fail += 1
        print(f"  FAIL  {msg}")


# --------------------------------------------------------------------------- E3

def _eval_size(expr: str) -> int | None:
    """Evaluate a Lean/C size literal: 16, 1024, `1 <<< 16`, `1u << 20`, `1<<16`."""
    e = re.sub(r"[uUlL]", "", expr.strip()).strip()
    e = e.split("--")[0].split("//")[0].strip()  # drop trailing comment
    m = re.fullmatch(r"(\d+)\s*(?:<<<|<<)\s*(\d+)", e)
    if m:
        return int(m.group(1)) << int(m.group(2))
    m = re.fullmatch(r"(\d+)", e)
    return int(m.group(1)) if m else None


def _grep_value(path: Path, pat: str) -> int | None:
    if not path.exists():
        return None
    m = re.search(pat, path.read_text())
    return _eval_size(m.group(1)) if m else None


def _resolved_maxlens() -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for t in C.discover_targets().values():
        out[t.name] = {v: int(C.resolve(t, v)["max_len"]) for v in ("default", *t.variants)}
    return out


def _corpus_of(tname: str) -> set[str]:
    t = C.discover_targets()[tname]
    entries: set[str] = set()
    for v in ("default", *t.variants):
        entries.update(C.resolve(t, v)["corpus"])
    return entries


def check_thresholds(r: Report) -> None:
    print("# E3 size-threshold audit\n")
    ml = _resolved_maxlens()
    flac_targets = {n for n, t in C.discover_targets().items() if t.input_kind == "flac_stream"}
    flac_maxlens = [v for n in flac_targets for v in ml[n].values()]
    global_max = max((v for d in ml.values() for v in d.values()), default=0)
    # A size threshold is only TRULY crossed when a real committed seed reaches it,
    # not merely when some max_len is configured that large -- E3 must not false-green.
    _tg = C.discover_targets()
    _seed_dirs = {e for n in flac_targets for v in ("default", *_tg[n].variants)
                  for e in C.resolve(_tg[n], v)["corpus"]}
    largest_seed = 0
    for _e in _seed_dirs:
        _d = C.CORPUS_DIR / _e
        if _d.is_dir():
            for _f in _d.iterdir():
                try:
                    if _f.is_file():
                        largest_seed = max(largest_seed, _f.stat().st_size)
                except OSError:
                    pass

    par = _grep_value(NATIVE / "Decode.lean", r"def\s+parThreshold\s*:\s*Nat\s*:=\s*([^\n]+)")
    syncw = _grep_value(NATIVE / "Decode.lean", r"def\s+syncWindow\s*:\s*Nat\s*:=\s*([^\n]+)")
    minfb = _grep_value(NATIVE / "Decode.lean", r"def\s+minFrameBytes\s*:\s*Nat\s*:=\s*([^\n]+)")
    maxst = _grep_value(NATIVE / "Decode.lean", r"def\s+maxStepTasks\s*:\s*Nat\s*:=\s*([^\n]+)")
    pcmw = _grep_value(NATIVE / "Stream.lean", r"def\s+pcmWindow\s*:\s*Nat\s*:=\s*([^\n]+)")
    vpair = _grep_value(TARGETS_C / "fz_proven_pairs.c", r"#define\s+VM_PAIR_MAX\s+([0-9xu <]+)")
    vref = _grep_value(TARGETS_C / "fz_decode_modes.c", r"#define\s+VM_REF_MAX_INPUT\s+([0-9xu <]+)")
    genmax = _grep_value(COMMON / "vinyl_gen.c", r"#define\s+GEN_MAX_SAMPLES\s+([0-9xu <]+)")
    scap = _grep_value(COMMON / "vinyl_checks.h", r"#define\s+VINYL_ENCODE_SAMPLE_CAP\s+([0-9xu <]+)")
    bcap = _grep_value(COMMON / "vinyl_checks.h", r"#define\s+VINYL_ENCODE_BYTE_CAP\s+([0-9xu <]+)")
    fmax = _grep_value(COMMON / "fuzz_main.c", r"g_max_samples\s*=\s*([0-9xu <]+)")

    modes = ml.get("fz_decode_modes", {})
    ref_reached = any(v <= (vref or 0) for v in modes.values())
    par16_wired = "decode/parallel16" in _corpus_of("fz_decode_modes") if "fz_decode_modes" in ml else False

    rows = [
        ("parThreshold", par, "Flac/Native/Decode.lean",
         largest_seed >= (par or 1 << 62),
         f"largest committed seed is {largest_seed}B (>= parThreshold; parallel branch reached on replay)"
         if largest_seed >= (par or 1 << 62) else
         f"largest committed seed is only {largest_seed}B < parThreshold -- add a >={par}B seed"),
        ("syncWindow", syncw, "Flac/Native/Decode.lean",
         largest_seed >= (syncw or 1 << 62),
         f"largest committed seed is {largest_seed}B (>= syncWindow)"
         if largest_seed >= (syncw or 1 << 62) else
         f"largest committed seed is only {largest_seed}B; syncWindow needs a >{syncw}B stream (B1 par-window seed)"),
        ("pcmWindow", pcmw, "Flac/Native/Stream.lean",
         par16_wired,
         "crossed via decode/parallel16 (80k-sample stream) wired into fz_decode_modes"
         if par16_wired else "needs an >65536-sample stream wired to a decodePcm16A consumer"),
        ("minFrameBytes", minfb, "Flac/Native/Decode.lean",
         False,
         "MEASURE, do NOT patch (Z6 security threshold): run a minimal-frame stream "
         "through fz_decode_modes.par-forced and read ran=0 -- unsafe-note, not a crossing"),
        ("maxStepTasks", maxst, "Flac/Native/Decode.lean",
         global_max >= (maxst or 0) * 16,
         "needs a large multi-candidate stream (decode/large16 variants) to exceed the task cap"),
        ("VM_PAIR_MAX", vpair, "targets/fz_proven_pairs.c",
         False,
         "HARNESS CAP: input truncated to <= VM_PAIR_MAX; raising max_len cannot cross it "
         "(C3: a compact decode/pairs_small corpus is the lever, not max_len)"),
        ("VM_REF_MAX_INPUT", vref, "targets/fz_decode_modes.c",
         ref_reached,
         "fz_decode_modes.small (max_len<=8192) keeps every input under the cap so the "
         "fast<->reference lane runs" if ref_reached else "needs a <=8192 max_len variant"),
        ("GEN_MAX_SAMPLES", genmax, "common/vinyl_gen.c",
         False,
         "generator sample cap; the RAW gen targets cannot emit more -- unsafe-note "
         "(C2: raise behind a low-output guard to reach variable-blocking paths)"),
        ("VINYL_ENCODE_SAMPLE_CAP", scap, "common/vinyl_checks.h",
         global_max >= (scap or 1 << 62),
         "encode-based cross-checks skip audio above this sample count (throughput guard); "
         "large decode corpora exceed it by design -- unsafe-note"),
        ("VINYL_ENCODE_BYTE_CAP", bcap, "common/vinyl_checks.h",
         False,
         "estimated-output byte guard paired with the sample cap -- unsafe-note"),
        ("FUZZ_MAX_SAMPLES", fmax, "common/fuzz_main.c",
         False,
         "default per-input sample gate (env-overridable, 0 disables) -- unsafe-note"),
    ]
    print(f"{'constant':24s} {'value':>10s}  status")
    for name, val, where, crossed, why in rows:
        if val is None:
            r.warned(f"{name:22s} value NOT LOCATED in {where} -- audit stale")
            continue
        if crossed:
            r.ok(f"{name:22s} {val:>10d}  CROSSED  ({why})  [{where}]")
        else:
            r.warned(f"{name:22s} {val:>10d}  needs-crossing/unsafe-note: {why}  [{where}]")


# --------------------------------------------------------------------------- E4

# RAW targets carve their input differently; kind alone misses this (fable). Value:
# (human description, consumed-prefix bytes or None for variable).
RAW_CONSUMED: dict[str, tuple[str, int | None]] = {
    "fz_gen_roundtrip": ("G1 8-byte packed header (bps/ch/pop/bs|chooser/ns/sr); PCM synthesized", 8),
    "fz_emit_conformance": ("G1 8-byte packed header via vinyl_gen_encode", 8),
    "fz_residual_bound": ("G1 8-byte packed header via vinyl_gen_encode", 8),
    "fz_encode_pair": ("G1 8-byte packed header via vinyl_gen_encode_pair", 8),
    "fz_overlong_utf8": ("V = first 5 bytes (36-bit) + k = data[5]%7 -> 6 bytes consumed", 6),
    "fz_float_exact": ("3-byte header (bps/order/prec) + 4 bytes/sample float payload", None),
    "fz_md5": ("opaque byte message (whole input hashed)", None),
}


def _lead4(p: Path) -> bytes:
    try:
        with p.open("rb") as f:
            return f.read(4)
    except OSError:
        return b""


def _scan_dir(d: Path, sample: int = 200) -> tuple[int, int, int]:
    """(n_files, n_flac_led, n_empty) over up to `sample` files."""
    n = flac = empty = 0
    for p in sorted(d.rglob("*")):
        if not p.is_file():
            continue
        n += 1
        sz = p.stat().st_size
        if sz == 0:
            empty += 1
        elif _lead4(p) == b"fLaC":
            flac += 1
        if n >= sample:
            break
    return n, flac, empty


def check_corpus(r: Report) -> None:
    print("# E4 corpus format / consumed-layout lint\n")
    targets = C.discover_targets()
    cache: dict[Path, tuple[int, int, int]] = {}
    for n in sorted(targets):
        t = targets[n]
        entries = _corpus_of(n)
        for entry in sorted(entries):
            d = C.CORPUS_DIR / entry
            if not d.is_dir():
                r.note(f"{n}: corpus dir {entry!r} absent (regenerate corpus)")
                continue
            if d not in cache:
                cache[d] = _scan_dir(d)
            nf, flac, empty = cache[d]
            if nf == 0:
                r.note(f"{n}: {entry} empty (0 files)")
                continue
            # Format is judged by the DOMINANT class: a decode corpus legitimately
            # carries a minority of non-fLaC reject/conformance seeds, and a PCM
            # corpus must not be dominated by FLAC streams. must_reject is exempt
            # (deliberately malformed). A wrong-format dir (a PCM corpus wired to a
            # flac_stream target, or vice-versa) flips the majority and FAILs.
            exempt = d.name == "must_reject"
            nonempty = nf - empty
            frac = flac / nonempty if nonempty else 0.0
            if t.input_kind == "flac_stream":
                if exempt:
                    r.ok(f"{n} [flac_stream]: {entry} exempt (must_reject: malformed by design)")
                elif nonempty == 0:
                    r.note(f"{n} [flac_stream]: {entry} all {empty} files empty")
                elif frac >= 0.5:
                    tail = f" ({nonempty - flac} non-fLaC reject/conformance seeds)" if flac < nonempty else ""
                    r.ok(f"{n} [flac_stream]: {entry} {flac}/{nonempty} fLaC-led{tail}")
                else:
                    r.failed(f"{n} [flac_stream]: {entry} only {flac}/{nonempty} fLaC-led "
                             f"(a PCM/param corpus wired to a flac_stream target?)")
            else:  # packed_pcm / raw
                if frac >= 0.5:
                    r.failed(f"{n} [{t.input_kind}]: {entry} {flac}/{nonempty} fLaC-led "
                             f"(FLAC streams in a PCM/param corpus)")
                elif flac:
                    r.warned(f"{n} [{t.input_kind}]: {entry} has {flac}/{nonempty} fLaC-led files "
                             f"(unexpected in a PCM/param corpus)")
                else:
                    r.ok(f"{n} [{t.input_kind}]: {entry} {nonempty} non-fLaC files (PCM/param)")
        # consumed-layout note + max_len sanity for RAW targets
        if n in RAW_CONSUMED:
            desc, consumed = RAW_CONSUMED[n]
            mx = int(C.resolve(t, "default")["max_len"])
            r.note(f"{n} consumed-layout: {desc}")
            if consumed is not None and mx > max(64, consumed * 8):
                r.warned(f"{n}: max_len={mx} >> {consumed}-byte consumed prefix "
                         f"(bytes past offset {consumed} are unused; mutation there is wasted)")


# --------------------------------------------------------------------------- E5

def _flac() -> str | None:
    from shutil import which
    return which("flac")


def _lpc_orders(path: Path) -> list[int] | None:
    flac = _flac()
    if not flac:
        return None
    p = subprocess.run([flac, "-a", "--stdout", "-s", str(path)],
                       capture_output=True, text=True)
    orders = [int(m) for m in re.findall(r"type=LPC\s+order=(\d+)", p.stdout + p.stderr)]
    return orders


def _crc8(bs: bytes) -> int:
    c = 0
    for x in bs:
        c ^= x
        for _ in range(8):
            c = ((c << 1) ^ 0x07) & 0xFF if c & 0x80 else (c << 1) & 0xFF
    return c


def _frame_start(b: bytes) -> int | None:
    """Byte offset of the first audio frame (after fLaC + metadata blocks)."""
    if b[:4] != b"fLaC":
        return None
    pos = 4
    while pos + 4 <= len(b):
        last = b[pos] & 0x80
        length = (b[pos + 1] << 16) | (b[pos + 2] << 8) | b[pos + 3]
        pos += 4 + length
        if last:
            return pos
    return None


def _header_crc_stale(path: Path) -> bool | None:
    """True if the frame-header CRC-8 does not match a recomputation (a stale CRC
    that rejects before the intended reserved-code branch). None if unparseable."""
    b = path.read_bytes()
    fs = _frame_start(b)
    if fs is None or fs + 4 >= len(b):
        return None
    if b[fs] != 0xFF or (b[fs + 1] & 0xF8) != 0xF8:
        return None
    bs_code = (b[fs + 2] >> 4) & 0xF
    sr_code = b[fs + 2] & 0xF
    b0 = b[fs + 4]
    ones = 0
    while ones < 8 and (b0 & (0x80 >> ones)):
        ones += 1
    utf8_len = 1 if ones == 0 else ones
    extra_bs = {6: 1, 7: 2}.get(bs_code, 0)
    extra_sr = {12: 1, 13: 2, 14: 2}.get(sr_code, 0)
    crc_pos = fs + 4 + utf8_len + extra_bs + extra_sr
    if crc_pos >= len(b):
        return None
    return _crc8(b[fs:crc_pos]) != b[crc_pos]


def check_seeds(r: Report) -> None:
    print("# E5 seed-structure + comment<->wiring verification\n")
    mr = C.CORPUS_DIR / "decode" / "must_reject"
    hires = C.CORPUS_DIR / "decode" / "hires"

    # (a) LPC-order claim in a filename vs the actual decoded order.
    if _flac() is None:
        r.note("flac CLI absent -- LPC-order seed checks skipped")
    else:
        for d in (hires, C.CORPUS_DIR / "decode"):
            if not d.is_dir():
                continue
            for p in sorted(d.rglob("*lpc[0-9]*")):
                m = re.search(r"lpc(\d+)", p.name)
                if not m or not p.is_file():
                    continue
                claim = int(m.group(1))
                orders = _lpc_orders(p)
                if not orders:
                    r.note(f"{p.name}: no LPC subframe decoded (cannot verify order {claim})")
                    continue
                got = max(orders)
                if got != claim:
                    r.warned(f"{p.name}: filename claims LPC order {claim} but actual max "
                             f"order is {got} (mislabeled seed -- regenerate/rename; A4b)")
                else:
                    r.ok(f"{p.name}: LPC order {got} matches name")
            break  # only the first existing dir level

    # (b) stale header CRC-8 on the reserved-channel-code reject seeds.
    if mr.is_dir():
        checked = 0
        for p in sorted(mr.glob("13_channel_code_*")):
            stale = _header_crc_stale(p)
            checked += 1
            if stale is None:
                r.note(f"{p.name}: frame header unparseable (cannot check CRC-8)")
            elif stale:
                r.warned(f"{p.name}: frame-header CRC-8 is STALE (does not match recomputation) "
                         f"-- rejects in readHeader before the reserved-channel branch; regenerate (A4b)")
            else:
                r.ok(f"{p.name}: header CRC-8 recomputes correctly")
        if checked == 0:
            r.note("no 13_channel_code_* reject seeds present")

    # (c) corpus_gen.sh comment asserts a seed feeds a target -> config must wire it.
    _check_comment_wiring(r)


_FEED = re.compile(r"\b(feed|feeds|fed|feeding|wire|wires|wired|consum\w+|driv\w+|reads?)\b", re.I)
_NEG = re.compile(r"\b(not|never|no|excludes?|without)\b|n't", re.I)
_FZ = re.compile(r"\bfz_[a-z0-9_]+\b")
_CORPUS_TOK = re.compile(r"corpus/([A-Za-z0-9_./-]+)")


def _norm_entry(tok: str) -> str:
    tok = re.sub(r"/\*+$", "", tok.rstrip("/"))
    parts = tok.split("/")
    if parts and "." in parts[-1]:      # a file path -> its dir
        parts = parts[:-1]
    return "/".join(parts)


def _gen_functions(text: str) -> dict[str, str]:
    """{function_name: body} for each `gen_xxx() { ... }` in corpus_gen.sh."""
    out: dict[str, str] = {}
    for m in re.finditer(r"^(gen_\w+)\(\)\s*\{", text, re.M):
        name = m.group(1)
        depth, i, start = 0, m.end() - 1, m.end()
        while i < len(text):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    out[name] = text[start:i]
                    break
            i += 1
    return out


def _check_comment_wiring(r: Report) -> None:
    if not CORPUS_GEN.exists():
        r.note("corpus_gen.sh absent -- comment<->wiring check skipped")
        return
    targets = C.discover_targets()
    funcs = _gen_functions(CORPUS_GEN.read_text())
    any_claim = False
    for fname, body in funcs.items():
        entries = {_norm_entry(t) for t in _CORPUS_TOK.findall(body)}
        entries = {e for e in entries if e}
        claimed: set[str] = set()
        for line in body.splitlines():
            if not _FEED.search(line) or _NEG.search(line):
                continue
            for fz in _FZ.findall(line):
                if fz in targets:
                    claimed.add(fz)
        for fz in sorted(claimed):
            any_claim = True
            wired = _corpus_of(fz)
            if entries & wired:
                r.ok(f"{fname}: comment feeds {fz} and config wires {sorted(entries & wired)}")
            else:
                r.failed(f"{fname}: comment asserts a seed feeds {fz}, but config wires NONE of "
                         f"{sorted(entries)} into {fz} (stale-comment / unwired class; V8)")
    if not any_claim:
        r.note("no positive seed->target feed assertions found in corpus_gen.sh comments")


# --------------------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--thresholds", action="store_true", help="E3 only")
    ap.add_argument("--corpus", action="store_true", help="E4 only")
    ap.add_argument("--seeds", action="store_true", help="E5 only")
    args = ap.parse_args()
    run_all = not (args.thresholds or args.corpus or args.seeds)

    r = Report()
    if args.thresholds or run_all:
        check_thresholds(r)
        print()
    if args.corpus or run_all:
        check_corpus(r)
        print()
    if args.seeds or run_all:
        check_seeds(r)
        print()

    print(f"lint: {r.fail} FAIL, {r.warn} WARN")
    return 1 if r.fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
