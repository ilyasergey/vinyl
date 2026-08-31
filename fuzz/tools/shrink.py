#!/usr/bin/env python3
"""Structure-aware delta-debugger for Vinyl FLAC reproducers.

Given a .flac reproducer and a "still interesting" predicate command, shrink the
input while preserving the interesting behaviour. "Interesting" == the predicate
command exits non-zero OR is killed by a signal (a crash) on the candidate file.

    shrink.py <reproducer.flac> [options] -- <cmd ...  @@ ...>

`@@` in the command is replaced by the path of the candidate file under test
(appended as the last argument if `@@` is absent). Example:

    shrink.py repro.flac -- vinyl --decode-fast @@ /tmp/out

Reduction strategy, applied in order and repeated to a fixpoint:
  1. drop whole trailing frames
  2. drop metadata blocks (keeping STREAMINFO unless the predicate allows more)
  3. shrink frame bodies  (cut the largest reducible structural unit -- the
     residual bit-soup of each frame -- with a halving chunk size)
  4. byte-level ddmin      (classic Zeller/Hildebrandt minimisation)

After every structural edit that would invalidate a CRC, the candidate is passed
through the compiled `tools/flac_repair` (a thin CLI over flac_rescan_repair in
fuzz/common/flac_struct.c): the frame walker recomputes each frame's true end,
fixes the CRC-8 over the header, zeroes byte-alignment padding, and writes the
CRC-16 at the frame end -- so every shrunk stream stays CRC-valid, exactly the
invariant the mutator maintains. This is Phase-4 dedup: the CRC and bit-level
walk live ONCE, in C, and this driver shells out to them instead of carrying a
second Python port. Pass --no-repair when the bug depends on an already-broken
CRC. Frame boundaries are located by a lightweight structural header scan (sync +
code-field validity only -- no CRC, no residual decode); the repaired stream and
the predicate are the source of truth.
"""

import argparse
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FUZZ = os.path.dirname(HERE)
# The compiled repair CLI (make tools). Overridable for out-of-tree builds.
FLAC_REPAIR = os.environ.get("FLAC_REPAIR_BIN") or os.path.join(FUZZ, "build", "bin", "flac_repair")


def repair(data: bytes) -> bytes:
    """Shell out to tools/flac_repair (stdin->stdout). Returns data unchanged if
    the tool is missing or fails, so a shrink run degrades rather than aborts."""
    try:
        p = subprocess.run([FLAC_REPAIR], input=data, stdout=subprocess.PIPE)
    except FileNotFoundError:
        sys.stderr.write(
            f"shrink.py: {FLAC_REPAIR} not found -- run `make tools` (or set FLAC_REPAIR_BIN)\n"
        )
        sys.exit(2)
    return p.stdout if p.returncode == 0 else data


# ============================================= lightweight structural scan
# Frame/metadata *location* only -- offsets and code-field validity, no CRC and
# no residual bit walk (those live in C now). Just enough to know where frames
# and metadata blocks begin so the reduction can cut on structural boundaries.


def _utf8_len(b: int) -> int:
    if b < 0x80:
        return 1
    if (b & 0xE0) == 0xC0:
        return 2
    if (b & 0xF0) == 0xE0:
        return 3
    if (b & 0xF8) == 0xF0:
        return 4
    if (b & 0xFC) == 0xF8:
        return 5
    if (b & 0xFE) == 0xFC:
        return 6
    if b == 0xFE:
        return 7
    return 0


def _header_len(b: bytes, p: int) -> int | None:
    """Bytes of frame header before the CRC-8, or None if `p` is not a
    structurally valid frame sync. Mirrors flac_hdr_parse_core's offset rules
    (common/flac_bits.h) without the CRC or the body walk."""
    n = len(b)
    if p + 5 > n:
        return None
    if b[p] != 0xFF or (b[p + 1] & 0xFE) != 0xF8:
        return None
    bsc = b[p + 2] >> 4
    src = b[p + 2] & 0xF
    chc = b[p + 3] >> 4
    bpc = (b[p + 3] >> 1) & 7
    if bsc == 0 or src == 15 or chc > 10 or bpc == 3 or (b[p + 3] & 1):
        return None
    u = _utf8_len(b[p + 4])
    if not u or p + 4 + u > n:
        return None
    for i in range(1, u):
        if (b[p + 4 + i] & 0xC0) != 0x80:
            return None
    hlen = 4 + u + (1 if bsc == 6 else 2 if bsc == 7 else 0) + (1 if src == 12 else 2 if src in (13, 14) else 0)
    if p + hlen + 1 > n:
        return None
    return hlen


def meta_end(b: bytes) -> int:
    n = len(b)
    if n < 4 or b[:4] != b"fLaC":
        return 0
    p = 4
    while p + 4 <= n:
        last = b[p] & 0x80
        ln = (b[p + 1] << 16) | (b[p + 2] << 8) | b[p + 3]
        if p + 4 + ln > n:
            return p
        p += 4 + ln
        if last:
            break
    return p


def frames(b: bytes) -> list[tuple[int, int, int]]:
    """(start, end, hlen) per frame, end == next frame start (or EOF). Frames are
    located by scanning for the next structurally valid sync after each header."""
    n = len(b)
    p = meta_end(b)
    if p == 0 or p >= n:
        return []
    starts: list[tuple[int, int]] = []
    while p + 5 <= n:
        h = _header_len(b, p)
        if h is None:
            p += 1
            continue
        starts.append((p, h))
        q = p + h + 1
        while q + 5 <= n and _header_len(b, q) is None:
            q += 1
        p = q
    out: list[tuple[int, int, int]] = []
    for i, (s, h) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else n
        out.append((s, end, h))
    return out


def metadata_blocks(b: bytes) -> list[tuple[int, int, int, bool]]:
    """(offset, total_len, type, is_last) for each metadata block."""
    n = len(b)
    if n < 4 or b[:4] != b"fLaC":
        return []
    out: list[tuple[int, int, int, bool]] = []
    p = 4
    while p + 4 <= n:
        last = bool(b[p] & 0x80)
        typ = b[p] & 0x7F
        ln = (b[p + 1] << 16) | (b[p + 2] << 8) | b[p + 3]
        if p + 4 + ln > n:
            break
        out.append((p, 4 + ln, typ, last))
        p += 4 + ln
        if last:
            break
    return out


# ======================================================= predicate harness
class Predicate:
    def __init__(self, cmd: list[str], timeout: float, do_repair: bool, work_dir: str):
        self.cmd = cmd
        self.timeout = timeout
        self.do_repair = do_repair
        self.work_dir = work_dir
        self.calls = 0

    def _materialise(self, data: bytes) -> bytes:
        return repair(data) if self.do_repair else data

    def interesting(self, data: bytes) -> bytes | None:
        """Return the (repaired) bytes if still interesting, else None."""
        payload = self._materialise(data)
        fd, path = tempfile.mkstemp(suffix=".flac", dir=self.work_dir)
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(payload)
            args = [path if a == "@@" else a for a in self.cmd]
            if "@@" not in self.cmd:
                args = args + [path]
            self.calls += 1
            try:
                r = subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=self.timeout)
            except subprocess.TimeoutExpired:
                return None  # a hang is treated as NOT interesting (conservative)
            return payload if r.returncode != 0 else None
        finally:
            os.unlink(path)


# ============================================================== strategies
def drop_trailing_frames(data: bytes, pred: Predicate) -> bytes:
    changed = True
    while changed:
        changed = False
        fr = frames(data)
        if len(fr) < 2:
            break
        # Largest cut first: try to keep only the first k frames.
        for k in range(1, len(fr)):
            cand = data[: fr[k][0]]
            got = pred.interesting(cand)
            if got is not None:
                data = got
                changed = True
                break
    return data


def drop_metadata_blocks(data: bytes, pred: Predicate) -> bytes:
    changed = True
    while changed:
        changed = False
        blocks = metadata_blocks(data)
        if not blocks:
            break
        # Prefer dropping non-STREAMINFO blocks; the predicate is the final judge.
        order = sorted(range(len(blocks)), key=lambda i: blocks[i][2] == 0)
        for i in order:
            off, ln, _typ, _last = blocks[i]
            body = bytearray(data[4:])  # everything after fLaC
            del body[off - 4 : off - 4 + ln]
            rebuilt = _rebuild_meta_last_flag(b"fLaC" + bytes(body))
            got = pred.interesting(rebuilt)
            if got is not None:
                data = got
                changed = True
                break
    return data


def _rebuild_meta_last_flag(data: bytes) -> bytes:
    blocks = metadata_blocks(data)
    if not blocks:
        return data
    out = bytearray(data)
    for off, _ln, _typ, last in blocks:
        out[off] &= 0x7F  # clear last-flag everywhere ...
    last_off = blocks[-1][0]
    out[last_off] |= 0x80  # ... then set it on the final surviving block
    return bytes(out)


def shrink_frame_bodies(data: bytes, pred: Predicate) -> bytes:
    changed = True
    while changed:
        changed = False
        for start, end, hlen in reversed(frames(data)):
            lo = start + hlen + 1
            hi = end - 2  # exclude the CRC-16 tail; re-repair rewrites it
            if hi - lo < 2:
                continue
            chunk = hi - lo
            while chunk >= 1:
                pos = hi - chunk
                cut = False
                while pos >= lo:
                    cand = data[:pos] + data[pos + chunk :]
                    got = pred.interesting(cand)
                    if got is not None:
                        data = got
                        changed = cut = True
                        break
                    pos -= chunk
                if cut:
                    break
                chunk //= 2
            if changed:
                break
    return data


def ddmin_bytes(data: bytes, pred: Predicate) -> bytes:
    """Classic ddmin over byte granularity, with re-repair on every candidate."""
    n = 2
    while len(data) >= 2:
        chunk = max(1, len(data) // n)
        removed = False
        start = 0
        while start < len(data):
            cand = data[:start] + data[start + chunk :]
            got = pred.interesting(cand)
            if got is not None:
                data = got
                n = max(n - 1, 2)
                removed = True
                # re-derive positions against the shrunk buffer
                chunk = max(1, len(data) // n)
            else:
                start += chunk
        if not removed:
            if n >= len(data):
                break
            n = min(len(data), n * 2)
    return data


def main() -> int:
    argv = sys.argv[1:]
    if "--" not in argv:
        sys.stderr.write("shrink.py: need a predicate command after `--`\n")
        return 2
    split = argv.index("--")
    left, cmd = argv[:split], argv[split + 1 :]
    if not cmd:
        sys.stderr.write("shrink.py: empty predicate command after `--`\n")
        return 2

    ap = argparse.ArgumentParser(usage="shrink.py <reproducer.flac> [opts] -- <cmd ... @@ ...>")
    ap.add_argument("reproducer")
    ap.add_argument("-o", "--out", help="write minimized file here (default: <repro>.min.flac)")
    ap.add_argument("--timeout", type=float, default=15.0, help="per-predicate-call timeout (s)")
    ap.add_argument("--no-repair", action="store_true", help="do not re-repair CRCs between edits")
    args = ap.parse_args(left)

    with open(args.reproducer, "rb") as f:
        original = f.read()

    work_dir = os.path.dirname(os.path.abspath(args.reproducer)) or "."
    pred = Predicate(cmd, args.timeout, not args.no_repair, work_dir)

    base = pred.interesting(original)
    if base is None:
        sys.stderr.write("shrink.py: the ORIGINAL input is not interesting under this predicate; refusing to shrink.\n")
        return 2
    data = base

    for stage in (drop_trailing_frames, drop_metadata_blocks, shrink_frame_bodies, ddmin_bytes):
        data = stage(data, pred)

    # Final sanity check: the minimized artefact must still be interesting.
    if pred.interesting(data) is None:
        sys.stderr.write("shrink.py: internal error, minimized result is not interesting; keeping original.\n")
        data = original

    out = args.out or (args.reproducer + ".min.flac")
    with open(out, "wb") as f:
        f.write(data)

    print(f"original : {len(original)} bytes")
    print(f"minimized: {len(data)} bytes  ({100.0 * len(data) / max(1, len(original)):.1f}% of original)")
    print(f"predicate calls: {pred.calls}")
    print(f"wrote    : {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
