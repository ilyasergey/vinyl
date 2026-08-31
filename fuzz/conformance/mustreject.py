#!/usr/bin/env python3
"""Must-reject / reserved-code seed generator + verdict table.

Emits one RFC-invalid FLAC stream per row into corpus/decode/must_reject, then
decodes each with the three Vinyl modes (--decode, --decode-fast, --decode-pcm16)
and with `flac -t`, recording accept/reject.  Prints a markdown verdict table and
flags:

  * any row where a Vinyl mode ACCEPTS a stream that both `flac` and the RFC
    reject  -> "candidate finding - needs confirmation";
  * any row where --decode-fast and --decode disagree -> a simulation-stack
    divergence (high value).

Every cell comes from an actual CLI run; nothing is fabricated.  Stdlib only.

Phase-4 dedup: this driver no longer carries a Python CRC or bit-writer port. It
builds ONE valid base stream (a CONSTANT mono 16-bit frame, 16 samples) by
writing the STREAMINFO / frame-header fields at the offsets named ONCE in
common/flac_bits.h, then lets the compiled tools/flac_repair (a thin CLI over
flac_rescan_repair) compute every CRC. Each case is then a TARGETED FIELD REWRITE
of that base, repaired again so -- wherever flac_struct.c's shared walker still
recognises the frame -- the only reason to reject is the targeted semantic.

Reserved *header* codes (block-size 0, sample-rate 15, bit-depth 3, channel
11/15) are, by design, rejected by that shared walker (flac_hdr_parse_core), so
flac_repair cannot re-bless their CRC-8: those rows carry a stale header CRC as
well as the reserved code -- still RFC-invalid, still a reject path, exactly the
limitation Phase-4 note #5 describes. Subframe-internal reserved codes (LPC
precision 1111, residual method 2/3, indivisible partition order, wasted>=bps)
are left to the fuzz targets + the CRC-aware mutator, which manufacture them
structurally; reproducing them here would require the bit-writer this rewrite
deliberately removes.
"""

import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FUZZ = os.path.dirname(HERE)
# Derive the Vinyl CLI like mk/toolchain.mk does (REPO = the fuzz/ dir's parent);
# overridable via $VINYL_BIN.
REPO = os.path.dirname(FUZZ)
VINYL = os.environ.get("VINYL_BIN") or os.path.join(REPO, ".lake", "build", "bin", "vinyl")
FLAC = os.environ.get("FLAC_BIN", "flac")
FLAC_REPAIR = os.environ.get("FLAC_REPAIR_BIN") or os.path.join(FUZZ, "build", "bin", "flac_repair")
OUT_DIR = os.path.join(FUZZ, "corpus", "decode", "must_reject")

# --------------------------------------------------------------------------
# STREAMINFO bit offsets -- the single source is common/flac_bits.h; mirrored
# here as the FLAC_SI_* macros' values (payload at file bit 64).
# --------------------------------------------------------------------------
SI_MINBLOCK_BIT = 64 + 0
SI_MAXBLOCK_BIT = 64 + 16
SI_SAMPLERATE_BIT = 64 + 80
SI_CHANNELS_BIT = 64 + 100
SI_BPS_BIT = 64 + 103
SI_TOTAL_BIT = 64 + 108

MARKER = b"fLaC"
FRAME_START = 42  # fLaC(4) + SI block header(4) + SI payload(34)


# --------------------------------------------------------------------------
# Random-access bit field-rewrite primitives (NOT a stream bit-writer): set /
# read an n-bit big-endian field at an absolute bit offset. These are the
# "targeted field rewrite" the generator is built on.
# --------------------------------------------------------------------------
def put_bits(b: bytearray, bitpos: int, n: int, val: int) -> None:
    for i in range(n):
        bp = bitpos + i
        bit = (val >> (n - 1 - i)) & 1
        byte, off = bp // 8, 7 - (bp % 8)
        if bit:
            b[byte] |= 1 << off
        else:
            b[byte] &= ~(1 << off) & 0xFF


def get_bits(b: bytes, bitpos: int, n: int) -> int:
    v = 0
    for i in range(n):
        bp = bitpos + i
        v = (v << 1) | ((b[bp // 8] >> (7 - (bp % 8))) & 1)
    return v


def repair(data: bytes) -> bytes:
    """CRC repair via tools/flac_repair (stdin->stdout)."""
    try:
        p = subprocess.run([FLAC_REPAIR], input=bytes(data), stdout=subprocess.PIPE)
    except FileNotFoundError:
        sys.stderr.write(f"mustreject.py: {FLAC_REPAIR} not found -- run `make tools`\n")
        sys.exit(2)
    return p.stdout if p.returncode == 0 else bytes(data)


# --------------------------------------------------------------------------
# The one valid base: a CONSTANT mono 16-bit frame, 16 samples. Built by
# writing fields at named offsets, then repaired to fill CRC-8 / CRC-16.
# --------------------------------------------------------------------------
def build_base() -> bytes:
    b = bytearray(55)
    b[0:4] = MARKER
    b[4:8] = bytes([0x80, 0x00, 0x00, 0x22])  # last=1, type=STREAMINFO, len=34
    put_bits(b, SI_MINBLOCK_BIT, 16, 16)
    put_bits(b, SI_MAXBLOCK_BIT, 16, 16)
    put_bits(b, SI_SAMPLERATE_BIT, 20, 44100)
    put_bits(b, SI_CHANNELS_BIT, 3, 0)  # mono (stored channels-1)
    put_bits(b, SI_BPS_BIT, 5, 15)  # 16-bit (stored bps-1)
    put_bits(b, SI_TOTAL_BIT, 36, 16)
    # Frame header: sync 0x3FFE + reserved0 + blocking0 = 0xFFF8; bs code 7
    # (explicit 16-bit block size = 15), sr code 9, mono, bit-depth code 4.
    b[FRAME_START + 0] = 0xFF
    b[FRAME_START + 1] = 0xF8
    b[FRAME_START + 2] = 0x79  # bs_code=7, sr_code=9
    b[FRAME_START + 3] = 0x08  # ch_code=0, bps_code=4, reserved=0
    b[FRAME_START + 4] = 0x00  # coded frame number 0
    put_bits(b, (FRAME_START + 5) * 8, 16, 15)  # explicit block size - 1
    # b[FRAME_START+7] = CRC-8 (filled by flac_repair)
    # Subframe (bytes 50..52): CONSTANT (0 + 000000 + wasted0 + value16) == zeros.
    # b[53..54] = CRC-16 (filled by flac_repair)
    return repair(b)


# --------------------------------------------------------------------------
# Case table. Each case -> (name, bytes, note describing the decision site).
# All are field rewrites of the valid base; `rep=True` re-runs flac_repair.
# --------------------------------------------------------------------------
def cases() -> list[tuple[str, bytes, str]]:
    base = build_base()
    out: list[tuple[str, bytes, str]] = []

    def add(name, data, note):
        out.append((name, bytes(data), note))

    def edit(fn, rep=True):
        b = bytearray(base)
        fn(b)
        return repair(b) if rep else bytes(b)

    # Controls ---------------------------------------------------------------
    add("00_baseline_valid", base, "control: valid stream, MUST be accepted everywhere")
    add("01_empty_file", b"", "control: truly empty, MUST reject everywhere")
    add("02_bad_marker", b"fLbC" + base[4:], "marker MUST be fLaC (Decode.lean readMagic)")

    # Reserved frame-header codes (flac_hdr_parse_core rejects -> stale CRC-8) --
    add("10_blocksize_code_0",
        edit(lambda b: put_bits(b, (FRAME_START + 2) * 8, 4, 0)),
        "resolveBlockSize code 0 reserved (§9.1.1)")
    add("11_samplerate_code_15",
        edit(lambda b: put_bits(b, (FRAME_START + 2) * 8 + 4, 4, 15)),
        "skipSampleRate code 15 forbidden (§9.1.2)")
    add("12_bitdepth_code_3",
        edit(lambda b: put_bits(b, (FRAME_START + 3) * 8 + 4, 3, 3)),
        "bpsOfCode code 3 reserved (§9.1.4)")
    for cc in (11, 15):
        add(f"13_channel_code_{cc}",
            edit(lambda b, cc=cc: put_bits(b, (FRAME_START + 3) * 8, 4, cc)),
            f"readChannels chCode {cc} reserved (§9.1.3)")

    # Frame reserved bits ----------------------------------------------------
    add("14_frame_reserved_r0",
        edit(lambda b: put_bits(b, (FRAME_START + 1) * 8 + 7, 1, 1)),
        "frame reserved bit after sync MUST be 0 (§9.1)")
    add("15_frame_reserved_r1",
        edit(lambda b: put_bits(b, (FRAME_START + 3) * 8 + 7, 1, 1)),
        "frame header trailing reserved bit MUST be 0 (§9.1)")

    # Subframe-internal, in-place (header still parses -> CRC repaired) -------
    body_bit = (FRAME_START + 8) * 8  # subframe starts after 7 header bytes + CRC-8
    add("16_subframe_reserved_bit",
        edit(lambda b: put_bits(b, body_bit, 1, 1)),
        "readSubframe leading bit MUST be 0 (§9.2.1)")
    add("17_reserved_subframe_type",
        edit(lambda b: put_bits(b, body_bit + 1, 6, 2)),
        "readContent subframe type 0b000010 reserved (§9.2.1)")

    # Overlong UTF-8 coded number (header still parses; +1 byte) -------------
    add("22_utf8_overlong_2byte",
        repair(bytearray(base[:FRAME_START + 4] + bytes([0xC0, 0x80]) + base[FRAME_START + 5:])),
        "readUtf8 overlong 2-byte form, no min-value check (§9.1.6)")

    # STREAMINFO problems (no CRC; frame stays valid) ------------------------
    add("30_streaminfo_absent",
        edit(lambda b: b.__setitem__(4, (b[4] & 0x80) | 4)),
        "first metadata block MUST be STREAMINFO (§8.1)")
    add("33_streaminfo_len_33",
        edit(lambda b: put_bits(b, 8, 24, 33)),
        "STREAMINFO length MUST be 34 (§8.2)")
    add("40_streaminfo_sr0_with_audio",
        edit(lambda b: put_bits(b, SI_SAMPLERATE_BIT, 20, 0)),
        "sample rate MUST NOT be 0 with audio (§9.1.7)")
    add("41_frame_contradicts_streaminfo_bps",
        edit(lambda b: put_bits(b, SI_BPS_BIT, 5, 7)),  # STREAMINFO says 8-bit, frame 16-bit
        "STREAMINFO bps (8) contradicts frame depth (16)")
    add("42_frame_contradicts_streaminfo_channels",
        edit(lambda b: put_bits(b, SI_CHANNELS_BIT, 3, 1)),  # STREAMINFO says stereo, frame mono
        "STREAMINFO channels (2) contradicts frame (mono)")

    # Metadata structure edits (byte-level) ---------------------------------
    # type-127 block inserted after STREAMINFO (SI last-flag cleared).
    si_not_last = bytearray(base)
    si_not_last[4] &= 0x7F
    add("34_metadata_type_127",
        repair(si_not_last[:FRAME_START] + bytes([0x80 | 127, 0, 0, 0]) + si_not_last[FRAME_START:]),
        "metadata block type 127 forbidden (§8.1)")
    # last-flag never set: SI last-flag cleared, no further block before frame.
    add("35_last_flag_never_set",
        edit(lambda b: b.__setitem__(4, b[4] & 0x7F)),
        "no metadata block carries the last-block flag (§8.1)")
    # metadata length past EOF.
    add("36_metadata_len_past_eof",
        edit(lambda b: put_bits(b, 8, 24, 0xFFFF)),
        "STREAMINFO length runs past end of input (§8.1)")

    return out


# --------------------------------------------------------------------------
# Runners
# --------------------------------------------------------------------------
def run(cmd: list[str]) -> bool:
    """True == the tool accepted (exit 0)."""
    try:
        p = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=60)
        return p.returncode == 0
    except subprocess.TimeoutExpired:
        return False


def verdict(path: str) -> dict[str, bool]:
    with tempfile.TemporaryDirectory(prefix="mustreject_") as td:
        out = os.path.join(td, "out.raw")
        return {
            "decode": run([VINYL, "--decode", path, out]),
            "decode_fast": run([VINYL, "--decode-fast", path, out]),
            "decode_pcm16": run([VINYL, "--decode-pcm16", path, out]),
            "flac": run([FLAC, "-t", "-s", path]),
        }


def cell(accepted: bool) -> str:
    return "ACCEPT" if accepted else "REJECT"


def main() -> int:
    os.makedirs(OUT_DIR, exist_ok=True)
    rows = []
    for name, data, note in cases():
        path = os.path.join(OUT_DIR, f"{name}.flac")
        with open(path, "wb") as f:
            f.write(data)
        rows.append((name, verdict(path), note))

    # Verdict table ---------------------------------------------------------
    print("## Must-reject / reserved-code verdict table\n")
    print(f"seeds written to {OUT_DIR}\n")
    print("| Case | --decode | --decode-fast | --decode-pcm16 | flac -t | Decision site |")
    print("|------|----------|---------------|----------------|---------|---------------|")
    for name, v, note in rows:
        print(
            f"| {name} | {cell(v['decode'])} | {cell(v['decode_fast'])} | "
            f"{cell(v['decode_pcm16'])} | {cell(v['flac'])} | {note} |"
        )

    # Flags -----------------------------------------------------------------
    candidate = []
    divergence = []
    for name, v, note in rows:
        if name.startswith("00_"):
            continue  # the valid control is expected to be accepted
        vinyl_any = v["decode"] or v["decode_fast"] or v["decode_pcm16"]
        if vinyl_any and not v["flac"]:
            candidate.append((name, v, note))
        if v["decode"] != v["decode_fast"]:
            divergence.append((name, v, note))

    print("\n## Candidate findings (a Vinyl mode accepts an RFC-invalid stream that `flac` rejects)\n")
    if not candidate:
        print("_none_")
    for name, v, note in candidate:
        modes = [m for m in ("decode", "decode_fast", "decode_pcm16") if v[m]]
        print(f"- **{name}** - candidate finding, needs confirmation. "
              f"Accepted by Vinyl mode(s): {', '.join(modes)}; rejected by flac. {note}")

    print("\n## Simulation-stack divergences (--decode-fast disagrees with --decode)\n")
    if not divergence:
        print("_none_")
    for name, v, note in divergence:
        print(f"- **{name}** - --decode={cell(v['decode'])}, "
              f"--decode-fast={cell(v['decode_fast'])}. {note}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
