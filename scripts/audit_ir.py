#!/usr/bin/env python3
"""Compiled-path audit of Lean's generated C.

Two properties no theorem can state, both checked here against
`.lake/build/ir/**/*.c` after `lake build`:

**Positive — the kernels reach the shipped binary.** A `@[csimp]` swap only
rewrites code generated *after* it is elaborated, and a theorem in `Flac/Spec/`
says nothing about which function a compiled caller invokes. The public
`Flac.encode` and `Flac.decodePcm16` compiled to the reference shapes for months
with their fast equalities proven and unused. So: each shipped entry point's
module must mention the kernel symbol it is supposed to call.

**Negative — the hot loops do not read the input object's header.** The Rice
reader, the unary scan, `byteU` and the sync scan carry the buffer size as an
erased-proof `USize` parameter precisely so that `uget` needs no size load. That
load sits at offset 8 of a `lean_sarray_object`, sharing a cache line with the
reference count decode workers update atomically, so reading it per byte turns
into repeated coherence invalidations — ~32% of the 16-thread decode wall when it
was there. It is **invisible at one thread**, where the line is L1-hot, so no
timing gate and no single-thread profile can catch a regression. A grep can. Any
refactor that reintroduces `d.usize` inside one of these loops fails here.

Function bodies are located by their definition line and matched by brace depth,
so a forbidden symbol elsewhere in the same file (the generic bit readers still
have theirs) does not trip the check.
"""
import pathlib
import re
import sys

IR = pathlib.Path(__file__).resolve().parents[1] / ".lake/build/ir"

# module -> symbols that must appear somewhere in it
REQUIRED = {
    "Flac/Native/Decode.c": [
        "lp_vinyl_Flac_Decode_riceRunU",
        "lp_vinyl_Flac_Decode_scanOneU",
        "lp_vinyl_Flac_Decode_readSIntSeqU",
        "lp_vinyl_Flac_Lpc_restoreFast",
        "lp_vinyl_Flac_Crc_crc16RangeFast",
        "lp_vinyl_Flac_Stereo_decodeMSAFast",
    ],
    "Flac/Native/Lpc.c": ["lp_vinyl_Flac_Lpc_restoreRoll12"],
    "Flac/Native/Stream.c": ["lp_vinyl_Flac_Stream_pcmStereoFill"],
    "Flac/Native/Encode.c": [
        "lp_vinyl_Flac_Encode_channelSegU",
        "lp_vinyl_Flac_Crc_crc16RangeFast",
    ],
    "Flac/Native/Codec.c": ["lp_vinyl_Flac_Emit_W_encode"],
    "FlacTest/Cli.c": [
        "lp_vinyl_Flac_decodePcm16A",
        "lp_vinyl_Flac_Decode_decodeBytes",
    ],
}

# (module, function) -> symbols that must NOT appear inside that function's body
FORBIDDEN_IN = {
    ("Flac/Native/Decode.c", "lp_vinyl_Flac_Decode_byteU___redArg"): ["lean_sarray_size", "lean_byte_array_size"],
    ("Flac/Native/Decode.c", "lp_vinyl_Flac_Decode_scanOneU___redArg"): ["lean_sarray_size", "lean_byte_array_size"],
    ("Flac/Native/Decode.c", "lp_vinyl_Flac_Decode_riceRunU___redArg"): ["lean_sarray_size", "lean_byte_array_size"],
    ("Flac/Native/Decode.c", "lp_vinyl_Flac_Decode_syncScanGo___redArg"): ["lean_sarray_size", "lean_byte_array_size"],
    ("Flac/Native/Decode.c", "lp_vinyl_Flac_Decode_readSIntSeqU___redArg"): ["lean_sarray_size", "lean_byte_array_size"],
    ("Flac/Native/Md5.c", "lp_vinyl___private_Flac_Native_Md5_0__Flac_Md5_compressIn___redArg"):
        ["lean_sarray_size", "lean_byte_array_size"],
    ("Flac/Native/Md5.c", "lp_vinyl___private_Flac_Native_Md5_0__Flac_Md5_blocksIn___redArg"):
        ["lean_sarray_size", "lean_byte_array_size"],
}


def function_body(text: str, name: str) -> str | None:
    """The body of the C function `name`, matched by brace depth from its definition line.

    The signature may wrap across lines — `riceRunU` has eleven parameters — so the
    opening brace is looked for rather than required at the end of the first line.
    A declaration (`;` before any `{`) is skipped.
    """
    lines = text.split("\n")
    opener = re.compile(rf"^(LEAN_EXPORT|static)\b.*\b{re.escape(name)}\(")
    for i, line in enumerate(lines):
        if not opener.match(line):
            continue
        head = "\n".join(lines[i : i + 8])
        brace, semi = head.find("{"), head.find(";")
        if brace < 0 or (0 <= semi < brace):
            continue
        depth = 0
        out = []
        for l in lines[i:]:
            out.append(l)
            depth += l.count("{") - l.count("}")
            if depth == 0 and "{" in "\n".join(out):
                return "\n".join(out)
    return None


def main() -> int:
    fail = 0
    for module, symbols in REQUIRED.items():
        path = IR / module
        if not path.is_file():
            print(f"FAIL: {path} not built")
            fail = 1
            continue
        text = path.read_text()
        for sym in symbols:
            if sym not in text:
                print(f"FAIL: {sym} absent from {module} (kernel not on the compiled path)")
                fail = 1

    for (module, fn), symbols in FORBIDDEN_IN.items():
        path = IR / module
        if not path.is_file():
            print(f"FAIL: {path} not built")
            fail = 1
            continue
        body = function_body(path.read_text(), fn)
        if body is None:
            print(f"FAIL: {fn} not found in {module} (renamed, inlined away, or the kernel is gone)")
            fail = 1
            continue
        for sym in symbols:
            if sym in body:
                print(f"FAIL: {fn} in {module} contains {sym} — the hot loop reads the "
                      f"input object's header again; that is a multi-thread regression "
                      f"no single-thread measurement can see")
                fail = 1

    print("ok" if not fail else "compiled-path audit FAILED")
    return fail


if __name__ == "__main__":
    sys.exit(main())
