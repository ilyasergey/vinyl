"""Audio-frame payload size of a FLAC file, shared by both benchmark harnesses.

libFLAC writes padding, a seektable, and a vendor comment — 8,826 bytes per
file at its defaults; Vinyl writes STREAMINFO alone, 42 bytes.  A compression
comparison that includes those bytes is measuring metadata policy, so both
dashboards report the coded frames separately.
"""

from __future__ import annotations

from pathlib import Path


def audio_bytes(path: Path) -> int:
    """File size minus the metadata blocks.

    RFC 9639 §8: `fLaC`, then metadata blocks each carrying a four-byte header
    whose top bit marks the last one, then the coded frames.
    """
    size = path.stat().st_size
    with path.open("rb") as stream:
        if stream.read(4) != b"fLaC":
            raise SystemExit(f"{path}: not a FLAC stream")
        offset = 4
        while True:
            header = stream.read(4)
            if len(header) != 4:
                raise SystemExit(f"{path}: truncated metadata block header")
            offset += 4 + int.from_bytes(header[1:4], "big")
            if offset > size:
                raise SystemExit(f"{path}: metadata block overruns the file")
            if header[0] & 0x80:
                return size - offset
            stream.seek(offset)
