#!/usr/bin/env python3
"""Turn the prepared real-audio corpora into benchmark units.

`real_fetch.py` writes one canonical S16LE PCM file per source recording.
Those files are the right granularity for EBU SQAM, whose tracks average
8.9 MB, but not for LibriSpeech, whose 5,559 utterances average 0.22 MB:
at that size a codec invocation measures process startup, not throughput.
LibriSpeech utterances are therefore concatenated per speaker, in sorted
utterance order, into 73 streams of 5–20 MB.  Concatenation is raw-PCM
only — no resampling, no gain, no reordering — and both codecs under test
receive byte-identical input.

Writes `bench/real_data/units.csv`; re-running is incremental (an existing
stream of the expected size and hash is kept).
"""

from __future__ import annotations

import csv
import hashlib
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
REAL = ROOT / "bench" / "real_data"
MANIFEST = REAL / "manifest.csv"
STREAMS = REAL / "streams"
UNITS = REAL / "units.csv"

FIELDS = (
    "unit", "suite", "category", "path", "channels", "sample_rate",
    "bits_per_sample", "raw_bytes", "source_files", "pcm_sha256",
)


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _speaker(file_id: str) -> str:
    # librispeech-test-clean/LibriSpeech/test-clean/<speaker>/<chapter>/<utt>
    return file_id.split("/")[3]


def _concatenate(sources: list[Path], destination: Path, expected: int) -> None:
    if destination.exists() and destination.stat().st_size == expected:
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    partial = destination.with_suffix(".pcm.partial")
    with partial.open("wb") as out:
        for source in sources:
            with source.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1 << 22), b""):
                    out.write(chunk)
    written = partial.stat().st_size
    if written != expected:
        partial.unlink()
        raise SystemExit(f"{destination.name}: wrote {written}, expected {expected}")
    partial.replace(destination)


def main() -> None:
    if not MANIFEST.exists():
        raise SystemExit(
            f"{MANIFEST} not found — run bench/real_fetch.py first "
            "(see bench/CORPORA.md)"
        )
    rows = list(csv.DictReader(MANIFEST.open()))
    units: list[dict[str, object]] = []

    # SQAM: one unit per track, benchmarked in place.
    for row in rows:
        if row["suite"] != "sqam":
            continue
        units.append(
            {
                "unit": row["file"],
                "suite": "sqam",
                "category": row["category"],
                "path": row["path"],
                "channels": row["channels"],
                "sample_rate": row["sample_rate"],
                "bits_per_sample": row["bits_per_sample"],
                "raw_bytes": row["raw_bytes"],
                "source_files": 1,
                "pcm_sha256": row["pcm_sha256"],
            }
        )

    # LibriSpeech: one unit per speaker, concatenated in sorted utterance order.
    speakers: dict[tuple[str, str], list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        if not row["suite"].startswith("librispeech"):
            continue
        speakers[(row["suite"], _speaker(row["file"]))].append(row)

    for (suite, speaker), members in sorted(speakers.items()):
        members.sort(key=lambda r: r["file"])
        formats = {(r["channels"], r["sample_rate"], r["bits_per_sample"])
                   for r in members}
        if len(formats) != 1:
            raise SystemExit(f"{suite}/{speaker}: mixed PCM formats {formats}")
        channels, sample_rate, bits = formats.pop()
        expected = sum(int(r["raw_bytes"]) for r in members)
        destination = STREAMS / suite / f"{speaker}.pcm"
        _concatenate([ROOT / r["path"] for r in members], destination, expected)
        units.append(
            {
                "unit": f"{suite}/{speaker}",
                "suite": suite,
                "category": members[0]["category"],
                "path": destination.relative_to(ROOT).as_posix(),
                "channels": channels,
                "sample_rate": sample_rate,
                "bits_per_sample": bits,
                "raw_bytes": expected,
                "source_files": len(members),
                "pcm_sha256": _sha256(destination),
            }
        )
        print(f"stream: {suite}/{speaker} "
              f"({len(members)} utterances, {expected / 1e6:.1f} MB)",
              file=sys.stderr, flush=True)

    with UNITS.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(units)

    total = sum(int(u["raw_bytes"]) for u in units)
    print(f"units: {UNITS} ({len(units)} units, {total / 2**30:.2f} GiB S16LE)")


if __name__ == "__main__":
    main()
