#!/usr/bin/env python3
"""Benchmark Vinyl and libFLAC on the real-audio corpora.

Methodology matches `bench/run.py`: one persistent high-resolution timer in
the parent process, one untimed warmup per case, ``BENCH_RUNS`` measured runs
(five by default) shuffled with a fixed seed, and the median reported.
Correctness checks run outside every timed interval.

Two things differ from the synthetic harness, both because real audio makes
them measurable:

* Sizes are recorded twice — whole file and audio-frame payload (the bytes
  after the last metadata block).  libFLAC writes padding, a seektable, and a
  vendor comment; Vinyl writes STREAMINFO alone.  On the synthetic corpus that
  fixed overhead was larger than the gap being reported, so only the payload
  column supports a compression claim.
* libFLAC is measured single-threaded (its default) *and* at the same thread
  count Vinyl uses.  Vinyl's encoder and decoder are frame-parallel, so the
  single-threaded row alone would not be a like-for-like wall-clock number.
"""

from __future__ import annotations

import csv
import os
import random
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from flacsize import audio_bytes


sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT = Path(__file__).resolve().parent.parent
BENCH = ROOT / "bench"
UNITS = BENCH / "real_data" / "units.csv"
OUT = BENCH / "real_out"
RESULTS = BENCH / "real_results.csv"
VINYL = ROOT / ".lake" / "build" / "bin" / "flactest"

BLOCK_SIZE = 4096          # libFLAC's -8 default, so both encoders frame alike
THREADS = int(os.environ.get("BENCH_THREADS", os.cpu_count() or 1))


@dataclass(frozen=True)
class Case:
    label: str
    command: tuple[str, ...]
    output: Path
    threads: int


def run(command: tuple[str, ...]) -> None:
    subprocess.run(
        command,
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=True,
    )


def timed(command: tuple[str, ...]) -> float:
    start = time.perf_counter_ns()
    run(command)
    return (time.perf_counter_ns() - start) / 1_000_000_000


def flac_encode(level: int, threads: int, pcm: Path, output: Path,
                channels: int, rate: int, bits: int) -> tuple[str, ...]:
    return (
        "flac", f"-{level}", f"-j{threads}", "--force-raw-format",
        "--sign=signed", "--endian=little", f"--channels={channels}",
        f"--bps={bits}", f"--sample-rate={rate}", "-s", "-f",
        "-o", str(output), str(pcm),
    )


def cases_for(unit: dict[str, str]) -> list[Case]:
    pcm = ROOT / unit["path"]
    name = unit["unit"].replace("/", "_")
    channels = int(unit["channels"])
    rate = int(unit["sample_rate"])
    bits = int(unit["bits_per_sample"])
    vinyl_flac = OUT / f"{name}.vinyl.flac"

    cases = [
        Case(
            "vinyl",
            (str(VINYL), "--encode", str(pcm), str(vinyl_flac),
             str(BLOCK_SIZE), str(channels), str(rate)),
            vinyl_flac,
            THREADS,
        ),
        Case(
            "vinyl decode",
            (str(VINYL), "--decode-fast", str(vinyl_flac), str(OUT / "dec.raw")),
            vinyl_flac,
            THREADS,
        ),
        Case(
            "flac decode",
            ("flac", "-d", "-s", "--force-raw-format", "--sign=signed",
             "--endian=little", "-f", "-o", str(OUT / "dec2.raw"),
             str(vinyl_flac)),
            vinyl_flac,
            1,
        ),
    ]
    for level, threads in ((5, 1), (8, 1), (8, THREADS)):
        suffix = f"flac{level}" + (f"j{threads}" if threads != 1 else "")
        output = OUT / f"{name}.{suffix}.flac"
        label = f"flac -{level}" + (f" -j{threads}" if threads != 1 else "")
        cases.append(
            Case(
                label,
                flac_encode(level, threads, pcm, output, channels, rate, bits),
                output,
                threads,
            )
        )
    return cases


def main() -> None:
    if not UNITS.exists():
        raise SystemExit(f"{UNITS} not found — run bench/real_units.py first")
    repetitions = int(os.environ.get("BENCH_RUNS", "5"))
    if repetitions < 1:
        raise SystemExit("BENCH_RUNS must be at least 1")
    only = os.environ.get("BENCH_SUITES")
    suites = set(only.split(",")) if only else None

    OUT.mkdir(parents=True, exist_ok=True)
    units = [u for u in csv.DictReader(UNITS.open())
             if suites is None or u["suite"] in suites]
    limit = int(os.environ.get("BENCH_LIMIT", "0"))
    if limit:
        units = units[:limit]
    if not units:
        raise SystemExit("no units selected")
    rng = random.Random(0)
    rows: list[dict[str, object]] = []
    total = sum(int(u["raw_bytes"]) for u in units)
    print(f"{len(units)} units, {total / 2**30:.2f} GiB, "
          f"{repetitions} measured runs, {THREADS} threads", flush=True)

    for index, unit in enumerate(units, 1):
        pcm = ROOT / unit["path"]
        raw = pcm.read_bytes()
        cases = cases_for(unit)
        vinyl_flac = cases[0].output
        flac8 = next(c.output for c in cases if c.label == "flac -8")

        # Materialize decoder input before the warmups, then warm each process.
        run(cases[0].command)
        for case in cases:
            run(case.command)

        samples: dict[str, list[float]] = {case.label: [] for case in cases}
        schedule = [case for case in cases for _ in range(repetitions)]
        rng.shuffle(schedule)
        for case in schedule:
            samples[case.label].append(timed(case.command))

        # Correctness, outside every timed interval:
        #   1. libFLAC accepts Vinyl's stream and its MD5 matches,
        #   2. Vinyl's own decoder reproduces the input exactly,
        #   3. Vinyl's decoder reproduces libFLAC's -8 stream exactly.
        run(("flac", "-t", "-s", str(vinyl_flac)))
        if (OUT / "dec.raw").read_bytes() != raw:
            raise SystemExit(f"Vinyl decode mismatch: {unit['unit']}")
        run((str(VINYL), "--decode-fast", str(flac8), str(OUT / "cross.raw")))
        if (OUT / "cross.raw").read_bytes() != raw:
            raise SystemExit(f"Vinyl cross-decode mismatch on flac -8: {unit['unit']}")

        for case in cases:
            rows.append(
                {
                    "unit": unit["unit"],
                    "suite": unit["suite"],
                    "category": unit["category"],
                    "encoder": case.label,
                    "threads": case.threads,
                    "seconds": statistics.median(samples[case.label]),
                    "bytes": case.output.stat().st_size,
                    "audio_bytes": audio_bytes(case.output),
                    "raw_bytes": len(raw),
                    "channels": unit["channels"],
                    "sample_rate": unit["sample_rate"],
                }
            )
        print(f"done {index}/{len(units)}: {unit['unit']} "
              f"({len(raw) / 1e6:.1f} MB)", flush=True)

    with RESULTS.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {RESULTS}")


if __name__ == "__main__":
    main()
