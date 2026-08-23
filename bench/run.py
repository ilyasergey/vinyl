#!/usr/bin/env python3
"""Benchmark Vinyl and libFLAC with one persistent high-resolution timer.

Each command receives one untimed warmup and ``BENCH_RUNS`` measured runs
(five by default).  The measured cases are shuffled with a fixed seed so a
single implementation does not consistently inherit the same thermal/cache
position.  ``results.csv`` retains the historical one-row-per-case schema;
its ``seconds`` column now contains the median measured duration.
"""

from __future__ import annotations

import csv
import os
import random
import statistics
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
BENCH = ROOT / "bench"
CORPUS = BENCH / "corpus"
OUT = BENCH / "out"
RESULTS = BENCH / "results.csv"
VINYL = ROOT / ".lake" / "build" / "bin" / "flactest"


@dataclass(frozen=True)
class Case:
    label: str
    command: tuple[str, ...]
    output: Path


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


def cases_for(pcm: Path, name: str, channels: int) -> list[Case]:
    vinyl_flac = OUT / f"{name}.vinyl.flac"
    cases = [
        Case(
            "vinyl",
            (str(VINYL), "--encode", str(pcm), str(vinyl_flac), "4096", str(channels)),
            vinyl_flac,
        ),
        Case(
            "vinyl decode",
            (str(VINYL), "--decode-fast", str(vinyl_flac), str(OUT / "dec.raw")),
            vinyl_flac,
        ),
        Case(
            "flac decode",
            (
                "flac", "-d", "-s", "--force-raw-format", "--sign=signed",
                "--endian=little", "-f", "-o", str(OUT / "dec2.raw"),
                str(vinyl_flac),
            ),
            vinyl_flac,
        ),
    ]
    for level in (0, 5, 8):
        output = OUT / f"{name}.flac{level}.flac"
        cases.append(
            Case(
                f"flac -{level}",
                (
                    "flac", f"-{level}", "--force-raw-format", "--sign=signed",
                    "--endian=little", f"--channels={channels}", "--bps=16",
                    "--sample-rate=44100", "-s", "-f", "-o", str(output), str(pcm),
                ),
                output,
            )
        )
    return cases


def main() -> None:
    repetitions = int(os.environ.get("BENCH_RUNS", "5"))
    if repetitions < 1:
        raise SystemExit("BENCH_RUNS must be at least 1")
    OUT.mkdir(parents=True, exist_ok=True)
    rng = random.Random(0)
    rows: list[tuple[str, str, float, int, int]] = []

    for pcm in sorted(CORPUS.glob("*.pcm")):
        stem = pcm.stem
        channels = 2 if stem.endswith(".2ch") else 1
        name = stem.removesuffix(".2ch")
        raw_bytes = pcm.stat().st_size
        cases = cases_for(pcm, name, channels)

        # Materialize decoder input before warmups, then warm every process.
        run(cases[0].command)
        run(("flac", "-t", "-s", str(cases[0].output)))
        for case in cases:
            run(case.command)

        samples: dict[str, list[float]] = {case.label: [] for case in cases}
        schedule = [case for case in cases for _ in range(repetitions)]
        rng.shuffle(schedule)
        for case in schedule:
            samples[case.label].append(timed(case.command))

        # Correctness checks remain outside all timed intervals.
        run(("flac", "-t", "-s", str(cases[0].output)))
        if (OUT / "dec.raw").read_bytes() != pcm.read_bytes():
            raise SystemExit(f"Vinyl decode mismatch: {pcm.name}")

        for case in cases:
            rows.append(
                (
                    name,
                    case.label,
                    statistics.median(samples[case.label]),
                    case.output.stat().st_size,
                    raw_bytes,
                )
            )
        print(f"done: {name}", flush=True)

    with RESULTS.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("file", "encoder", "seconds", "bytes", "raw_bytes"))
        writer.writerows(rows)


if __name__ == "__main__":
    main()
