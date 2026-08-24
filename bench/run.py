#!/usr/bin/env python3
"""Benchmark Vinyl and libFLAC with one persistent high-resolution timer.

Each command receives one untimed warmup and ``BENCH_RUNS`` measured runs
(five by default).  The measured cases are shuffled with a fixed seed so a
single implementation does not consistently inherit the same thermal/cache
position.  Both codecs are swept over thread counts, as in
``bench/real_run.py``: ``BENCH_THREAD_SWEEP`` (default ``1,2,4,8``, clamped to
the core count) runs Vinyl encode, Vinyl decode and ``flac -8`` at every count,
so no row compares a frame-parallel codec against a single-threaded one by
accident.  Note that at 1 MB per file process startup is about a third of the
measurement, so read the per-core numbers off the real-audio suite instead;
these exist to keep the two dashboards comparable.

``results.csv`` keeps one row per case; its ``seconds`` column
holds the median measured duration, and ``audio_bytes`` the coded-frame size
apart from the metadata blocks (see ``bench/flacsize.py``) — the only size a
compression claim can rest on, because libFLAC writes 8.8 kB of padding,
seektable and vendor comment per file where Vinyl writes 42 bytes.
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

sys.path.insert(0, str(Path(__file__).resolve().parent))

from flacsize import audio_bytes

ROOT = Path(__file__).resolve().parent.parent
BENCH = ROOT / "bench"
CORPUS = BENCH / "corpus"
OUT = BENCH / "out"
RESULTS = BENCH / "results.csv"
VINYL = ROOT / ".lake" / "build" / "bin" / "flactest"

CORES = int(os.environ.get("BENCH_THREADS", os.cpu_count() or 1))
SWEEP = sorted({
    min(CORES, int(n))
    for n in os.environ.get("BENCH_THREAD_SWEEP", "1,2,4,8").split(",")
    if n.strip()
})


@dataclass(frozen=True)
class Case:
    label: str
    command: tuple[str, ...]
    output: Path
    threads: int
    env: tuple[tuple[str, str], ...] = ()


def run(command: tuple[str, ...], env: tuple[tuple[str, str], ...] = ()) -> None:
    subprocess.run(
        command,
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=True,
        env={**os.environ, **dict(env)} if env else None,
    )


def timed(case: Case) -> float:
    start = time.perf_counter_ns()
    run(case.command, case.env)
    return (time.perf_counter_ns() - start) / 1_000_000_000


def cases_for(pcm: Path, name: str, channels: int) -> list[Case]:
    vinyl_flac = OUT / f"{name}.vinyl.flac"
    # Vinyl's pool comes from the environment: Lean reads LEAN_NUM_THREADS
    # before `main`, so the `vinyl -j` flag re-executes and a benchmark
    # should not pay for that.
    cases = [
        Case(
            f"vinyl -j{n}",
            (str(VINYL), "--encode", str(pcm), str(vinyl_flac), "4096", str(channels)),
            vinyl_flac,
            n,
            (("LEAN_NUM_THREADS", str(n)),),
        )
        for n in SWEEP
    ] + [
        Case(
            f"vinyl decode -j{n}",
            (str(VINYL), "--decode-fast", str(vinyl_flac), str(OUT / "dec.raw")),
            vinyl_flac,
            n,
            (("LEAN_NUM_THREADS", str(n)),),
        )
        for n in SWEEP
    ] + [
        # libFLAC's decoder takes no -j (it accepts the flag and ignores it)
        Case(
            "flac decode -j1",
            (
                "flac", "-d", "-s", "--force-raw-format", "--sign=signed",
                "--endian=little", "-f", "-o", str(OUT / "dec2.raw"),
                str(vinyl_flac),
            ),
            vinyl_flac,
            1,
        ),
    ]
    # `-8` swept alongside Vinyl; `-0`/`-5` at one thread as ratio context
    for level, counts in ((0, [1]), (5, [1]), (8, SWEEP)):
        for threads in counts:
            output = OUT / f"{name}.flac{level}j{threads}.flac"
            cases.append(
                Case(
                    f"flac -{level} -j{threads}",
                    (
                        "flac", f"-{level}", f"-j{threads}", "--force-raw-format",
                        "--sign=signed", "--endian=little", f"--channels={channels}",
                        "--bps=16", "--sample-rate=44100", "-s", "-f",
                        "-o", str(output), str(pcm),
                    ),
                    output,
                    threads,
                )
            )
    return cases


def main() -> None:
    repetitions = int(os.environ.get("BENCH_RUNS", "5"))
    if repetitions < 1:
        raise SystemExit("BENCH_RUNS must be at least 1")
    OUT.mkdir(parents=True, exist_ok=True)
    rng = random.Random(0)
    rows: list[tuple[str, str, int, float, int, int, int]] = []

    for pcm in sorted(CORPUS.glob("*.pcm")):
        stem = pcm.stem
        channels = 2 if stem.endswith(".2ch") else 1
        name = stem.removesuffix(".2ch")
        raw_bytes = pcm.stat().st_size
        cases = cases_for(pcm, name, channels)

        # Materialize decoder input before warmups, then warm every process.
        run(cases[0].command, cases[0].env)
        run(("flac", "-t", "-s", str(cases[0].output)))
        for case in cases:
            run(case.command, case.env)

        samples: dict[str, list[float]] = {case.label: [] for case in cases}
        schedule = [case for case in cases for _ in range(repetitions)]
        rng.shuffle(schedule)
        for case in schedule:
            samples[case.label].append(timed(case))

        # Correctness checks remain outside all timed intervals.
        run(("flac", "-t", "-s", str(cases[0].output)))
        if (OUT / "dec.raw").read_bytes() != pcm.read_bytes():
            raise SystemExit(f"Vinyl decode mismatch: {pcm.name}")

        for case in cases:
            rows.append(
                (
                    name,
                    case.label,
                    case.threads,
                    statistics.median(samples[case.label]),
                    case.output.stat().st_size,
                    audio_bytes(case.output),
                    raw_bytes,
                )
            )
        print(f"done: {name}", flush=True)

    with RESULTS.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(
            ("file", "encoder", "threads", "seconds", "bytes", "audio_bytes",
             "raw_bytes"))
        writer.writerows(rows)


if __name__ == "__main__":
    main()
