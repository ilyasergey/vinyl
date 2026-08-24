#!/usr/bin/env python3
"""Fetch and prepare reproducible real-audio benchmark corpora.

The generated tree is::

    bench/real_data/
      downloads/       publisher archives and download metadata
      source/          safely extracted source FLAC files
      pcm/             canonical signed interleaved S16LE PCM
      manifest.csv     source, format, size, and checksum metadata

Examples::

    python3 bench/real_fetch.py --corpus sqam --accept-ebu-terms
    python3 bench/real_fetch.py --corpus librispeech
    python3 bench/real_fetch.py --corpus all --accept-ebu-terms
    python3 bench/real_fetch.py --corpus sqam --accept-ebu-terms --offline

The EBU permits SQAM use here as an R&D tool, but not other commercial use.
Passing ``--accept-ebu-terms`` records an explicit acknowledgement; it does
not alter those terms.  The versioned EBU object publishes a byte size and an
S3 entity tag, but no cryptographic digest.  A fresh download is pinned to
both, SHA-256 hashed locally, and accompanied by a metadata sidecar.  An
existing EBU archive without that sidecar is rejected unless explicitly
accepted with ``--trust-existing-ebu``.  OpenSLR publishes MD5 digests for
both LibriSpeech archives; those are always checked, and SHA-256 is recorded
as an additional local identity.

Audio is never resampled.  SQAM is 44.1 kHz and LibriSpeech is 16 kHz; both
are decoded losslessly to S16LE.  Consumers must use the manifest sample rate
rather than assuming every input is 44.1 kHz.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import BinaryIO, Iterable


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DATA = ROOT / "bench" / "real_data"
BUFFER_SIZE = 1024 * 1024
MAX_EXTRACTED_BYTES = 16 * 1024 * 1024 * 1024

MANIFEST_FIELDS = (
    "suite",
    "category",
    "file",
    "path",
    "source_path",
    "channels",
    "sample_rate",
    "bits_per_sample",
    "samples_per_channel",
    "raw_bytes",
    "pcm_sha256",
    "source_sha256",
    "source_streaminfo_md5",
    "source_url",
    "archive",
    "archive_sha256",
    "archive_checksum_kind",
    "archive_checksum",
    "license",
)


@dataclass(frozen=True)
class ArchiveSpec:
    suite: str
    filename: str
    url: str
    archive_format: str
    license: str
    published_checksum_kind: str
    published_checksum: str
    expected_size: int | None = None
    expected_etag: str | None = None


@dataclass(frozen=True)
class StreamInfo:
    channels: int
    sample_rate: int
    bits_per_sample: int
    samples_per_channel: int
    pcm_md5: str


ARCHIVES = {
    "sqam": ArchiveSpec(
        suite="sqam",
        filename="TECH3253_SQAM_FLAC.zip",
        url="https://qc.ebu.io/testmaterials/523/1/download/",
        archive_format="zip",
        license="EBU SQAM: non-commercial use except as an R&D tool",
        published_checksum_kind="etag+size",
        published_checksum="aec89ca407910382d98a7fea74f64a14-9",
        expected_size=175_545_976,
        expected_etag="aec89ca407910382d98a7fea74f64a14-9",
    ),
    "librispeech-test-clean": ArchiveSpec(
        suite="librispeech-test-clean",
        filename="test-clean.tar.gz",
        url="https://www.openslr.org/resources/12/test-clean.tar.gz",
        archive_format="tar.gz",
        license="CC BY 4.0",
        published_checksum_kind="md5",
        published_checksum="32fa31d27d2e1cad72775fee3f4849a9",
    ),
    "librispeech-test-other": ArchiveSpec(
        suite="librispeech-test-other",
        filename="test-other.tar.gz",
        url="https://www.openslr.org/resources/12/test-other.tar.gz",
        archive_format="tar.gz",
        license="CC BY 4.0",
        published_checksum_kind="md5",
        published_checksum="fb5a50374b501bb3bac4815ee91d3135",
    ),
}


def _hash_file(path: Path, *algorithms: str) -> dict[str, str]:
    hashes = {name: hashlib.new(name) for name in algorithms}
    with path.open("rb") as stream:
        while chunk := stream.read(BUFFER_SIZE):
            for digest in hashes.values():
                digest.update(chunk)
    return {name: digest.hexdigest() for name, digest in hashes.items()}


def _normalise_etag(value: str | None) -> str | None:
    if value is None:
        return None
    value = value.strip()
    if value.startswith("W/"):
        value = value[2:]
    return value.strip('"')


def _atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.",
            suffix=".tmp", delete=False,
        ) as stream:
            temp_name = stream.name
            json.dump(value, stream, indent=2, sort_keys=True)
            stream.write("\n")
        os.replace(temp_name, path)
        temp_name = None
    finally:
        if temp_name is not None:
            Path(temp_name).unlink(missing_ok=True)


def _download_metadata_path(archive: Path) -> Path:
    return archive.with_name(f"{archive.name}.download.json")


def _load_download_metadata(path: Path) -> dict[str, object] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read download metadata {path}: {error}") from error
    if not isinstance(value, dict):
        raise RuntimeError(f"download metadata is not an object: {path}")
    return value


def _check_published_archive_identity(
    spec: ArchiveSpec, archive: Path, hashes: dict[str, str]
) -> None:
    size = archive.stat().st_size
    if spec.expected_size is not None and size != spec.expected_size:
        raise RuntimeError(
            f"{archive}: expected {spec.expected_size} bytes, found {size}"
        )
    if spec.published_checksum_kind == "md5":
        actual = hashes["md5"]
        if actual != spec.published_checksum:
            raise RuntimeError(
                f"{archive}: publisher MD5 mismatch; expected "
                f"{spec.published_checksum}, found {actual}"
            )


def _verify_existing_archive(
    spec: ArchiveSpec, archive: Path, trust_existing_ebu: bool
) -> str:
    algorithms = ("sha256", "md5") if spec.published_checksum_kind == "md5" else ("sha256",)
    hashes = _hash_file(archive, *algorithms)
    _check_published_archive_identity(spec, archive, hashes)

    metadata_path = _download_metadata_path(archive)
    metadata = _load_download_metadata(metadata_path)
    if metadata is not None:
        recorded = metadata.get("sha256")
        if recorded != hashes["sha256"]:
            raise RuntimeError(
                f"{archive}: SHA-256 differs from {metadata_path.name}; "
                "remove or replace the corrupt archive explicitly"
            )
    elif spec.suite == "sqam" and not trust_existing_ebu:
        raise RuntimeError(
            f"{archive} has no provenance sidecar and EBU publishes no "
            "cryptographic checksum. Remove it to download from EBU, or rerun "
            "with --trust-existing-ebu after verifying its provenance."
        )

    if metadata is None:
        _atomic_json(
            metadata_path,
            {
                "archive": spec.filename,
                "bytes": archive.stat().st_size,
                "publisher_checksum": spec.published_checksum,
                "publisher_checksum_kind": spec.published_checksum_kind,
                "provenance": "trusted existing file" if spec.suite == "sqam" else "publisher MD5",
                "sha256": hashes["sha256"],
                "url": spec.url,
            },
        )
    return hashes["sha256"]


def _download_archive(spec: ArchiveSpec, archive: Path, timeout: float) -> str:
    archive.parent.mkdir(parents=True, exist_ok=True)
    request = urllib.request.Request(
        spec.url,
        headers={"User-Agent": "vinyl-real-benchmark-fetch/1.0"},
    )
    temp_name: str | None = None
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            response_etag = _normalise_etag(response.headers.get("ETag"))
            if spec.expected_etag is not None and response_etag != spec.expected_etag:
                raise RuntimeError(
                    f"{spec.suite}: EBU object ETag changed; expected "
                    f"{spec.expected_etag}, found {response_etag!r}. Review the "
                    "new object before updating this script."
                )

            declared_length_text = response.headers.get("Content-Length")
            declared_length = (
                int(declared_length_text) if declared_length_text is not None else None
            )
            if (
                spec.expected_size is not None
                and declared_length is not None
                and declared_length != spec.expected_size
            ):
                raise RuntimeError(
                    f"{spec.suite}: server announced {declared_length} bytes; "
                    f"expected {spec.expected_size}"
                )

            sha256 = hashlib.sha256()
            md5 = hashlib.md5()
            downloaded = 0
            next_report = 32 * 1024 * 1024
            with tempfile.NamedTemporaryFile(
                "wb", dir=archive.parent, prefix=f".{archive.name}.",
                suffix=".part", delete=False,
            ) as output:
                temp_name = output.name
                while chunk := response.read(BUFFER_SIZE):
                    output.write(chunk)
                    sha256.update(chunk)
                    md5.update(chunk)
                    downloaded += len(chunk)
                    if downloaded >= next_report:
                        print(
                            f"  {spec.suite}: downloaded {downloaded / (1024 ** 2):.0f} MiB",
                            file=sys.stderr,
                        )
                        next_report += 32 * 1024 * 1024

        if declared_length is not None and downloaded != declared_length:
            raise RuntimeError(
                f"{spec.suite}: truncated download; expected {declared_length} "
                f"bytes, received {downloaded}"
            )
        hashes = {"sha256": sha256.hexdigest(), "md5": md5.hexdigest()}
        temp_path = Path(temp_name)
        _check_published_archive_identity(spec, temp_path, hashes)
        os.replace(temp_path, archive)
        temp_name = None
        _atomic_json(
            _download_metadata_path(archive),
            {
                "archive": spec.filename,
                "bytes": downloaded,
                "etag": response_etag,
                "publisher_checksum": spec.published_checksum,
                "publisher_checksum_kind": spec.published_checksum_kind,
                "provenance": "downloaded over TLS from publisher URL",
                "sha256": hashes["sha256"],
                "url": spec.url,
            },
        )
        return hashes["sha256"]
    finally:
        if temp_name is not None:
            Path(temp_name).unlink(missing_ok=True)


def _ensure_archive(
    spec: ArchiveSpec,
    downloads: Path,
    *,
    offline: bool,
    trust_existing_ebu: bool,
    timeout: float,
) -> tuple[Path, str]:
    archive = downloads / spec.filename
    if archive.exists():
        print(f"verify: {archive.relative_to(ROOT) if archive.is_relative_to(ROOT) else archive}")
        return archive, _verify_existing_archive(spec, archive, trust_existing_ebu)
    if offline:
        raise RuntimeError(f"offline mode: missing archive {archive}")
    print(f"download: {spec.url}")
    return archive, _download_archive(spec, archive, timeout)


def _member_parts(name: str) -> tuple[str, ...]:
    if not name or "\x00" in name or "\\" in name:
        raise RuntimeError(f"unsafe archive member name: {name!r}")
    path = PurePosixPath(name)
    if path.is_absolute() or any(part in ("", "..") for part in path.parts):
        raise RuntimeError(f"unsafe archive member path: {name!r}")
    parts = tuple(part for part in path.parts if part != ".")
    if not parts:
        raise RuntimeError(f"unsafe empty archive member path: {name!r}")
    return parts


def _safe_destination(root: Path, name: str) -> Path:
    destination = root.joinpath(*_member_parts(name))
    resolved_root = root.resolve()
    try:
        destination.resolve().relative_to(resolved_root)
    except ValueError as error:
        raise RuntimeError(f"archive member escapes destination: {name!r}") from error
    return destination


def _copy_atomic(source: BinaryIO, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    temp_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            "wb", dir=destination.parent, prefix=f".{destination.name}.",
            suffix=".tmp", delete=False,
        ) as output:
            temp_name = output.name
            shutil.copyfileobj(source, output, length=BUFFER_SIZE)
        os.chmod(temp_name, 0o644)
        os.replace(temp_name, destination)
        temp_name = None
    finally:
        if temp_name is not None:
            Path(temp_name).unlink(missing_ok=True)


def _check_extract_budget(sizes: Iterable[int], archive: Path) -> None:
    total = sum(sizes)
    if total > MAX_EXTRACTED_BYTES:
        raise RuntimeError(
            f"{archive}: declared extracted content is {total} bytes, above the "
            f"{MAX_EXTRACTED_BYTES}-byte safety limit"
        )


def _extract_zip(archive: Path, destination: Path) -> list[Path]:
    extracted: list[Path] = []
    with zipfile.ZipFile(archive) as bundle:
        infos = bundle.infolist()
        _check_extract_budget((info.file_size for info in infos), archive)
        seen: set[str] = set()
        for info in infos:
            target = _safe_destination(destination, info.filename)
            key = str(target).casefold()
            if key in seen:
                raise RuntimeError(f"{archive}: duplicate member path {info.filename!r}")
            seen.add(key)
            unix_mode = info.external_attr >> 16
            if stat.S_IFMT(unix_mode) == stat.S_IFLNK:
                raise RuntimeError(f"{archive}: symbolic link is not allowed: {info.filename!r}")
            if info.is_dir():
                continue
            if info.flag_bits & 0x1:
                raise RuntimeError(f"{archive}: encrypted member is not allowed: {info.filename!r}")
            if target.suffix.lower() != ".flac":
                continue
            with bundle.open(info, "r") as source:
                _copy_atomic(source, target)
            extracted.append(target)
    return sorted(extracted)


def _extract_tar(archive: Path, destination: Path) -> list[Path]:
    extracted: list[Path] = []
    with tarfile.open(archive, "r:gz") as bundle:
        members = bundle.getmembers()
        _check_extract_budget((member.size for member in members if member.isfile()), archive)
        seen: set[str] = set()
        for member in members:
            target = _safe_destination(destination, member.name)
            key = str(target).casefold()
            if key in seen:
                raise RuntimeError(f"{archive}: duplicate member path {member.name!r}")
            seen.add(key)
            if member.issym() or member.islnk():
                raise RuntimeError(f"{archive}: link is not allowed: {member.name!r}")
            if member.isdir():
                continue
            if not member.isfile():
                raise RuntimeError(
                    f"{archive}: special member is not allowed: {member.name!r}"
                )
            if target.suffix.lower() != ".flac":
                continue
            source = bundle.extractfile(member)
            if source is None:
                raise RuntimeError(f"{archive}: cannot read member {member.name!r}")
            with source:
                _copy_atomic(source, target)
            extracted.append(target)
    return sorted(extracted)


def _extract_archive(spec: ArchiveSpec, archive: Path, source_root: Path) -> list[Path]:
    destination = source_root / spec.suite
    destination.mkdir(parents=True, exist_ok=True)
    print(f"extract: {spec.suite}")
    if spec.archive_format == "zip":
        files = _extract_zip(archive, destination)
    elif spec.archive_format == "tar.gz":
        files = _extract_tar(archive, destination)
    else:
        raise AssertionError(f"unknown archive format: {spec.archive_format}")
    if not files:
        raise RuntimeError(f"{archive}: archive contains no FLAC files")
    return files


def _read_streaminfo(path: Path) -> StreamInfo:
    with path.open("rb") as stream:
        if stream.read(4) != b"fLaC":
            raise RuntimeError(f"not a native FLAC stream: {path}")
        header = stream.read(4)
        if len(header) != 4:
            raise RuntimeError(f"truncated FLAC metadata header: {path}")
        block_type = header[0] & 0x7F
        block_length = int.from_bytes(header[1:4], "big")
        if block_type != 0 or block_length != 34:
            raise RuntimeError(f"FLAC STREAMINFO is not the first 34-byte block: {path}")
        payload = stream.read(block_length)
        if len(payload) != block_length:
            raise RuntimeError(f"truncated FLAC STREAMINFO: {path}")

    packed = int.from_bytes(payload[10:18], "big")
    return StreamInfo(
        channels=((packed >> 41) & 0x7) + 1,
        sample_rate=(packed >> 44) & 0xFFFFF,
        bits_per_sample=((packed >> 36) & 0x1F) + 1,
        samples_per_channel=packed & ((1 << 36) - 1),
        pcm_md5=payload[18:34].hex(),
    )


def _manifest_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(ROOT).as_posix()
    except ValueError:
        return str(resolved)


def _sqam_category(path: Path) -> str:
    match = re.match(r"^\s*(\d{1,3})(?:[\s._-]|$)", path.stem)
    if match is None:
        return "programme-or-test-signal"
    return "test-signal" if int(match.group(1)) <= 7 else "programme"


def _category(spec: ArchiveSpec, path: Path) -> str:
    if spec.suite == "sqam":
        return _sqam_category(path)
    return "speech-clean" if spec.suite.endswith("clean") else "speech-other"


def _decode_pcm(flac_binary: str, source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    temp_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            "wb", dir=destination.parent, prefix=f".{destination.name}.",
            suffix=".tmp", delete=False,
        ) as output:
            temp_name = output.name
        command = (
            flac_binary,
            "--decode",
            "--silent",
            "--force",
            "--force-raw-format",
            "--sign=signed",
            "--endian=little",
            "--output-name",
            temp_name,
            str(source),
        )
        completed = subprocess.run(command, text=True, capture_output=True)
        if completed.returncode != 0:
            detail = completed.stderr.strip() or completed.stdout.strip()
            raise RuntimeError(f"flac failed for {source}: {detail}")
        os.replace(temp_name, destination)
        temp_name = None
    finally:
        if temp_name is not None:
            Path(temp_name).unlink(missing_ok=True)


def _can_reuse_pcm(
    previous: dict[str, str] | None,
    source_sha256: str,
    destination: Path,
    expected_bytes: int,
    streaminfo_md5: str,
) -> tuple[str, str] | None:
    if previous is None or not destination.is_file():
        return None
    if previous.get("source_sha256") != source_sha256:
        return None
    if previous.get("raw_bytes") != str(expected_bytes):
        return None
    hashes = _hash_file(destination, "sha256", "md5")
    if hashes["sha256"] != previous.get("pcm_sha256"):
        return None
    if streaminfo_md5 != "0" * 32 and hashes["md5"] != streaminfo_md5:
        return None
    return hashes["sha256"], hashes["md5"]


def _prepare_one(
    spec: ArchiveSpec,
    source: Path,
    source_suite_root: Path,
    pcm_root: Path,
    archive_sha256: str,
    flac_binary: str,
    previous: dict[str, str] | None,
) -> dict[str, str | int]:
    info = _read_streaminfo(source)
    if info.bits_per_sample != 16:
        raise RuntimeError(
            f"{source}: expected 16-bit source material, found "
            f"{info.bits_per_sample}-bit"
        )
    if info.channels not in (1, 2):
        raise RuntimeError(
            f"{source}: Vinyl benchmark supports mono/stereo, found "
            f"{info.channels} channels"
        )
    if info.sample_rate <= 0 or info.samples_per_channel <= 0:
        raise RuntimeError(f"{source}: invalid or unknown STREAMINFO sample count/rate")

    relative = source.relative_to(source_suite_root)
    destination = pcm_root / spec.suite / relative.with_suffix(".pcm")
    source_sha256 = _hash_file(source, "sha256")["sha256"]
    expected_bytes = info.samples_per_channel * info.channels * 2
    pcm_hashes = _can_reuse_pcm(
        previous, source_sha256, destination, expected_bytes, info.pcm_md5
    )
    if pcm_hashes is None:
        _decode_pcm(flac_binary, source, destination)
        actual_bytes = destination.stat().st_size
        if actual_bytes != expected_bytes:
            raise RuntimeError(
                f"{source}: decoded {actual_bytes} bytes, STREAMINFO predicts "
                f"{expected_bytes}"
            )
        hashes = _hash_file(destination, "sha256", "md5")
        if info.pcm_md5 != "0" * 32 and hashes["md5"] != info.pcm_md5:
            raise RuntimeError(
                f"{source}: decoded PCM MD5 {hashes['md5']} does not match "
                f"STREAMINFO {info.pcm_md5}"
            )
        pcm_sha256 = hashes["sha256"]
    else:
        pcm_sha256, _ = pcm_hashes

    logical_stem = relative.with_suffix("").as_posix()
    return {
        "suite": spec.suite,
        "category": _category(spec, relative),
        "file": f"{spec.suite}/{logical_stem}",
        "path": _manifest_path(destination),
        "source_path": _manifest_path(source),
        "channels": info.channels,
        "sample_rate": info.sample_rate,
        "bits_per_sample": info.bits_per_sample,
        "samples_per_channel": info.samples_per_channel,
        "raw_bytes": expected_bytes,
        "pcm_sha256": pcm_sha256,
        "source_sha256": source_sha256,
        "source_streaminfo_md5": info.pcm_md5,
        "source_url": spec.url,
        "archive": spec.filename,
        "archive_sha256": archive_sha256,
        "archive_checksum_kind": spec.published_checksum_kind,
        "archive_checksum": spec.published_checksum,
        "license": spec.license,
    }


def _load_manifest(path: Path) -> list[dict[str, str]]:
    try:
        stream = path.open(newline="", encoding="utf-8")
    except FileNotFoundError:
        return []
    with stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != list(MANIFEST_FIELDS):
            raise RuntimeError(
                f"{path}: unsupported manifest columns; expected "
                f"{','.join(MANIFEST_FIELDS)}"
            )
        return list(reader)


def _write_manifest(path: Path, rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            "w", newline="", encoding="utf-8", dir=path.parent,
            prefix=f".{path.name}.", suffix=".tmp", delete=False,
        ) as stream:
            temp_name = stream.name
            writer = csv.DictWriter(
                stream, fieldnames=MANIFEST_FIELDS, lineterminator="\n"
            )
            writer.writeheader()
            writer.writerows(rows)
        os.replace(temp_name, path)
        temp_name = None
    finally:
        if temp_name is not None:
            Path(temp_name).unlink(missing_ok=True)


def _expand_suites(values: list[str]) -> list[str]:
    expanded: set[str] = set()
    for value in values:
        if value == "all":
            expanded.update(ARCHIVES)
        elif value == "librispeech":
            expanded.update(("librispeech-test-clean", "librispeech-test-other"))
        else:
            expanded.add(value)
    return [suite for suite in ARCHIVES if suite in expanded]


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fetch EBU SQAM and/or LibriSpeech and emit canonical S16LE PCM.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--corpus",
        action="append",
        required=True,
        choices=("sqam", "librispeech", "librispeech-test-clean", "librispeech-test-other", "all"),
        help="corpus to prepare; may be repeated",
    )
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=DEFAULT_DATA,
        help="generated corpus root",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="parallel FLAC decode/hash workers",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="per-network-operation timeout in seconds",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="use verified archives already in downloads/; never access the network",
    )
    parser.add_argument(
        "--accept-ebu-terms",
        action="store_true",
        help="acknowledge SQAM's R&D/non-commercial-use restriction",
    )
    parser.add_argument(
        "--trust-existing-ebu",
        action="store_true",
        help="accept a size-pinned SQAM archive lacking this script's SHA-256 sidecar",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    suites = _expand_suites(args.corpus)
    if "sqam" in suites and not args.accept_ebu_terms:
        parser.error("SQAM requires --accept-ebu-terms; see the EBU terms linked in the script")
    args.suites = suites
    return args


def main() -> None:
    args = _parse_args()
    flac_binary = shutil.which("flac")
    if flac_binary is None:
        raise SystemExit("flac executable not found; install libFLAC's command-line tools")

    data_root = args.data_dir.resolve()
    downloads = data_root / "downloads"
    source_root = data_root / "source"
    pcm_root = data_root / "pcm"
    manifest_path = data_root / "manifest.csv"
    downloads.mkdir(parents=True, exist_ok=True)
    source_root.mkdir(parents=True, exist_ok=True)
    pcm_root.mkdir(parents=True, exist_ok=True)

    old_rows = _load_manifest(manifest_path)
    selected = set(args.suites)
    previous_by_source = {
        (row["suite"], row["source_path"]): row
        for row in old_rows
        if row["suite"] in selected
    }
    new_rows: list[dict[str, object]] = [
        dict(row) for row in old_rows if row["suite"] not in selected
    ]

    for suite in args.suites:
        spec = ARCHIVES[suite]
        archive, archive_sha256 = _ensure_archive(
            spec,
            downloads,
            offline=args.offline,
            trust_existing_ebu=args.trust_existing_ebu,
            timeout=args.timeout,
        )
        sources = _extract_archive(spec, archive, source_root)
        suite_source_root = source_root / suite
        print(f"prepare: {suite} ({len(sources)} FLAC files)")
        completed_rows: list[dict[str, str | int]] = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {}
            for source in sources:
                source_key = (suite, _manifest_path(source))
                future = pool.submit(
                    _prepare_one,
                    spec,
                    source,
                    suite_source_root,
                    pcm_root,
                    archive_sha256,
                    flac_binary,
                    previous_by_source.get(source_key),
                )
                futures[future] = source
            total = len(futures)
            for count, future in enumerate(as_completed(futures), start=1):
                try:
                    completed_rows.append(future.result())
                except Exception as error:
                    source = futures[future]
                    raise RuntimeError(f"failed while preparing {source}: {error}") from error
                if count == total or count % 100 == 0:
                    print(f"  {suite}: prepared {count}/{total}")
        new_rows.extend(completed_rows)

    new_rows.sort(key=lambda row: (str(row["suite"]), str(row["file"])))
    _write_manifest(manifest_path, new_rows)
    total_bytes = sum(int(row["raw_bytes"]) for row in new_rows)
    print(
        f"manifest: {_manifest_path(manifest_path)} "
        f"({len(new_rows)} files, {total_bytes / (1024 ** 3):.2f} GiB S16LE)"
    )


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, tarfile.TarError, zipfile.BadZipFile) as error:
        raise SystemExit(f"error: {error}") from error
