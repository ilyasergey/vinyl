# Real-audio benchmark corpora

The audio is downloaded into `bench/real_data/` and is deliberately not
committed.  The repository contains the fetcher, publisher checksums, licence
notes, and preparation rules needed to reproduce it.  The results themselves
are committed: [`real_results.csv`](real_results.csv) and
[`real_summary.md`](real_summary.md).  [`real_corpora.lock.json`](real_corpora.lock.json)
records the exact archives fetched for this preparation, including locally
observed SHA-256 digests.

## Quick start: EBU SQAM

SQAM is the default because its 167.4 MiB archive is compact, varied, and
already in Vinyl's current encoder format: stereo signed 16-bit PCM at
44.1 kHz.  Review the linked EBU terms before accepting them:

```sh
python3 bench/real_fetch.py --list
python3 bench/real_fetch.py --accept-ebu-terms
```

The command downloads, verifies, safely extracts, and losslessly decodes all
70 tracks.  It writes `bench/real_data/manifest.csv`, including the native
format, source and PCM SHA-256 hashes, STREAMINFO MD5, provenance, and licence
for every input.  A completed preparation contains 620,398,800 raw PCM bytes
(0.58 GiB, 58.6 minutes).

The manifest uses the categories from EBU Tech 3253:

| category | tracks | files |
|---|---|---:|
| alignment | 1–2 | 2 |
| artificial | 3–7 | 5 |
| single-instrument | 8–43 | 36 |
| vocal | 44–48 | 5 |
| speech | 49–54 | 6 |
| solo-instrument | 55–60 | 6 |
| vocal-orchestra | 61–64 | 4 |
| orchestra | 65–68 | 4 |
| pop | 69–70 | 2 |

To inspect or make a category-specific manifest without copying audio:

```sh
awk -F, 'NR == 1 || $2 == "speech"' bench/real_data/manifest.csv
awk -F, 'NR == 1 || $2 ~ /^(vocal|vocal-orchestra|orchestra|pop)$/' \
  bench/real_data/manifest.csv > /tmp/sqam-music.csv
```

The EBU download is approved for R&D use but restricts other commercial use.
It publishes a versioned byte size and S3 ETag rather than a cryptographic
digest.  The fetcher validates those properties, calculates SHA-256, and
stores a provenance sidecar beside the archive.  Do not commit or redistribute
the recordings.  Sources: [download record](https://qc.ebu.io/testmaterials/523/)
and [Tech 3253 handbook](https://tech.ebu.ch/publications/tech3253).

## Optional: LibriSpeech test sets

LibriSpeech is an explicit opt-in because the two test archives total
644.1 MiB before extraction and produce thousands of files:

```sh
# One category only
python3 bench/real_fetch.py --corpus librispeech-test-clean
python3 bench/real_fetch.py --corpus librispeech-test-other

# Both speech categories
python3 bench/real_fetch.py --corpus librispeech
```

| selector | archive bytes | official MD5 | category |
|---|---:|---|---|
| `librispeech-test-clean` | 346,663,984 | `32fa31d27d2e1cad72775fee3f4849a9` | `speech-clean` |
| `librispeech-test-other` | 328,757,843 | `fb5a50374b501bb3bac4815ee91d3135` | `speech-other` |

The fetcher verifies the OpenSLR MD5 and records a local SHA-256.  The material
is CC BY 4.0, signed 16-bit, 16 kHz mono.  It is never resampled.  Vinyl's
current public encoder hardcodes 44.1 kHz metadata, so use these files for
decoder testing or wait for a sample-rate-aware encoder driver; do not publish
an encode comparison with incorrect metadata.  Source: [OpenSLR 12](https://www.openslr.org/12/).

## Optional multi-gigabyte corpora

These are not part of the default fetch.  Their commands and identities are
recorded here so a human or later agent can opt in deliberately.

### FSD50K evaluation audio

FSD50K provides uncompressed signed 16-bit, 44.1 kHz mono WAV, directly
compatible with Vinyl.  The complete dataset is 24.7 GB; the evaluation audio
alone is a split archive of roughly 6.2 GB containing 10,231 short clips.

```sh
mkdir -p bench/real_data/downloads/fsd50k
cd bench/real_data/downloads/fsd50k
curl -fLO 'https://zenodo.org/records/4060432/files/FSD50K.eval_audio.z01?download=1'
curl -fLO 'https://zenodo.org/records/4060432/files/FSD50K.eval_audio.zip?download=1'
curl -fLO 'https://zenodo.org/records/4060432/files/FSD50K.ground_truth.zip?download=1'
curl -fLO 'https://zenodo.org/records/4060432/files/FSD50K.metadata.zip?download=1'
md5sum FSD50K.eval_audio.z01 FSD50K.eval_audio.zip
zip -s 0 FSD50K.eval_audio.zip --out FSD50K.eval_audio.unsplit.zip
unzip FSD50K.eval_audio.unsplit.zip
```

Expected MD5 values are `3090670eaeecc013ca1ff84fe4442aeb` for `.z01`,
`6fa47636c3a3ad5c7dfeba99f2637982` for `.zip`,
`ca27382c195e37d2269c4c866dd73485` for ground truth, and
`b9ea0c829a411c1d42adb9da539ed237` for metadata.  Select only CC0/CC-BY clips
using the supplied per-clip metadata, then choose deterministically by class
and file id.  Concatenate short clips into fixed-size streams for steady-state
throughput; keep individual clips only for a separately labelled startup test.
Source: [FSD50K 1.0](https://zenodo.org/records/4060432).

### MUSDB18-HQ

MUSDB18-HQ is 22.7 GB and contains 150 full-length 44.1 kHz stereo songs.
Access is gated and academic-use-only, so there is no unattended fetch command.
Request access from the [official MUSDB page](https://sigsep.github.io/datasets/musdb.html#musdb18-hq-uncompressed-wav),
place `musdb18hq.zip` under `bench/real_data/downloads/`, and verify MD5
`12d4f2ecd55245a4688754dd76363103`.  Benchmark `mixture.wav` only—using the
four stems as extra tracks would overweight correlated copies.  Prefer all 50
test mixtures, or document an immutable hash-selected subset.

### MAESTRO v3

MAESTRO is a useful long, tonal stress corpus, not a balanced headline corpus.
The archive is 101 GB (120.2 GB extracted), contains 16-bit stereo WAV at
44.1–48 kHz, and is CC BY-NC-SA 4.0:

```sh
curl -fL -o bench/real_data/downloads/maestro-v3.0.0.zip \
  https://storage.googleapis.com/magentadata/datasets/maestro/v3.0.0/maestro-v3.0.0.zip
shasum -a 256 bench/real_data/downloads/maestro-v3.0.0.zip
```

Expected SHA-256:
`6680fea5be2339ea15091a249fbd70e49551246ddbd5ca50f1b2352c08c95291`.
Use the published test split and preserve native rates.  Source:
[MAESTRO v3](https://magenta.tensorflow.org/datasets/maestro).

## Reusing an existing download

Preparation is incremental.  To verify and rebuild from local archives without
network access:

```sh
python3 bench/real_fetch.py --corpus sqam --accept-ebu-terms --offline
python3 bench/real_fetch.py --corpus librispeech --offline
```

`--trust-existing-ebu` is intentionally required once for an EBU archive that
predates its generated provenance sidecar.  It should be used only after the
human has independently established where that existing file came from.

## Clearing it and starting over

There is no `--force`: every stage reuses what it finds, so a refetch means
deleting the stage you want rebuilt.  `rm -rf bench/real_data` then re-running
the fetch commands above rebuilds everything from the publishers (811.5 MiB of
downloads, 4.6 GB prepared).  For a partial reset — which directory maps to
which stage, and the three reuse rules that decide whether a partial delete does
what you want — see
[Clearing and re-fetching](README.md#clearing-and-re-fetching) in the benchmark
README.
