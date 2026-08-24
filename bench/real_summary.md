### Compression, audio-frame payload as % of raw PCM

| category | units | vinyl | flac -5 | flac -8 |
|---|---:|---|---|---|
| alignment | 2 | 22.0% | 22.0% | 20.9% |
| artificial | 5 | 7.6% | 7.8% | 7.4% |
| single-instrument | 36 | 29.0% | 27.4% | 27.1% |
| solo-instrument | 6 | 32.4% | 30.8% | 30.5% |
| vocal | 5 | 34.9% | 33.2% | 32.6% |
| vocal-orchestra | 4 | 41.3% | 39.6% | 39.3% |
| orchestra | 4 | 34.1% | 32.2% | 32.1% |
| pop | 2 | 40.4% | 38.9% | 38.4% |
| speech | 6 | 31.9% | 30.8% | 30.4% |
| speech-clean | 40 | 57.5% | 55.9% | 55.2% |
| speech-other | 33 | 55.2% | 53.6% | 52.9% |
| **TOTAL** | 143 | 47.6% | 46.1% | 45.5% |

### Whole-file size as % of raw PCM (metadata included)

| vinyl | flac -5 | flac -8 |
|---|---|---|
| 47.6% | 46.1% | 45.6% |

### Corpus throughput, total raw MB ÷ total seconds

| suite | vinyl | flac -5 | flac -8 | flac -8 -j8 | vinyl decode | flac decode |
|---|---|---|---|---|---|---|
| sqam | 101 MB/s | 122 MB/s | 62 MB/s | 256 MB/s | 214 MB/s | 197 MB/s |
| librispeech-test-clean | 95 MB/s | 153 MB/s | 89 MB/s | 374 MB/s | 207 MB/s | 187 MB/s |
| librispeech-test-other | 88 MB/s | 151 MB/s | 86 MB/s | 355 MB/s | 195 MB/s | 183 MB/s |
| **TOTAL** | 94 MB/s | 140 MB/s | 77 MB/s | 319 MB/s | 205 MB/s | 189 MB/s |
