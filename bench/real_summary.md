### Compression, audio-frame payload as % of raw PCM

| category | units | vinyl | flac -5 | flac -8 |
|---|---:|---|---|---|
| alignment | 2 | 23.5% | 22.0% | 20.9% |
| artificial | 5 | 8.3% | 7.8% | 7.4% |
| single-instrument | 36 | 29.2% | 27.4% | 27.1% |
| solo-instrument | 6 | 32.6% | 30.8% | 30.5% |
| vocal | 5 | 35.4% | 33.2% | 32.6% |
| vocal-orchestra | 4 | 41.7% | 39.6% | 39.3% |
| orchestra | 4 | 34.2% | 32.2% | 32.1% |
| pop | 2 | 40.7% | 38.9% | 38.4% |
| speech | 6 | 32.0% | 30.8% | 30.4% |
| speech-clean | 40 | 57.7% | 55.9% | 55.2% |
| speech-other | 33 | 55.5% | 53.6% | 52.9% |
| **TOTAL** | 143 | 47.9% | 46.1% | 45.5% |

### Whole-file size as % of raw PCM (metadata included)

| vinyl | flac -5 | flac -8 |
|---|---|---|
| 47.9% | 46.1% | 45.6% |

### Corpus throughput at 8 threads, total raw MB ÷ total seconds

| suite | vinyl -j8 | flac -5 -j1 | flac -8 -j1 | flac -8 -j8 | vinyl decode -j8 | flac decode -j1 |
|---|---|---|---|---|---|---|
| sqam | 422 MB/s | 265 MB/s | 117 MB/s | 620 MB/s | 505 MB/s | 289 MB/s |
| librispeech-test-clean | 405 MB/s | 303 MB/s | 155 MB/s | 669 MB/s | 539 MB/s | 276 MB/s |
| librispeech-test-other | 358 MB/s | 285 MB/s | 145 MB/s | 621 MB/s | 466 MB/s | 256 MB/s |
| **TOTAL** | 393 MB/s | 283 MB/s | 137 MB/s | 636 MB/s | 502 MB/s | 273 MB/s |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode (decode) | flac decode |
|---:|---|---|---|---|
| 1 | 72 MB/s | 137 MB/s | 153 MB/s | 273 MB/s |
| 2 | 135 MB/s | 255 MB/s | 260 MB/s | no `-j` |
| 4 | 241 MB/s | 450 MB/s | 400 MB/s | no `-j` |
| 8 | 393 MB/s | 636 MB/s | 502 MB/s | no `-j` |

Speedup at 8 threads: vinyl 5.47×, flac -8 4.63×, vinyl decode 3.29×.
