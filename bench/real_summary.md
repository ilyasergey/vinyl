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
| sqam | 310 MB/s | 164 MB/s | 83 MB/s | 438 MB/s | 378 MB/s | 261 MB/s |
| librispeech-test-clean | 284 MB/s | 201 MB/s | 115 MB/s | 570 MB/s | 359 MB/s | 245 MB/s |
| librispeech-test-other | 292 MB/s | 207 MB/s | 117 MB/s | 596 MB/s | 371 MB/s | 250 MB/s |
| **TOTAL** | 295 MB/s | 189 MB/s | 102 MB/s | 524 MB/s | 369 MB/s | 252 MB/s |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode (decode) | flac decode |
|---:|---|---|---|---|
| 1 | 46 MB/s | 102 MB/s | 68 MB/s | 252 MB/s |
| 2 | 90 MB/s | 193 MB/s | 129 MB/s | no `-j` |
| 4 | 170 MB/s | 355 MB/s | 234 MB/s | no `-j` |
| 8 | 295 MB/s | 524 MB/s | 369 MB/s | no `-j` |

Speedup at 8 threads: vinyl 6.38×, flac -8 5.13×, vinyl decode 5.47×.
