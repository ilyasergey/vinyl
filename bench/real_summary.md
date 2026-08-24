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
| sqam | 150 MB/s | 122 MB/s | 63 MB/s | 262 MB/s | 227 MB/s | 201 MB/s |
| librispeech-test-clean | 137 MB/s | 153 MB/s | 89 MB/s | 368 MB/s | 212 MB/s | 188 MB/s |
| librispeech-test-other | 138 MB/s | 155 MB/s | 89 MB/s | 376 MB/s | 215 MB/s | 189 MB/s |
| **TOTAL** | 142 MB/s | 142 MB/s | 78 MB/s | 326 MB/s | 218 MB/s | 192 MB/s |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode (decode) | flac decode |
|---:|---|---|---|---|
| 1 | 28 MB/s | 78 MB/s | 49 MB/s | 192 MB/s |
| 2 | 52 MB/s | 147 MB/s | 89 MB/s | no `-j` |
| 4 | 101 MB/s | 269 MB/s | 166 MB/s | no `-j` |
| 8 | 142 MB/s | 326 MB/s | 218 MB/s | no `-j` |

Speedup at 8 threads: vinyl 5.12×, flac -8 4.17×, vinyl decode 4.48×.
