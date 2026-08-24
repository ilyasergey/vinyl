### Compression, audio-frame payload as % of raw PCM

| category | units | vinyl | flac -5 | flac -8 |
|---|---:|---|---|---|
| alignment | 2 | 23.2% | 22.0% | 20.9% |
| artificial | 5 | 8.3% | 7.8% | 7.4% |
| single-instrument | 36 | 29.0% | 27.4% | 27.1% |
| solo-instrument | 6 | 32.4% | 30.8% | 30.5% |
| vocal | 5 | 34.9% | 33.2% | 32.6% |
| vocal-orchestra | 4 | 41.3% | 39.6% | 39.3% |
| orchestra | 4 | 34.1% | 32.2% | 32.1% |
| pop | 2 | 40.4% | 38.9% | 38.4% |
| speech | 6 | 32.0% | 30.8% | 30.4% |
| speech-clean | 40 | 57.5% | 55.9% | 55.2% |
| speech-other | 33 | 55.3% | 53.6% | 52.9% |
| **TOTAL** | 143 | 47.7% | 46.1% | 45.5% |

### Whole-file size as % of raw PCM (metadata included)

| vinyl | flac -5 | flac -8 |
|---|---|---|
| 47.7% | 46.1% | 45.6% |

### Corpus throughput at 8 threads, total raw MB ÷ total seconds

| suite | vinyl -j8 | flac -5 -j1 | flac -8 -j1 | flac -8 -j8 | vinyl decode -j8 | flac decode -j1 |
|---|---|---|---|---|---|---|
| sqam | 142 MB/s | 123 MB/s | 63 MB/s | 266 MB/s | 223 MB/s | 200 MB/s |
| librispeech-test-clean | 132 MB/s | 154 MB/s | 89 MB/s | 379 MB/s | 210 MB/s | 187 MB/s |
| librispeech-test-other | 133 MB/s | 156 MB/s | 90 MB/s | 388 MB/s | 213 MB/s | 188 MB/s |
| **TOTAL** | 136 MB/s | 143 MB/s | 79 MB/s | 334 MB/s | 215 MB/s | 191 MB/s |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode (decode) | flac decode |
|---:|---|---|---|---|
| 1 | 26 MB/s | 79 MB/s | 46 MB/s | 191 MB/s |
| 2 | 48 MB/s | 148 MB/s | 85 MB/s | no `-j` |
| 4 | 94 MB/s | 272 MB/s | 159 MB/s | no `-j` |
| 8 | 136 MB/s | 334 MB/s | 215 MB/s | no `-j` |

Speedup at 8 threads: vinyl 5.30×, flac -8 4.24×, vinyl decode 4.63×.
