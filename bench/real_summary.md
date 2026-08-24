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
| sqam | 156 MB/s | 121 MB/s | 63 MB/s | 257 MB/s | 221 MB/s | 199 MB/s |
| librispeech-test-clean | 138 MB/s | 152 MB/s | 88 MB/s | 354 MB/s | 205 MB/s | 187 MB/s |
| librispeech-test-other | 146 MB/s | 154 MB/s | 89 MB/s | 376 MB/s | 215 MB/s | 189 MB/s |
| **TOTAL** | 146 MB/s | 141 MB/s | 78 MB/s | 320 MB/s | 213 MB/s | 191 MB/s |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode (decode) | flac decode |
|---:|---|---|---|---|
| 1 | 29 MB/s | 78 MB/s | 48 MB/s | 191 MB/s |
| 2 | 55 MB/s | 146 MB/s | 88 MB/s | no `-j` |
| 4 | 106 MB/s | 266 MB/s | 164 MB/s | no `-j` |
| 8 | 146 MB/s | 320 MB/s | 213 MB/s | no `-j` |

Speedup at 8 threads: vinyl 5.02×, flac -8 4.10×, vinyl decode 4.42×.
