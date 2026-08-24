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

### Corpus throughput at 8 threads, total raw MB ÷ total seconds

| suite | vinyl -j8 | flac -5 -j1 | flac -8 -j1 | flac -8 -j8 | vinyl decode -j8 | flac decode -j1 |
|---|---|---|---|---|---|---|
| sqam | 107 MB/s | 121 MB/s | 63 MB/s | 268 MB/s | 225 MB/s | 197 MB/s |
| librispeech-test-clean | 98 MB/s | 153 MB/s | 86 MB/s | 383 MB/s | 213 MB/s | 186 MB/s |
| librispeech-test-other | 97 MB/s | 155 MB/s | 89 MB/s | 382 MB/s | 213 MB/s | 187 MB/s |
| **TOTAL** | 101 MB/s | 141 MB/s | 77 MB/s | 335 MB/s | 217 MB/s | 190 MB/s |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode (decode) | flac decode |
|---:|---|---|---|---|
| 1 | 18 MB/s | 77 MB/s | 46 MB/s | 190 MB/s |
| 2 | 35 MB/s | 147 MB/s | 85 MB/s | no `-j` |
| 4 | 67 MB/s | 270 MB/s | 158 MB/s | no `-j` |
| 8 | 101 MB/s | 335 MB/s | 217 MB/s | no `-j` |

Speedup at 8 threads: vinyl 5.53×, flac -8 4.33×, vinyl decode 4.70×.
