| category | vinyl | flac -0 | flac -5 | flac -8 |
|---|---|---|---|---|
| tonal | 22.9% | 39.4% | 21.5% | 19.3% |
| wave | 39.2% | 43.7% | 43.1% | 40.1% |
| noise | 77.8% | 77.1% | 76.7% | 76.7% |
| mixed | 72.2% | 71.7% | 70.2% | 70.0% |
| degen | 22.1% | 45.8% | 22.0% | 22.0% |
| stereo | 27.5% | 31.4% | 26.3% | 26.2% |
| TOTAL | 40.6% | 48.6% | 40.2% | 39.0% |

Whole-file totals, metadata included (libFLAC writes 8.8 kB per file, Vinyl 42 bytes):

| vinyl | flac -0 | flac -5 | flac -8 |
|---|---|---|---|
| 40.6% | 49.4% | 40.9% | 39.8% |

### Scaling with thread count, corpus throughput

| threads | vinyl (encode) | flac -8 (encode) | vinyl decode | flac decode |
|---:|---|---|---|---|
| 1 | 46.6 MB/s | 87.6 MB/s | 69.8 MB/s | 149.9 MB/s |
| 2 | 79.6 MB/s | 127.3 MB/s | 108.3 MB/s | no `-j` |
| 4 | 122.9 MB/s | 171.6 MB/s | 142.6 MB/s | no `-j` |
| 8 | 158.6 MB/s | 185.3 MB/s | 160.7 MB/s | no `-j` |

Speedup at 8 threads: vinyl 3.40×, flac -8 2.11×, vinyl decode 2.30×.
