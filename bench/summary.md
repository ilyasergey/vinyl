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
| 1 | 63.9 MB/s | 144.0 MB/s | 122.7 MB/s | 230.7 MB/s |
| 2 | 106.6 MB/s | 219.5 MB/s | 170.5 MB/s | no `-j` |
| 4 | 157.0 MB/s | 310.3 MB/s | 207.8 MB/s | no `-j` |
| 8 | 192.8 MB/s | 335.1 MB/s | 221.3 MB/s | no `-j` |

Speedup at 8 threads: vinyl 3.02×, flac -8 2.33×, vinyl decode 1.80×.
