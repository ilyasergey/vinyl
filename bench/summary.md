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
| 1 | 31.1 MB/s | 72.8 MB/s | 51.2 MB/s | 133.4 MB/s |
| 2 | 53.5 MB/s | 113.3 MB/s | 80.4 MB/s | no `-j` |
| 4 | 88.8 MB/s | 162.1 MB/s | 110.9 MB/s | no `-j` |
| 8 | 111.2 MB/s | 175.6 MB/s | 123.0 MB/s | no `-j` |

Speedup at 8 threads: vinyl 3.57×, flac -8 2.41×, vinyl decode 2.40×.
