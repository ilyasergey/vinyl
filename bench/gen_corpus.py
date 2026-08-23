#!/usr/bin/env python3
"""Generate the synthetic benchmark corpus: mono 16-bit LE PCM, 500k samples
per file. Deterministic (seeded); files are cheap to regenerate and are not
committed (see .gitignore)."""
import math
import os
import random
import struct
import sys

N = 500_000
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "corpus")
os.makedirs(OUT, exist_ok=True)

def clamp(v):
    return max(-32768, min(32767, int(v)))

def write(name, samples):
    with open(os.path.join(OUT, name + ".pcm"), "wb") as f:
        f.write(b"".join(struct.pack("<h", clamp(v)) for v in samples))
    print(name)

rng = random.Random(9639)

# pure tones at several frequencies and amplitudes
for f in (110, 440, 1000, 3000, 8000):
    write(f"sine-{f}", (12000 * math.sin(2 * math.pi * f * i / 44100) for i in range(N)))
write("fullscale-sine", (32767 * math.sin(2 * math.pi * 100 * i / 44100) for i in range(N)))
write("quiet-sine", (300 * math.sin(2 * math.pi * 440 * i / 44100) for i in range(N)))

# sweeps at different rates
for tag, span in (("slow", 2000), ("fast", 8000)):
    write(f"sweep-{tag}", (10000 * math.sin(2 * math.pi * (100 + span * i / N) * i / 44100) for i in range(N)))

# chords / harmonic stacks
write("chord-major", (4000 * math.sin(2 * math.pi * 261.6 * i / 44100)
                      + 4000 * math.sin(2 * math.pi * 329.6 * i / 44100)
                      + 4000 * math.sin(2 * math.pi * 392.0 * i / 44100) for i in range(N)))
write("harmonics", (sum(3000 / k * math.sin(2 * math.pi * 220 * k * i / 44100)
                        for k in range(1, 8)) for i in range(N)))

# square / saw / triangle at two rates each
for f in (200, 1000):
    write(f"square-{f}", (9000 if (i * f // 44100) % 2 == 0 else -9000 for i in range(N)))
    period = 44100 // f
    write(f"saw-{f}", ((i % period) * (20000 // period) - 10000 for i in range(N)))
    write(f"triangle-{f}", ((abs((i % period) - period // 2) * (40000 // period)) - 10000 for i in range(N)))

# degenerate content
write("silence", (0 for _ in range(N)))
write("dc-offset", (1234 for _ in range(N)))
write("wasted-3bits", ((rng.randint(-4000, 4000) * 8) for _ in range(N)))
write("alternating-max", (32767 if i % 2 == 0 else -32768 for i in range(N)))

# noise at several amplitudes
for amp in (500, 5000, 20000, 32000):
    write(f"white-{amp}", (rng.randint(-amp, amp) for _ in range(N)))

# brown noise at two step sizes
for tag, step in (("smooth", 60), ("rough", 400)):
    acc, brown = 0, []
    for _ in range(N):
        acc = max(-30000, min(30000, acc + rng.randint(-step, step)))
        brown.append(acc)
    write(f"brown-{tag}", brown)

# tonal + noise mixes at several SNRs
for tag, namp in (("clean", 60), ("mid", 600), ("dirty", 3000)):
    write(f"music-{tag}", (
        (0.5 + 0.5 * math.sin(2 * math.pi * i / 80000))
        * (6000 * math.sin(2 * math.pi * 220 * i / 44100)
           + 3000 * math.sin(2 * math.pi * 277.2 * i / 44100))
        + rng.gauss(0, namp) for i in range(N)))

# speech-like: bursts of AM noise separated by near-silence
for tag, blen in (("fast", 3000), ("slow", 12000)):
    speech = []
    for i in range(N):
        burst = (i // blen) % 3 != 2
        env = 0.5 + 0.5 * math.sin(2 * math.pi * i / 3000)
        speech.append(rng.gauss(0, 5000 * env) if burst else rng.gauss(0, 60))
    write(f"speech-{tag}", speech)

# stereo-ish decorrelation test folded to mono (rapid pan)
write("tremolo", (8000 * math.sin(2 * math.pi * 440 * i / 44100)
                  * math.sin(2 * math.pi * 8 * i / 44100) for i in range(N)))
