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

write("sine-440", (12000 * math.sin(2 * math.pi * 440 * i / 44100) for i in range(N)))
write("sine-sweep", (10000 * math.sin(2 * math.pi * (100 + 4000 * i / N) * i / 44100) for i in range(N)))
write("chord", (4000 * math.sin(2 * math.pi * 261.6 * i / 44100)
                + 4000 * math.sin(2 * math.pi * 329.6 * i / 44100)
                + 4000 * math.sin(2 * math.pi * 392.0 * i / 44100) for i in range(N)))
write("square-1k", (9000 if (i * 1000 // 44100) % 2 == 0 else -9000 for i in range(N)))
write("sawtooth", ((i % 200) * 100 - 10000 for i in range(N)))
write("silence", (0 for _ in range(N)))
write("dc-offset", (1234 for _ in range(N)))
write("white-noise", (rng.randint(-20000, 20000) for _ in range(N)))

# brown-ish noise: integrated white (very predictable)
acc, brown = 0, []
for _ in range(N):
    acc = max(-30000, min(30000, acc + rng.randint(-200, 200)))
    brown.append(acc)
write("brown-noise", brown)

# music-like: enveloped chord + soft noise
write("music-like", (
    (0.5 + 0.5 * math.sin(2 * math.pi * i / 80000))
    * (6000 * math.sin(2 * math.pi * 220 * i / 44100)
       + 3000 * math.sin(2 * math.pi * 277.2 * i / 44100))
    + rng.gauss(0, 120) for i in range(N)))

# speech-like: bursts of AM noise separated by near-silence
speech = []
for i in range(N):
    burst = (i // 8000) % 3 != 2
    env = 0.5 + 0.5 * math.sin(2 * math.pi * i / 3000)
    speech.append(rng.gauss(0, 5000 * env) if burst else rng.gauss(0, 60))
write("speech-like", speech)

# full-scale (clipping-adjacent) sine
write("fullscale-sine", (32767 * math.sin(2 * math.pi * 100 * i / 44100) for i in range(N)))
