#!/usr/bin/env python3
"""Generate the synthetic benchmark corpus: 16-bit LE PCM, 500k samples per
channel. File names are `<category>-<name>[.2ch].pcm`; the category prefix
(tonal / wave / noise / mixed / degen / stereo) drives the per-category
report. Deterministic (seeded); not committed."""
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

def write2(name, pairs):
    with open(os.path.join(OUT, name + ".2ch.pcm"), "wb") as f:
        f.write(b"".join(struct.pack("<hh", clamp(l), clamp(r)) for l, r in pairs))
    print(name + " (stereo)")

rng = random.Random(9639)

# ── tonal: sines, chords, harmonic stacks ────────────────────────────────
for f in (110, 440, 1000, 3000, 8000):
    write(f"tonal-sine-{f}", (12000 * math.sin(2 * math.pi * f * i / 44100) for i in range(N)))
write("tonal-fullscale", (32767 * math.sin(2 * math.pi * 100 * i / 44100) for i in range(N)))
write("tonal-quiet", (300 * math.sin(2 * math.pi * 440 * i / 44100) for i in range(N)))
for tag, span in (("slow", 2000), ("fast", 8000)):
    write(f"tonal-sweep-{tag}", (10000 * math.sin(2 * math.pi * (100 + span * i / N) * i / 44100) for i in range(N)))
write("tonal-chord", (4000 * math.sin(2 * math.pi * 261.6 * i / 44100)
                      + 4000 * math.sin(2 * math.pi * 329.6 * i / 44100)
                      + 4000 * math.sin(2 * math.pi * 392.0 * i / 44100) for i in range(N)))
write("tonal-harmonics", (sum(3000 / k * math.sin(2 * math.pi * 220 * k * i / 44100)
                              for k in range(1, 8)) for i in range(N)))

# ── wave: square / saw / triangle ────────────────────────────────────────
for f in (200, 1000):
    write(f"wave-square-{f}", (9000 if (i * f // 44100) % 2 == 0 else -9000 for i in range(N)))
    period = 44100 // f
    write(f"wave-saw-{f}", ((i % period) * (20000 // period) - 10000 for i in range(N)))
    write(f"wave-triangle-{f}", ((abs((i % period) - period // 2) * (40000 // period)) - 10000 for i in range(N)))
write("wave-tremolo", (8000 * math.sin(2 * math.pi * 440 * i / 44100)
                       * math.sin(2 * math.pi * 8 * i / 44100) for i in range(N)))

# ── noise: white at several amplitudes, brown ────────────────────────────
for amp in (500, 5000, 20000, 32000):
    write(f"noise-white-{amp}", (rng.randint(-amp, amp) for _ in range(N)))
for tag, step in (("smooth", 60), ("rough", 400)):
    acc, brown = 0, []
    for _ in range(N):
        acc = max(-30000, min(30000, acc + rng.randint(-step, step)))
        brown.append(acc)
    write(f"noise-brown-{tag}", brown)

# ── mixed: tonal + noise, speech-like bursts ─────────────────────────────
for tag, namp in (("clean", 60), ("mid", 600), ("dirty", 3000)):
    write(f"mixed-music-{tag}", (
        (0.5 + 0.5 * math.sin(2 * math.pi * i / 80000))
        * (6000 * math.sin(2 * math.pi * 220 * i / 44100)
           + 3000 * math.sin(2 * math.pi * 277.2 * i / 44100))
        + rng.gauss(0, namp) for i in range(N)))
for tag, blen in (("fast", 3000), ("slow", 12000)):
    speech = []
    for i in range(N):
        burst = (i // blen) % 3 != 2
        env = 0.5 + 0.5 * math.sin(2 * math.pi * i / 3000)
        speech.append(rng.gauss(0, 5000 * env) if burst else rng.gauss(0, 60))
    write(f"mixed-speech-{tag}", speech)

# ── degen: silence, DC, wasted bits, worst-case alternation ──────────────
write("degen-silence", (0 for _ in range(N)))
write("degen-dc", (1234 for _ in range(N)))
write("degen-wasted3", ((rng.randint(-4000, 4000) * 8) for _ in range(N)))
write("degen-altmax", (32767 if i % 2 == 0 else -32768 for i in range(N)))

# ── stereo: correlated and decorrelated channel pairs ────────────────────
def tone(i, f, a):
    return a * math.sin(2 * math.pi * f * i / 44100)

write2("stereo-corr", ((tone(i, 330, 9000), tone(i, 330, 9000) * 0.85 + 200)
                       for i in range(N)))
write2("stereo-wide", ((tone(i, 330, 9000) + rng.gauss(0, 300),
                        tone(i, 553, 9000) + rng.gauss(0, 300)) for i in range(N)))
write2("stereo-mono2", ((tone(i, 220, 8000), tone(i, 220, 8000)) for i in range(N)))
write2("stereo-panned", ((tone(i, 440, 11000) * (0.5 + 0.5 * math.sin(2 * math.pi * i / 100000)),
                          tone(i, 440, 11000) * (0.5 - 0.5 * math.sin(2 * math.pi * i / 100000)))
                         for i in range(N)))
