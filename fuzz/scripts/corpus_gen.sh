#!/usr/bin/env bash
# Generate seed corpora declared in corpus/sources.toml. Run from fuzz/.
#
#   scripts/corpus_gen.sh --all
#   scripts/corpus_gen.sh --decode      (mut_bench CRC-correct archetypes)
#   scripts/corpus_gen.sh --encode      (packed-PCM, checked envelope)
#   scripts/corpus_gen.sh --encode-edge (packed-PCM at/above the 4608 cap)
#   scripts/corpus_gen.sh --wide        (re-carve the 16-bit subset from corpus/decode/wide)
#   scripts/corpus_gen.sh --hires       (non-16-bit + LPC 13-32 from flac/ffmpeg/IETF)
#   scripts/corpus_gen.sh --must-reject (RFC-invalid streams)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
ROOT="$PWD"

gen_decode() {
  [ -x build/bin/mut_bench ] || { echo "build mut_bench first (make tools)"; exit 1; }
  build/bin/mut_bench gen corpus/decode/gen 400 0xC0FFEE
}

gen_wide16() {  # the 16-bit SUBSET of decode/wide, for the 16-bit-GATED targets.
  # fz_decode_diff/structured/modes DEC_SKIP every non-16-bit stream after a full
  # readMeta + whole-input sarray alloc, so feeding them the full multi-depth wide
  # bundle wastes ~3/4 of their execs (F3). This carves out just the 16-bit seeds
  # so those three highest-core-count jobs spend every exec on a stream they test.
  command -v metaflac >/dev/null || { echo "metaflac needed for wide16"; exit 1; }
  local src=corpus/decode/wide dest=corpus/decode/wide16 n=0
  mkdir -p "$dest"
  rm -f "$dest"/*
  for f in "$src"/*; do
    [ -f "$f" ] || continue
    [ "$(metaflac --show-bps "$f" 2>/dev/null)" = "16" ] && { cp "$f" "$dest/"; n=$((n+1)); }
  done
  echo "wrote $n 16-bit seeds -> $dest (from $(ls "$src" | wc -l) in $src)"
}

gen_hires() {  # non-16-bit + never-decoded-region seeds from EXTERNAL encoders.
  # The committed corpus/decode/wide holds Vinyl's own encoder image at 8/12/16/
  # 24-bit with FIXED subframes. This adds streams Vinyl never produces: real libFLAC/
  # ffmpeg output at 24/32-bit, LPC orders 13-32 (`-e -l 32`, which flac -8 and
  # the 1.73 GiB cross-check never reached), and the IETF 20-bit predictor-
  # overflow vector -- 20-bit exists in no encoder we can drive (flac --bps takes
  # only 8/16/24/32; ffmpeg clamps to 24), so it comes from the IETF corpus. All
  # feed the 3-way any-depth oracle (fz_samples_diff: Vinyl vs libFLAC vs ffmpeg).
  local dest=corpus/decode/hires tmp
  mkdir -p "$dest"
  tmp=$(mktemp -d)
  python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
def raw(name, ch, cb, n=512):           # cb = container bytes per sample
    amp = 2 ** (cb * 8 - 3)
    with open(os.path.join(t, name), "wb") as f:
        for i in range(n):
            for c in range(ch):
                v = int(amp * 0.6 * math.sin(i * 0.03 * (c + 1)) + 0.2 * amp * math.sin(i * 0.2))
                if cb == 2:
                    f.write(struct.pack("<h", max(-32768, min(32767, v))))
                elif cb == 3:
                    v &= 0xFFFFFF
                    f.write(bytes([v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF]))
                else:
                    f.write(struct.pack("<i", v))
for nm, ch, cb in [("s2.pcm",2,2),("m3.pcm",1,3),("s3.pcm",2,3),("s4.pcm",2,4)]:
    raw(nm, ch, cb)
raw("long16.pcm", 1, 2, n=80000)   # > pcmWindow (65536) -> parallel pcm16 serialization
PY
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 -f"
  # depths flac's encoder CAN emit from raw (12-bit already covered by gen_wide):
  $F --channels=2 --bps=8  -o "$dest/flac_08bit.flac"       "$tmp/s2.pcm" 2>/dev/null || true
  $F --channels=1 --bps=24 -o "$dest/flac_24bit_mono.flac"  "$tmp/m3.pcm" 2>/dev/null || true
  $F --channels=2 --bps=24 -o "$dest/flac_24bit.flac"       "$tmp/s3.pcm" 2>/dev/null || true
  $F --channels=2 --bps=32 -o "$dest/flac_32bit.flac"       "$tmp/s4.pcm" 2>/dev/null || true
  # 16-bit but > 65536 samples/channel: the ONLY shape that trips decodePcm16A's
  # parallel serialization (Codec.pcm16Tasks/pcm16Chunks over Stream.pcmWindows,
  # window = 1<<16). This hires COPY feeds the any-depth oracles (fz_samples_diff/
  # fz_self_consistent/fz_metamorphic via _DECODE_ANY). NOTE fz_decode_modes does
  # NOT consume it from here -- its parallel-pcm16 lane reads the dedicated
  # decode/parallel16 dir (gen_parallel16), which config.py wires into that target
  # (V8: corrects the old stale claim that this hires seed drove fz_decode_modes).
  $F --channels=1 --bps=16 -o "$dest/parallel_pcm16_16bit_long.flac" "$tmp/long16.pcm" 2>/dev/null || true
  # high-order LPC region: `-e -l 32 -p` SEARCHES up to order 32 with exhaustive
  # precision. NOTE `-l 32` is a MAXIMUM, not a forced order: for this smooth
  # 2-tone signal the encoder settles near order ~11, so the 16-bit file is named
  # for what it IS (encoder-chosen high LPC), not a false "order 32" claim (A4b:
  # the old flac_lpc32_16bit.flac name overstated its structure). The 24-bit
  # variant keeps the -l 32 ceiling name as the exhaustive-search probe.
  $F --lax --channels=2 --bps=16 -e -l 32 -p -o "$dest/flac_lpchi_16bit.flac" "$tmp/s2.pcm" 2>/dev/null || true
  $F --lax --channels=2 --bps=24 -e -l 32    -o "$dest/flac_lpchi_24bit.flac" "$tmp/s3.pcm" 2>/dev/null || true
  # a SECOND encoder (ffmpeg) whose output Vinyl has never round-tripped.
  if command -v ffmpeg >/dev/null; then
    ffmpeg -hide_banner -loglevel error -f lavfi \
      -i "aevalsrc='0.3*sin(880*t)|0.2*sin(1200*t)':d=0.05:s=48000" \
      -sample_fmt s32 -c:a flac -bits_per_raw_sample 24 -f flac "$dest/ffmpeg_24bit.flac" -y 2>/dev/null || true
    ffmpeg -hide_banner -loglevel error -f lavfi \
      -i "sine=frequency=440:duration=0.05:sample_rate=44100" \
      -sample_fmt s16 -c:a flac -f flac "$dest/ffmpeg_16bit.flac" -y 2>/dev/null || true
  fi
  # 20-bit: emitted by no encoder we can drive; take the IETF predictor-overflow
  # vector (the predictor-overflow class) if the corpus clone is present. Probe several
  # locations -- $FLAC_TEST_FILES can be a stale path inherited from the shell.
  local IETF=""
  for cand in "${FLAC_TEST_FILES:-}" "$ROOT/../../reference/flac-test-files" \
              "$ROOT/corpus/external/flac-test-files" /tmp/flac-test-files; do
    [ -n "$cand" ] && [ -d "$cand/subset" ] && { IETF="$cand"; break; }
  done
  if [ -n "$IETF" ]; then
    cp "$IETF/subset/62 - predictor overflow check, 20-bit.flac" \
       "$dest/ietf_20bit_predictor_overflow.flac" 2>/dev/null || true
  else
    echo "  note: IETF flac-test-files not found -- 20-bit seed skipped"
  fi
  rm -rf "$tmp"
  echo "wrote $(ls "$dest" | wc -l) hires seeds -> $dest"
}

gen_encode() {  # $1 = mode: envelope | edge
  local mode="$1" dest
  dest=$([ "$mode" = edge ] && echo corpus/encode/edge || echo corpus/encode/gen)
  mkdir -p "$dest"
  python3 - "$dest" "$mode" <<'PY'
import struct, os, random, math, sys
dest, mode = sys.argv[1], sys.argv[2]
random.seed(0xC0FFEE if mode == "envelope" else 0xED6E)
SR = [22050,1,8000,44100,48000,96000,192000,655350,1048575]
for k in range(60):
    ch = random.randint(1, 6)
    if mode == "edge":                       # around and beyond the 4608 cap
        bs = random.choice([4600, 4608, 4609, 6000, 8192, 16000])
    else:                                     # inside the checked envelope
        bs = random.randint(16, 4608)
    sridx = random.randrange(9)
    frames = random.choice([64, 256, 1024, 4096])
    # Encode the header the way pack.h / the wide unpacker DECODE it:
    #   ch = 1 + (data[0] % 8)      -> store ch-1
    #   bs = 16 + (LE16 % N)        -> store bs-16
    # so a "ch=1, bs=4608" seed actually decodes to ch=1, bs=4608 (the old code
    # stored ch/bs literally, so mono decoded as 2ch and bs=4608 decoded as 31).
    raw_bs = bs - 16
    hdr = bytes([(ch - 1) & 0xff, raw_bs & 0xff, (raw_bs >> 8) & 0xff,
                 sridx & 0xff, (sridx >> 8) & 0xff, random.randrange(9)])
    pcm = bytearray()
    for i in range(frames):
        for c in range(ch):
            v = int(20000 * math.sin(i * 0.05 * (c + 1))) + random.randint(-40, 40)
            pcm += struct.pack('<h', max(-32768, min(32767, v)))
    open(os.path.join(dest, f"{mode}_{k:03d}"), "wb").write(hdr + bytes(pcm))
print("wrote", len(os.listdir(dest)), "packed-PCM seeds ->", dest)
PY
}

gen_genparams() {  # RAW parameter seeds for fz_gen_roundtrip (G1). The generator
  # reads bps/ch/population/blockSize/samples/rate from the first bytes; these
  # seeds force the interesting corners the plain mutator reaches only rarely: the
  # stereo out-of-range construction across depths, and valid streams at the
  # depths (17-32) no other encode path emits.
  local dest=corpus/decode/gen_params
  mkdir -p "$dest"
  python3 - "$dest" <<'PY'
import os, sys, struct
dest = sys.argv[1]
def seed(name, bps, ch, adversarial, advkind, bs_sel=5, sr_sel=4, ns=512, population=0,
         chooser=0, tail=b"\x2a\x11\x22\x33"):
    d0 = (bps - 1) & 0xff                  # bps = 1 + d0%32
    d1 = (ch - 1) & 0xff                   # ch  = 1 + d1%8
    d2 = (adversarial & 1) | ((advkind & 3) << 1) | ((population & 3) << 3)  # bits3-4 = shape
    d3 = (bs_sel & 7) | ((chooser & 7) << 3)  # bits0-2 = blockSize, bits3-5 = chooser kind
    d4, d5 = (ns - 16) & 0xff, ((ns - 16) >> 8) & 0xff
    d6, d7 = sr_sel & 0xff, 0x2a
    open(os.path.join(dest, name), "wb").write(bytes([d0,d1,d2,d3,d4,d5,d6,d7]) + tail)
# ADVERSARIAL CHOOSERS (FlacTest/FuzzGen.lean): force LPC order 9-32, mid/side
# decorrelation, and high partition order on correlated (sine) audio -- the decode
# paths the default chooser never emits. Round-trip must still hold (oracle) since
# the configs are Valid; else orVerbatim falls back to VERBATIM.
for ck, cn in ((1, "lpc32"), (2, "stereo"), (3, "part")):
    for bps in (8, 12, 16, 24):
        seed(f"hostile_{cn}_bps{bps:02d}", bps, 2, 0, 0, population=3, chooser=ck, ns=1024)
    seed(f"hostile_{cn}_mono_bps16", 16, 1, 0, 0, population=3, chooser=ck, bs_sel=5, ns=768)
# hostileFixed (chooser 4, RICE-coded not escape): mono single-frame (bs=16) so
# fz_residual_bound analyses it. At 32-bit, alternating extremes (advkind=0) give
# a first difference > 2^31 -- a §9.2.7.3 residual-bound witness the escape-coded
# choosers cannot produce. 24-bit exercises the FIXED+rice decode without a
# violation (fz_residual_bound's 16-bit self-check must stay 0, so no bps<=16).
for bps in (24, 32):
    seed(f"hostile_fixed_bps{bps:02d}", bps, 1, 1, 0, chooser=4, bs_sel=0, ns=16)
# CORRELATED valid populations (ramp/walk/sine) across depths incl. 17-32 and an
# 8-channel case: uniform noise -> VERBATIM, so without these the residual-bound
# and emit-conformance targets analyse almost nothing. These make the default
# chooser pick FIXED/LPC and produce real residuals + a coded frame number.
for pop, pn in ((1, "ramp"), (2, "walk"), (3, "sine")):
    for bps in (8, 16, 17, 24, 32):
        seed(f"{pn}_bps{bps:02d}", bps, 2, 0, 0, population=pop, ns=1024)
        seed(f"{pn}_mono_bps{bps:02d}", bps, 1, 0, 0, population=pop, bs_sel=0, ns=512)  # bs=16 -> many frames
    seed(f"{pn}_8ch_bs16384", 16, 8, 0, 0, population=pop, bs_sel=5, ns=2000)
# stereo out-of-range reconstruction, one per depth (advkind=1, ch=2):
for bps in (8, 12, 16, 20, 24, 32):
    seed(f"s41_bps{bps:02d}", bps, 2, 1, 1)
# valid population across the depths no other path reaches:
for bps in (8, 16, 17, 24, 32):
    seed(f"valid_bps{bps:02d}", bps, 2, 0, 0)
# adversarial extremes / boundary / wide-range, a couple of channel counts:
for k in (0, 2, 3):
    seed(f"adv_k{k}_c2", 24, 2, 1, k)
seed("adv_mono_boundary", 32, 1, 1, 0)
# MONO SINGLE-FRAME seeds for fz_residual_bound: ch=1, small sample count
# (<= blockSize so exactly one frame), across depths incl. 17-32. bs_sel=5 -> 4096.
for bps in (8, 16, 17, 20, 24, 32):
    seed(f"mono_valid_bps{bps:02d}", bps, 1, 0, 0, bs_sel=5, ns=256)
    seed(f"mono_adv_bps{bps:02d}", bps, 1, 1, 3, bs_sel=5, ns=256)  # wide-range -> big residuals
print("wrote", len(os.listdir(dest)), "G1 param seeds ->", dest)
PY
}

gen_must_reject() {
  # RFC-invalid + reserved-code seeds. Extends the existing dir (conformance/
  # mustreject.py and build/bin/mk_reject also write here). Self-contained: the
  # CRC-8/CRC-16 helpers mirror common/flac_bits.h (poly 0x07 / 0x8005, init 0,
  # MSB-first) so no external tool is needed for the base-derived seeds below.
  mkdir -p corpus/decode/must_reject
  python3 - corpus/decode/must_reject <<'PY'
import os, sys
d = sys.argv[1]

def crc8(b):
    c = 0
    for x in b:
        c ^= x
        for _ in range(8):
            c = ((c << 1) ^ 0x07) & 0xff if c & 0x80 else (c << 1) & 0xff
    return c

def crc16(b):
    c = 0
    for x in b:
        c ^= x << 8
        for _ in range(8):
            c = ((c << 1) ^ 0x8005) & 0xffff if c & 0x8000 else (c << 1) & 0xffff
    return c

def put_bits(buf, bitpos, n, val):  # random-access big-endian field write
    for i in range(n):
        bp = bitpos + i
        bit = (val >> (n - 1 - i)) & 1
        by, off = bp // 8, 7 - (bp % 8)
        if bit:
            buf[by] |= 1 << off
        else:
            buf[by] &= ~(1 << off) & 0xff

# One valid base: CONSTANT mono 16-bit frame, 16 samples. Fields at the offsets
# named in common/flac_bits.h; CRC-8 (header) and CRC-16 (frame) filled directly.
FS = 42  # frame start = fLaC(4) + SI block header(4) + SI payload(34)
def build_base():
    b = bytearray(55)
    b[0:4] = b"fLaC"
    b[4:8] = bytes([0x80, 0x00, 0x00, 0x22])   # last=1, STREAMINFO, len 34
    put_bits(b, 64 + 0,   16, 16)              # min block size
    put_bits(b, 64 + 16,  16, 16)              # max block size
    put_bits(b, 64 + 80,  20, 44100)           # sample rate
    put_bits(b, 64 + 100,  3, 0)               # channels - 1 (mono)
    put_bits(b, 64 + 103,  5, 15)              # bps - 1 (16-bit)
    put_bits(b, 64 + 108, 36, 16)              # total samples
    b[FS + 0] = 0xFF
    b[FS + 1] = 0xF8                            # sync + reserved0 + fixed blocking
    b[FS + 2] = 0x79                            # bs code 7, sr code 9
    b[FS + 3] = 0x08                            # ch code 0, bps code 4, reserved 0
    b[FS + 4] = 0x00                            # coded frame number 0
    put_bits(b, (FS + 5) * 8, 16, 15)          # explicit block size - 1
    b[FS + 7] = crc8(b[FS:FS + 7])             # header CRC-8 (bytes 42..48)
    fc = crc16(b[FS:53])                        # frame CRC-16 (bytes 42..52)
    b[53], b[54] = (fc >> 8) & 0xff, fc & 0xff
    return b

base = build_base()

# Legacy minimal RFC-invalid microseeds (unchanged) --------------------------
cases = {
    "empty": b"",
    "marker_only": b"fLaC",
    "bad_marker": b"fLaX" + b"\x00" * 40,
    "truncated_streaminfo": b"fLaC\x00\x00\x00\x22" + b"\x00" * 10,
    "garbage_after_marker": b"fLaC" + bytes(range(64)),
    "streaminfo_sr_zero": b"fLaC\x80\x00\x00\x22" + b"\x00" * 34,  # last STREAMINFO, all-zero (sr=0)
}
for name, data in cases.items():
    open(os.path.join(d, f"mustreject_{name}.flac"), "wb").write(data)

# A4b: reserved channel codes 11/15 with header CRC-8 REPAIRED. conformance/
# mustreject.py leaves a stale 0x4c here (its permissive walker rejects reserved
# codes before it can re-bless the CRC), so those seeds reject in readHeader
# BEFORE the readChannels reserved-code branch they exist to hit. Flip the
# channel nibble, then recompute BOTH CRC-8 (header) and CRC-16 (frame) so the
# only remaining defect is the reserved channel code -- the target branch.
for cc in (11, 15):
    b = bytearray(base)
    put_bits(b, (FS + 3) * 8, 4, cc)
    b[FS + 7] = crc8(b[FS:FS + 7])
    fc = crc16(b[FS:53])
    b[53], b[54] = (fc >> 8) & 0xff, fc & 0xff
    open(os.path.join(d, f"13_channel_code_{cc}.flac"), "wb").write(bytes(b))

# C6: ID3v2 prefix before a valid fLaC stream (fz_trailing_data's ID3v2-prefix
# case; RFC 9639 requires the stream to begin with fLaC, so this MUST reject).
# ID3v2.3 header: "ID3", version 03 00, flags 00, 4-byte syncsafe size 0 (empty
# tag body) -> the fLaC stream begins immediately after the 10-byte header.
id3 = b"ID3" + bytes([0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])
open(os.path.join(d, "id3v2_prefixed_stream.flac"), "wb").write(id3 + bytes(base))

print("wrote base-derived + legacy must_reject seeds ->", d)
PY
  # B5: reserved/truncated/65536/min-block/type-127 field-violation seeds with
  # header CRC-8 repaired, from the dedicated tool (built by another agent).
  if [ -x build/bin/mk_reject ]; then
    build/bin/mk_reject corpus/decode/must_reject || echo "  note: mk_reject returned nonzero"
    echo "wrote mk_reject field-violation seeds -> corpus/decode/must_reject"
  else
    echo "  note: build/bin/mk_reject not built -- reserved/truncated/65536/min-block/type-127 seeds skipped"
  fi
}

gen_parallel16() {  # A4c: the dir config.py wires into fz_decode_modes for the
  # parallel-pcm16 lane (decodePcm16A over Stream.pcmWindows, window 1<<16). Holds
  # the 80k-sample 16-bit stream; every other decode seed is below the window.
  local dest=corpus/decode/parallel16 src=corpus/decode/hires/parallel_pcm16_16bit_long.flac
  mkdir -p "$dest"
  rm -f "$dest"/*
  if [ -f "$src" ]; then
    cp "$src" "$dest/parallel_pcm16_16bit_long.flac"
    echo "wrote 1 parallel16 seed (copied from hires) -> $dest"
  elif command -v flac >/dev/null; then
    local tmp; tmp=$(mktemp -d)
    python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
with open(os.path.join(t, "long16.pcm"), "wb") as f:
    for i in range(80000):
        v = int(0.6 * (2 ** 13) * math.sin(i * 0.03) + 0.2 * (2 ** 13) * math.sin(i * 0.2))
        f.write(struct.pack("<h", max(-32768, min(32767, v))))
PY
    flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 -f \
      --channels=1 --bps=16 -o "$dest/parallel_pcm16_16bit_long.flac" "$tmp/long16.pcm" 2>/dev/null || true
    rm -rf "$tmp"
    echo "wrote parallel16 seed (synthesized) -> $dest"
  else
    echo "  note: neither hires seed nor flac CLI available -- parallel16 skipped (dir kept)"
  fi
}

gen_large() {  # B1: large multi-frame streams (> 65536 B) that cross parThreshold
  # (1<<16) and light up the parallel-decode family (syncCandidates/syncScan/
  # stepChunk/byteStepChunk/stepsPar/byteStepsPar/findStep/findByteStep) absent
  # from the fleet union. decode-only / fast-only variants consume these.
  local d16=corpus/decode/large16 d24=corpus/decode/large24_32
  mkdir -p "$d16" "$d24"
  rm -f "$d16"/* "$d24"/*
  # (a) reuse the 16-bit IETF multi-frame files already on disk (all > 65536 B).
  local IETF=""
  for cand in "${FLAC_TEST_FILES:-}" "$ROOT/../../reference/flac-test-files" \
              "$ROOT/corpus/external/flac-test-files" /tmp/flac-test-files; do
    [ -n "$cand" ] && [ -d "$cand/subset" ] && { IETF="$cand"; break; }
  done
  if [ -n "$IETF" ]; then
    for rel in "uncommon/09 - Rice partition order 15.flac" \
               "subset/64 - rice partitions with escape code zero.flac" \
               "subset/16 - partition order 8 containing escaped partitions.flac" \
               "subset/14 - wasted bits.flac"; do
      [ -f "$IETF/$rel" ] || continue
      cp "$IETF/$rel" "$d16/ietf_$(basename "$rel" | tr ' ' '_')" 2>/dev/null || true
    done
  else
    echo "  note: IETF flac-test-files not found -- large16 uses synth only"
  fi
  # (b) synthesize incompressible (noise) multi-frame streams so output > 65536 B.
  if command -v flac >/dev/null; then
    local tmp; tmp=$(mktemp -d)
    python3 - "$tmp" <<'PY'
import struct, os, sys
t = sys.argv[1]
s = 0x1234567
def nxt():
    global s
    s = (s * 1103515245 + 12345) & 0x7fffffff
    return s
def write(name, ch, cb, n):
    with open(os.path.join(t, name), "wb") as f:
        for _ in range(n):
            for _c in range(ch):
                v = (nxt() % (1 << (cb * 8))) - (1 << (cb * 8 - 1))
                if cb == 2:
                    f.write(struct.pack("<h", max(-32768, min(32767, v))))
                elif cb == 3:
                    v &= 0xFFFFFF
                    f.write(bytes([v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF]))
                else:
                    f.write(struct.pack("<i", v))
write("l16s.pcm", 2, 2, 60000)   # 16-bit stereo noise -> ~200 KB compressed-ish
write("l16m.pcm", 1, 2, 90000)
write("l24s.pcm", 2, 3, 60000)   # 24-bit stereo noise
write("l32s.pcm", 2, 4, 60000)   # 32-bit stereo noise
write("pw.pcm",   1, 2, 1200000) # >1 MiB incompressible -> crosses syncWindow (1<<20)
PY
    local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 -f"
    $F --channels=2 --bps=16 -o "$d16/synth_16bit_stereo_long.flac" "$tmp/l16s.pcm" 2>/dev/null || true
    $F --channels=1 --bps=16 -o "$d16/synth_16bit_mono_long.flac"   "$tmp/l16m.pcm" 2>/dev/null || true
    $F --channels=2 --bps=24 -o "$d24/synth_24bit_stereo_long.flac" "$tmp/l24s.pcm" 2>/dev/null || true
    $F --channels=2 --bps=32 -o "$d24/synth_32bit_stereo_long.flac" "$tmp/l32s.pcm" 2>/dev/null || true
    # >1 MiB incompressible stream so syncWindow (1<<20) is genuinely crossable AND
    # reproducible -- E3 (lint.py) gates syncWindow on the largest committed seed, so
    # this MUST be regenerated by --all/--large after the rm -f above (not a manual seed).
    $F --channels=1 --bps=16 -o "$d16/par_window_noise.flac" "$tmp/pw.pcm" 2>/dev/null || true
    rm -rf "$tmp"
  else
    echo "  note: flac CLI absent -- large16/large24_32 synth skipped"
  fi
  echo "wrote $(ls "$d16" 2>/dev/null | wc -l) -> $d16, $(ls "$d24" 2>/dev/null | wc -l) -> $d24"
}

gen_g1_hostile() {  # B2: materialize the G1 hostile choosers as real FLAC seeds
  # (RICE2/escape/k>17 + high-order LPC on the DECODE side) via build/bin/gen_g1_flac
  # (built by another agent). Dir is kept even when the tool is absent so config.py
  # corpus resolution does not fail.
  local dest=corpus/decode/g1_hostile
  mkdir -p "$dest"
  if [ -x build/bin/gen_g1_flac ]; then
    build/bin/gen_g1_flac "$dest" || echo "  note: gen_g1_flac returned nonzero"
    echo "wrote $(ls "$dest" 2>/dev/null | wc -l) g1 hostile seeds -> $dest"
  else
    echo "  note: build/bin/gen_g1_flac not built -- g1_hostile skipped (dir kept)"
  fi
}

gen_shapes() {  # B4: deterministic packed-PCM shape matrix (rig packed format,
  # pack.h): 6-byte header [ch-1, LE16(bs-16), LE16(sr_idx), level] + signed LE16
  # samples. Each family pins an encoder-search branch a byte-mutated sine cannot
  # synthesize. Consumed by the packed-PCM encode targets once config.py wires it.
  local dest=corpus/encode/shapes
  mkdir -p "$dest"
  rm -f "$dest"/*
  python3 - "$dest" <<'PY'
import os, sys, struct, math, random
dest = sys.argv[1]
random.seed(0x5140)
SR_IDX = 3  # 44100 in pack.h k_sr_table

def hdr(ch, bs, level=5):
    raw_bs = bs - 16
    return bytes([(ch - 1) & 0xff, raw_bs & 0xff, (raw_bs >> 8) & 0xff,
                  SR_IDX & 0xff, (SR_IDX >> 8) & 0xff, level & 0xff])

def clamp(v):
    return max(-32768, min(32767, int(v)))

def emit(name, ch, bs, samples):   # samples: flat interleaved ints
    body = b"".join(struct.pack("<h", clamp(v)) for v in samples)
    open(os.path.join(dest, name), "wb").write(hdr(ch, bs) + body)

# constant / zero -> CONSTANT subframe
emit("const_zero_mono", 1, 4096, [0] * 4096)
emit("const_pos_mono", 1, 4096, [1000] * 4096)

# wasted bits: non-constant samples all divisible by 2^w
for w in (1, 4, 8, 12, 15):
    sig = [(clamp(3000 * math.sin(i * 0.02)) >> w) << w for i in range(2048)]
    emit(f"wasted_w{w:02d}_mono", 1, 2048, sig)

# exact polynomials -> the FIXED-order search (fixedSearchF) evaluates orders 0..4
mod = {1: 256, 2: 150, 3: 30, 4: 13}
for deg in (1, 2, 3, 4):
    m = mod[deg]
    emit(f"fixed_poly_deg{deg}_mono", 1, 512, [(i % m) ** deg for i in range(512)])

# 1/2/3-tone sums -> LPC search
tones = {1: [440.0], 2: [440.0, 1100.0], 3: [440.0, 1100.0, 2630.0]}
for k, freqs in tones.items():
    sig = [clamp(sum(9000 / len(freqs) * math.sin(2 * math.pi * f * i / 44100) for f in freqs))
           for i in range(4096)]
    emit(f"lpc_{k}tone_mono", 1, 4096, sig)

# 64-band variance -> partition order 6 (bs 4096 -> 64 samples/partition)
sig = []
for band in range(64):
    amp = 50 * (band + 1)
    sig += [clamp(random.uniform(-amp, amp)) for _ in range(64)]
emit("partition64_variance_mono", 1, 4096, sig)

# rank-deficient / single boundary pulse -> levinson err<=0 dead path
pulse = [0] * 4096
pulse[0] = 20000
emit("rankdef_pulse_mono", 1, 4096, pulse)
emit("rankdef_const_stereo", 2, 4096, [500, -500] * 4096)

# wide-quotient Rice fallback: one isolated extreme residual in a flat block
wq = [0] * 4096
wq[2048], wq[2049] = 32767, -32768
emit("rice_wide_quotient_mono", 1, 4096, wq)

print("wrote", len(os.listdir(dest)), "shape seeds ->", dest)
PY
}

gen_pairs_small() {  # C3: compact <= 2 KiB valid FLAC for fz_proven_pairs' `small`
  # variant (VM_PAIR_MAX=4096 skips ~80% of _DECODE). Padding-stripped external LPC
  # via the flac CLI when present; supplemented by the smallest committed valid
  # decode seeds under 2 KiB.
  local dest=corpus/decode/pairs_small n=0
  mkdir -p "$dest"
  rm -f "$dest"/*
  if command -v flac >/dev/null; then
    local tmp; tmp=$(mktemp -d)
    python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
def raw(name, n, f0):
    with open(os.path.join(t, name), "wb") as fh:
        for i in range(n):
            v = int(9000 * math.sin(2 * math.pi * f0 * i / 44100)
                    + 3000 * math.sin(2 * math.pi * 3 * f0 * i / 44100))
            fh.write(struct.pack("<h", max(-32768, min(32767, v))))
raw("p128.pcm", 128, 440.0)
raw("p256.pcm", 256, 660.0)
raw("p384.pcm", 384, 330.0)
raw("p512.pcm", 512, 880.0)
PY
    local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --no-padding --lax -f"
    for p in "$tmp"/*.pcm; do
      $F -e -l 32 -p --channels=1 --bps=16 -o "$dest/$(basename "$p" .pcm).flac" "$p" 2>/dev/null || true
    done
    rm -rf "$tmp"
  else
    echo "  note: flac CLI absent -- pairs_small uses copied seeds only"
  fi
  # supplement with the smallest committed VALID decode seeds under 2 KiB.
  for f in corpus/decode/wide/* corpus/decode/gen/*; do
    [ -f "$f" ] || continue
    [ "$(stat -c%s "$f")" -le 2048 ] || continue
    cp "$f" "$dest/$(basename "$(dirname "$f")")_$(basename "$f")" 2>/dev/null && n=$((n + 1))
    [ "$n" -ge 10 ] && break
  done
  echo "wrote $(ls "$dest" 2>/dev/null | wc -l) pairs_small seeds -> $dest"
}

gen_framenum() {  # C1: exercise the 3-byte coded frame number (pushUtf8/pushConts).
  # mono, bs=16 header + exactly 32,769 constant samples -> 2049 frames, last
  # frame number 2048 (0x800) needs the 3-byte UTF-8 form. Total 6 + 2*32769 =
  # 65,544 B, matching fz_encode_diff/fz_encode_validity max_len=65544. Written
  # into encode/gen (the dir those targets consume); gen_encode never removes it.
  local dest=corpus/encode/gen
  mkdir -p "$dest"
  python3 - "$dest" <<'PY'
import os, sys, struct
dest = sys.argv[1]
# packed header: ch=1 (b0=0), bs=16 (raw_bs=0 -> b1=b2=0), sr_idx=3, level=5
hdr = bytes([0x00, 0x00, 0x00, 0x03, 0x00, 0x05])
pcm = struct.pack("<h", 0) * 32769
open(os.path.join(dest, "framenum_3byte_32769"), "wb").write(hdr + pcm)
print("wrote 1 frame-number seed (65544 B) ->", dest)
PY
}

gen_blocksizes() {  # Header block-size codes Vinyl's OWN writer can NEVER emit (it
  # always writes code 7). libFLAC picks the frame-header block-size code that
  # matches --blocksize: 192->code1, 576/1152/2304/4608->codes2-5, the powers of
  # two 256..32768->codes8-15, and a couple of non-standard sizes (200,1000) that
  # force the 8-bit(code6)/16-bit(code7) explicit forms. Exercises every arm of
  # Frame.readBlockSize. A smooth low-amplitude sine keeps every file far under the
  # 24 KB reference-decode lane cap. --lax permits the non-subset block sizes.
  command -v flac >/dev/null || { echo "  note: flac CLI absent -- blocksizes skipped"; return 0; }
  local dest=corpus/decode/blocksizes tmp
  mkdir -p "$dest"
  rm -f "$dest"/*
  tmp=$(mktemp -d)
  python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
# >= one FULL block so the standard code shows up in a full (non-partial) frame;
# big sizes use exactly one full frame to stay small.
def raw(name, ch, total):
    with open(os.path.join(t, name), "wb") as f:
        for i in range(total):
            for c in range(ch):
                v = int(2000 * math.sin(i * 0.008 * (c + 1)))
                f.write(struct.pack("<h", max(-32768, min(32767, v))))
for bs in (192, 576, 1152, 2304, 4608, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 200, 1000):
    raw(f"m_{bs}.pcm", 1, bs if bs >= 4096 else 2 * bs)
for bs in (192, 576, 1000, 4096, 4608):
    raw(f"s_{bs}.pcm", 2, bs if bs >= 4096 else 2 * bs)
PY
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=16 --lax -f"
  for p in "$tmp"/m_*.pcm; do
    local bs; bs=$(basename "$p" .pcm); bs=${bs#m_}
    $F --channels=1 --blocksize="$bs" -o "$dest/mono_bs${bs}.flac" "$p" 2>/dev/null || true
  done
  for p in "$tmp"/s_*.pcm; do
    local bs; bs=$(basename "$p" .pcm); bs=${bs#s_}
    $F --channels=2 --blocksize="$bs" -o "$dest/stereo_bs${bs}.flac" "$p" 2>/dev/null || true
  done
  rm -rf "$tmp"
  echo "wrote $(ls "$dest" 2>/dev/null | wc -l) blocksize seeds -> $dest"
}

gen_multichan() {  # 3-8 channel streams (channel-assignment codes 2-7, which
  # Vinyl's writer never emits) plus strongly-correlated stereo so libFLAC picks
  # mid/side, left/side and right/side decorrelation. Drives Frame.readChannels /
  # readSubframes' multichannel arms, the Codec interleaveN/deinterleaveN general-N
  # loops, and the Stereo.c side-channel reconstructors. libFLAC supports up to 8
  # channels. Sample counts shrink at high channel counts to stay under 24 KB.
  command -v flac >/dev/null || { echo "  note: flac CLI absent -- multichan skipped"; return 0; }
  local dest=corpus/decode/multichan tmp
  mkdir -p "$dest"
  rm -f "$dest"/*
  tmp=$(mktemp -d)
  python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
def raw(name, ch, total, corr=False):
    with open(os.path.join(t, name), "wb") as f:
        for i in range(total):
            base = 6000 * math.sin(i * 0.02)
            for c in range(ch):
                v = base + 30 * math.sin(i * 0.05 * (c + 1)) if corr \
                    else 4000 * math.sin(i * 0.02 * (c + 1)) + 2000 * math.sin(i * 0.005)
                f.write(struct.pack("<h", max(-32768, min(32767, int(v)))))
for ch in (3, 4, 5, 6, 7, 8):
    raw(f"c{ch}.pcm", ch, 2048 if ch <= 5 else 1024)
raw("sA.pcm", 2, 4096, corr=True)   # L ~= R -> mid/side
raw("sB.pcm", 2, 4096, corr=True)
PY
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=16 --lax -f"
  for p in "$tmp"/c*.pcm; do
    local ch; ch=$(basename "$p" .pcm); ch=${ch#c}
    $F --channels="$ch" -o "$dest/ch${ch}.flac" "$p" 2>/dev/null || true
  done
  # -m makes libFLAC per-frame choose among independent/left-side/right-side/mid-side.
  $F --channels=2 -m -o "$dest/stereo_corr_a.flac" "$tmp/sA.pcm" 2>/dev/null || true
  $F --channels=2 -m -e -o "$dest/stereo_corr_b.flac" "$tmp/sB.pcm" 2>/dev/null || true
  rm -rf "$tmp"
  echo "wrote $(ls "$dest" 2>/dev/null | wc -l) multichannel seeds -> $dest"
}

gen_metablocks() {  # metadata-block-type variants before the audio, to drive the
  # Decode.readMeta / skipBlocks type arms: PADDING, VORBIS_COMMENT, SEEKTABLE, and
  # an APPLICATION block (hand-spliced) followed by a metaflac PADDING block. All
  # share one tiny valid 16-bit mono stream so each isolates a metadata arm.
  command -v flac >/dev/null || { echo "  note: flac CLI absent -- metablocks skipped"; return 0; }
  local dest=corpus/decode/metablocks tmp
  mkdir -p "$dest"
  rm -f "$dest"/*
  tmp=$(mktemp -d)
  python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
with open(os.path.join(t, "base.pcm"), "wb") as f:
    for i in range(2048):
        v = int(3000 * math.sin(i * 0.02) + 1500 * math.sin(i * 0.005))
        f.write(struct.pack("<h", max(-32768, min(32767, v))))
PY
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=16 --channels=1 --lax -f"
  local src="$tmp/base.pcm"
  $F -P 1024 -o "$dest/padding1024.flac"           "$src" 2>/dev/null || true
  $F --no-padding -T "TITLE=x" -T "ARTIST=vinyl" -o "$dest/vorbis_comment.flac" "$src" 2>/dev/null || true
  $F --no-padding -S 10x -o "$dest/seektable.flac" "$src" 2>/dev/null || true
  $F --no-padding -o "$tmp/base.flac"              "$src" 2>/dev/null || true
  # APPLICATION block (type 2): hand-splice it in as the block after STREAMINFO,
  # then let metaflac append a PADDING block (fixing the last-block flags).
  if [ -f "$tmp/base.flac" ]; then
    cp "$tmp/base.flac" "$dest/application_padding.flac"
    python3 - "$dest/application_padding.flac" <<'PY'
import sys
p = sys.argv[1]
b = bytearray(open(p, "rb").read())
assert b[:4] == b"fLaC"
si_end = 8 + ((b[5] << 16) | (b[6] << 8) | b[7])   # after STREAMINFO block
payload = b"VNYL" + b"seed"                         # 4-byte id + app data
# insert APPLICATION (type 2) as a NON-last block; the stream's existing trailing
# metadata blocks (and the metaflac PADDING added below) keep the last-block flag.
hdr = bytes([2, (len(payload) >> 16) & 0xff, (len(payload) >> 8) & 0xff, len(payload) & 0xff])
open(p, "wb").write(bytes(b[:si_end]) + hdr + payload + bytes(b[si_end:]))
PY
    command -v metaflac >/dev/null && metaflac --add-padding=512 "$dest/application_padding.flac" 2>/dev/null || true
  fi
  rm -rf "$tmp"
  echo "wrote $(ls "$dest" 2>/dev/null | wc -l) metablock seeds -> $dest"
}


case "${1:---all}" in
  --all)         gen_decode; gen_wide16; gen_hires; gen_parallel16; gen_genparams; \
                 gen_encode envelope; gen_encode edge; gen_framenum; gen_shapes; \
                 gen_large; gen_g1_hostile; gen_pairs_small; gen_must_reject; \
                 gen_blocksizes; gen_multichan; gen_metablocks ;;
  --decode)      gen_decode ;;
  --wide)        gen_wide16 ;;
  --hires)       gen_hires ;;
  --parallel16)  gen_parallel16 ;;
  --genparams)   gen_genparams ;;
  --encode)      gen_encode envelope ;;
  --encode-edge) gen_encode edge ;;
  --framenum)    gen_framenum ;;
  --shapes)      gen_shapes ;;
  --large)       gen_large ;;
  --g1-hostile)  gen_g1_hostile ;;
  --pairs-small) gen_pairs_small ;;
  --must-reject) gen_must_reject ;;
  --blocksizes)  gen_blocksizes ;;
  --multichan)   gen_multichan ;;
  --metablocks)  gen_metablocks ;;
  *) echo "unknown: $1"; exit 2 ;;
esac
