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
# residual-heavy 24/32-bit bases: a partly-predictable tone plus bounded noise, so
# libFLAC still picks LPC but emits many residual bits (deep readPartA/readRiceSeqScan).
import random as _rnd
_rnd.seed(0xF1AC)
def noisy(name, ch, cb, n=512):
    amp = 2 ** (cb * 8 - 3)
    with open(os.path.join(t, name), "wb") as f:
        for i in range(n):
            for c in range(ch):
                v = int(amp * 0.5 * math.sin(i * 0.03 * (c + 1))) + _rnd.randint(-amp // 3, amp // 3)
                if cb == 3:
                    v &= 0xFFFFFF
                    f.write(bytes([v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF]))
                else:
                    f.write(struct.pack("<i", v))
noisy("resid24.pcm", 2, 3)
noisy("resid32.pcm", 2, 4)
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
  # more external explicit-frame-bps bases for fz_streaminfo_contradict: its bit-depth
  # contradiction needs frames carrying an EXPLICIT depth code, which only libFLAC/ffmpeg
  # output provides. `-e -l N` are exhaustive LPC searches at mid/high orders (name kept
  # order-free -- `-l N` is a ceiling, not a forced order, so no false lpcNN claim). The
  # noisy bases are residual-heavy so readPartA/readRiceSeqScan run deep.
  $F --lax --channels=2 --bps=24 -e -l 16 -p -o "$dest/flac_lpcheavy_24bit.flac"      "$tmp/s3.pcm"     2>/dev/null || true
  $F --lax --channels=1 --bps=24 -e -l 12 -p -o "$dest/flac_lpcheavy_24bit_mono.flac" "$tmp/m3.pcm"     2>/dev/null || true
  $F --lax --channels=2 --bps=32 -e -l 24    -o "$dest/flac_lpcheavy_32bit.flac"      "$tmp/s4.pcm"     2>/dev/null || true
  $F --lax --channels=2 --bps=24 -e -l 8  -p -o "$dest/flac_residheavy_24bit.flac"    "$tmp/resid24.pcm" 2>/dev/null || true
  $F --lax --channels=2 --bps=32 -e -l 8     -o "$dest/flac_residheavy_32bit.flac"    "$tmp/resid32.pcm" 2>/dev/null || true
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
# bps31 is the strongest NEGATIVE control immediately below the RFC ceiling: the
# maximum first difference of alternating extremes is 2^31-1 and must NOT violate
# the residual bound, whereas the bps32 cell crosses it (positive witness).
for bps in (24, 31, 32):
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
# B3 chooser-5/6/7 + variable-blocking RAW cells (exact 9-byte parameter blocks
# from the second-batch coverage analyses). The seed() helper cannot express these:
# chooser kinds 5-7 need data[8] (the captured-argument byte) and variable blocking
# needs data[2] bit5, neither of which seed() writes. gen_build layout is
# [bps-1, ch-1, shape, bs_idx|chooser<<3, ns_lo, ns_hi, sr_idx, seed, arg]. These
# open the never-entered Emit.lpcResGo{3,5,6,7} bodies, the left/right-side stereo
# plans, the invalid-assignment orVerbatim reject arm, forced partition orders 5/6/8,
# the k>17 RICE2 readRiceSeqScan path, and the two-byte coded-frame-number branches.
def cell(name, hexbytes):
    open(os.path.join(dest, name), "wb").write(bytes.fromhex(hexbytes))
raw_cells = [
    # chooser 5 hostileLpcN -- LPC orders 3/5/6/7/8, mono sine, correlated
    ("g1_lpcN_ord3_bs1024", "0f 00 18 2f f0 03 04 00 02"),
    ("g1_lpcN_ord5_bs1024", "0f 00 18 2f f0 03 04 00 04"),
    ("g1_lpcN_ord6_bs1024", "0f 00 18 2f f0 03 04 00 05"),
    ("g1_lpcN_ord7_bs1024", "0f 00 18 2f f0 03 04 00 06"),
    ("g1_lpcN_ord8_bs1024", "0f 00 18 2f f0 03 04 00 07"),
    ("g1_lpcN_ord3_bs192",  "0f 00 18 29 b0 00 04 2a 02"),
    ("g1_lpcN_ord5_bs192",  "0f 00 18 29 b0 00 04 2a 04"),
    ("g1_lpcN_ord6_bs192",  "0f 00 18 29 b0 00 04 2a 05"),
    ("g1_lpcN_ord7_bs192",  "0f 00 18 29 b0 00 04 2a 06"),
    ("g1_lpcN_ord7_bs16",   "0f 00 18 28 00 00 04 00 06"),
    ("g1_lpcN_ord8_bs16",   "0f 00 18 28 00 00 04 00 07"),
    # chooser 7 args 65/66 -- left/side and right/side stereo (ch=2, correlated)
    ("g1_stereo_ls_bps16_bs16",   "0f 01 18 38 00 00 04 00 41"),
    ("g1_stereo_rs_bps16_bs16",   "0f 01 18 38 00 00 04 00 42"),
    ("g1_stereo_ls_bps16_bs1024", "0f 01 18 3f f0 03 04 00 41"),
    ("g1_stereo_rs_bps16_bs1024", "0f 01 18 3f f0 03 04 00 42"),
    ("g1_stereo_ls_bps24_bs1024", "17 01 18 3f f0 03 04 00 41"),
    ("g1_stereo_rs_bps24_bs1024", "17 01 18 3f f0 03 04 00 42"),
    # chooser 7 arg 128 -- hostileInvalid (safeChooser orVerbatim reject/fallback)
    ("g1_invalid_ch2_bs16",    "0f 01 18 38 00 00 04 00 80"),
    ("g1_invalid_mono_bs1024", "0f 00 18 3f f0 03 04 00 80"),
    # chooser 6 args 1/2/3 -- forced partition orders 5/6/8 on a full 1024 frame
    ("g1_part_po5_bs1024", "0f 00 18 37 f0 03 04 00 01"),
    ("g1_part_po6_bs1024", "0f 00 18 37 f0 03 04 00 02"),
    ("g1_part_po8_bs1024", "0f 00 18 37 f0 03 04 00 03"),
    # chooser 7 args 0-3 -- RICE2 k>17 (readRiceSeqScan). bps21 alternating-extremes
    # (kmin=bps-3=18) + low-depth bps12 sine sweeping k={18,24,28,30}.
    ("g1_rice2_k18_bps21_bs16",   "14 00 01 38 00 00 04 00 00"),
    ("g1_rice2_k18_bps12_bs1024", "0b 00 18 3f f0 03 04 00 00"),
    ("g1_rice2_k24_bps12_bs1024", "0b 00 18 3f f0 03 04 00 01"),
    ("g1_rice2_k28_bps12_bs1024", "0b 00 18 3f f0 03 04 00 02"),
    ("g1_rice2_k30_bps12_bs1024", "0b 00 18 3f f0 03 04 00 03"),
    # variable blocking (data[2] bit5=1), bs=16, ns=2047 -> frame numbers 128..2032
    # take the two-byte W.pushUtf8 / W.pushConts coded-number branch.
    ("g1_vblock_bps8_ramp_ns2047",  "07 00 28 00 ef 07 04 00 00"),
    ("g1_vblock_bps16_sine_ns2047", "0f 00 38 00 ef 07 04 00 00"),
    ("g1_vblock_bps8_sine_ns2047",  "07 00 38 00 ef 07 04 00 00"),
    # short last frame: bs=16, ns=18 -> a 2-sample tail (defaultChooser short arm)
    ("g1_shortlast_ramp_ns18", "0f 00 08 00 02 00 04 2a"),
]
for _name, _hx in raw_cells:
    cell(_name, _hx)
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

# ---- correlated STEREO shapes: make chooseFrame LEAVE independent mode. The lone
# rankdef_const_stereo above ties independent == mid/side, so it never decorrelates.
# These force mid/side (anti-phase L=-R), left/side (R=L-delta) and right/side
# (L=R+delta) to beat independent, plus a pair whose SIDE channel is the LPC signal.
def interleave(chans):
    out = []
    for i in range(len(chans[0])):
        for ch in chans:
            out.append(ch[i])
    return out

BS = 2048
base = [clamp(9000 * math.sin(2 * math.pi * 500 * i / 44100)
              + 3000 * math.sin(2 * math.pi * 1300 * i / 44100)) for i in range(BS)]
delta = [clamp(180 * math.sin(2 * math.pi * 90 * i / 44100)) for i in range(BS)]
emit("stereo_ms_antiphase", 2, BS, interleave([base, [-v for v in base]]))
emit("stereo_ls_biased", 2, BS, interleave([base, [base[i] - delta[i] for i in range(BS)]]))
emit("stereo_rs_biased", 2, BS, interleave([[base[i] + delta[i] for i in range(BS)], base]))
side = [clamp(6000 * math.sin(2 * math.pi * 300 * i / 44100)) for i in range(BS)]
mid = [clamp(400 * math.sin(2 * math.pi * 47 * i / 44100)) for i in range(BS)]
emit("stereo_side_predictive", 2, BS,
     interleave([[mid[i] + side[i] for i in range(BS)], [mid[i] - side[i] for i in range(BS)]]))

# ---- correlated MULTICHANNEL shapes (3/4/6/8-ch: general-N channel assignment +
# mixed per-channel subframe kinds -- constant / fixed-poly / LPC / wasted-bits).
def const_ch(n, val):
    return [val] * n
def fixed_ch(n, deg):
    m = {1: 256, 2: 150, 3: 30, 4: 13}[deg]
    return [clamp((i % m) ** deg) for i in range(n)]
def lpc_ch(n, f):
    return [clamp(7000 * math.sin(2 * math.pi * f * i / 44100)) for i in range(n)]
def wasted_ch(n, w):
    return [(clamp(3000 * math.sin(i * 0.02)) >> w) << w for i in range(n)]
mc_kinds = [lambda n: const_ch(n, 700), lambda n: fixed_ch(n, 2),
            lambda n: lpc_ch(n, 440.0), lambda n: wasted_ch(n, 4),
            lambda n: lpc_ch(n, 1100.0), lambda n: fixed_ch(n, 3),
            lambda n: const_ch(n, -300), lambda n: lpc_ch(n, 2630.0)]
for ch in (3, 4, 6, 8):
    n = 1024 if ch <= 4 else 512
    emit(f"multichan_mixed_ch{ch}", ch, n,
         interleave([mc_kinds[c % len(mc_kinds)](n) for c in range(ch)]))

# ---- AR-order 4/5/6 predictable shapes (within lpcMaxOrder=6). A stable AR process
# (reflection coefficients |k|<1) is well predicted by an order-p LPC.
def ar_signal(refl, n, seed):
    A = []
    for i, ki in enumerate(refl, start=1):
        newA = [0.0] * i
        for j in range(1, i):
            newA[j - 1] = A[j - 1] + ki * A[(i - j) - 1]
        newA[i - 1] = ki
        A = newA
    pc = [-a for a in A]                 # predictor coefficients
    st = seed & 0x7fffffff
    def nxt():
        nonlocal st
        st = (st * 1103515245 + 12345) & 0x7fffffff
        return (st / 0x7fffffff) - 0.5
    p = len(pc)
    hist = [0.0] * p
    out = []
    for _ in range(n):
        s = sum(pc[j] * hist[j] for j in range(p)) + 900.0 * nxt()
        s = max(-30000.0, min(30000.0, s))
        out.append(clamp(s))
        hist = [s] + hist[:-1]
    return out
refl_by_order = {4: [0.7, -0.5, 0.4, -0.3], 5: [0.7, -0.5, 0.4, -0.3, 0.2],
                 6: [0.7, -0.5, 0.4, -0.3, 0.2, -0.1]}
for order, refl in refl_by_order.items():
    emit(f"lpc_ar{order}_mono", 1, 2048, ar_signal(refl, 2048, 0x1000 + order))
arL = ar_signal(refl_by_order[6], 2048, 0xA5)
arR = [arL[max(0, i - 1)] for i in range(2048)]   # 1-sample lag -> strongly correlated
emit("lpc_ar6_stereo", 2, 2048, interleave([arL, arR]))

# ---- AR(1) with a strongly NEGATIVE coefficient. The estimator deterministically
# selects LPC order 1 (verified: order 1, precision 12, shift 11, Rice po=1),
# opening the never-entered Emit.lpcResGo1 -- order 1 is costed during search on the
# other seeds but never WINS emission, so this is the only route into that body.
arng = random.Random(0xA14D)
ar1, x = [], 10000
for _ in range(4096):
    x = clamp((-3 * x) // 4 + arng.randint(-64, 64))
    ar1.append(x)
emit("lpc_ar1_neg_mono", 1, 4096, ar1)

# ---- standard block sizes 192/576/1152/2304/4608 -> libFLAC frame-header block-size
# codes 1-5 on the cross-decode side (the positive arm of resolveBlockSize; Vinyl's
# own writer only ever emits code 7, and the existing shapes only hit codes 6/7/8-15).
# Two FULL blocks of a smooth predictable sine keep each file small and canonical.
for stdbs in (192, 576, 1152, 2304, 4608):
    stdsig = [clamp(6000 * math.sin(2 * math.pi * 300 * i / 44100)) for i in range(2 * stdbs)]
    emit(f"stdblock_bs{stdbs}_mono", 1, stdbs, stdsig)

# ---- predictive partition/escape: a globally order-1-predictable random walk with
# ONE hostile 64-sample band (partition 32). Order-1 prediction stays profitable over
# ~98% of the block (high partition order), while the isolated full-range band forces
# an escape partition -- a discrete outcome byte-mutation is very unlikely to synthesize.
prng = random.Random(0x9E3B)
walk, x = [], 0
for i in range(4096):
    if 2048 <= i < 2112:                       # hostile band -- walk value is NOT advanced
        walk.append(clamp(prng.randint(-32768, 32767)))
    else:
        x = clamp(x + prng.randint(-2, 2))
        walk.append(x)
emit("partition_rw_escape_mono", 1, 4096, walk)

# ---- LEFT_SIDE / RIGHT_SIDE selectors. (L,R)=(x,2x) makes left/side strictly cheaper
# than independent and mid/side in chooseFrame; (2x,x) makes right/side win. The prior
# stereo_ls/rs_biased seeds picked neither in measurement; these deterministically emit
# LS and RS (channel codes 8/9). 2*5900 stays inside s16.
xb = [clamp(5000 * math.sin(2 * math.pi * 440 * i / 44100)
            + 900 * math.sin(2 * math.pi * 1230 * i / 44100)) for i in range(4096)]
emit("stereo_ls_ratio2", 2, 4096, interleave([xb, [2 * v for v in xb]]))
emit("stereo_rs_ratio2", 2, 4096, interleave([[2 * v for v in xb], xb]))

print("wrote", len(os.listdir(dest)), "shape seeds ->", dest)
PY
}

gen_pairs_small() {  # C3: compact <= 4 KiB valid FLAC for fz_proven_pairs' `small`
  # variant (VM_PAIR_MAX=4096 skips ~26% of _DECODE, incl. every blocksizes/multichan
  # seed). Padding-stripped external LPC via the flac CLI, plus compact correlated
  # stereo (LS/RS/MS), ch5/ch7, explicit-blocksize codes 6/7 (bs=200,1000) and a
  # hostile high-partition-order/RICE residual. These <=4096 B seeds feed
  # fz_proven_pairs.small (corpus decode/pairs_small); the smallest committed valid
  # decode seeds under 2 KiB supplement them.
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
  # compact correlated stereo (LS/RS/MS), ch5/ch7, explicit blocksize codes 6/7,
  # and a hostile high-partition/RICE residual -- all kept well under the 4096 cap.
  if command -v flac >/dev/null; then
    local tmp2; tmp2=$(mktemp -d)
    python3 - "$tmp2" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
def clip(v):
    return max(-32768, min(32767, int(v)))
def raw(name, ch, total, corr=None):
    with open(os.path.join(t, name), "wb") as f:
        for i in range(total):
            L = int(7000 * math.sin(2 * math.pi * 440 * i / 44100)
                    + 2000 * math.sin(2 * math.pi * 1300 * i / 44100))
            d = int(120 * math.sin(2 * math.pi * 90 * i / 44100))
            if ch == 1:
                f.write(struct.pack("<h", clip(L))); continue
            for c in range(ch):
                if ch == 2 and corr == "ms":
                    v = L if c == 0 else -L
                elif ch == 2 and corr == "ls":
                    v = L if c == 0 else L - d
                elif ch == 2 and corr == "rs":
                    v = (L + d) if c == 0 else L
                else:
                    v = L + 40 * c * int(math.sin(i * 0.03))
                f.write(struct.pack("<h", clip(v)))
for mode in ("ms", "ls", "rs"):
    raw(f"st_{mode}.pcm", 2, 256, corr=mode)
raw("c5.pcm", 5, 160)
raw("c7.pcm", 7, 120)
raw("bs200.pcm", 1, 400)
raw("bs1000.pcm", 1, 2000)
s = 0x2468ace
def nxt():
    global s
    s = (s * 1103515245 + 12345) & 0x7fffffff
    return s
with open(os.path.join(t, "hostile.pcm"), "wb") as f:
    for _ in range(1024):
        f.write(struct.pack("<h", (nxt() % 65536) - 32768))
PY
    local G="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=16 --lax --no-padding --no-seektable -f"
    for m in ms ls rs; do
      $G --channels=2 -m -e --blocksize=256 -o "$dest/st_${m}.flac" "$tmp2/st_${m}.pcm" 2>/dev/null || true
    done
    $G --channels=5 --blocksize=160 -o "$dest/ch5.flac" "$tmp2/c5.pcm" 2>/dev/null || true
    $G --channels=7 --blocksize=120 -o "$dest/ch7.flac" "$tmp2/c7.pcm" 2>/dev/null || true
    $G --channels=1 --blocksize=200  -o "$dest/mono_bs200.flac"  "$tmp2/bs200.pcm"  2>/dev/null || true
    $G --channels=1 --blocksize=1000 -o "$dest/mono_bs1000.flac" "$tmp2/bs1000.pcm" 2>/dev/null || true
    $G --channels=1 -e -p -r 8 --blocksize=1024 -o "$dest/hostile_rice_po.flac" "$tmp2/hostile.pcm" 2>/dev/null || true
    rm -rf "$tmp2"
  fi
  # supplement with the smallest committed VALID decode seeds under 2 KiB.
  for f in corpus/decode/wide/* corpus/decode/gen/*; do
    [ -f "$f" ] || continue
    [ "$(stat -c%s "$f")" -le 2048 ] || continue
    cp "$f" "$dest/$(basename "$(dirname "$f")")_$(basename "$f")" 2>/dev/null && n=$((n + 1))
    [ "$n" -ge 10 ] && break
  done
  find "$dest" -type f -size +4096c -delete   # hard-enforce the VM_PAIR_MAX cap
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
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=16 --lax --no-padding --no-seektable -f"
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

gen_ref_small() {  # <=8 KB variants of the non-canonical block-size + multichannel
  # seeds, so they also feed fz_decode_modes' REFERENCE lane (VM_REF_MAX_INPUT=8192,
  # a stack-safety bound). blocksizes/multichan proper are 8-15 KB and reach only the
  # fast lane; these small 1-2 frame versions drive decodeReference -> Frame.readChannels
  # (channel codes 2-7), resolveBlockSize (small block codes 1-5,8-11), and the Stereo.c
  # reference reconstructors. Any file that still exceeds 8000 B is pruned.
  command -v flac >/dev/null || { echo "  note: flac CLI absent -- ref_small skipped"; return 0; }
  local dest=corpus/decode/ref_small tmp
  mkdir -p "$dest"; rm -f "$dest"/*
  tmp=$(mktemp -d)
  python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
def raw(name, ch, total, corr=False):
    with open(os.path.join(t, name), "wb") as f:
        for i in range(total):
            base = 5000 * math.sin(i * 0.03)
            for c in range(ch):
                v = base + 20 * math.sin(i * 0.07 * (c + 1)) if corr \
                    else 3000 * math.sin(i * 0.03 * (c + 1))
                f.write(struct.pack("<h", max(-32768, min(32767, int(v)))))
# small-block mono+stereo: 2 frames each (block codes 1-5, 8-11); bs=200 -> the
# 8-bit explicit block-size code 6, which no power-of-two/standard size produces.
for bs in (192, 576, 1152, 2304, 256, 512, 1024, 200):
    raw(f"m_{bs}.pcm", 1, bs * 2)
    raw(f"s_{bs}.pcm", 2, bs * 2)
# multichannel at a small block, 1-2 frames (channel codes 2-7): ch5/ch7 added so
# every 3-8 channel geometry is present in the reference lane, not just 3/4/6/8.
for ch in (3, 4, 5, 6, 7, 8):
    raw(f"c{ch}.pcm", ch, 512)
# CONSTANT stream at a 32768-sample block -> reference block-size code 15, kept tiny
# by the CONSTANT subframe (well under the 8 KB ref-lane cap).
with open(os.path.join(t, "const32768.pcm"), "wb") as f:
    f.write(struct.pack("<h", 1234) * 32768)
PY
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=16 --lax --no-padding --no-seektable -f"
  for p in "$tmp"/m_*.pcm; do bs=$(basename "$p" .pcm); bs=${bs#m_}; $F --channels=1 --blocksize="$bs" -o "$dest/mono_bs${bs}.flac" "$p" 2>/dev/null || true; done
  for p in "$tmp"/s_*.pcm; do bs=$(basename "$p" .pcm); bs=${bs#s_}; $F --channels=2 -m --blocksize="$bs" -o "$dest/stereo_bs${bs}.flac" "$p" 2>/dev/null || true; done
  for p in "$tmp"/c*.pcm; do ch=$(basename "$p" .pcm); ch=${ch#c}; $F --channels="$ch" --blocksize=256 -o "$dest/ch${ch}.flac" "$p" 2>/dev/null || true; done
  $F --channels=1 --blocksize=32768 -o "$dest/const_bs32768.flac" "$tmp/const32768.pcm" 2>/dev/null || true
  # explicit sample-rate codes 12/13/14 (skipSampleRate ref arms): non-table rates
  # force flac to emit the 8-bit-kHz / 16-bit-Hz / 16-bit-daHz header forms, which
  # Vinyl's own writer (always sample-rate code 0 from STREAMINFO) never produces.
  # The trailing --sample-rate overrides the 44100 baked into $F.
  for sr in 5000 44101 441000; do
    $F --channels=1 --blocksize=512 --sample-rate="$sr" -o "$dest/sr_${sr}.flac" "$tmp/m_512.pcm" 2>/dev/null || true
  done
  rm -rf "$tmp"
  # prune anything above the reference-lane cap so the whole dir feeds both lanes
  find "$dest" -type f -size +8000c -delete
  echo "wrote $(ls "$dest" 2>/dev/null | wc -l) ref-lane (<=8 KB) seeds -> $dest"
}


gen_float_exact() {  # target-native RAW seeds for fz_float_exact: 3-byte header
  # [bps_idx, order-1, prec-5] + 4-byte LE sample payload (size >= 3 + 4*(order+1)).
  # The committed decode/gen_params corpus is the WRONG format here (8-byte G1 param
  # blocks), so on replay almost every seed gives n<=2 and only order 1 is analysed.
  # These native seeds sweep 16/24/32-bit x orders 3..16 with correlated-sine
  # (normal levinson/quantize), impulse (cmax<=0 zero-coefficient path) and full-scale
  # (rounding/clamp edge) payloads. config.py wires decode/float_seeds into fz_float_exact.
  local dest=corpus/decode/float_seeds
  mkdir -p "$dest"
  rm -f "$dest"/*
  python3 - "$dest" <<'PY'
import os, sys, struct, math
dest = sys.argv[1]
BPS_IDX = {16: 0, 20: 2, 24: 3, 32: 6}   # data[0] & 7 -> fz_float_exact bps_tab
def write(name, bps, order, prec, samples):
    hdr = bytes([BPS_IDX[bps] & 7, (order - 1) & 0xff, (prec - 5) & 0xff])
    body = b"".join(struct.pack("<i", int(v)) for v in samples)
    open(os.path.join(dest, name), "wb").write(hdr + body)
N = 256
for bps in (16, 24, 32):
    amp = (1 << (bps - 1)) - 1
    sine = [round(0.5 * amp * math.sin(2 * math.pi * 3 * i / 64)
                  + 0.3 * amp * math.sin(2 * math.pi * 7 * i / 64)
                  + 0.1 * amp * math.sin(2 * math.pi * 13 * i / 64)) for i in range(N)]
    for order in (3, 5, 8, 11, 16):
        for prec in (6, 14, 15):
            write(f"sine_bps{bps:02d}_ord{order:02d}_p{prec:02d}", bps, order, prec, sine)
    write(f"impulse_bps{bps:02d}", bps, 8, 14, [amp] + [0] * (N - 1))          # cmax<=0 path
    write(f"fullscale_alt_bps{bps:02d}", bps, 6, 15,
          [amp if i % 2 == 0 else -amp for i in range(N)])
    write(f"fullscale_ramp_bps{bps:02d}", bps, 11, 14,
          [round(amp * (2 * i / (N - 1) - 1)) for i in range(N)])
print("wrote", len(os.listdir(dest)), "float_exact seeds ->", dest)
PY
}

gen_multichan_hi() {  # 24-bit 3-8ch + explicit-sample-rate small seeds for the
  # any-depth decoders. gen_multichan is 16-bit only; these add high-depth channel-
  # assignment (chCode 2-7 + stereo 8/9/10) and explicit sample-rate codes 12/13/14
  # coverage. config.py wires decode/multichan_hi into _DECODE_ANY, so it feeds
  # fz_samples_diff and fz_decode_capacity. Kept small (<=16 KB) for the default lane.
  command -v flac >/dev/null || { echo "  note: flac CLI absent -- multichan_hi skipped"; return 0; }
  local dest=corpus/decode/multichan_hi tmp
  mkdir -p "$dest"
  rm -f "$dest"/*
  tmp=$(mktemp -d)
  python3 - "$tmp" <<'PY'
import struct, math, os, sys
t = sys.argv[1]
def raw24(name, ch, total, corr=False):
    with open(os.path.join(t, name), "wb") as f:
        for i in range(total):
            base = 2_000_000 * math.sin(i * 0.02)
            for c in range(ch):
                v = base + 8000 * math.sin(i * 0.05 * (c + 1)) if corr \
                    else 1_500_000 * math.sin(i * 0.02 * (c + 1)) + 400_000 * math.sin(i * 0.005)
                v = max(-(1 << 23), min((1 << 23) - 1, int(v))) & 0xFFFFFF
                f.write(bytes([v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF]))
for ch in (3, 4, 5, 6, 7, 8):
    raw24(f"c{ch}.pcm", ch, 512 if ch <= 6 else 384)
raw24("sA.pcm", 2, 1024, corr=True)   # correlated 24-bit stereo -> LS/RS/MS
raw24("m.pcm", 1, 512)
PY
  local F="flac --silent --force-raw-format --endian=little --sign=signed --sample-rate=44100 --bps=24 --lax -f"
  for p in "$tmp"/c*.pcm; do
    local ch; ch=$(basename "$p" .pcm); ch=${ch#c}
    $F --channels="$ch" -o "$dest/hi24_ch${ch}.flac" "$p" 2>/dev/null || true
  done
  $F --channels=2 -m -e -o "$dest/hi24_stereo_corr.flac" "$tmp/sA.pcm" 2>/dev/null || true
  for sr in 5000 44101 441000; do   # explicit sample-rate codes 12/13/14 (trailing arg wins)
    $F --channels=1 --sample-rate="$sr" -o "$dest/hi24_sr_${sr}.flac" "$tmp/m.pcm" 2>/dev/null || true
  done
  rm -rf "$tmp"
  find "$dest" -type f -size +16000c -delete
  echo "wrote $(ls "$dest" 2>/dev/null | wc -l) high-depth multichannel seeds -> $dest"
}

gen_g1_hostile16() {  # the 16-bit SUBSET of decode/g1_hostile, for the 16-bit-GATED
  # targets. Like gen_wide16: those targets DEC_SKIP every non-16-bit stream after
  # readMeta, so the full 200-file bundle wastes ~4/5 of their execs on the ~160
  # non-16-bit seeds. This subset feeds fz_decode_diff, fz_decode_structured and
  # fz_decode_modes (16-bit-gated); config wires decode/g1_hostile16 into all three,
  # while the full decode/g1_hostile stays with the any-depth decoders.
  command -v metaflac >/dev/null || { echo "metaflac needed for g1_hostile16"; exit 1; }
  local src=corpus/decode/g1_hostile dest=corpus/decode/g1_hostile16 n=0
  mkdir -p "$dest"
  rm -f "$dest"/*
  for f in "$src"/*; do
    [ -f "$f" ] || continue
    [ "$(metaflac --show-bps "$f" 2>/dev/null)" = "16" ] && { cp "$f" "$dest/"; n=$((n+1)); }
  done
  echo "wrote $n 16-bit g1 hostile seeds -> $dest (from $(ls "$src" 2>/dev/null | wc -l) in $src)"
}

case "${1:---all}" in
  --all)         gen_decode; gen_wide16; gen_hires; gen_parallel16; gen_genparams; \
                 gen_encode envelope; gen_encode edge; gen_framenum; gen_shapes; \
                 gen_large; gen_g1_hostile; gen_g1_hostile16; gen_pairs_small; gen_must_reject; \
                 gen_blocksizes; gen_multichan; gen_multichan_hi; gen_metablocks; gen_ref_small; \
                 gen_float_exact ;;
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
  --g1-hostile16) gen_g1_hostile16 ;;
  --pairs-small) gen_pairs_small ;;
  --must-reject) gen_must_reject ;;
  --blocksizes)  gen_blocksizes ;;
  --multichan)   gen_multichan ;;
  --multichan-hi) gen_multichan_hi ;;
  --metablocks)  gen_metablocks ;;
  --ref-small)   gen_ref_small ;;
  --float-exact) gen_float_exact ;;
  *) echo "unknown: $1"; exit 2 ;;
esac
