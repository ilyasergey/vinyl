# mk/flags.mk — THE canonical flag and link-order definitions. Nothing else in
# this build defines instrumentation flags or a link recipe; every rule goes
# through the macros below so they cannot drift out of sync.

# NO ASan/UBSan by default: Lean ships its own allocator and refcounting, GMP
# aborts by design on allocation failure, and ASan interacts badly with all
# three, burying real findings in noise.
COMMON_WARN   := -Wall -Wextra -Wno-unused-parameter
COMMON_OPT    := -O2 -g -fno-omit-frame-pointer

CFLAGS_FUZZ   := $(COMMON_OPT) $(COMMON_WARN) -fsanitize=fuzzer-no-link
CFLAGS_AFL    := $(COMMON_OPT) $(COMMON_WARN) -include $(FUZZ_ROOT)/engine/no_fuzzing_mode.h
CFLAGS_PLAIN  := $(COMMON_OPT) $(COMMON_WARN)

# covfuzz flavour (mk/cov.mk, Phase 1): a coverage-instrumented SIBLING of the
# real fleet binaries -- CFLAGS_FUZZ (so it is a genuine libFuzzer binary, usable
# for -runs=0 replay AND -merge) plus clang source-based coverage, at the fleet's
# own -O2 so the measured reachable/inlined set matches the campaign binary. This
# is what makes per-target coverage HONEST: we profile a sibling of the exact
# target that ran, not a separate hand-written replay driver. libFLAC links
# UNINSTRUMENTED here (libflac.plain.a) -- it is the referee, not measured.
CFLAGS_COVFUZZ := $(CFLAGS_FUZZ) -fprofile-instr-generate -fcoverage-mapping

# ubsan flavour (Phase 5A): a SCOPED UBSan sibling that instruments ONLY the
# ~4000 lines of hand-written harness C (common/targets/engine/tools) -- NOT the
# Lean-generated IR and NOT libFLAC. Global UBSan is wrong here: the Lean IR
# deliberately wraps (Int.toInt64 mod 2^64, UInt64 lanes, pcmBytesRange two's-
# complement) and libFLAC has its own defined-wrapping idioms; instrumenting them
# drowns real harness findings in noise. Keeps -fsanitize=fuzzer-no-link from
# CFLAGS_FUZZ so it is still a libFuzzer binary usable for -runs=0 replay.
# EXPLICITLY WITHOUT `integer`: unsigned-overflow is NOT UB and the harness PRNGs,
# CRC and FNV rely on defined wrapping.
CFLAGS_UBSAN := $(CFLAGS_FUZZ) -fsanitize=shift,signed-integer-overflow,bounds,integer-divide-by-zero,return,alignment,float-cast-overflow

# Lean-generated IR is machine-generated; its warnings are noise. Appended
# AFTER the flavour's own -Wall -Wextra so -w actually wins (last flag on the
# command line takes precedence).
CFLAGS_IR_EXTRA := -w

# -I$(GEN) exposes the generated vinyl_symbols.h (mk/lean.mk). FFMPEG_CFLAGS adds
# the libavcodec/format/util headers for wide_diff.c's 2nd reference decoder.
INCLUDES := -I$(FUZZ_ROOT)/common -I$(GEN) -I$(LEAN_INC) -I$(FLAC_SRC)/include -I$(FUZZ_ROOT) \
            $(FFMPEG_CFLAGS)

# ffmpeg is pulled ONLY by the target that references it (fz_samples_diff, via
# wide_diff.o): --as-needed means a link that never calls libavcodec gets no
# DT_NEEDED for it. Uninstrumented on purpose -- it is a reference decoder.
FFMPEG_LINK := -Wl,--as-needed $(FFMPEG_LIBS) -Wl,--no-as-needed

# ============ link order — THE fiddly part ================================
# Order below is load-bearing; each line's reason is why it is where it is.
#
# 1. The target object, its aux objects, the engine adapter objects.
# 2. libfuzzcommon.*.a (the shared C layer) -- archive members are pulled per
#    referenced object, so a target that never calls the oracle never links
#    oracle.o. It must come BEFORE libvinyl.*.a but AFTER the target object.
# 3. The fuzzer runtime as an EXPLICIT ARCHIVE, *before* libvinyl.*.a. crt1.o
#    has an undefined `main`; if libvinyl.*.a came first the linker would
#    satisfy it from a Lean-generated main and the binary would not be a
#    fuzzer at all.
# 4. libvinyl.*.a, libflac.*.a — the instrumented codecs.
# 5. Lean runtime archives inside --start-group: libleancpp and libleanrt are
#    MUTUALLY referencing, so a single pass cannot resolve them.
# 6. gmp, uv — Lean's C deps.
# 7. Lean's hermetic libc++ / libc++abi / libunwind.
# 8. -lstdc++ LAST: Debian's libclang_rt.fuzzer / AFL++'s driver are built
#    against GNU libstdc++ (std::__cxx11 symbols), which Lean's libc++ cannot
#    satisfy.
# NO libcrypto / libssl: the codec needs no TLS and it only slows the link.
define LEAN_LINK
  -Wl,--start-group \
    $(LEAN_LEANLIB)/libleancpp.a $(LEAN_LEANLIB)/libInit.a \
    $(LEAN_LEANLIB)/libStd.a     $(LEAN_LEANLIB)/libleanrt.a \
  -Wl,--end-group \
  $(LEAN_LIBDIR)/libgmp.a $(LEAN_LIBDIR)/libuv.a \
  $(LEAN_LIBDIR)/libc++.a $(LEAN_LIBDIR)/libc++abi.a $(LEAN_LIBDIR)/libunwind.a \
  -lstdc++ -lm -lpthread -ldl -lrt
endef

# libFuzzer link. $(1) is the object/archive list (target obj + aux + engine
# adapters + libfuzzcommon.fuzz.a), already ordered by the make rule.
define LINK_FUZZ
  $(CLANG) -g -o $@ $(1) $(FUZZER_RT) \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a $(LEAN_LINK) $(FFMPEG_LINK)
endef

# AFL++ link. --whole-archive on the driver: aflpp_driver's main() is WEAK, so
# the linker would not pull the member in to satisfy crt1's undefined main
# otherwise.
define LINK_AFL
  $(AFL_CC) -g -o $@ $(1) \
    -Wl,--whole-archive $(AFL_DRIVER) -Wl,--no-whole-archive \
    $(BUILD)/lib/libvinyl.afl.a $(BUILD)/lib/libflac.afl.a $(LEAN_LINK) $(FFMPEG_LINK)
endef

# CMPLog / RedQueen flavour (Phase 3E-afl): the AFL toolchain with
# AFL_LLVM_CMPLOG=1 at compile AND link, so afl-fuzz's `-c` binary logs comparison
# operands and solves the non-CRC magic values (sync / block-size / sample-rate /
# bps code tables, STREAMINFO fields). The CRC-repairing mutator already handles
# the checksums, so this is strictly additive. Reuses libflac.afl.a as the referee
# (no separate cmplog libFLAC build needed -- the RedQueen signal comes from the
# cmplog-instrumented Vinyl + harness).
CFLAGS_CMPLOG := $(CFLAGS_AFL)
define LINK_CMPLOG
  AFL_LLVM_CMPLOG=1 $(AFL_CC) -g -o $@ $(1) \
    -Wl,--whole-archive $(AFL_DRIVER) -Wl,--no-whole-archive \
    $(BUILD)/lib/libvinyl.cmplog.a $(BUILD)/lib/libflac.afl.a $(LEAN_LINK) $(FFMPEG_LINK)
endef

# Tools (no fuzzer main): the *no_main* runtime satisfies the sancov symbols the
# instrumented archives reference, without providing main().
define LINK_TOOL
  $(CLANG) -g -o $@ $(1) $(FUZZER_RT_NOMAIN) \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a $(LEAN_LINK) $(FFMPEG_LINK)
endef

# covfuzz link (Phase 1): identical to LINK_FUZZ but (a) libvinyl.covfuzz.a and
# the UNINSTRUMENTED libflac.plain.a referee, and (b) -fprofile-instr-generate on
# the link line to pull clang's profiling runtime. FUZZER_RT stays BEFORE the
# codec archives (same load-bearing order as LINK_FUZZ -- crt1's undefined main
# must resolve to the fuzzer driver, not a Lean main).
define LINK_COVFUZZ
  $(CLANG) -g -fprofile-instr-generate -o $@ $(1) $(FUZZER_RT) \
    $(BUILD)/lib/libvinyl.covfuzz.a $(BUILD)/lib/libflac.plain.a $(LEAN_LINK) $(FFMPEG_LINK)
endef

# ubsan link (Phase 5A): mirrors LINK_FUZZ but (a) adds the SAME -fsanitize list
# on the link line to pull clang's UBSan runtime, and (b) links the NON-ubsan
# libvinyl.fuzz.a (the IR must NOT be ubsan-instrumented -- it wraps by design)
# plus the UNINSTRUMENTED referee libflac.plain.a. FUZZER_RT stays BEFORE the
# codec archives (same load-bearing "runtime before codec" order as LINK_FUZZ:
# crt1's undefined main must resolve to the fuzzer driver, not a Lean main).
define LINK_UBSAN
  $(CLANG) -g -fsanitize=shift,signed-integer-overflow,bounds,integer-divide-by-zero,return,alignment,float-cast-overflow -o $@ $(1) $(FUZZER_RT) \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.plain.a $(LEAN_LINK) $(FFMPEG_LINK)
endef
