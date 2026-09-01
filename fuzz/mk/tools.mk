# mk/tools.mk — the mutator .so (loaded by AFL at run time) and the offline
# helpers (mut_bench, pcm_check). None of these is a fuzz target.

# AFL custom mutator: uninstrumented, PIC, no Lean, no libFuzzer.
# flac_bits.c carries the shared selftest symbol flac_struct.c now consumes.
$(BUILD)/lib/afl_mutator.so: engine/afl_mutator.c common/flac_struct.c common/flac_bits.c
	@mkdir -p $(@D)
	$(CLANG) $(CFLAGS_PLAIN) -I$(FUZZ_ROOT)/common -fPIC -shared -o $@ $^

# PCM AFL custom mutator: the encode-side (packed-PCM / G1 param) sibling of
# afl_mutator.so. Its own afl_custom_* API lives in common/pcm_mutator.c, which
# links only libc + the header-only pack.h -- no flac_struct, no Lean, no libFuzzer.
# Loaded on the AFL arm of a mutator="pcm" job via AFL_CUSTOM_MUTATOR_LIBRARY.
$(BUILD)/lib/pcm_mutator.so: common/pcm_mutator.c
	@mkdir -p $(@D)
	$(CLANG) $(CFLAGS_PLAIN) -I$(FUZZ_ROOT)/common -fPIC -shared -o $@ $^

# mut_bench: uninstrumented libFLAC archive, NOT system -lFLAC.
$(BUILD)/bin/mut_bench: tools/mut_bench.c common/flac_struct.c common/flac_bits.c \
    $(BUILD)/lib/libflac.plain.a
	@mkdir -p $(@D)
	$(CLANG) $(CFLAGS_PLAIN) -I$(FUZZ_ROOT)/common -I$(FLAC_SRC)/include -o $@ \
	  tools/mut_bench.c common/flac_struct.c common/flac_bits.c $(BUILD)/lib/libflac.plain.a -lm

# flac_repair: the stdin->stdout CRC-repair CLI the Python drivers shell out to.
# Uninstrumented, no Lean, no libFLAC -- just flac_struct.c + the shared bit layer.
$(BUILD)/bin/flac_repair: tools/flac_repair.c common/flac_struct.c common/flac_bits.c
	@mkdir -p $(@D)
	$(CLANG) $(CFLAGS_PLAIN) -I$(FUZZ_ROOT)/common -o $@ $^

# pcm_check: links the instrumented archives (a verification helper, not a
# fuzz target) via the *_no_main libFuzzer runtime, which satisfies the sancov
# symbols the instrumented objects reference without providing main().
$(BUILD)/bin/pcm_check: $(BUILD)/obj/fuzz/tools/pcm_check.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o $(BUILD)/obj/fuzz/common/flac_api.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# measure_decode: the resource-measurement replay. Links libvinyl like
# pcm_check (no fuzzer main).
$(BUILD)/bin/measure_decode: $(BUILD)/obj/fuzz/tools/measure_decode.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# measure_encode (P8): encode-side resource measurement (task storm + stack feed).
$(BUILD)/bin/measure_encode: $(BUILD)/obj/fuzz/tools/measure_encode.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# sweep_md5 (Phase 6A): the deterministic CI sibling of fz_md5. Differentials
# Flac.Md5.md5 (via vinyl_md5, the same extern fz_md5.c uses -- bodies in
# vinyl_modes.o) against common/md5_ref.o over KAT + padding + fixed-seed random
# vectors. Links like measure_decode (no fuzzer main).
$(BUILD)/bin/sweep_md5: $(BUILD)/obj/fuzz/tools/sweep_md5.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o $(BUILD)/obj/fuzz/common/vinyl_modes.o \
    $(BUILD)/obj/fuzz/common/md5_ref.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# sweep_float_exact (Phase 6A): the deterministic CI sibling of fz_float_exact.
# Drives Vinyl's Float autocorrF/levinson/quantizeCoefs over a fixed bps x order
# x prec x signal grid and pins the divergence set. Declares the Heuristics
# externs itself (like the fuzz target), so it needs only vinyl_api.o for init.
$(BUILD)/bin/sweep_float_exact: $(BUILD)/obj/fuzz/tools/sweep_float_exact.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# gen_g1_flac (B2): bakes the G1 hostile-chooser space into committed FLAC seeds.
# Drives vinyl_gen.c (Stream.Unchecked.encode), so it links vinyl_gen.o + vinyl_api.o
# (init) against libvinyl like the sweep tools (no fuzzer main).
$(BUILD)/bin/gen_g1_flac: $(BUILD)/obj/fuzz/tools/gen_g1_flac.o \
    $(BUILD)/obj/fuzz/common/vinyl_gen.o $(BUILD)/obj/fuzz/common/vinyl_api.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# vinyl_encode_probe (C04): the single-shot bounded-stack encode fz_encode_stack
# forks + execs. Runs the SLOW encode (vm_encode_slow, in vinyl_modes.o) so its
# writeFrames/chunkChannels per-frame recursion overflows a small RLIMIT_STACK.
# Links like sweep_md5 (vinyl_api.o for init + vinyl_modes.o for the encoder, no
# fuzzer main).
$(BUILD)/bin/vinyl_encode_probe: $(BUILD)/obj/fuzz/tools/vinyl_encode_probe.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o $(BUILD)/obj/fuzz/common/vinyl_modes.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# vinyl_decode_probe: the decode-side mirror of vinyl_encode_probe, the single-shot
# bounded-stack DECODE fz_decode_stack forks + execs. Builds a deep stream with either
# the checked Lean encoder (vm_encode_slow, bs<=4608) or libFLAC (flac_encode, bs up to
# 65535, in flac_api.o) -- both off the decoder's attribution -- then decodes it with the
# shipped Flac.decodePcm16A (vm_decode_pcm16, in vinyl_modes.o), whose per-frame array
# readers are tail-swapped and expected to survive a small RLIMIT_STACK. Links like
# vinyl_encode_probe plus flac_api.o (the libFLAC emitter lane) and libflac.
$(BUILD)/bin/vinyl_decode_probe: $(BUILD)/obj/fuzz/tools/vinyl_decode_probe.o \
    $(BUILD)/obj/fuzz/common/vinyl_api.o $(BUILD)/obj/fuzz/common/vinyl_modes.o \
    $(BUILD)/obj/fuzz/common/flac_api.o \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $(@D)
	$(call LINK_TOOL,$(filter %.o,$^))

# mk_reject (B5): emits the single-field rejection-microseed corpus. Pure C over
# the header-only common/flac_bits.h primitives -- no Lean, no libFLAC -- so it
# builds plainly like flac_repair (a single translation unit).
$(BUILD)/bin/mk_reject: tools/mk_reject.c
	@mkdir -p $(@D)
	$(CLANG) $(CFLAGS_PLAIN) -I$(FUZZ_ROOT)/common -o $@ $^

# gen_g1_flac + mk_reject join the default build. build-all's recipe lives in
# mk/build.mk (included first); these prerequisite-only lines extend its
# dependency list without redefining the recipe, so `make all` builds them after
# lean-ir, exactly like the sweep_* tools alongside them.
build-all: $(BUILD)/bin/gen_g1_flac $(BUILD)/bin/mk_reject $(BUILD)/bin/vinyl_encode_probe \
           $(BUILD)/bin/vinyl_decode_probe $(BUILD)/lib/pcm_mutator.so
