# mk/build.mk — generic, name-free build rules. The target set, the common
# source set, and each target's private aux sources are all DISCOVERED by
# glob; no target name appears anywhere in this file.

# ---- discovery: the ONLY place the target/common sets are defined --------
TARGET_SRCS := $(sort $(wildcard $(FUZZ_ROOT)/targets/*.c))
TARGETS     := $(patsubst $(FUZZ_ROOT)/targets/%.c,%,$(TARGET_SRCS))
COMMON_SRCS := $(sort $(wildcard $(FUZZ_ROOT)/common/*.c))
aux_srcs     = $(sort $(wildcard $(FUZZ_ROOT)/targets/$(1).aux/*.c))

# ---- libFLAC via its own CMake (correct config.h) -----------------------
# Three flavours: fuzz (clang, coverage), afl (afl-clang-fast, AFL coverage),
# plain (clang, no coverage) for tools/mut_bench, which must not link a
# libFuzzer-instrumented archive (that would drag in the libFuzzer runtime and
# resolve the mutator's weak LLVMFuzzerMutate outside a fuzzer run).
FLAC_CMAKE_OPTS := -DBUILD_SHARED_LIBS=OFF -DWITH_OGG=OFF -DBUILD_PROGRAMS=OFF \
                   -DBUILD_EXAMPLES=OFF -DBUILD_TESTING=OFF -DBUILD_DOCS=OFF \
                   -DBUILD_CXXLIBS=OFF -DINSTALL_MANPAGES=OFF \
                   -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_FLAGS_RELEASE=-DNDEBUG

define FLAC_BUILD   # $(1)=flavour  $(2)=cc  $(3)=cflags
$(BUILD)/lib/libflac.$(1).a:
	@mkdir -p $$(@D)
	$(CMAKE) -S $(FLAC_SRC) -B $(BUILD)/flac-$(1) -DCMAKE_C_COMPILER=$(2) \
	  -DCMAKE_C_FLAGS="$(3)" $(FLAC_CMAKE_OPTS) >/dev/null
	$(CMAKE) --build $(BUILD)/flac-$(1) --target FLAC -j $(NPROC) >/dev/null
	cp $(BUILD)/flac-$(1)/src/libFLAC/libFLAC.a $$@
endef
$(eval $(call FLAC_BUILD,fuzz,$(CLANG),$(CFLAGS_FUZZ)))
$(eval $(call FLAC_BUILD,afl,$(AFL_CC),$(CFLAGS_AFL)))
$(eval $(call FLAC_BUILD,plain,$(CLANG),$(CFLAGS_PLAIN)))

# ---- compile rules, one per (flavour x source dir) ----------------------
# Replaces the reference rig's hand-written pattern rules -- and fixes its
# missing AFL rule for engine/ and tools/.
define COMPILE_RULES   # $(1)=flavour  $(2)=cc  $(3)=cflags  $(4)=subdir
$(BUILD)/obj/$(1)/$(4)/%.o: $(FUZZ_ROOT)/$(4)/%.c $(GEN)/vinyl_symbols.h
	@mkdir -p $$(@D)
	$(2) $(3) $(INCLUDES) -MMD -MP -c $$< -o $$@
endef
$(foreach d,common targets engine tools, \
  $(eval $(call COMPILE_RULES,fuzz,$(CLANG),$(CFLAGS_FUZZ),$(d))) \
  $(eval $(call COMPILE_RULES,afl,$(AFL_CC),$(CFLAGS_AFL),$(d))) \
  $(eval $(call COMPILE_RULES,covfuzz,$(CLANG),$(CFLAGS_COVFUZZ),$(d))) \
  $(eval $(call COMPILE_RULES,ubsan,$(CLANG),$(CFLAGS_UBSAN),$(d))) \
  $(eval $(call COMPILE_RULES,cmplog,AFL_LLVM_CMPLOG=1 $(AFL_CC),$(CFLAGS_CMPLOG),$(d))))

# ---- ONE archive of the whole common layer ------------------------------
# Replaces per-target OBJS_<t> lists. Archive members are pulled per object,
# so a target that never calls the oracle never links oracle.o (and so never
# drags in flac_struct.o) -- the same granularity, self-maintaining.
COMMON_OBJS_FUZZ    := $(patsubst $(FUZZ_ROOT)/common/%.c,$(BUILD)/obj/fuzz/common/%.o,$(COMMON_SRCS))
COMMON_OBJS_AFL     := $(patsubst $(FUZZ_ROOT)/common/%.c,$(BUILD)/obj/afl/common/%.o,$(COMMON_SRCS))
COMMON_OBJS_COVFUZZ := $(patsubst $(FUZZ_ROOT)/common/%.c,$(BUILD)/obj/covfuzz/common/%.o,$(COMMON_SRCS))
COMMON_OBJS_UBSAN   := $(patsubst $(FUZZ_ROOT)/common/%.c,$(BUILD)/obj/ubsan/common/%.o,$(COMMON_SRCS))
COMMON_OBJS_CMPLOG  := $(patsubst $(FUZZ_ROOT)/common/%.c,$(BUILD)/obj/cmplog/common/%.o,$(COMMON_SRCS))

$(BUILD)/lib/libfuzzcommon.fuzz.a: $(COMMON_OBJS_FUZZ)
	@mkdir -p $(@D)
	rm -f $@ && ar rcs $@ $^
$(BUILD)/lib/libfuzzcommon.afl.a: $(COMMON_OBJS_AFL)
	@mkdir -p $(@D)
	rm -f $@ && ar rcs $@ $^
$(BUILD)/lib/libfuzzcommon.covfuzz.a: $(COMMON_OBJS_COVFUZZ)
	@mkdir -p $(@D)
	rm -f $@ && ar rcs $@ $^
$(BUILD)/lib/libfuzzcommon.ubsan.a: $(COMMON_OBJS_UBSAN)
	@mkdir -p $(@D)
	rm -f $@ && ar rcs $@ $^
$(BUILD)/lib/libfuzzcommon.cmplog.a: $(COMMON_OBJS_CMPLOG)
	@mkdir -p $(@D)
	rm -f $@ && ar rcs $@ $^

# ---- one rule pair per target, identical for all ------------------------
# libFuzzer targets link the mutator adapter (mutator_policy + libfuzzer_mutator)
# so "mutator on/off" is a runtime FUZZ_MUTATOR choice, never a relink. AFL
# targets load the mutator as a .so at run time instead (mk/tools.mk).
define TARGET_RULES
$(1)_AUX_FUZZ    := $$(patsubst $(FUZZ_ROOT)/%.c,$(BUILD)/obj/fuzz/%.o,$$(call aux_srcs,$(1)))
$(1)_AUX_AFL     := $$(patsubst $(FUZZ_ROOT)/%.c,$(BUILD)/obj/afl/%.o,$$(call aux_srcs,$(1)))
$(1)_AUX_COVFUZZ := $$(patsubst $(FUZZ_ROOT)/%.c,$(BUILD)/obj/covfuzz/%.o,$$(call aux_srcs,$(1)))
$(1)_AUX_UBSAN   := $$(patsubst $(FUZZ_ROOT)/%.c,$(BUILD)/obj/ubsan/%.o,$$(call aux_srcs,$(1)))
$(1)_AUX_CMPLOG  := $$(patsubst $(FUZZ_ROOT)/%.c,$(BUILD)/obj/cmplog/%.o,$$(call aux_srcs,$(1)))

# libvinyl/libflac are prerequisites (so a codec rebuild relinks the target) but
# LINK_FUZZ/LINK_AFL place them itself, AFTER the fuzzer runtime -- the load-
# bearing "runtime before codec" order (mk/flags.mk). Filter them out of the
# passed object list so they are not also listed BEFORE the runtime.
$(BUILD)/bin/$(1).fuzz: $(BUILD)/obj/fuzz/targets/$(1).o $$($(1)_AUX_FUZZ) \
    $(BUILD)/obj/fuzz/engine/mutator_policy.o \
    $(BUILD)/obj/fuzz/engine/libfuzzer_mutator.o \
    $(BUILD)/lib/libfuzzcommon.fuzz.a \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a
	@mkdir -p $$(@D)
	$$(call LINK_FUZZ,$$(filter-out $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.fuzz.a,$$(filter %.o %.a,$$^)))

$(BUILD)/bin/$(1).afl: $(BUILD)/obj/afl/targets/$(1).o $$($(1)_AUX_AFL) \
    $(BUILD)/lib/libfuzzcommon.afl.a \
    $(BUILD)/lib/libvinyl.afl.a $(BUILD)/lib/libflac.afl.a
	@mkdir -p $$(@D)
	$$(call LINK_AFL,$$(filter-out $(BUILD)/lib/libvinyl.afl.a $(BUILD)/lib/libflac.afl.a,$$(filter %.o %.a,$$^)))
	@# H7: probe the real map size; NEVER fall back to AFL's 64 KiB default.
	@loc=$$$$(AFL_DEBUG=1 $$@ /dev/null 2>&1 | \
	    sed -n 's/.*__afl_final_loc = \([0-9]*\).*/\1/p' | head -1); \
	  if [ -z "$$$$loc" ]; then \
	    echo "FATAL: could not probe __afl_final_loc for $(1).afl -- refusing to fall" >&2; \
	    echo "       back to a default AFL_MAP_SIZE that would truncate coverage" >&2; \
	    exit 1; \
	  fi; \
	  echo $$$$(( (loc + 8192) / 8192 * 8192 )) > $$@.mapsize; \
	  echo "  $(1).afl: AFL_MAP_SIZE=$$$$(cat $$@.mapsize)"

# covfuzz binary (Phase 1): the coverage-instrumented sibling of the .fuzz target.
# Same object graph and mutator adapter as .fuzz (so it is a real libFuzzer binary
# for -runs=0 replay / -merge), but linked against libvinyl.covfuzz.a + the
# uninstrumented libflac.plain.a referee. Coverage maps come from THIS binary;
# divergence verdicts NEVER do (instrumentation changes codegen).
$(BUILD)/bin/$(1).covfuzz: $(BUILD)/obj/covfuzz/targets/$(1).o $$($(1)_AUX_COVFUZZ) \
    $(BUILD)/obj/covfuzz/engine/mutator_policy.o \
    $(BUILD)/obj/covfuzz/engine/libfuzzer_mutator.o \
    $(BUILD)/lib/libfuzzcommon.covfuzz.a \
    $(BUILD)/lib/libvinyl.covfuzz.a $(BUILD)/lib/libflac.plain.a
	@mkdir -p $$(@D)
	$$(call LINK_COVFUZZ,$$(filter-out $(BUILD)/lib/libvinyl.covfuzz.a $(BUILD)/lib/libflac.plain.a,$$(filter %.o %.a,$$^)))

# ubsan binary (Phase 5A): the SCOPED-UBSan sibling of the .fuzz target. Same
# object graph and mutator adapter as .fuzz (so it is a real libFuzzer binary for
# -runs=0 replay), but the target/aux/common/engine objects carry UBSan while the
# codec archives do not: libvinyl.fuzz.a is the NON-ubsan IR (wraps by design) and
# libflac.plain.a is the uninstrumented referee. Only the hand-written harness C
# is instrumented -- that is where the real UB risk lives.
$(BUILD)/bin/$(1).ubsan: $(BUILD)/obj/ubsan/targets/$(1).o $$($(1)_AUX_UBSAN) \
    $(BUILD)/obj/ubsan/engine/mutator_policy.o \
    $(BUILD)/obj/ubsan/engine/libfuzzer_mutator.o \
    $(BUILD)/lib/libfuzzcommon.ubsan.a \
    $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.plain.a
	@mkdir -p $$(@D)
	$$(call LINK_UBSAN,$$(filter-out $(BUILD)/lib/libvinyl.fuzz.a $(BUILD)/lib/libflac.plain.a,$$(filter %.o %.a,$$^)))

# cmplog binary (Phase 3E-afl): AFL's `-c` RedQueen comparison-logging sibling of
# the .afl target. Same object graph as .afl (mutator loaded as a .so at run time),
# cmplog-instrumented Vinyl + harness, referee reused from libflac.afl.a. No map-size
# probe: afl-fuzz uses the .afl binary's map; the .cmplog binary only logs operands.
$(BUILD)/bin/$(1).cmplog: $(BUILD)/obj/cmplog/targets/$(1).o $$($(1)_AUX_CMPLOG) \
    $(BUILD)/lib/libfuzzcommon.cmplog.a \
    $(BUILD)/lib/libvinyl.cmplog.a $(BUILD)/lib/libflac.afl.a
	@mkdir -p $$(@D)
	$$(call LINK_CMPLOG,$$(filter-out $(BUILD)/lib/libvinyl.cmplog.a $(BUILD)/lib/libflac.afl.a,$$(filter %.o %.a,$$^)))
endef
$(foreach t,$(TARGETS),$(eval $(call TARGET_RULES,$(t))))

# Auto-generated header deps.
-include $(shell find $(BUILD)/obj -name '*.d' 2>/dev/null)

.PHONY: build-all
build-all: $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).fuzz $(BUILD)/bin/$(t).afl) \
           $(BUILD)/lib/afl_mutator.so $(BUILD)/bin/mut_bench $(BUILD)/bin/pcm_check \
           $(BUILD)/bin/flac_repair \
           $(BUILD)/bin/measure_decode $(BUILD)/bin/measure_encode \
           $(BUILD)/bin/sweep_md5 $(BUILD)/bin/sweep_float_exact
