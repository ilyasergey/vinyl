# Vinyl fuzzing subsystem — single build entry point.
#
#   make -j$(nproc)   lake build, IR, 3 libFLAC flavours, every target x 2
#                     engines, the mutator .so, and the tools
#   make list         discovered targets + their variants + corpora
#   make validate     every targets/*.c FUZZ_TARGET macro parses, matches its
#                     fleet/config.py run config, and every campaign resolves
#   make check        toolchain + check-symbols + validate + mut_bench selftest
#   make check-symbols  every required lp_vinyl_* is exported by the codec
#   make smoke        10s per target per engine; non-zero on a spurious abort
#   make corpus       unpack the committed seed archive (corpus/seeds.tar.gz)
#                     into the gitignored per-target seed dirs (run once/clone)
#   make libfuzzer | afl | tools | mutator | clean | distclean
#
# Two-phase: `all` first runs `lake build` and emits the symbol map (mk/lean.mk
# lean-ir), THEN re-invokes make so the IR wildcard sees a populated tree. This
# is what makes a brand-new checkout build in a single `make` even though the
# .lake/build/ir directory does not exist until lake has run.
SHELL := /bin/bash

include mk/toolchain.mk
include mk/flags.mk
include mk/lean.mk
include mk/build.mk
include mk/tools.mk
include mk/cov.mk

.DEFAULT_GOAL := all
.PHONY: all libfuzzer afl covfuzz ubsan cmplog tools mutator corpus corpus-pack check validate list smoke clean distclean print-config

all:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory build-all

libfuzzer:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).fuzz)

afl:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).afl) $(BUILD)/lib/afl_mutator.so

# Coverage-instrumented siblings of the fleet binaries (Phase 1). Not part of
# `all`: built on demand by cov/per_target.py to measure honest per-target
# region/branch coverage over Flac/Native/*.c and the harness.
covfuzz:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).covfuzz)

# Scoped-UBSan siblings of the fleet binaries (Phase 5A). Not part of `all`:
# built on demand. Instruments ONLY the hand-written harness C (common/targets/
# engine/tools); the Lean IR (libvinyl.fuzz.a) and libFLAC (libflac.plain.a) link
# uninstrumented -- they wrap by design and would drown real findings in noise.
ubsan:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).ubsan)

# CMPLog / RedQueen `-c` sibling binaries for the AFL arm (Phase 3E-afl). Opt-in;
# afl-fuzz runs `-c <t>.cmplog -- <t>.afl` (launch.py wires it when the .cmplog
# exists for a flac_stream AFL job). Additive over the CRC mutator + dict.
cmplog:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).cmplog)

tools:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(BUILD)/bin/mut_bench $(BUILD)/bin/pcm_check $(BUILD)/bin/flac_repair

mutator: $(BUILD)/lib/afl_mutator.so

# The committed seed corpus ships as a single archive (corpus/seeds.tar.gz); the
# extracted per-target seed dirs are gitignored. `make corpus` unpacks it so the
# fleet has its seeds after a fresh clone. `make corpus-pack` rebuilds the archive
# deterministically after regenerating seeds (scripts/corpus_gen.sh --all).
corpus:
	@if [ -d corpus/decode/gen ]; then echo "corpus already unpacked (corpus/decode/gen exists)"; \
	else echo "unpacking corpus/seeds.tar.gz ..."; tar xzf corpus/seeds.tar.gz && \
	     echo "unpacked $$(find corpus/decode corpus/encode corpus/md5 -type f | wc -l) seeds"; fi

corpus-pack:
	@tar --sort=name --owner=0 --group=0 --numeric-owner --mtime='2020-01-01 00:00:00' \
	     -cf - corpus/decode corpus/encode corpus/md5 | gzip -9 -n > corpus/seeds.tar.gz
	@echo "wrote corpus/seeds.tar.gz ($$(du -h corpus/seeds.tar.gz | cut -f1), sha256 $$(sha256sum corpus/seeds.tar.gz | cut -c1-16)...)"

print-config:
	@echo "FUZZ_ROOT   = $(FUZZ_ROOT)"
	@echo "REPO        = $(REPO)"
	@echo "FLAC_SRC    = $(FLAC_SRC)"
	@echo "LEAN_PREFIX = $(LEAN_PREFIX)"
	@echo "LAKE_BIN    = $(LAKE_BIN)"
	@echo "CLANG       = $(CLANG)"
	@echo "AFL_CC      = $(AFL_CC)"
	@echo "AFL_DRIVER  = $(AFL_DRIVER)"
	@echo "NPROC       = $(NPROC)"
	@echo "TARGETS     = $(TARGETS)"
	@echo "IR_SRCS     = $(words $(IR_SRCS)) files"

check: print-config check-symbols validate
	@test -d "$(LEAN_PREFIX)/include/lean" || { echo "FAIL: no lean headers under LEAN_PREFIX"; exit 1; }
	@test -f "$(FUZZER_RT)" || { echo "FAIL: libFuzzer runtime not found"; exit 1; }
	@command -v $(AFL_CC) >/dev/null || { echo "FAIL: $(AFL_CC) not found (apt install afl++, or set AFL_CC)"; exit 1; }
	@test -n "$(AFL_DRIVER)" && test -f "$(AFL_DRIVER)" || { echo "FAIL: libAFLDriver.a not found"; exit 1; }
	@echo "OK: toolchain looks complete."
	@$(MAKE) --no-print-directory $(BUILD)/bin/mut_bench
	$(BUILD)/bin/mut_bench selftest

validate:
	@python3 -m fleet validate

list:
	@python3 -m fleet list

smoke:
	@FUZZ_SMOKE_SECONDS=$${FUZZ_SMOKE_SECONDS:-10} python3 -m fleet smoke

clean:
	rm -rf $(BUILD)

distclean: clean
	rm -rf runs
