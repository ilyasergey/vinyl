# mk/cov.mk -- coverage entry points (Phase 1).
#
# Coverage is measured on the covfuzz flavour (mk/flags.mk CFLAGS_COVFUZZ,
# mk/lean.mk libvinyl.covfuzz.a, mk/build.mk the per-target .covfuzz link): a
# coverage-instrumented SIBLING of each real fleet binary. cov/per_target.py
# replays each target's corpus through its own .covfuzz binary and reports raw
# `llvm-cov` region/branch coverage over Flac/Native/*.c -- the HONEST denominator.
#
# The old `cov_replay` driver + libvinyl.cov.a measured a hand-written replay of a
# HAND-PICKED entry-point subset, not the 21 targets, which is what produced the
# bogus "213/888 = 24% saturated" number. Both are deleted; per-target .covfuzz
# replaces them.

.PHONY: coverage coverage-build
coverage-build:
	@$(MAKE) --no-print-directory lean-ir
	@$(MAKE) --no-print-directory $(foreach t,$(TARGETS),$(BUILD)/bin/$(t).covfuzz)

# `make coverage` -> all targets; `make coverage T=fz_decode_diff` -> one.
# EXTRA passes through flags such as --contribution / --delta.
coverage: coverage-build
	python3 cov/per_target.py $(T) $(EXTRA)
