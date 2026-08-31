# mk/toolchain.mk — locate lean/clang/afl/libFLAC. No absolute/hardcoded
# paths: everything is derived from this file's own location, from $(HOME), or
# from the *contents* of ../lean-toolchain.

# ---- repo anchors -------------------------------------------------------
# FUZZ_ROOT = the fuzz/ directory (this file is always fuzz/mk/toolchain.mk).
# REPO      = the Vinyl repo root (fuzz/ is a sibling of Flac/, bench/, ...).
FUZZ_ROOT   := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/..)
REPO        := $(abspath $(FUZZ_ROOT)/..)
IR_DIR      := $(REPO)/.lake/build/ir
BUILD       := $(FUZZ_ROOT)/build
GEN         := $(BUILD)/gen

# libFLAC source: vendored under third_party/ (deps_fetch.sh), with a dev
# fallback to an existing workspace checkout so a checkout that already has
# reference/flac-src alongside the repo still builds without a fetch.
FLAC_SRC    ?= $(FUZZ_ROOT)/third_party/flac-src
ifeq ($(wildcard $(FLAC_SRC)/include/FLAC/stream_decoder.h),)
  FLAC_SRC := $(firstword $(wildcard $(REPO)/../reference/flac-src))
endif
ifeq ($(wildcard $(FLAC_SRC)/include/FLAC/stream_decoder.h),)
  $(error libFLAC source not found -- run fuzz/scripts/deps_fetch.sh (or set FLAC_SRC=<path>))
endif

ifeq ($(wildcard $(REPO)/lean-toolchain),)
  $(error Cannot find $(REPO)/lean-toolchain -- fuzz/ must be a sibling of the Vinyl repo root)
endif

# ---- Lean toolchain: no hardcoded absolute paths ------------------------
# Discovery order, first hit wins:
#   1. explicit LEAN_PREFIX=... on the command line / environment
#   2. `lean --print-prefix`, run from INSIDE $(REPO) so the directory override
#      (repo/lean-toolchain) selects the version. This prints the toolchain
#      root whether `lean` on PATH is the real binary or the elan shim --
#      deriving the prefix from `command -v lean`'s dirname is WRONG for the
#      shim, whose parent is ~/.elan, not a toolchain.
#   3. elan (`elan which lean` -> real binary, not the shim)
#   4. elan's toolchain-directory naming convention ('/' -> '--', ':' -> '---')
#      applied to repo/lean-toolchain's own contents -- last resort.
ifeq ($(origin LEAN_PREFIX), undefined)
  LEAN_PREFIX := $(shell cd $(REPO) && lean --print-prefix 2>/dev/null)
  ifeq ($(LEAN_PREFIX),)
    ELAN_BIN := $(shell command -v elan 2>/dev/null)
    ifeq ($(ELAN_BIN),)
      ELAN_BIN := $(firstword $(wildcard $(HOME)/.elan/bin/elan))
    endif
    ifneq ($(ELAN_BIN),)
      LEAN_BIN := $(shell cd $(REPO) && $(ELAN_BIN) which lean 2>/dev/null)
      ifneq ($(LEAN_BIN),)
        LEAN_PREFIX := $(abspath $(dir $(LEAN_BIN))/..)
      endif
    endif
  endif
  ifeq ($(LEAN_PREFIX),)
    WANT_TOOLCHAIN := $(shell tr -d ' \t\n' < $(REPO)/lean-toolchain 2>/dev/null)
    TOOLCHAIN_DIR   := $(subst :,---,$(subst /,--,$(WANT_TOOLCHAIN)))
    LEAN_PREFIX     := $(HOME)/.elan/toolchains/$(TOOLCHAIN_DIR)
  endif
endif
LEAN_PREFIX := $(abspath $(LEAN_PREFIX))

ifeq ($(wildcard $(LEAN_PREFIX)/include/lean),)
  $(error Cannot find a Lean toolchain at LEAN_PREFIX=$(LEAN_PREFIX). Install elan (see \
    $(REPO)/lean-toolchain), or set LEAN_PREFIX=<toolchain dir> explicitly)
endif

LEAN_INC     := $(LEAN_PREFIX)/include
LEAN_LIBDIR  := $(LEAN_PREFIX)/lib
LEAN_LEANLIB := $(LEAN_PREFIX)/lib/lean
LAKE_BIN     ?= $(if $(wildcard $(LEAN_PREFIX)/bin/lake),$(LEAN_PREFIX)/bin/lake,$(shell command -v lake 2>/dev/null))

# ---- other tools --------------------------------------------------------
CLANG    ?= clang
AFL_CC   ?= afl-clang-fast
CMAKE    ?= cmake
NPROC    := $(shell nproc 2>/dev/null || echo 4)

# ---- ffmpeg (libavcodec/format/util): the 2nd differential reference decoder.
# A reference, not the system-under-test, so it links UNINSTRUMENTED as an
# ordinary shared library (no coverage build). Only the target that calls it
# (fz_samples_diff -> wide_diff.o) pulls it, via -Wl,--as-needed in the link.
FFMPEG_CFLAGS := $(shell pkg-config --cflags libavformat libavcodec libavutil 2>/dev/null)
FFMPEG_LIBS   := $(shell pkg-config --libs   libavformat libavcodec libavutil 2>/dev/null)
ifeq ($(strip $(FFMPEG_LIBS)),)
  $(error ffmpeg dev libraries not found -- apt install libavcodec-dev libavformat-dev libavutil-dev)
endif

FUZZER_RT        := $(shell $(CLANG) --print-file-name=libclang_rt.fuzzer-x86_64.a)
FUZZER_RT_NOMAIN := $(shell $(CLANG) --print-file-name=libclang_rt.fuzzer_no_main-x86_64.a)
AFL_DRIVER       := $(firstword $(wildcard /usr/lib/afl/libAFLDriver.a \
                                           /usr/local/lib/afl/libAFLDriver.a) \
                                $(wildcard $(shell command -v afl-config >/dev/null 2>&1 && afl-config --libdir 2>/dev/null)/libAFLDriver.a))
