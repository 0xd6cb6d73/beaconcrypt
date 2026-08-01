# SPDX-License-Identifier: 0BSD

# This Makefile is invoked with extraction/ as its working directory. Keeping
# it one directory above the generated files prevents hand-maintained proof
# infrastructure from being mistaken for hax output.

FSTAR_BIN ?= fstar.exe
CACHE_DIR ?= .cache
HINT_DIR ?= $(CACHE_DIR)/hints
DEPEND_FILE := $(CACHE_DIR)/depend
ROOTS := $(wildcard *.fst *.fsti)
MANUAL_ROOTS := $(wildcard ../*.fst ../*.fsti)

ifeq ($(strip $(HAX_PROOF_LIBS_HOME)),)
$(error HAX_PROOF_LIBS_HOME is not set; run `make verify` from the protocol-core crate)
endif

ifeq ($(strip $(HAX_LIBS_HOME)),)
$(error HAX_LIBS_HOME is not set; run `make verify` from the protocol-core crate)
endif

ifeq ($(strip $(ROOTS)),)
$(error no generated F* modules found; run the extraction target first)
endif

FSTAR_INCLUDE_DIRS := \
	$(HAX_PROOF_LIBS_HOME)/rust_primitives \
	$(HAX_PROOF_LIBS_HOME)/core \
	$(HAX_LIBS_HOME)

FSTAR_FLAGS := \
	--cmi \
	--warn_error -331 \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached '+Prims+FStar+LowStar+C+Spec.Loops+TestLib' \
	$(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR := $(FSTAR_BIN) $(FSTAR_FLAGS)

.PHONY: verify verify-generated verify-manual

$(CACHE_DIR) $(HINT_DIR):
	mkdir -p $@

$(DEPEND_FILE): $(ROOTS) | $(CACHE_DIR) $(HINT_DIR)
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar' > $@

include $(DEPEND_FILE)

$(CACHE_DIR)/%.checked: | $(DEPEND_FILE) $(CACHE_DIR) $(HINT_DIR)
	$(FSTAR) $< --hint_file $(HINT_DIR)/$(notdir $*).hints

verify-generated: $(addsuffix .checked,$(addprefix $(CACHE_DIR)/,$(ROOTS)))

# Hand-maintained lemmas live outside extraction/ so hax can freely regenerate
# that directory.  They are checked only after the extracted modules and share
# the same strict flags and checked-module cache.
verify-manual: verify-generated
	$(FSTAR) --include . $(MANUAL_ROOTS) \
		$(foreach root,$(MANUAL_ROOTS),--hint_file $(HINT_DIR)/$(notdir $(root)).hints)

verify: verify-manual
