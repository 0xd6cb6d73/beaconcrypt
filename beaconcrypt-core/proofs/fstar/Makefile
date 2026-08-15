# SPDX-License-Identifier: 0BSD

# This Makefile is invoked with extraction/ as its working directory. Keeping
# it one directory above the generated files prevents hand-maintained proof
# infrastructure from being mistaken for hax output.

override FSTAR_BIN := fstar.exe
CACHE_DIR ?= .cache
HINT_DIR ?= $(CACHE_DIR)/hints
DEPEND_FILE := $(CACHE_DIR)/depend
ROOTS := $(wildcard *.fst *.fsti)
MANUAL_ROOTS := $(wildcard ../*.fst ../*.fsti)
ALL_ROOTS := $(ROOTS) $(MANUAL_ROOTS)
GENERATED_CHECKED := $(addsuffix .checked,$(addprefix $(CACHE_DIR)/,$(ROOTS)))
MANUAL_CHECKED := $(addsuffix .checked,$(addprefix $(CACHE_DIR)/,$(notdir $(MANUAL_ROOTS))))

ifeq ($(strip $(HAX_PROOF_LIBS_HOME)),)
$(error HAX_PROOF_LIBS_HOME is not set; run `make verify` from the beaconcrypt-core crate)
endif

ifeq ($(strip $(HAX_LIBS_HOME)),)
$(error HAX_LIBS_HOME is not set; run `make verify` from the beaconcrypt-core crate)
endif

ifeq ($(strip $(ROOTS)),)
$(error no generated F* modules found; run the extraction target first)
endif

FSTAR_INCLUDE_DIRS := \
	$(HAX_PROOF_LIBS_HOME)/rust_primitives \
	$(HAX_PROOF_LIBS_HOME)/core \
	$(HAX_LIBS_HOME)

override FSTAR_FLAGS := \
	--cmi \
	--z3version 4.15.3 \
	--warn_error -331 \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached '+Prims+FStar+LowStar+C+Spec.Loops+TestLib' \
	$(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

override FSTAR := $(FSTAR_BIN) $(FSTAR_FLAGS)

.PHONY: verify verify-generated verify-manual

$(CACHE_DIR) $(HINT_DIR):
	mkdir -p $@

$(DEPEND_FILE): $(ALL_ROOTS) | $(CACHE_DIR) $(HINT_DIR)
	$(FSTAR) --include . --include .. --dep full $(ALL_ROOTS) \
		--extract '* -Prims -LowStar -FStar' > $@

include $(DEPEND_FILE)

$(CACHE_DIR)/%.checked: | $(DEPEND_FILE) $(CACHE_DIR) $(HINT_DIR)
	$(FSTAR) --include . --include .. $< --hint_file $(HINT_DIR)/$(notdir $*).hints

verify-generated: $(GENERATED_CHECKED)

# Hand-maintained lemmas live outside extraction/ so hax can freely regenerate that directory.
# Their individual checked targets share the strict flags, cache, and generated dependency graph.
verify-manual: verify-generated $(MANUAL_CHECKED)

verify: verify-manual
