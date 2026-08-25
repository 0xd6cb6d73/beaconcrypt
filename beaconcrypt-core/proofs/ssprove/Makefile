# SPDX-License-Identifier: 0BSD

SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c

NIX ?= nix
REPOSITORY_ROOT := $(abspath ../../..)
PROOF_SHELL := path:$(REPOSITORY_ROOT)\#proofs
OUTPUT_DIR := $(REPOSITORY_ROOT)/target/formal-verification/ssprove
ASSUMPTIONS_LOG := $(OUTPUT_DIR)/CtxEventReduction.assumptions
PROOF_OBJECT := $(OUTPUT_DIR)/CtxEventReduction.vo

.PHONY: verify check check-policy

verify:
	$(NIX) --extra-experimental-features 'nix-command flakes' develop \
		--no-update-lock-file '$(PROOF_SHELL)' -c $(MAKE) check

check: check-policy
	mkdir -p '$(OUTPUT_DIR)'
	coqc -noglob -Q . BeaconcryptSSProve -o '$(PROOF_OBJECT)' \
		CtxEventReduction.v | tee '$(ASSUMPTIONS_LOG)'
	diff -u expected-assumptions.txt \
		<(awk '/^Axioms:/{report=1; next} report && /^[^[:space:]][^[:space:]]*[[:space:]]+:/{sub(/[[:space:]]+:.*/, ""); print}' '$(ASSUMPTIONS_LOG)')
	coqchk -silent -Q '$(OUTPUT_DIR)' \
		BeaconcryptSSProve.CtxEventReduction

check-policy:
	@if rg -n --pcre2 '(?i:\badmit(?:ted)?\b)|\b(?:Axiom|Conjecture|Parameters?|Abort)\b|__admitted__|falso|(?:exact|vm_cast|native_cast)_no_check|(?:Unset[[:space:]]+(?:Guard|Positivity|Universe)[[:space:]]+Checking|Set[[:space:]]+(?:Type[[:space:]]+in[[:space:]]+Type|Impredicative[[:space:]]+Set))' \
		--glob '*.v' .; then \
		echo 'unexpected proof bypass in repository-owned SSProve source' >&2; \
		exit 1; \
	fi
	@if rg -n '\bHacspec\b|Hacspec_|Beaconcrypt_core_' --glob '*.v' .; then \
		echo 'unqualified hax SSProve prelude or extraction import' >&2; \
		exit 1; \
	fi
	@artifacts="$$(find . -type f \
		\( -name '*.vo' -o -name '*.vos' -o -name '*.vok' \
		-o -name '*.glob' -o -name '.*.aux' \) -print)"; \
	if [[ -n "$$artifacts" ]]; then \
		echo 'compiled SSProve artifacts must stay outside proofs/:' >&2; \
		printf '%s\n' "$$artifacts" >&2; \
		exit 1; \
	fi
