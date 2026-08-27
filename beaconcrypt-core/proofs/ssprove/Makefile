# SPDX-License-Identifier: 0BSD

SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c

NIX ?= nix
REPOSITORY_ROOT := $(abspath ../../..)
PROOF_SHELL_RUNNER := $(REPOSITORY_ROOT)/scripts/run-proof-shell
OUTPUT_DIR := $(REPOSITORY_ROOT)/target/formal-verification/ssprove
MODULES := BoundedRom CtxEventReduction CtxGame CtxPrivacy PqxdhRatchetGames PqxdhRatchetRom PqxdhHybridSecurity RatchetForwardSecrecy RecordIntegrity RecordIntegrityBound

.PHONY: verify check check-policy

verify:
	@NIX='$(NIX)' '$(PROOF_SHELL_RUNNER)' run -- $(MAKE) check

check: check-policy
	mkdir -p '$(OUTPUT_DIR)'
	@for module in $(MODULES); do \
		coqc -noglob \
			-Q '$(OUTPUT_DIR)' BeaconcryptSSProve \
			-Q . BeaconcryptSSProve \
			-o "$(OUTPUT_DIR)/$$module.vo" "$$module.v" | \
			tee "$(OUTPUT_DIR)/$$module.assumptions"; \
		diff -u expected-assumptions.txt \
			<(awk '/^Axioms:/{report=1; next} report && /^[^[:space:]][^[:space:]]*[[:space:]]+:/{sub(/[[:space:]]+:.*/, ""); if (!seen[$$0]++) print}' \
				"$(OUTPUT_DIR)/$$module.assumptions"); \
	done
	coqchk -silent -Q '$(OUTPUT_DIR)' BeaconcryptSSProve \
		$(addprefix BeaconcryptSSProve.,$(MODULES))

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
