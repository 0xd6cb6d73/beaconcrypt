# SPDX-License-Identifier: 0BSD

SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c

REPOSITORY_ROOT := $(abspath ../../..)
OUTPUT_DIR := $(REPOSITORY_ROOT)/target/formal-verification/crypto-verif
CRYPTOVERIF ?= cryptoverif
CRYPTOVERIF_TIMEOUT ?= 240
PQ_MODELS := \
	automated-established-channel.ocv \
	passive-post-quantum-one-record.ocv \
	ratchet-forward-secrecy.ocv \
	record-authentication-replay.ocv
DEFAULT_MODELS := \
	automated-registration-confidentiality.ocv \
	automated-registration-first-record.ocv \
	assigned-id-binding-negative-control.ocv
MODELS := $(PQ_MODELS) $(DEFAULT_MODELS)

.PHONY: check check-policy

check: check-policy
	@test -n "$${CRYPTOVERIF_PQ_LIB:-}" || { \
		echo 'CRYPTOVERIF_PQ_LIB is not set' >&2; \
		exit 1; \
	}
	@test -r "$$CRYPTOVERIF_PQ_LIB" || { \
		echo "CryptoVerif post-quantum library is not readable: $$CRYPTOVERIF_PQ_LIB" >&2; \
		exit 1; \
	}
	@test -n "$${CRYPTOVERIF_DEFAULT_LIB:-}" || { \
		echo 'CRYPTOVERIF_DEFAULT_LIB is not set' >&2; \
		exit 1; \
	}
	@test -r "$$CRYPTOVERIF_DEFAULT_LIB" || { \
		echo "CryptoVerif default library is not readable: $$CRYPTOVERIF_DEFAULT_LIB" >&2; \
		exit 1; \
	}
	mkdir -p '$(OUTPUT_DIR)'
	@for model in $(MODELS); do \
		log='$(OUTPUT_DIR)'/"$${model%.ocv}.log"; \
		case ' $(DEFAULT_MODELS) ' in \
			*" $$model "*) library="$$CRYPTOVERIF_DEFAULT_LIB" ;; \
			*) library="$$CRYPTOVERIF_PQ_LIB" ;; \
		esac; \
		if ! timeout '$(CRYPTOVERIF_TIMEOUT)' '$(CRYPTOVERIF)' \
				-lib "$$library" "$$model" > "$$log" 2>&1; then \
			echo "CryptoVerif failed for $$model; complete output follows" >&2; \
			cat "$$log" >&2; \
			exit 1; \
		fi; \
		./check-results.sh "$$model" "$$log"; \
	done

check-policy:
	@if rg -n --pcre2 '^[[:space:]]*(?:equiv|collision|equation|statement)\b' \
		--glob '*.ocv' .; then \
		echo 'local CryptoVerif equivalences, equations, or collision statements are not permitted in these models' >&2; \
		exit 1; \
	fi
	@artifacts="$$(find . -type f \( -name '*.log' -o -name '*.tex' -o -name '*.ocv.out' \) -print)"; \
	if [[ -n "$$artifacts" ]]; then \
		echo 'generated CryptoVerif artifacts must stay outside proofs/:' >&2; \
		printf '%s\n' "$$artifacts" >&2; \
		exit 1; \
	fi
