# SPDX-License-Identifier: 0BSD

EASYCRYPT ?= easycrypt
CVC5 ?= cvc5
SOURCES := Common.ec ProtocolGames.ec ActiveQuantum.ec Ctx.ec CtxRom.ec \
	CtxAdaptiveFullRom.ec \
	ProbabilityBounds.ec PqxdhGames.ec PqxdhHybrid.ec ProtocolRom.ec \
	AdaptiveRom.ec HybridAdaptiveRom.ec RatchetForward.ec \
	RatchetAdaptiveRom.ec RecordIntegrity.ec

.PHONY: check check-contracts check-easycrypt check-policy
check: check-policy check-contracts check-easycrypt

check-policy:
	@sh ./check-policy.sh

check-contracts: check-policy

check-easycrypt:
	@command -v '$(EASYCRYPT)' >/dev/null || { \
		echo 'easycrypt executable not found on PATH' >&2; \
		exit 127; \
	}
	@command -v '$(CVC5)' >/dev/null || { \
		echo 'cvc5 executable not found on PATH' >&2; \
		exit 127; \
	}
	@set -eu; \
	config_root=$$(mktemp -d); \
	trap 'rm -rf "$$config_root"' EXIT HUP INT TERM; \
	XDG_CONFIG_HOME="$$config_root" '$(EASYCRYPT)' why3config; \
	for source in $(SOURCES); do \
		'$(EASYCRYPT)' compile -no-eco -why3 "$$config_root/easycrypt/why3.conf" \
			-p CVC5 -I . "$$source"; \
	done
