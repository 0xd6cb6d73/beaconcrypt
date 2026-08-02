# SPDX-License-Identifier: 0BSD

SHELL := /bin/bash

HAX_REV := 5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3
HAX_SHELL := github:cryspen/hax/$(HAX_REV)\#ci-examples
HAX_ITEMS := -** \
	+beaconcrypt_protocol_core::ratchet::SequenceCache \
	+beaconcrypt_protocol_core::ratchet::advance_send \
	+beaconcrypt_protocol_core::ratchet::finish_send \
	+beaconcrypt_protocol_core::ratchet::plan_receive_until \
	+beaconcrypt_protocol_core::ratchet::advance_receive \
	+beaconcrypt_protocol_core::ratchet::finish_receive \
	+beaconcrypt_protocol_core::ratchet::start_restore \
	+beaconcrypt_protocol_core::ratchet::restore_receive_key \
	+beaconcrypt_protocol_core::ratchet::finish_restore \
	+beaconcrypt_protocol_core::ratchet::replace_ratchet_for_peer \
	+beaconcrypt_protocol_core::ratchet::advance_send_for_peer \
	+beaconcrypt_protocol_core::pqxdh::beacon_start \
	+beaconcrypt_protocol_core::pqxdh::validate_init_kex \
	+beaconcrypt_protocol_core::pqxdh::build_root_key_input \
	+beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization \
	+beaconcrypt_protocol_core::pqxdh::server_ratchet_initialization \
	+beaconcrypt_protocol_core::pqxdh::**::ratchet_initialization \
	+beaconcrypt_protocol_core::pqxdh::**::key_id_binding \
	+beaconcrypt_protocol_core::pqxdh::beacon_prepare_finish \
	+beaconcrypt_protocol_core::pqxdh::registration_key_id_binding \
	+beaconcrypt_protocol_core::pqxdh::authenticate_registration_key_id_binding \
	+beaconcrypt_protocol_core::pqxdh::beacon_commit \
	+beaconcrypt_protocol_core::pqxdh::beacon_abort_candidate \
	+beaconcrypt_protocol_core::pqxdh::beacon_abort_init \
	+beaconcrypt_protocol_core::pqxdh::beacon_abort_fresh \
	+beaconcrypt_protocol_core::pqxdh::server_accept \
	+beaconcrypt_protocol_core::pqxdh::validate_registration_status \
	+beaconcrypt_protocol_core::pqxdh::server_next_key_id \
	+beaconcrypt_protocol_core::pqxdh::server_prepare_commit \
	+beaconcrypt_protocol_core::pqxdh::server_commit \
	+beaconcrypt_protocol_core::pqxdh::server_abort_candidate \
	+beaconcrypt_protocol_core::pqxdh::build_associated_data

HAX_PROVERIF_ITEMS := -** \
	+!beaconcrypt_protocol_core::pqxdh::InitKex \
	+!beaconcrypt_protocol_core::pqxdh::VerifiedInitKex \
	+!beaconcrypt_protocol_core::pqxdh::RegistrationId \
	+!beaconcrypt_protocol_core::pqxdh::PqxdhSharedSecrets \
	+!beaconcrypt_protocol_core::pqxdh::RootKeyInput \
	+!beaconcrypt_protocol_core::pqxdh::RegistrationKeyIdBinding \
	+!beaconcrypt_protocol_core::pqxdh::registration_id \
	+!beaconcrypt_protocol_core::pqxdh::build_root_key_input \
	+!beaconcrypt_protocol_core::pqxdh::build_associated_data

PROVERIF_DIR := proofs/pro-verif
PROVERIF_EXTRACTION := $(PROVERIF_DIR)/extraction/lib.pvl
PROVERIF_COMMON_LIBS := \
	-lib $(PROVERIF_DIR)/crypto.pvl \
	-lib $(PROVERIF_EXTRACTION) \
	-lib $(PROVERIF_DIR)/environment.pvl
PROVERIF_CHECKER := $(PROVERIF_DIR)/check-results.awk
PROVERIF_TIMEOUT ?= 240
PROVERIF ?= proverif

.PHONY: verify verify-in-shell verify-proverif verify-proverif-in-shell \
	extract-fstar check-fstar extract-proverif check-proverif \
	check-proverif-extraction check-generated

# Enter hax's pinned CI shell, regenerate both backends, and check every proof.
verify:
	nix --extra-experimental-features 'nix-command flakes' \
		develop '$(HAX_SHELL)' -c $(MAKE) verify-in-shell

# This target is split out so CI and developers can reuse an existing pinned
# shell without recursively starting Nix.
verify-in-shell:
	$(MAKE) extract-fstar
	$(MAKE) check-fstar
	$(MAKE) extract-proverif
	$(MAKE) check-proverif

verify-proverif:
	nix --extra-experimental-features 'nix-command flakes' \
		develop '$(HAX_SHELL)' -c $(MAKE) verify-proverif-in-shell

verify-proverif-in-shell:
	$(MAKE) extract-proverif
	$(MAKE) check-proverif

extract-fstar:
	cargo hax into -i '$(HAX_ITEMS)' fstar

check-fstar:
	$(MAKE) -C proofs/fstar/extraction -f ../Makefile verify

extract-proverif:
	cargo hax -C --features=proverif ';' into \
		-i '$(HAX_PROVERIF_ITEMS)' \
		--output-dir $(PROVERIF_DIR)/extraction pro-verif

check-proverif-extraction:
	@if rg -n 'rust_primitives__hax__failure|REPLACE by|todo return|unimplemented' \
		'$(PROVERIF_EXTRACTION)'; then \
		echo 'unexpected ProVerif extraction placeholder' >&2; \
		exit 1; \
	fi
	@for required in \
		'beaconcrypt_protocol_core__pqxdh__registration_id' \
		'beaconcrypt_protocol_core__pqxdh__build_root_key_input' \
		'beaconcrypt_protocol_core__pqxdh__build_associated_data'; do \
		rg -q "$$required" '$(PROVERIF_EXTRACTION)' || { \
			echo "missing ProVerif extraction item: $$required" >&2; \
			exit 1; \
		}; \
	done

check-proverif: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/queries.pvl \
			$(PROVERIF_DIR)/baseline.pv | \
		awk -v scenario=baseline -f '$(PROVERIF_CHECKER)'
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/reachability-queries.pvl \
			$(PROVERIF_DIR)/baseline.pv | \
		awk -v scenario=reachability -f '$(PROVERIF_CHECKER)'
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/compromise-queries.pvl \
			$(PROVERIF_DIR)/compromise.pv | \
		awk -v scenario=compromise -f '$(PROVERIF_CHECKER)'

# Run this after committing generated output to ensure extraction is stable.
check-generated: verify
	git diff --exit-code -- proofs/fstar/extraction proofs/pro-verif/extraction
