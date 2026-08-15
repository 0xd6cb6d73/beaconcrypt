# SPDX-License-Identifier: 0BSD

SHELL := /bin/bash

NIX ?= nix
PROOF_SHELL := path:../..\#proofs
EXPECTED_RUSTC := rustc 1.93.0-nightly (843f8ce2e 2025-11-07)
EXPECTED_CARGO := cargo 1.93.0-nightly (636800288 2025-10-31)
EXPECTED_HAX := 0.3.7
EXPECTED_FSTAR := F* 2025.10.06~dev
EXPECTED_Z3 := Z3 version 4.15.3 - 64 bit
EXPECTED_PROVERIF := Proverif 2.05. Cryptographic protocol verifier, by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre
HAX_ITEMS := -** \
	+beaconcrypt_protocol_core::commitment::build_commitment_transcript \
	+beaconcrypt_protocol_core::ratchet::SequenceCache \
	+beaconcrypt_protocol_core::ratchet::RatchetChain \
	+beaconcrypt_protocol_core::ratchet::RatchetKey \
	+beaconcrypt_protocol_core::ratchet::RatchetNonce \
	+beaconcrypt_protocol_core::ratchet::RatchetMaterial \
	+beaconcrypt_protocol_core::ratchet::SymmetricRatchetKdfRequest \
	+beaconcrypt_protocol_core::ratchet::RatchetKdfOutput \
	+beaconcrypt_protocol_core::ratchet::split_ratchet_kdf_output \
	+beaconcrypt_protocol_core::ratchet::derive_ratchet_step \
	+beaconcrypt_protocol_core::ratchet::ConcreteRatchetChain \
	+beaconcrypt_protocol_core::ratchet::concrete_ratchet_step \
	+beaconcrypt_protocol_core::ratchet::RatchetStep \
	+beaconcrypt_protocol_core::ratchet::CachedReceiveKey \
	+beaconcrypt_protocol_core::ratchet::RefinedRatchet \
	+beaconcrypt_protocol_core::ratchet::ConcreteRatchetKernel \
	+beaconcrypt_protocol_core::ratchet::RefinedSendKey \
	+beaconcrypt_protocol_core::ratchet::RefinedRatchetRestore \
	+beaconcrypt_protocol_core::ratchet::ConcreteRatchetRestore \
	+beaconcrypt_protocol_core::ratchet::**::new \
	+beaconcrypt_protocol_core::ratchet::**::from_counters \
	+beaconcrypt_protocol_core::ratchet::**::send_sequence \
	+beaconcrypt_protocol_core::ratchet::**::receive_sequence \
	+beaconcrypt_protocol_core::ratchet::**::receive_cache_len \
	+beaconcrypt_protocol_core::ratchet::**::send_chain \
	+beaconcrypt_protocol_core::ratchet::**::receive_chain \
	+beaconcrypt_protocol_core::ratchet::**::receive_entry_at \
	+beaconcrypt_protocol_core::ratchet::**::sequence \
	+beaconcrypt_protocol_core::ratchet::**::material \
	+beaconcrypt_protocol_core::ratchet::**::key \
	+beaconcrypt_protocol_core::ratchet::**::next_chain \
	+beaconcrypt_protocol_core::ratchet::**::nonce \
	+beaconcrypt_protocol_core::ratchet::**::as_bytes \
	+beaconcrypt_protocol_core::ratchet::**::into_bytes \
	+beaconcrypt_protocol_core::ratchet::**::into_parts \
	+beaconcrypt_protocol_core::ratchet::**::into_step \
	+beaconcrypt_protocol_core::ratchet::refined_advance_send \
	+beaconcrypt_protocol_core::ratchet::refined_finish_send \
	+beaconcrypt_protocol_core::ratchet::refined_seal_next \
	+beaconcrypt_protocol_core::ratchet::refined_advance_receive \
	+beaconcrypt_protocol_core::ratchet::refined_advance_receive_until \
	+beaconcrypt_protocol_core::ratchet::refined_receive_key \
	+beaconcrypt_protocol_core::ratchet::refined_finish_receive \
	+beaconcrypt_protocol_core::ratchet::PreparedReceive \
	+beaconcrypt_protocol_core::ratchet::PreparedCachedReceive \
	+beaconcrypt_protocol_core::ratchet::PreparedFutureTarget \
	+beaconcrypt_protocol_core::ratchet::PendingReceive \
	+beaconcrypt_protocol_core::ratchet::prepare_cached_receive \
	+beaconcrypt_protocol_core::ratchet::prepare_future_receive_steps \
	+beaconcrypt_protocol_core::ratchet::receive_control_prefix_matches \
	+beaconcrypt_protocol_core::ratchet::pending_receive_slots_are_valid \
	+beaconcrypt_protocol_core::ratchet::pending_receive_is_valid \
	+beaconcrypt_protocol_core::ratchet::prepare_receive \
	+beaconcrypt_protocol_core::ratchet::publish_cached_receive \
	+beaconcrypt_protocol_core::ratchet::publish_future_receive_slots \
	+beaconcrypt_protocol_core::ratchet::publish_future_receive \
	+beaconcrypt_protocol_core::ratchet::refined_open_and_finish \
	+beaconcrypt_protocol_core::ratchet::concrete_seal_next \
	+beaconcrypt_protocol_core::ratchet::concrete_open_and_finish \
	+beaconcrypt_protocol_core::ratchet::start_refined_restore \
	+beaconcrypt_protocol_core::ratchet::refined_restore_receive_key \
	+beaconcrypt_protocol_core::ratchet::finish_refined_restore \
	+beaconcrypt_protocol_core::ratchet::start_concrete_restore \
	+beaconcrypt_protocol_core::ratchet::concrete_restore_receive_key \
	+beaconcrypt_protocol_core::ratchet::finish_concrete_restore \
	+beaconcrypt_protocol_core::ratchet::advance_send \
	+beaconcrypt_protocol_core::ratchet::finish_send \
	+beaconcrypt_protocol_core::ratchet::plan_receive_until \
	+beaconcrypt_protocol_core::ratchet::advance_receive \
	+beaconcrypt_protocol_core::ratchet::lookup_receive_key \
	+beaconcrypt_protocol_core::ratchet::ReceiveRemoval \
	+beaconcrypt_protocol_core::ratchet::ReceiveFinishWithRemoval \
	+beaconcrypt_protocol_core::ratchet::finish_receive_with_removal \
	+beaconcrypt_protocol_core::ratchet::finish_receive \
	+beaconcrypt_protocol_core::ratchet::start_restore \
	+beaconcrypt_protocol_core::ratchet::ReceiveRestoreStep \
	+beaconcrypt_protocol_core::ratchet::restore_receive_key_with_slot \
	+beaconcrypt_protocol_core::ratchet::restore_receive_key \
	+beaconcrypt_protocol_core::ratchet::finish_restore \
	+beaconcrypt_protocol_core::ratchet::replace_ratchet_for_peer \
	+beaconcrypt_protocol_core::ratchet::advance_send_for_peer \
	+beaconcrypt_protocol_core::pqxdh::beacon_start \
	+beaconcrypt_protocol_core::pqxdh::validate_init_kex \
	+beaconcrypt_protocol_core::pqxdh::build_root_key_input \
	+beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization \
	+beaconcrypt_protocol_core::pqxdh::server_ratchet_initialization \
	+beaconcrypt_protocol_core::pqxdh::InitialRatchetChains \
	+beaconcrypt_protocol_core::pqxdh::split_initial_ratchet_kdf_output \
	+beaconcrypt_protocol_core::pqxdh::derive_initial_ratchet_chains \
	+beaconcrypt_protocol_core::pqxdh::derive_initial_ratchet_kernel \
	+beaconcrypt_protocol_core::pqxdh::derive_beacon_ratchet_kernel \
	+beaconcrypt_protocol_core::pqxdh::derive_server_ratchet_kernel \
	+beaconcrypt_protocol_core::pqxdh::**::derive_ratchet_kernel \
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
PROVERIF_AEAD_CONTROL_LIBS := \
	-lib $(PROVERIF_DIR)/crypto.pvl \
	-lib $(PROVERIF_DIR)/aead-commitment-negative-control.pvl \
	-lib $(PROVERIF_DIR)/aead-commitment-negative-control-queries.pvl
PROVERIF_CHECKER := $(PROVERIF_DIR)/check-results.awk
PROVERIF_TIMEOUT ?= 240
override PROVERIF := proverif

.PHONY: verify verify-in-shell verify-proverif verify-proverif-in-shell \
	check-toolchain check-fstar-policy check-inventory \
	extract-fstar check-fstar extract-proverif check-proverif \
	check-proverif-extraction check-generated

# Enter the repository-locked proof shell, regenerate both backends, and check
# every proof. --no-update-lock-file makes a stale or incomplete lock fail.
verify:
	$(NIX) --extra-experimental-features 'nix-command flakes' \
		develop --no-update-lock-file '$(PROOF_SHELL)' -c \
		$(MAKE) verify-in-shell

# This target is split out so CI and developers can reuse the locked shell
# without recursively starting Nix.
verify-in-shell:
	$(MAKE) check-toolchain
	$(MAKE) extract-fstar
	$(MAKE) check-fstar
	$(MAKE) extract-proverif
	$(MAKE) check-proverif

verify-proverif:
	$(NIX) --extra-experimental-features 'nix-command flakes' \
		develop --no-update-lock-file '$(PROOF_SHELL)' -c \
		$(MAKE) verify-proverif-in-shell

verify-proverif-in-shell:
	$(MAKE) check-toolchain
	$(MAKE) extract-proverif
	$(MAKE) check-proverif

# Review tripwire for the complete production/proof trust boundary. Run after
# extraction and proof checks so generated output is checked against the
# reviewed baseline without preventing an intentional changed artifact from
# first being analyzed.
check-inventory:
	bash proofs/check-inventory.sh

# Fail before extraction if PATH or a flake edit selected a tool other than the
# reviewed proof bundle. F* uses this same exposed z3-4.15.3 executable.
check-toolchain:
	@set -euo pipefail; \
		check_version() { \
			local tool="$$1" expected="$$2" actual="$$3"; \
			if [[ "$$actual" != "$$expected" ]]; then \
				echo "unexpected $$tool version" >&2; \
				echo "  expected: $$expected" >&2; \
				echo "  actual:   $$actual" >&2; \
				exit 1; \
			fi; \
			printf '%s: %s\n' "$$tool" "$$actual"; \
		}; \
		check_version rustc '$(EXPECTED_RUSTC)' "$$(rustc --version)"; \
		check_version cargo '$(EXPECTED_CARGO)' "$$(cargo --version)"; \
		check_version hax '$(EXPECTED_HAX)' \
			"$$(cargo hax --version | awk -F= '$$1 == "version" { print $$2 }')"; \
		check_version Fstar '$(EXPECTED_FSTAR)' \
			"$$(fstar.exe --version | sed -n '1p')"; \
		check_version Z3 '$(EXPECTED_Z3)' "$$(z3-4.15.3 -version)"; \
		check_version ProVerif '$(EXPECTED_PROVERIF)' \
			"$$(proverif -help 2>&1 | sed -n '1p')"

extract-fstar:
	# Enable hax-lib so the bounded recursive lookup carries its checked measure.
	cargo hax -C --locked --features=proverif ';' into -i '$(HAX_ITEMS)' fstar

# F* accepts explicit assumptions and lax/admit flags, so strict typechecking
# alone is not a sufficient policy gate for repository-owned proof modules.
check-fstar-policy:
	@if rg -n --pcre2 '\b(?:assume|admit)\b' proofs/fstar \
		--glob '*.fst' --glob '*.fsti'; then \
		echo 'unexpected assume/admit in repository-owned F* proof' >&2; \
		exit 1; \
	fi
	@if rg -n -- '--(lax|admit_smt_queries|admit_except|use_hint_hashes)' \
		proofs/fstar/Makefile; then \
		echo 'unexpected lax/admit flag in the F* checker' >&2; \
		exit 1; \
	fi

check-fstar: check-fstar-policy
	$(MAKE) -C proofs/fstar/extraction -f ../Makefile verify

extract-proverif:
	cargo hax -C --locked --features=proverif ';' into \
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
			$(PROVERIF_AEAD_CONTROL_LIBS) \
			$(PROVERIF_DIR)/aead-commitment.pv | \
		awk -v scenario=aead-commitment -f '$(PROVERIF_CHECKER)'
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_AEAD_CONTROL_LIBS) \
			$(PROVERIF_DIR)/aead-no-commitment.pv | \
		awk -v scenario=aead-no-commitment -f '$(PROVERIF_CHECKER)'
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
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/failed-receive-queries.pvl \
			$(PROVERIF_DIR)/failed-receive.pv | \
		awk -v scenario=failed-receive -f '$(PROVERIF_CHECKER)'
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/failed-receive-reachability-queries.pvl \
			$(PROVERIF_DIR)/failed-receive.pv | \
		awk -v scenario=failed-receive-reachability \
			-f '$(PROVERIF_CHECKER)'
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/failed-receive-compromise-queries.pvl \
			$(PROVERIF_DIR)/failed-receive-compromise.pv | \
		awk -v scenario=failed-receive-compromise \
			-f '$(PROVERIF_CHECKER)'
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib \
			$(PROVERIF_DIR)/failed-receive-compromise-reachability-queries.pvl \
			$(PROVERIF_DIR)/failed-receive-compromise.pv | \
		awk -v scenario=failed-receive-compromise-reachability \
			-f '$(PROVERIF_CHECKER)'

# Run this after committing generated output to ensure extraction is stable.
check-generated: verify
	git diff --exit-code -- proofs/fstar/extraction proofs/pro-verif/extraction
	@untracked="$$(git ls-files --others --exclude-standard -- \
		proofs/fstar/extraction proofs/pro-verif/extraction)"; \
		if [[ -n "$$untracked" ]]; then \
			echo 'untracked generated proof artifacts:' >&2; \
			printf '%s\n' "$$untracked" >&2; \
			exit 1; \
		fi
