# SPDX-License-Identifier: 0BSD

SHELL := /bin/bash

NIX ?= nix
PROOF_SHELL := path:..\#proofs
EXPECTED_RUSTC := rustc 1.93.0-nightly (843f8ce2e 2025-11-07)
EXPECTED_CARGO := cargo 1.93.0-nightly (636800288 2025-10-31)
EXPECTED_HAX := 0.3.7
EXPECTED_FSTAR := F* 2025.10.06~dev
EXPECTED_Z3 := Z3 version 4.15.3 - 64 bit
EXPECTED_PROVERIF := Proverif 2.05. Cryptographic protocol verifier, by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre
HAX_ITEMS := -** \
	+beaconcrypt_core::commitment::build_commitment_transcript \
	+beaconcrypt_core::ratchet::control::SequenceCache \
	+beaconcrypt_core::ratchet::RatchetChain \
	+beaconcrypt_core::ratchet::RatchetKey \
	+beaconcrypt_core::ratchet::RatchetNonce \
	+beaconcrypt_core::ratchet::RatchetMaterial \
	+beaconcrypt_core::ratchet::SymmetricRatchetKdfRequest \
	+beaconcrypt_core::ratchet::RatchetKdfOutput \
	+beaconcrypt_core::ratchet::split_ratchet_kdf_output \
	+beaconcrypt_core::ratchet::derive_ratchet_step \
	+beaconcrypt_core::ratchet::ConcreteRatchetChain \
	+beaconcrypt_core::ratchet::concrete_ratchet_step \
	+beaconcrypt_core::ratchet::refined::RatchetStep \
	+beaconcrypt_core::ratchet::refined::CachedReceiveKey \
	+beaconcrypt_core::ratchet::refined::RefinedRatchet \
	+beaconcrypt_core::ratchet::ConcreteRatchetKernel \
	+beaconcrypt_core::ratchet::refined::RefinedSendKey \
	+beaconcrypt_core::ratchet::refined::RefinedRatchetRestore \
	+beaconcrypt_core::ratchet::ConcreteRatchetRestore \
	+beaconcrypt_core::ratchet::**::new \
	+beaconcrypt_core::ratchet::**::from_counters \
	+beaconcrypt_core::ratchet::**::send_sequence \
	+beaconcrypt_core::ratchet::**::receive_sequence \
	+beaconcrypt_core::ratchet::**::receive_cache_len \
	+beaconcrypt_core::ratchet::**::send_chain \
	+beaconcrypt_core::ratchet::**::receive_chain \
	+beaconcrypt_core::ratchet::**::receive_entry_at \
	+beaconcrypt_core::ratchet::**::sequence \
	+beaconcrypt_core::ratchet::**::material \
	+beaconcrypt_core::ratchet::**::key \
	+beaconcrypt_core::ratchet::**::next_chain \
	+beaconcrypt_core::ratchet::**::nonce \
	+beaconcrypt_core::ratchet::**::as_bytes \
	+beaconcrypt_core::ratchet::**::into_bytes \
	+beaconcrypt_core::ratchet::**::into_parts \
	+beaconcrypt_core::ratchet::**::into_step \
	+beaconcrypt_core::ratchet::refined::refined_advance_send \
	+beaconcrypt_core::ratchet::refined::refined_finish_send \
	+beaconcrypt_core::ratchet::refined::refined_seal_next \
	+beaconcrypt_core::ratchet::refined::refined_advance_receive \
	+beaconcrypt_core::ratchet::refined::refined_advance_receive_until \
	+beaconcrypt_core::ratchet::refined::refined_receive_key \
	+beaconcrypt_core::ratchet::refined::refined_finish_receive \
	+beaconcrypt_core::ratchet::refined::PreparedReceive \
	+beaconcrypt_core::ratchet::refined::PreparedCachedReceive \
	+beaconcrypt_core::ratchet::refined::PreparedFutureTarget \
	+beaconcrypt_core::ratchet::refined::PendingReceive \
	+beaconcrypt_core::ratchet::refined::prepare_cached_receive \
	+beaconcrypt_core::ratchet::refined::prepare_future_receive_steps \
	+beaconcrypt_core::ratchet::refined::receive_control_prefix_matches \
	+beaconcrypt_core::ratchet::refined::pending_receive_slots_are_valid \
	+beaconcrypt_core::ratchet::refined::pending_receive_is_valid \
	+beaconcrypt_core::ratchet::refined::prepare_receive \
	+beaconcrypt_core::ratchet::refined::publish_cached_receive \
	+beaconcrypt_core::ratchet::refined::publish_future_receive_slots \
	+beaconcrypt_core::ratchet::refined::publish_future_receive \
	+beaconcrypt_core::ratchet::refined::refined_open_and_finish \
	+beaconcrypt_core::ratchet::concrete_seal_next \
	+beaconcrypt_core::ratchet::concrete_open_and_finish \
	+beaconcrypt_core::ratchet::refined::start_refined_restore \
	+beaconcrypt_core::ratchet::refined::refined_restore_receive_key \
	+beaconcrypt_core::ratchet::refined::finish_refined_restore \
	+beaconcrypt_core::ratchet::start_concrete_restore \
	+beaconcrypt_core::ratchet::concrete_restore_receive_key \
	+beaconcrypt_core::ratchet::finish_concrete_restore \
	+beaconcrypt_core::ratchet::control::advance_send \
	+beaconcrypt_core::ratchet::control::finish_send \
	+beaconcrypt_core::ratchet::control::plan_receive_until \
	+beaconcrypt_core::ratchet::control::advance_receive \
	+beaconcrypt_core::ratchet::control::lookup_receive_key \
	+beaconcrypt_core::ratchet::control::ReceiveRemoval \
	+beaconcrypt_core::ratchet::control::ReceiveFinishWithRemoval \
	+beaconcrypt_core::ratchet::control::finish_receive_with_removal \
	+beaconcrypt_core::ratchet::control::finish_receive \
	+beaconcrypt_core::ratchet::control::start_restore \
	+beaconcrypt_core::ratchet::control::ReceiveRestoreStep \
	+beaconcrypt_core::ratchet::control::restore_receive_key_with_slot \
	+beaconcrypt_core::ratchet::control::restore_receive_key \
	+beaconcrypt_core::ratchet::control::finish_restore \
	+beaconcrypt_core::ratchet::control::replace_ratchet_for_peer \
	+beaconcrypt_core::ratchet::control::advance_send_for_peer \
	+beaconcrypt_core::pqxdh::beacon_start \
	+beaconcrypt_core::pqxdh::validate_init_kex \
	+beaconcrypt_core::pqxdh::build_root_key_input \
	+beaconcrypt_core::pqxdh::beacon_ratchet_initialization \
	+beaconcrypt_core::pqxdh::server_ratchet_initialization \
	+beaconcrypt_core::pqxdh::InitialRatchetChains \
	+beaconcrypt_core::pqxdh::split_initial_ratchet_kdf_output \
	+beaconcrypt_core::pqxdh::derive_initial_ratchet_chains \
	+beaconcrypt_core::pqxdh::derive_initial_ratchet_kernel \
	+beaconcrypt_core::pqxdh::derive_beacon_ratchet_kernel \
	+beaconcrypt_core::pqxdh::derive_server_ratchet_kernel \
	+beaconcrypt_core::pqxdh::**::derive_ratchet_kernel \
	+beaconcrypt_core::pqxdh::**::ratchet_initialization \
	+beaconcrypt_core::pqxdh::**::key_id_binding \
	+beaconcrypt_core::pqxdh::beacon_prepare_finish \
	+beaconcrypt_core::pqxdh::registration_key_id_binding \
	+beaconcrypt_core::pqxdh::authenticate_registration_key_id_binding \
	+beaconcrypt_core::pqxdh::beacon_commit \
	+beaconcrypt_core::pqxdh::beacon_abort_candidate \
	+beaconcrypt_core::pqxdh::beacon_abort_init \
	+beaconcrypt_core::pqxdh::beacon_abort_fresh \
	+beaconcrypt_core::pqxdh::server_accept \
	+beaconcrypt_core::pqxdh::validate_registration_status \
	+beaconcrypt_core::pqxdh::server_next_key_id \
	+beaconcrypt_core::pqxdh::server_prepare_commit \
	+beaconcrypt_core::pqxdh::server_commit \
	+beaconcrypt_core::pqxdh::server_abort_candidate \
	+beaconcrypt_core::pqxdh::build_associated_data

HAX_PROVERIF_ITEMS := -** \
	+!beaconcrypt_core::pqxdh::InitKex \
	+!beaconcrypt_core::pqxdh::VerifiedInitKex \
	+!beaconcrypt_core::pqxdh::RegistrationId \
	+!beaconcrypt_core::pqxdh::PqxdhSharedSecrets \
	+!beaconcrypt_core::pqxdh::RootKeyInput \
	+!beaconcrypt_core::pqxdh::RegistrationKeyIdBinding \
	+!beaconcrypt_core::pqxdh::registration_id \
	+!beaconcrypt_core::pqxdh::build_root_key_input \
	+!beaconcrypt_core::pqxdh::build_associated_data

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
PROVERIF_SCENARIOS := \
	aead-commitment \
	aead-no-commitment \
	baseline \
	reachability \
	compromise \
	failed-receive \
	failed-receive-reachability \
	failed-receive-compromise \
	failed-receive-compromise-reachability
PROVERIF_CHECK_TARGETS := $(addprefix check-proverif-,$(PROVERIF_SCENARIOS))
PROVERIF_VERIFY_TARGETS := $(addprefix verify-proverif-,$(PROVERIF_SCENARIOS))
PROVERIF_GENERATED_TARGETS := $(addprefix check-generated-proverif-,$(PROVERIF_SCENARIOS))

LEAN_DIR := proofs/lean
LEAN_ROOT := $(LEAN_DIR)/BeaconcryptCore.lean
LEAN_PROOF_PATHS := $(LEAN_DIR)/BeaconcryptCore $(LEAN_DIR)/BeaconcryptCore.lean
LEAN_GENERATED_PATHS := \
	$(LEAN_DIR)/BeaconcryptCore/Extraction/Funs.lean \
	$(LEAN_DIR)/BeaconcryptCore/Extraction/FunsExternal_Template.lean \
	$(LEAN_DIR)/BeaconcryptCore/Extraction/Types.lean \
	$(LEAN_DIR)/BeaconcryptCore/Extraction/TypesExternal_Template.lean \
	$(LEAN_DIR)/llbc

# Hax creates the Lean project/root files only when they are absent.
# The checked-in root and Lake configuration are maintained verification entry points.
# Extraction preserves their proof imports and all-module build glob.

.PHONY: verify verify-in-shell verify-fstar verify-fstar-in-shell \
	verify-proverif verify-proverif-in-shell verify-proverif-scenario-in-shell \
	check-toolchain check-fstar-policy check-lean-policy check-lean-root check-inventory \
	extract-fstar check-fstar extract-proverif check-proverif \
	check-proverif-extraction check-generated check-generated-fstar check-generated-lean \
	$(PROVERIF_CHECK_TARGETS) $(PROVERIF_VERIFY_TARGETS) \
	$(PROVERIF_GENERATED_TARGETS) extract-lean check-lean verify-lean \
	verify-lean-in-shell

# Enter the repository-locked proof shell, regenerate every backend, and check
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
	$(MAKE) extract-lean
	$(MAKE) check-lean

verify-fstar:
	$(NIX) --extra-experimental-features 'nix-command flakes' \
		develop --no-update-lock-file '$(PROOF_SHELL)' -c \
		$(MAKE) verify-fstar-in-shell

verify-fstar-in-shell:
	$(MAKE) check-toolchain
	$(MAKE) extract-fstar
	$(MAKE) check-fstar

verify-proverif:
	$(NIX) --extra-experimental-features 'nix-command flakes' \
		develop --no-update-lock-file '$(PROOF_SHELL)' -c \
		$(MAKE) verify-proverif-in-shell

verify-proverif-in-shell:
	$(MAKE) check-toolchain
	$(MAKE) extract-proverif
	$(MAKE) check-proverif

$(PROVERIF_VERIFY_TARGETS): verify-proverif-%:
	$(NIX) --extra-experimental-features 'nix-command flakes' \
		develop --no-update-lock-file '$(PROOF_SHELL)' -c \
		$(MAKE) verify-proverif-scenario-in-shell PROVERIF_SCENARIO='$*'

verify-proverif-scenario-in-shell:
	$(MAKE) check-toolchain
	$(MAKE) extract-proverif
	$(MAKE) check-proverif-$(PROVERIF_SCENARIO)

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
		'beaconcrypt_core__pqxdh__registration_id' \
		'beaconcrypt_core__pqxdh__build_root_key_input' \
		'beaconcrypt_core__pqxdh__build_associated_data'; do \
		rg -q "$$required" '$(PROVERIF_EXTRACTION)' || { \
			echo "missing ProVerif extraction item: $$required" >&2; \
			exit 1; \
		}; \
	done

check-proverif:
	+$(MAKE) --no-print-directory -j$(words $(PROVERIF_SCENARIOS)) \
		$(PROVERIF_CHECK_TARGETS)

check-proverif-aead-commitment: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_AEAD_CONTROL_LIBS) \
			$(PROVERIF_DIR)/aead-commitment.pv | \
		awk -v scenario=aead-commitment -f '$(PROVERIF_CHECKER)'

check-proverif-aead-no-commitment: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_AEAD_CONTROL_LIBS) \
			$(PROVERIF_DIR)/aead-no-commitment.pv | \
		awk -v scenario=aead-no-commitment -f '$(PROVERIF_CHECKER)'

check-proverif-baseline: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/queries.pvl \
			$(PROVERIF_DIR)/baseline.pv | \
		awk -v scenario=baseline -f '$(PROVERIF_CHECKER)'

check-proverif-reachability: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/reachability-queries.pvl \
			$(PROVERIF_DIR)/baseline.pv | \
		awk -v scenario=reachability -f '$(PROVERIF_CHECKER)'

check-proverif-compromise: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/compromise-queries.pvl \
			$(PROVERIF_DIR)/compromise.pv | \
		awk -v scenario=compromise -f '$(PROVERIF_CHECKER)'

check-proverif-failed-receive: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/failed-receive-queries.pvl \
			$(PROVERIF_DIR)/failed-receive.pv | \
		awk -v scenario=failed-receive -f '$(PROVERIF_CHECKER)'

check-proverif-failed-receive-reachability: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/failed-receive-reachability-queries.pvl \
			$(PROVERIF_DIR)/failed-receive.pv | \
		awk -v scenario=failed-receive-reachability \
			-f '$(PROVERIF_CHECKER)'

check-proverif-failed-receive-compromise: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib $(PROVERIF_DIR)/failed-receive-compromise-queries.pvl \
			$(PROVERIF_DIR)/failed-receive-compromise.pv | \
		awk -v scenario=failed-receive-compromise \
			-f '$(PROVERIF_CHECKER)'

check-proverif-failed-receive-compromise-reachability: check-proverif-extraction
	@set -o pipefail; \
		timeout '$(PROVERIF_TIMEOUT)' '$(PROVERIF)' \
			$(PROVERIF_COMMON_LIBS) \
			-lib \
			$(PROVERIF_DIR)/failed-receive-compromise-reachability-queries.pvl \
			$(PROVERIF_DIR)/failed-receive-compromise.pv | \
		awk -v scenario=failed-receive-compromise-reachability \
			-f '$(PROVERIF_CHECKER)'

extract-lean:
	@test -f '$(LEAN_ROOT)' || { \
		echo 'missing maintained Lean verification root: $(LEAN_ROOT)' >&2; \
		exit 1; \
	}
	rm -rf $(LEAN_DIR)/llbc
	cargo hax -C --locked ';' into lean --lakefile

check-lean-policy:
	@if rg -n --pcre2 '\b(?:sorry|admit|axiom)\b|sorryAx' $(LEAN_PROOF_PATHS) \
		--glob '*.lean'; then \
		echo 'unexpected sorry/admit/axiom in repository-owned Lean proof' >&2; \
		exit 1; \
	fi

check-lean-root:
	@for module in \
		BeaconcryptCore.Model.RatchetControlRestore \
		BeaconcryptCore.Model.RatchetEffectRefinement; do \
		rg -Fqx "import $$module" '$(LEAN_ROOT)' || { \
			echo "missing verification-root import: $$module" >&2; \
			exit 1; \
		}; \
	done
	@rg -Fqx 'globs = ["BeaconcryptCore", "BeaconcryptCore.+"]' \
		$(LEAN_DIR)/lakefile.toml || { \
		echo 'Lean library must build the root and every BeaconcryptCore submodule' >&2; \
		exit 1; \
	}

check-lean: check-lean-policy check-lean-root
	cd $(LEAN_DIR) && lake build

# Regenerate and check the complete default beaconcrypt-core production surface.
verify-lean:
	$(NIX) --extra-experimental-features 'nix-command flakes' \
		develop --no-update-lock-file '$(PROOF_SHELL)' -c \
		$(MAKE) verify-lean-in-shell

verify-lean-in-shell:
	$(MAKE) check-toolchain
	$(MAKE) extract-lean
	$(MAKE) check-lean

check-generated-fstar: verify-fstar
	git diff --exit-code -- proofs/fstar/extraction
	@untracked="$$(git ls-files --others --exclude-standard -- \
		proofs/fstar/extraction)"; \
		if [[ -n "$$untracked" ]]; then \
			echo 'untracked generated F* proof artifacts:' >&2; \
			printf '%s\n' "$$untracked" >&2; \
			exit 1; \
		fi

check-generated-lean: verify-lean
	git diff --exit-code -- $(LEAN_GENERATED_PATHS)
	@untracked="$$(git ls-files --others --exclude-standard -- \
		$(LEAN_GENERATED_PATHS))"; \
	if [[ -n "$$untracked" ]]; then \
		echo 'untracked generated Lean proof artifacts:' >&2; \
		printf '%s\n' "$$untracked" >&2; \
		exit 1; \
	fi

$(PROVERIF_GENERATED_TARGETS): check-generated-proverif-%: verify-proverif-%
	git diff --exit-code -- proofs/pro-verif/extraction
	@untracked="$$(git ls-files --others --exclude-standard -- \
		proofs/pro-verif/extraction)"; \
		if [[ -n "$$untracked" ]]; then \
			echo 'untracked generated ProVerif proof artifacts:' >&2; \
			printf '%s\n' "$$untracked" >&2; \
			exit 1; \
		fi

# Run this after committing generated output to ensure extraction is stable.
check-generated: verify
	git diff --exit-code -- proofs/fstar/extraction proofs/pro-verif/extraction \
		$(LEAN_GENERATED_PATHS)
	@untracked="$$(git ls-files --others --exclude-standard -- \
		proofs/fstar/extraction proofs/pro-verif/extraction \
		$(LEAN_GENERATED_PATHS))"; \
		if [[ -n "$$untracked" ]]; then \
			echo 'untracked generated proof artifacts:' >&2; \
			printf '%s\n' "$$untracked" >&2; \
			exit 1; \
		fi
