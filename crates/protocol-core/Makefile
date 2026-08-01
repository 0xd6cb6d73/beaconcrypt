# SPDX-License-Identifier: 0BSD

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
	+beaconcrypt_protocol_core::ratchet::advance_send_for_peer

.PHONY: verify verify-in-shell extract-fstar check-fstar check-generated

# Enter hax's pinned CI shell, regenerate the extraction, and check it with F*.
verify:
	nix --extra-experimental-features 'nix-command flakes' \
		develop '$(HAX_SHELL)' -c $(MAKE) verify-in-shell

# This target is split out so CI and developers can reuse an existing pinned
# shell without recursively starting Nix.
verify-in-shell: extract-fstar check-fstar

extract-fstar:
	cargo hax into -i '$(HAX_ITEMS)' fstar

check-fstar:
	$(MAKE) -C proofs/fstar/extraction -f ../Makefile verify

# Run this after committing generated output to ensure extraction is stable.
check-generated: verify
	git diff --exit-code -- proofs/fstar/extraction
