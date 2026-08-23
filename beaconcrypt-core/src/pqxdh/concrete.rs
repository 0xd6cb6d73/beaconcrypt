// SPDX-License-Identifier: 0BSD

//! Production binding between proof-visible PQXDH state and concrete ratchet
//! initialization.
//!
//! The deterministic PQXDH protocol selects the exact initial KDF request and
//! retains the role-ordering continuation in an owned phase. The production
//! adapter performs only that request and resumes the phase with its fixed-size
//! response. No function pointer or borrowed continuation is retained by the
//! core state.

use super::{
	BEACON_RATCHETS, BeaconRegistrationCandidate, INITIAL_RATCHET_KDF_OUTPUT_SIZE,
	RATCHET_CHAIN_SIZE, RatchetInitialization, SERVER_RATCHETS, ServerRegistrationCandidate,
	split_initial_ratchet_kdf_output,
};

use crate::ratchet::{ConcreteRatchetKernel, SymmetricRatchetKdfRequest};

/// Owned continuation for one initial symmetric-ratchet KDF request.
///
/// The phase is deliberately neither `Clone` nor `Copy`. It owns the exact
/// core-constructed request and can be resumed only once with an
/// [`InitialRatchetKdfResponse`].
#[must_use = "the initial ratchet KDF request must be performed or the phase explicitly dropped"]
pub struct InitialRatchetKdfPending {
	request: SymmetricRatchetKdfRequest,
	initialization: RatchetInitialization,
}

impl InitialRatchetKdfPending {
	/// The exact fixed-domain request selected by the core.
	pub const fn request(&self) -> &SymmetricRatchetKdfRequest {
		&self.request
	}
}

/// Distinct fixed-size response to an initial symmetric-ratchet KDF request.
///
/// Keeping this separate from subsequent 76-byte ratchet-step responses makes
/// it impossible to resume the wrong phase class by type alone. It is not tied
/// to one particular pending request; provenance remains an interpreter
/// obligation.
#[must_use = "the initial ratchet KDF response must resume its pending phase"]
#[cfg_attr(not(hax_compilation), derive(zeroize::Zeroize, zeroize::ZeroizeOnDrop))]
pub struct InitialRatchetKdfResponse {
	bytes: [u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE],
}

impl InitialRatchetKdfResponse {
	pub const fn from_bytes(bytes: [u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE]) -> Self {
		Self { bytes }
	}

	pub const fn as_bytes(&self) -> &[u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE] {
		&self.bytes
	}
}

/// Start one initial-chain derivation for an explicit role-ordering plan.
///
/// The root is copied into the private fixed-domain request, so the returned
/// phase has no borrowed lifetime.
pub fn start_initial_ratchet_kdf(
	root: &[u8; RATCHET_CHAIN_SIZE],
	initialization: RatchetInitialization,
) -> InitialRatchetKdfPending {
	InitialRatchetKdfPending {
		request: SymmetricRatchetKdfRequest::new(*root),
		initialization,
	}
}

/// Resume one initial-chain derivation and construct its role-ordered kernel.
///
/// Input selection, output size, fixed-width partitioning, and send/receive
/// ordering remain owned by the core. The adapter supplies only the opaque
/// fixed-size primitive response.
pub fn resume_initial_ratchet_kdf(
	pending: InitialRatchetKdfPending,
	response: InitialRatchetKdfResponse,
) -> ConcreteRatchetKernel {
	let chains = split_initial_ratchet_kdf_output(response.as_bytes(), pending.initialization);
	let (send_chain, receive_chain) = chains.into_parts();

	ConcreteRatchetKernel::new(send_chain, receive_chain)
}

/// Start the beacon role's complementary initial-chain derivation.
pub fn start_beacon_ratchet_kdf(root: &[u8; RATCHET_CHAIN_SIZE]) -> InitialRatchetKdfPending {
	start_initial_ratchet_kdf(root, BEACON_RATCHETS)
}

/// Start the server role's complementary initial-chain derivation.
pub fn start_server_ratchet_kdf(root: &[u8; RATCHET_CHAIN_SIZE]) -> InitialRatchetKdfPending {
	start_initial_ratchet_kdf(root, SERVER_RATCHETS)
}

/// Bind an authenticated beacon registration candidate to the role selected
/// by its proof-visible typestate.
pub fn start_beacon_candidate_ratchet_kdf(
	candidate: &BeaconRegistrationCandidate,
	root: &[u8; RATCHET_CHAIN_SIZE],
) -> InitialRatchetKdfPending {
	start_initial_ratchet_kdf(root, candidate.ratchet_initialization())
}

/// Bind an accepted server registration candidate to the role selected by its
/// proof-visible typestate.
pub fn start_server_candidate_ratchet_kdf(
	candidate: &ServerRegistrationCandidate,
	root: &[u8; RATCHET_CHAIN_SIZE],
) -> InitialRatchetKdfPending {
	start_initial_ratchet_kdf(root, candidate.ratchet_initialization())
}
