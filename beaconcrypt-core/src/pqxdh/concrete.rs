// SPDX-License-Identifier: 0BSD

//! Production binding between proof-visible PQXDH state and concrete ratchet
//! executors.
//!
//! This module owns function-pointer capabilities and concrete-kernel
//! construction. The deterministic PQXDH protocol state and fixed-width KDF
//! output interpretation remain in the parent module.

use super::{
	BEACON_RATCHETS, BeaconRegistrationCandidate, INITIAL_RATCHET_KDF_OUTPUT_SIZE,
	InitialRatchetChains, RATCHET_CHAIN_SIZE, RatchetInitialization, SERVER_RATCHETS,
	ServerRegistrationCandidate, split_initial_ratchet_kdf_output,
};

use crate::ratchet::{ConcreteRatchetKernel, RatchetKdfExecutor, SymmetricRatchetKdfRequest};

/// Fixed-output executor for expanding one authenticated session root into
/// the two initial directional chain values.
pub type InitialRatchetKdfExecutor =
	fn(&SymmetricRatchetKdfRequest) -> [u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE];

/// Apply the sole opaque initial-chain primitive to the exact session root
/// and order its output.
///
/// The primitive's complete production-facing type is
/// `32-byte root -> 64-byte output`.
///
/// Label selection and HKDF details are private to that domain-specific
/// primitive. Input selection, output size, role ordering, partitioning, and
/// fixed-width construction remain owned by the core.
pub fn derive_initial_ratchet_chains(
	root: &[u8; RATCHET_CHAIN_SIZE],
	initialization: RatchetInitialization,
	kdf: InitialRatchetKdfExecutor,
) -> InitialRatchetChains {
	let request = SymmetricRatchetKdfRequest::new(*root);
	let output = kdf(&request);

	split_initial_ratchet_kdf_output(&output, initialization)
}

/// Construct a concrete kernel directly from one root, one role plan, and the
/// executors for initial and subsequent core-owned KDF requests.
pub fn derive_initial_ratchet_kernel(
	root: &[u8; RATCHET_CHAIN_SIZE],
	initialization: RatchetInitialization,
	initial_kdf: InitialRatchetKdfExecutor,
	ratchet_kdf: RatchetKdfExecutor,
) -> ConcreteRatchetKernel {
	let chains = derive_initial_ratchet_chains(root, initialization, initial_kdf);
	let (send_chain, receive_chain) = chains.into_parts();

	ConcreteRatchetKernel::new(send_chain, receive_chain, ratchet_kdf)
}

/// Construct the beacon role's complementary concrete kernel.
pub fn derive_beacon_ratchet_kernel(
	root: &[u8; RATCHET_CHAIN_SIZE],
	initial_kdf: InitialRatchetKdfExecutor,
	ratchet_kdf: RatchetKdfExecutor,
) -> ConcreteRatchetKernel {
	derive_initial_ratchet_kernel(root, BEACON_RATCHETS, initial_kdf, ratchet_kdf)
}

/// Construct the server role's complementary concrete kernel.
pub fn derive_server_ratchet_kernel(
	root: &[u8; RATCHET_CHAIN_SIZE],
	initial_kdf: InitialRatchetKdfExecutor,
	ratchet_kdf: RatchetKdfExecutor,
) -> ConcreteRatchetKernel {
	derive_initial_ratchet_kernel(root, SERVER_RATCHETS, initial_kdf, ratchet_kdf)
}

/// Bind an authenticated beacon registration candidate to its concrete
/// ratchet kernel.
///
/// Keeping this as a free function, rather than an inherent method on
/// `BeaconRegistrationCandidate`, ensures the proof-visible candidate type
/// has no dependency on executor function pointers or `ConcreteRatchetKernel`.
pub fn derive_beacon_candidate_ratchet_kernel(
	candidate: &BeaconRegistrationCandidate,
	root: &[u8; RATCHET_CHAIN_SIZE],
	initial_kdf: InitialRatchetKdfExecutor,
	ratchet_kdf: RatchetKdfExecutor,
) -> ConcreteRatchetKernel {
	derive_initial_ratchet_kernel(
		root,
		candidate.ratchet_initialization(),
		initial_kdf,
		ratchet_kdf,
	)
}

/// Bind an accepted server registration candidate to its concrete ratchet
/// kernel.
///
/// Keeping this as a free function, rather than an inherent method on
/// `ServerRegistrationCandidate`, ensures the proof-visible candidate type
/// has no dependency on executor function pointers or `ConcreteRatchetKernel`.
pub fn derive_server_candidate_ratchet_kernel(
	candidate: &ServerRegistrationCandidate,
	root: &[u8; RATCHET_CHAIN_SIZE],
	initial_kdf: InitialRatchetKdfExecutor,
	ratchet_kdf: RatchetKdfExecutor,
) -> ConcreteRatchetKernel {
	derive_initial_ratchet_kernel(
		root,
		candidate.ratchet_initialization(),
		initial_kdf,
		ratchet_kdf,
	)
}
