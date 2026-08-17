// SPDX-License-Identifier: 0BSD

use super::{
	RATCHET_KDF_OUTPUT_SIZE, RatchetChain, RatchetMaterial, RatchetStep, RefinedRatchet,
	RefinedRatchetRestore, SymmetricRatchetKdfRequest, finish_refined_restore,
	refined_open_and_finish, refined_restore_receive_key, refined_seal_next,
	split_ratchet_kdf_output, start_refined_restore,
};

/// The only primitive capability retained by a concrete ratchet kernel.
pub type RatchetKdfExecutor = fn(&SymmetricRatchetKdfRequest) -> [u8; RATCHET_KDF_OUTPUT_SIZE];

/// A concrete chain binds its fixed-width bytes to the sole KDF executor that
/// is carried through every later step. The fields stay private so callers
/// cannot replace the executor while retaining the same logical kernel.
#[cfg_attr(feature = "proverif", hax_lib::fstar::before("noeq"))]
struct ConcreteRatchetChain {
	chain: RatchetChain,
	kdf: RatchetKdfExecutor,
}

/// Apply the executor bound into `old_chain` to a core-constructed request and
/// carry that same executor into the returned next chain.
fn concrete_ratchet_step(
	old_chain: &ConcreteRatchetChain,
) -> RatchetStep<ConcreteRatchetChain, RatchetMaterial> {
	let stepped = derive_ratchet_step(&old_chain.chain, old_chain.kdf);
	RatchetStep {
		chain: ConcreteRatchetChain {
			chain: stepped.chain,
			kdf: old_chain.kdf,
		},
		material: stepped.material,
	}
}

/// Production-specialized ratchet kernel.
///
/// Both directional chains carry the same private KDF executor, and every
/// public transition below selects `concrete_ratchet_step` internally. This
/// removes the generic step callback from the production-facing lifecycle.
#[cfg_attr(feature = "proverif", hax_lib::fstar::before("noeq"))]
pub struct ConcreteRatchetKernel {
	refined: RefinedRatchet<ConcreteRatchetChain, ConcreteRatchetChain, RatchetMaterial>,
}

impl ConcreteRatchetKernel {
	/// Construct a fresh concrete kernel and bind one KDF executor for its lifetime.
	pub fn new(
		send_chain: RatchetChain,
		receive_chain: RatchetChain,
		kdf: RatchetKdfExecutor,
	) -> Self {
		Self::from_counters(0, 0, send_chain, receive_chain, kdf)
	}

	/// Construct a concrete kernel at checked persistence counters.
	pub fn from_counters(
		send_sequence: u64,
		receive_sequence: u64,
		send_chain: RatchetChain,
		receive_chain: RatchetChain,
		kdf: RatchetKdfExecutor,
	) -> Self {
		Self {
			refined: RefinedRatchet::from_counters(
				send_sequence,
				receive_sequence,
				ConcreteRatchetChain {
					chain: send_chain,
					kdf,
				},
				ConcreteRatchetChain {
					chain: receive_chain,
					kdf,
				},
			),
		}
	}

	pub const fn send_sequence(&self) -> u64 {
		self.refined.send_sequence()
	}

	pub const fn receive_sequence(&self) -> u64 {
		self.refined.receive_sequence()
	}

	pub const fn receive_cache_len(&self) -> u8 {
		self.refined.receive_cache_len()
	}

	pub const fn send_chain(&self) -> &RatchetChain {
		&self.refined.send_chain.chain
	}

	pub const fn receive_chain(&self) -> &RatchetChain {
		&self.refined.receive_chain.chain
	}

	pub fn receive_entry_at(&self, slot: u8) -> Option<(u64, &RatchetMaterial)> {
		self.refined.receive_entry_at(slot)
	}
}

/// Advance and seal with the core-fixed concrete step and KDF request.
pub fn concrete_seal_next<Context, Output>(
	state: &mut ConcreteRatchetKernel,
	context: &Context,
	seal: fn(&RatchetMaterial, u64, &Context) -> Option<Output>,
) -> Option<Output> {
	refined_seal_next(&mut state.refined, concrete_ratchet_step, context, seal)
}

/// Admit, select, open, and finish with the core-fixed concrete step and KDF request.
pub fn concrete_open_and_finish<Context, Plaintext>(
	state: &mut ConcreteRatchetKernel,
	target: u64,
	context: &Context,
	open: fn(&RatchetMaterial, u64, &Context) -> Option<Plaintext>,
) -> Option<Plaintext> {
	refined_open_and_finish(
		&mut state.refined,
		target,
		concrete_ratchet_step,
		context,
		open,
	)
}

/// Checked restoration builder that binds one concrete KDF executor to both
/// directional chains before any restored material can be published.
#[cfg_attr(feature = "proverif", hax_lib::fstar::before("noeq"))]
pub struct ConcreteRatchetRestore {
	refined: RefinedRatchetRestore<ConcreteRatchetChain, ConcreteRatchetChain, RatchetMaterial>,
}

pub fn start_concrete_restore(
	send_sequence: u64,
	receive_sequence: u64,
	send_chain: RatchetChain,
	receive_chain: RatchetChain,
	kdf: RatchetKdfExecutor,
) -> ConcreteRatchetRestore {
	ConcreteRatchetRestore {
		refined: start_refined_restore(
			send_sequence,
			receive_sequence,
			ConcreteRatchetChain {
				chain: send_chain,
				kdf,
			},
			ConcreteRatchetChain {
				chain: receive_chain,
				kdf,
			},
		),
	}
}

pub fn concrete_restore_receive_key(
	restore: &mut ConcreteRatchetRestore,
	sequence: u64,
	material: RatchetMaterial,
) -> bool {
	refined_restore_receive_key(&mut restore.refined, sequence, material)
}

pub fn finish_concrete_restore(restore: ConcreteRatchetRestore) -> ConcreteRatchetKernel {
	ConcreteRatchetKernel {
		refined: finish_refined_restore(restore.refined),
	}
}

/// Apply the sole opaque ratchet primitive to the exact old chain and interpret its fixed output.
///
/// The primitive's complete production-facing type is `old 32-byte chain -> 76-byte output`.
/// Label selection and HKDF details are private to that domain-specific primitive.
/// Input selection, output size, partitioning, and fixed-width construction are owned here.
pub fn derive_ratchet_step(
	old_chain: &RatchetChain,
	kdf: RatchetKdfExecutor,
) -> RatchetStep<RatchetChain, RatchetMaterial> {
	let request = SymmetricRatchetKdfRequest::new(*old_chain.as_bytes());
	let output = kdf(&request);
	let output = split_ratchet_kdf_output(&output);

	RatchetStep {
		chain: output.next_chain,
		material: RatchetMaterial {
			key: output.key,
			nonce: output.nonce,
		},
	}
}

/// Imperatively advance and retain every derived receive key for test fixture
/// construction. Production receive paths must use [`concrete_open_and_finish`].
#[cfg(any(test, feature = "test-utils"))]
pub fn concrete_advance_receive_until(
	state: &mut ConcreteRatchetKernel,
	target: u64,
) -> Option<u64> {
	use super::refined_advance_receive_until;

	refined_advance_receive_until(&mut state.refined, target, concrete_ratchet_step)
}
