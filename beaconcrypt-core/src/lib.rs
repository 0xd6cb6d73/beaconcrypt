// SPDX-License-Identifier: 0BSD

#![no_std]
#![forbid(unsafe_code)]

pub mod commitment;
pub mod constants;
pub mod pqxdh;
pub mod ratchet;

pub use ratchet::{
	CachedReceiveKey, ConcreteRatchetKernel, ConcreteRatchetRestore, PeerRatchetState,
	PeerSendAdvance, RATCHET_CHAIN_SIZE, RATCHET_KDF_OUTPUT_SIZE, RATCHET_MAX_GAP,
	RECEIVE_CACHE_CAPACITY, RatchetChain, RatchetKdfOutput, RatchetKdfResponse, RatchetKey,
	RatchetMaterial, RatchetNonce, RatchetRestore, RatchetState, RatchetStep, ReceiveAdvance,
	ReceiveDisposition, ReceiveEffect, ReceiveFinish, ReceiveFinishWithRemoval, ReceiveKdf,
	ReceiveOpen, ReceivePlan, ReceiveRemoval, ReceiveRestoreStep, RefinedRatchet,
	RefinedRatchetRestore, SYM_RATCHET_INFO, SYM_RATCHET_INFO_SIZE, SendAdvance, SendFinish,
	SendKdf, SendKey, SendSeal, SendStart, SymmetricRatchetKdfRequest, begin_receive, begin_send,
	concrete_restore_receive_key, finish_concrete_restore, finish_refined_restore, finish_restore,
	refined_restore_receive_key, replace_ratchet_for_peer, restore_receive_key,
	restore_receive_key_with_slot, split_ratchet_kdf_output, start_concrete_restore,
	start_refined_restore, start_restore,
};

#[cfg(any(test, feature = "test-utils"))]
#[doc(hidden)]
pub use ratchet::{ReceiveAdvanceEffect, ReceiveAdvanceKdf, begin_receive_advance};
