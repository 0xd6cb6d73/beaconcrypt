// SPDX-License-Identifier: 0BSD

#![no_std]
#![forbid(unsafe_code)]

pub mod commitment;
pub mod pqxdh;
pub mod ratchet;

pub use ratchet::{
	CachedReceiveKey, PeerRatchetState, PeerSendAdvance, RATCHET_KDF_OUTPUT_SIZE, RATCHET_MAX_GAP,
	RECEIVE_CACHE_CAPACITY, RatchetChain, RatchetKdfOutput, RatchetKey, RatchetMaterial,
	RatchetNonce, RatchetRestore, RatchetState, RatchetStep, ReceiveAdvance, ReceiveDisposition,
	ReceiveFinish, ReceiveFinishWithRemoval, ReceivePlan, ReceiveRemoval, ReceiveRestoreStep,
	RefinedRatchet, RefinedRatchetRestore, SendAdvance, SendFinish, SendKey, derive_ratchet_step,
	finish_refined_restore, finish_restore, refined_open_and_finish, refined_restore_receive_key,
	refined_seal_next, replace_ratchet_for_peer, restore_receive_key,
	restore_receive_key_with_slot, split_ratchet_kdf_output, start_refined_restore, start_restore,
};
