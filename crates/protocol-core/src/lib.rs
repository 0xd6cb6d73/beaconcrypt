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
	RefinedRatchet, RefinedRatchetRestore, RefinedSendKey, SendAdvance, SendFinish, SendKey,
	advance_receive, advance_send, advance_send_for_peer, derive_ratchet_step, finish_receive,
	finish_receive_with_removal, finish_refined_restore, finish_restore, finish_send,
	lookup_receive_key, plan_receive_until, refined_advance_receive, refined_advance_receive_until,
	refined_advance_send, refined_finish_receive, refined_finish_send, refined_receive_key,
	refined_restore_receive_key, replace_ratchet_for_peer, restore_receive_key,
	restore_receive_key_with_slot, split_ratchet_kdf_output, start_refined_restore, start_restore,
};
