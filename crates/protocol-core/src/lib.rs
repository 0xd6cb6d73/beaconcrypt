// SPDX-License-Identifier: 0BSD

#![no_std]
#![forbid(unsafe_code)]

pub mod commitment;
pub mod pqxdh;
pub mod ratchet;

pub use ratchet::{
	PeerRatchetState, PeerSendAdvance, RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetRestore,
	RatchetState, ReceiveAdvance, ReceiveDisposition, ReceiveFinish, ReceiveFinishWithRemoval,
	ReceivePlan, ReceiveRemoval, ReceiveRestoreStep, SendAdvance, SendFinish, SendKey,
	advance_receive, advance_send, advance_send_for_peer, finish_receive,
	finish_receive_with_removal, finish_restore, finish_send, lookup_receive_key,
	plan_receive_until, replace_ratchet_for_peer, restore_receive_key,
	restore_receive_key_with_slot, start_restore,
};
