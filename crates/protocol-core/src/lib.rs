// SPDX-License-Identifier: 0BSD

#![no_std]
#![forbid(unsafe_code)]

pub mod pqxdh;
pub mod ratchet;

pub use ratchet::{
	PeerRatchetState, PeerSendAdvance, RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetRestore,
	RatchetState, ReceiveAdvance, ReceiveDisposition, ReceiveFinish, ReceivePlan, SendAdvance,
	SendFinish, SendKey, advance_receive, advance_send, advance_send_for_peer, finish_receive,
	finish_restore, finish_send, plan_receive_until, replace_ratchet_for_peer, restore_receive_key,
	start_restore,
};
