// SPDX-License-Identifier: 0BSD

//! First-order production ratchet effects.
//!
//! The core owns each affine continuation and emits exact KDF, seal, and open
//! requests through borrowed accessors. The production adapter interprets one
//! request at a time and resumes the continuation with a fixed-width reply.

// Pinned Aeneas does not translate the `Try::branch` emitted by `?` reliably.
#![allow(clippy::question_mark)]

use super::control::{
	RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetState, SendKey, advance_receive,
	advance_receive_target, advance_send, finish_send, plan_receive_until,
};
#[cfg(any(test, feature = "test-utils"))]
use super::refined::publish_future_receive_slots;
use super::refined::{
	CachedReceiveKey, PendingReceive, PreparedReceive, RefinedRatchet, RefinedRatchetRestore,
	empty_material_slots, finish_refined_restore, pending_receive_is_valid, prepare_cached_receive,
	publish_cached_receive, publish_future_receive, refined_receive_slots_are_empty,
	refined_restore_receive_key, start_refined_restore,
};
use super::{
	RATCHET_KDF_OUTPUT_SIZE, RatchetChain, RatchetKdfResponse, RatchetMaterial, RatchetStep,
	SymmetricRatchetKdfRequest, split_ratchet_kdf_output,
};

/// Production-specialized ratchet state.
///
/// Cryptographic executors are deliberately not stored in this value. Every
/// transition instead emits a first-order request owned by an affine
/// continuation.
pub struct ConcreteRatchetKernel {
	refined: RefinedRatchet<RatchetChain, RatchetChain, RatchetMaterial>,
}

impl ConcreteRatchetKernel {
	pub fn new(send_chain: RatchetChain, receive_chain: RatchetChain) -> Self {
		Self::from_counters(0, 0, send_chain, receive_chain)
	}

	pub fn from_counters(
		send_sequence: u64,
		receive_sequence: u64,
		send_chain: RatchetChain,
		receive_chain: RatchetChain,
	) -> Self {
		Self {
			refined: RefinedRatchet::from_counters(
				send_sequence,
				receive_sequence,
				send_chain,
				receive_chain,
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
		self.refined.send_chain()
	}

	pub const fn receive_chain(&self) -> &RatchetChain {
		self.refined.receive_chain()
	}

	pub fn receive_entry_at(&self, slot: u8) -> Option<(u64, &RatchetMaterial)> {
		self.refined.receive_entry_at(slot)
	}
}

/// Interpret one fixed-width KDF reply using the core-owned byte partition.
fn ratchet_step_from_response(
	response: RatchetKdfResponse,
) -> RatchetStep<RatchetChain, RatchetMaterial> {
	let output = split_ratchet_kdf_output(response.as_bytes());
	RatchetStep {
		chain: output.next_chain,
		material: RatchetMaterial {
			key: output.key,
			nonce: output.nonce,
		},
	}
}

/// First phase of an owned send transaction.
#[must_use]
#[allow(clippy::large_enum_variant)]
pub enum SendStart<Context> {
	/// The send counter is exhausted. The returned kernel is unchanged.
	SendExhausted {
		kernel: ConcreteRatchetKernel,
		context: Context,
	},
	/// Execute the exact KDF request and resume its continuation.
	SendKdfRequested(SendKdf<Context>),
}

/// Affine continuation waiting for one symmetric-ratchet KDF response.
#[must_use]
pub struct SendKdf<Context> {
	entry: ConcreteRatchetKernel,
	context: Context,
	committed_control: RatchetState,
	logical: SendKey,
	sequence: u64,
	request: SymmetricRatchetKdfRequest,
}

/// Affine send capability containing the exact sequence and material to seal.
#[must_use]
pub struct SendSeal<Context> {
	advanced: ConcreteRatchetKernel,
	context: Context,
	logical: SendKey,
	sequence: u64,
	material: RatchetMaterial,
}

/// Allocate one send sequence and emit its exact chain KDF request.
pub fn begin_send<Context>(kernel: ConcreteRatchetKernel, context: Context) -> SendStart<Context> {
	let advanced = advance_send(kernel.refined.control);
	let sequence = match advanced.sequence {
		Some(sequence) => sequence,
		None => {
			return SendStart::SendExhausted { kernel, context };
		}
	};
	if !(advanced.key.sequence() == Some(sequence)) || !(advanced.state.send_sequence() == sequence)
	{
		return SendStart::SendExhausted { kernel, context };
	}

	let request = SymmetricRatchetKdfRequest::new(*kernel.refined.send_chain.as_bytes());
	SendStart::SendKdfRequested(SendKdf {
		entry: kernel,
		context,
		committed_control: advanced.state,
		logical: advanced.key,
		sequence,
		request,
	})
}

impl<Context> SendKdf<Context> {
	pub const fn request(&self) -> &SymmetricRatchetKdfRequest {
		&self.request
	}

	/// Cancel before interpreting a KDF response. The entry kernel is exact.
	pub fn cancel(self) -> (ConcreteRatchetKernel, Context) {
		(self.entry, self.context)
	}

	/// Interpret the KDF response and publish the new send chain and counter.
	///
	/// The response type fixes the phase class and width; the interpreter remains
	/// responsible for deriving it from this continuation's exact `request`.
	pub fn resume(mut self, response: RatchetKdfResponse) -> SendSeal<Context> {
		let stepped = ratchet_step_from_response(response);
		self.entry.refined.send_chain = stepped.chain;
		self.entry.refined.control = self.committed_control;
		SendSeal {
			advanced: self.entry,
			context: self.context,
			logical: self.logical,
			sequence: self.sequence,
			material: stepped.material,
		}
	}
}

impl<Context> SendSeal<Context> {
	pub const fn sequence(&self) -> u64 {
		self.sequence
	}

	/// Borrow the material selected by this one-use state capability.
	///
	/// Safe Rust prevents producing two successor kernels from this phase, but a
	/// caller can copy bytes through this borrow. A faithful interpreter must use
	/// the material for exactly this seal attempt and retain no copy.
	pub const fn material(&self) -> &RatchetMaterial {
		&self.material
	}

	pub const fn context(&self) -> &Context {
		&self.context
	}

	/// Consume the one-use send capability after either seal outcome.
	///
	/// The returned kernel remains advanced when `sealed` is `None`.
	pub fn finish<Output>(self, sealed: Option<Output>) -> (ConcreteRatchetKernel, Option<Output>) {
		let _ = finish_send(self.logical);
		(self.advanced, sealed)
	}
}

/// One phase of an owned receive transaction.
#[must_use]
#[allow(clippy::large_enum_variant)]
pub enum ReceiveEffect<Context> {
	/// Admission or an internal invariant rejected the operation. The returned
	/// kernel is the exact entry value.
	ReceiveRejected {
		kernel: ConcreteRatchetKernel,
		context: Context,
	},
	/// Execute one exact KDF request and resume its continuation.
	ReceiveKdfRequested(ReceiveKdf<Context>),
	/// Attempt to open with the exact selected sequence and material.
	ReceiveOpenRequested(ReceiveOpen<Context>),
}

/// Affine future-receive continuation waiting for exactly one KDF response.
#[must_use]
pub struct ReceiveKdf<Context> {
	entry: ConcreteRatchetKernel,
	context: Context,
	target: u64,
	working_control: RatchetState,
	staged_slots: [Option<CachedReceiveKey<RatchetMaterial>>; RECEIVE_CACHE_CAPACITY],
	first_slot: u8,
	skipped: u8,
	remaining: u8,
	request: SymmetricRatchetKdfRequest,
}

/// Affine receive capability containing a prevalidated cached or future
/// publication and the exact material to open.
#[must_use]
pub struct ReceiveOpen<Context> {
	entry: ConcreteRatchetKernel,
	context: Context,
	prepared: PreparedReceive<RatchetChain, RatchetMaterial>,
}

fn receive_rejected<Context>(
	kernel: ConcreteRatchetKernel,
	context: Context,
) -> ReceiveEffect<Context> {
	ReceiveEffect::ReceiveRejected { kernel, context }
}

/// Admit a target without mutating its entry kernel.
pub fn begin_receive<Context>(
	kernel: ConcreteRatchetKernel,
	target: u64,
	context: Context,
) -> ReceiveEffect<Context> {
	let plan = plan_receive_until(kernel.refined.control, target);
	let sequence = match plan.sequence {
		Some(sequence) => sequence,
		None => return receive_rejected(kernel, context),
	};

	if plan.derivations == 0 {
		let prepared = match prepare_cached_receive(&kernel.refined, sequence) {
			Some(prepared) => prepared,
			None => return receive_rejected(kernel, context),
		};
		return ReceiveEffect::ReceiveOpenRequested(ReceiveOpen {
			entry: kernel,
			context,
			prepared: PreparedReceive::PreparedReceiveCachedCase(prepared),
		});
	}

	let skipped = plan.derivations - 1;
	if skipped > RATCHET_MAX_GAP {
		return receive_rejected(kernel, context);
	}
	let remaining = plan.derivations as u8;
	let first_slot = kernel.refined.control.receive_cache_len();
	if !refined_receive_slots_are_empty(&kernel.refined, first_slot, skipped as u8) {
		return receive_rejected(kernel, context);
	}

	let request = SymmetricRatchetKdfRequest::new(*kernel.refined.receive_chain.as_bytes());
	let working_control = kernel.refined.control;
	ReceiveEffect::ReceiveKdfRequested(ReceiveKdf {
		entry: kernel,
		context,
		target: sequence,
		working_control,
		staged_slots: empty_material_slots(),
		first_slot,
		skipped: 0,
		remaining,
		request,
	})
}

impl<Context> ReceiveKdf<Context> {
	pub const fn request(&self) -> &SymmetricRatchetKdfRequest {
		&self.request
	}

	/// Cancel any private derivation prefix and recover the exact entry kernel.
	pub fn cancel(self) -> (ConcreteRatchetKernel, Context) {
		(self.entry, self.context)
	}

	/// Interpret exactly one KDF response. A non-final response produces the next
	/// request; the final response produces the sole open capability.
	///
	/// The response type fixes the phase class and width; the interpreter remains
	/// responsible for deriving it from this continuation's exact `request`.
	pub fn resume(mut self, response: RatchetKdfResponse) -> ReceiveEffect<Context> {
		if self.remaining == 0 {
			return receive_rejected(self.entry, self.context);
		}

		if self.remaining == 1 {
			let advanced = advance_receive_target(self.working_control);
			let sequence = match advanced.sequence {
				Some(sequence) => sequence,
				None => return receive_rejected(self.entry, self.context),
			};
			if !(sequence == self.target) {
				return receive_rejected(self.entry, self.context);
			}

			let stepped = ratchet_step_from_response(response);
			let pending = PendingReceive {
				committed_control: advanced.state,
				final_receive_chain: stepped.chain,
				staged_slots: self.staged_slots,
				target_sequence: sequence,
				target_material: stepped.material,
				first_slot: self.first_slot,
				skipped: self.skipped,
			};
			if !pending_receive_is_valid(&self.entry.refined, &pending, self.target) {
				return receive_rejected(self.entry, self.context);
			}

			return ReceiveEffect::ReceiveOpenRequested(ReceiveOpen {
				entry: self.entry,
				context: self.context,
				prepared: PreparedReceive::PreparedReceiveFutureCase(pending),
			});
		}

		let advanced = advance_receive(self.working_control);
		let sequence = match advanced.sequence {
			Some(sequence) => sequence,
			None => return receive_rejected(self.entry, self.context),
		};
		let slot = match advanced.slot {
			Some(slot) => slot,
			None => return receive_rejected(self.entry, self.context),
		};
		let slot_index = slot as usize;
		if !(advanced.state.receive_key_at(slot) == Some(sequence))
			|| slot_index >= RECEIVE_CACHE_CAPACITY
			|| !(slot_index == self.first_slot as usize + self.skipped as usize)
			|| self.staged_slots[slot_index].is_some()
		{
			return receive_rejected(self.entry, self.context);
		}

		if sequence >= self.target {
			return receive_rejected(self.entry, self.context);
		}
		let stepped = ratchet_step_from_response(response);
		self.staged_slots[slot_index] = Some(CachedReceiveKey {
			sequence,
			material: stepped.material,
		});
		self.working_control = advanced.state;
		self.skipped += 1;
		self.remaining -= 1;
		self.request = SymmetricRatchetKdfRequest::new(*stepped.chain.as_bytes());
		ReceiveEffect::ReceiveKdfRequested(self)
	}
}

impl<Context> ReceiveOpen<Context> {
	pub const fn sequence(&self) -> u64 {
		match &self.prepared {
			PreparedReceive::PreparedReceiveCachedCase(prepared) => prepared.sequence,
			PreparedReceive::PreparedReceiveFutureCase(pending) => pending.target_sequence,
		}
	}

	/// Borrow the selected material without moving a cached key out of the entry
	/// kernel. `None` is only a defensive result for an impossible malformed
	/// private continuation. A faithful interpreter uses the borrow only for this
	/// open attempt and retains no copy.
	pub fn material(&self) -> Option<&RatchetMaterial> {
		match &self.prepared {
			PreparedReceive::PreparedReceiveCachedCase(prepared) => {
				let slot_index = prepared.target_slot as usize;
				if slot_index >= RECEIVE_CACHE_CAPACITY {
					return None;
				}
				let cached = match self.entry.refined.receive_slots[slot_index].as_ref() {
					Some(cached) => cached,
					None => return None,
				};
				if !(cached.sequence == prepared.sequence) {
					return None;
				}
				Some(&cached.material)
			}
			PreparedReceive::PreparedReceiveFutureCase(pending) => Some(&pending.target_material),
		}
	}

	pub const fn context(&self) -> &Context {
		&self.context
	}

	/// Reject the open attempt and recover the exact entry kernel and context.
	pub fn reject(self) -> (ConcreteRatchetKernel, Context) {
		(self.entry, self.context)
	}

	/// Interpret the open outcome. Failure returns the exact entry kernel;
	/// success atomically publishes the prevalidated cached removal or future
	/// receive delta and returns the supplied plaintext unchanged.
	pub fn finish<Plaintext>(
		self,
		opened: Option<Plaintext>,
	) -> (ConcreteRatchetKernel, Option<Plaintext>) {
		let plaintext = match opened {
			Some(plaintext) => plaintext,
			None => return (self.entry, None),
		};
		let mut entry = self.entry;
		match self.prepared {
			PreparedReceive::PreparedReceiveCachedCase(prepared) => {
				publish_cached_receive(&mut entry.refined, prepared);
			}
			PreparedReceive::PreparedReceiveFutureCase(pending) => {
				publish_future_receive(&mut entry.refined, pending);
			}
		}
		(entry, Some(plaintext))
	}
}

/// Checked restoration builder for a direct-chain concrete kernel.
pub struct ConcreteRatchetRestore {
	refined: RefinedRatchetRestore<RatchetChain, RatchetChain, RatchetMaterial>,
}

pub fn start_concrete_restore(
	send_sequence: u64,
	receive_sequence: u64,
	send_chain: RatchetChain,
	receive_chain: RatchetChain,
) -> ConcreteRatchetRestore {
	ConcreteRatchetRestore {
		refined: start_refined_restore(send_sequence, receive_sequence, send_chain, receive_chain),
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

/// Test-only first-order derivation that retains every derived receive key,
/// including the target, matching the former fixture helper.
#[cfg(any(test, feature = "test-utils"))]
#[must_use]
#[allow(clippy::large_enum_variant)]
pub enum ReceiveAdvanceEffect {
	ReceiveAdvanceRejected(ConcreteRatchetKernel),
	ReceiveAdvanceKdfRequested(ReceiveAdvanceKdf),
	ReceiveAdvanceCompleted {
		kernel: ConcreteRatchetKernel,
		target: u64,
	},
}

#[cfg(any(test, feature = "test-utils"))]
#[must_use]
pub struct ReceiveAdvanceKdf {
	entry: ConcreteRatchetKernel,
	target: u64,
	working_control: RatchetState,
	staged_slots: [Option<CachedReceiveKey<RatchetMaterial>>; RECEIVE_CACHE_CAPACITY],
	first_slot: u8,
	derived: u8,
	remaining: u8,
	request: SymmetricRatchetKdfRequest,
}

#[cfg(any(test, feature = "test-utils"))]
pub fn begin_receive_advance(kernel: ConcreteRatchetKernel, target: u64) -> ReceiveAdvanceEffect {
	let plan = plan_receive_until(kernel.refined.control, target);
	let sequence = match plan.sequence {
		Some(sequence) => sequence,
		None => return ReceiveAdvanceEffect::ReceiveAdvanceRejected(kernel),
	};
	if plan.derivations == 0 {
		return ReceiveAdvanceEffect::ReceiveAdvanceCompleted {
			kernel,
			target: sequence,
		};
	}
	if plan.derivations > RATCHET_MAX_GAP {
		return ReceiveAdvanceEffect::ReceiveAdvanceRejected(kernel);
	}
	let remaining = plan.derivations as u8;
	let first_slot = kernel.refined.control.receive_cache_len();
	if !refined_receive_slots_are_empty(&kernel.refined, first_slot, remaining) {
		return ReceiveAdvanceEffect::ReceiveAdvanceRejected(kernel);
	}
	let request = SymmetricRatchetKdfRequest::new(*kernel.refined.receive_chain.as_bytes());
	let working_control = kernel.refined.control;
	ReceiveAdvanceEffect::ReceiveAdvanceKdfRequested(ReceiveAdvanceKdf {
		entry: kernel,
		target: sequence,
		working_control,
		staged_slots: empty_material_slots(),
		first_slot,
		derived: 0,
		remaining,
		request,
	})
}

#[cfg(any(test, feature = "test-utils"))]
impl ReceiveAdvanceKdf {
	pub const fn request(&self) -> &SymmetricRatchetKdfRequest {
		&self.request
	}

	pub fn cancel(self) -> ConcreteRatchetKernel {
		self.entry
	}

	pub fn resume(mut self, response: RatchetKdfResponse) -> ReceiveAdvanceEffect {
		if self.remaining == 0 {
			return ReceiveAdvanceEffect::ReceiveAdvanceRejected(self.entry);
		}
		let advanced = advance_receive(self.working_control);
		let sequence = match advanced.sequence {
			Some(sequence) => sequence,
			None => return ReceiveAdvanceEffect::ReceiveAdvanceRejected(self.entry),
		};
		let slot = match advanced.slot {
			Some(slot) => slot,
			None => return ReceiveAdvanceEffect::ReceiveAdvanceRejected(self.entry),
		};
		let slot_index = slot as usize;
		if !(advanced.state.receive_key_at(slot) == Some(sequence))
			|| slot_index >= RECEIVE_CACHE_CAPACITY
			|| !(slot_index == self.first_slot as usize + self.derived as usize)
			|| self.staged_slots[slot_index].is_some()
		{
			return ReceiveAdvanceEffect::ReceiveAdvanceRejected(self.entry);
		}

		let stepped = ratchet_step_from_response(response);
		self.staged_slots[slot_index] = Some(CachedReceiveKey {
			sequence,
			material: stepped.material,
		});
		self.working_control = advanced.state;
		self.derived += 1;
		self.remaining -= 1;

		if self.remaining == 0 {
			if !(sequence == self.target) {
				return ReceiveAdvanceEffect::ReceiveAdvanceRejected(self.entry);
			}
			publish_future_receive_slots(
				&mut self.entry.refined,
				&mut self.staged_slots,
				self.first_slot,
				self.derived,
			);
			self.entry.refined.receive_chain = stepped.chain;
			self.entry.refined.control = self.working_control;
			return ReceiveAdvanceEffect::ReceiveAdvanceCompleted {
				kernel: self.entry,
				target: self.target,
			};
		}

		self.request = SymmetricRatchetKdfRequest::new(*stepped.chain.as_bytes());
		ReceiveAdvanceEffect::ReceiveAdvanceKdfRequested(self)
	}
}

const _: () = assert!(RATCHET_KDF_OUTPUT_SIZE == 76);
