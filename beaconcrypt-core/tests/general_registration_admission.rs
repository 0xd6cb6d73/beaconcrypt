// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::{
	ConcreteRatchetKernel, RATCHET_KDF_OUTPUT_SIZE, RatchetChain, RatchetKdfResponse,
	ReceiveEffect, begin_receive,
};

fn kernel() -> ConcreteRatchetKernel {
	ConcreteRatchetKernel::new(
		RatchetChain::from_bytes([0; 32]),
		RatchetChain::from_bytes([1; 32]),
	)
}

// Distinct test material makes wrong ordering, skipped-slot publication, and target retention observable.
fn response(step: u8) -> RatchetKdfResponse {
	let mut bytes = [0; RATCHET_KDF_OUTPUT_SIZE];
	bytes[..32].fill(step);
	bytes[32..64].fill(step + 1);
	bytes[64..].fill(step + 128);
	RatchetKdfResponse::from_bytes(bytes)
}

fn initial_receive(target: u64) -> ConcreteRatchetKernel {
	let mut effect = begin_receive(kernel(), target, target);
	for step in 1..=target {
		let ReceiveEffect::ReceiveKdfRequested(request) = effect else {
			panic!("target {target}: missing derivation {step}")
		};
		assert_eq!(request.request().input(), &[step as u8; 32]);
		effect = request.resume(response(step as u8));
	}
	let ReceiveEffect::ReceiveOpenRequested(open) = effect else {
		panic!("target {target}: missing exact target open")
	};
	assert_eq!(open.sequence(), target);
	assert_eq!(open.context(), &target);
	assert_eq!(
		open.material().unwrap().key().as_bytes(),
		&[target as u8; 32]
	);
	assert_eq!(
		open.material().unwrap().nonce().as_bytes(),
		&[target as u8 + 128; 12]
	);
	let (committed, plaintext) = open.finish(Some(target));
	assert_eq!(plaintext, Some(target));
	committed
}

#[test]
fn all_51_initial_targets_have_exact_source_poststate() {
	for target in 1..=51 {
		let committed = initial_receive(target);
		assert_eq!(committed.send_sequence(), 0);
		assert_eq!(committed.send_chain().as_bytes(), &[0; 32]);
		assert_eq!(committed.receive_sequence(), target);
		assert_eq!(
			committed.receive_chain().as_bytes(),
			&[target as u8 + 1; 32]
		);
		assert_eq!(u64::from(committed.receive_cache_len()), target - 1);
		for slot in 0..50 {
			if u64::from(slot) < target - 1 {
				let (sequence, material) = committed.receive_entry_at(slot).unwrap();
				assert_eq!(sequence, u64::from(slot) + 1);
				assert_eq!(material.key().as_bytes(), &[slot + 1; 32]);
				assert_eq!(material.nonce().as_bytes(), &[slot + 129; 12]);
			} else {
				assert!(committed.receive_entry_at(slot).is_none());
			}
		}
	}
}

#[test]
fn zero_and_52_reject_before_any_kdf_or_open() {
	for target in [0, 52] {
		let ReceiveEffect::ReceiveRejected {
			kernel: restored,
			context,
		} = begin_receive(kernel(), target, target)
		else {
			panic!("target {target} admitted")
		};
		assert_eq!(context, target);
		assert_eq!(restored.send_sequence(), 0);
		assert_eq!(restored.receive_sequence(), 0);
		assert_eq!(restored.send_chain().as_bytes(), &[0; 32]);
		assert_eq!(restored.receive_chain().as_bytes(), &[1; 32]);
		assert_eq!(restored.receive_cache_len(), 0);
	}
}

#[test]
fn every_admitted_state_supports_each_cached_target_and_rejects_its_replay() {
	for initial in 2..=51 {
		for target in 1..initial {
			let ReceiveEffect::ReceiveOpenRequested(open) =
				begin_receive(initial_receive(initial), target, ())
			else {
				panic!("cached {target} after {initial} must open without derivation")
			};
			assert_eq!(
				open.material().unwrap().key().as_bytes(),
				&[target as u8; 32]
			);
			let (committed, result) = open.finish(Some(target));
			assert_eq!(result, Some(target));
			assert_eq!(u64::from(committed.receive_cache_len()), initial - 2);
			assert_eq!(committed.receive_sequence(), initial);
			assert_eq!(
				committed.receive_chain().as_bytes(),
				&[initial as u8 + 1; 32]
			);
			for slot in 0..50 {
				if slot < committed.receive_cache_len() {
					let expected = if u64::from(slot) == target - 1 {
						initial - 1
					} else {
						u64::from(slot) + 1
					};
					let (sequence, material) = committed.receive_entry_at(slot).unwrap();
					assert_eq!(sequence, expected);
					assert_eq!(material.key().as_bytes(), &[expected as u8; 32]);
					assert_eq!(material.nonce().as_bytes(), &[expected as u8 + 128; 12]);
				} else {
					assert!(committed.receive_entry_at(slot).is_none());
				}
			}
			assert!(matches!(
				begin_receive(committed, target, ()),
				ReceiveEffect::ReceiveRejected { .. }
			));
		}
	}
}
