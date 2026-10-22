// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::ratchet::{
	ConcreteRatchetKernel, RatchetChain, RatchetKdfResponse, ReceiveEffect, begin_receive,
};
use beaconcrypt_core::record::{
	OpenAfterCommitment, OpenCommitment, OpenFrameContext, OpenStart, begin_open, finish_frame_read,
};

fn kernel() -> ConcreteRatchetKernel {
	ConcreteRatchetKernel::new(
		RatchetChain::from_bytes([7; 32]),
		RatchetChain::from_bytes([9; 32]),
	)
}

fn prepare<'a>(
	kernel: ConcreteRatchetKernel,
	sequence: u64,
	payload: &'a [u8],
	ad: &'a [u8; 281],
) -> OpenCommitment<'a> {
	let context = OpenFrameContext::from_frame(payload, ad, 0x0807_0605_0403_0201).unwrap();
	let mut effect = begin_receive(kernel, sequence, context);
	loop {
		effect = match effect {
			ReceiveEffect::ReceiveKdfRequested(pending) => {
				let value = pending.request().input()[0].wrapping_add(1);
				pending.resume(RatchetKdfResponse::from_bytes([value; 76]))
			}
			ReceiveEffect::ReceiveOpenRequested(opening) => match begin_open(opening) {
				OpenStart::OpenCommitmentRequested(pending) => return pending,
				OpenStart::OpenRejected(_) => panic!("valid selected opening rejected"),
			},
			ReceiveEffect::ReceiveRejected { .. } => panic!("valid receive rejected"),
		};
	}
}

fn state(kernel: &ConcreteRatchetKernel) -> impl Eq + std::fmt::Debug + use<> {
	let entries: Vec<_> = (0..51)
		.map(|slot| {
			kernel.receive_entry_at(slot).map(|(seq, material)| {
				(
					seq,
					*material.key().as_bytes(),
					*material.nonce().as_bytes(),
				)
			})
		})
		.collect();
	(
		kernel.send_sequence(),
		kernel.receive_sequence(),
		kernel.receive_cache_len(),
		*kernel.send_chain().as_bytes(),
		*kernel.receive_chain().as_bytes(),
		entries,
	)
}

#[test]
fn complete_reader_and_empty_body_boundaries_remain_strict() {
	assert_eq!(finish_frame_read(&[], 7), Some(7));
	assert_eq!(finish_frame_read(&[0], 7), None);
	let payload = [0; 81];
	let ad = [3; 281];
	for length in 0..=80 {
		assert!(OpenFrameContext::from_frame(&payload[..length], &ad, 2).is_none());
	}
	assert!(OpenFrameContext::from_frame(&payload, &ad, 2).is_some());
}

#[test]
fn selected_request_retains_actual_payload_material_and_plaintext_metadata() {
	let payload = core::array::from_fn::<_, 100, _>(|i| i as u8);
	let ad = [0xA3; 281];
	let pending = prepare(kernel(), 3, &payload, &ad);
	let transcript = pending.transcript().as_bytes();
	assert_eq!(&transcript[..32], &[12; 32]);
	assert_eq!(&transcript[32..44], &[12; 12]);
	assert_eq!(&transcript[44..325], &ad);
	assert_eq!(&transcript[325..341], &payload[20..36]);
	assert_eq!(&transcript[341..349], &3u64.to_le_bytes());
	assert_eq!(&transcript[349..], &0x0807_0605_0403_0201u64.to_le_bytes());
	assert_eq!(pending.supplied_commitment(), &payload[36..]);
	let OpenAfterCommitment::OpenAeadRequested(opening) = pending.resume(true) else {
		panic!("matching commitment rejected");
	};
	let request = opening.request().unwrap();
	assert_eq!(request.ciphertext.as_ptr(), payload.as_ptr());
	assert_eq!(request.ciphertext, &payload[..36]);
	assert_eq!(request.associated_data.as_ptr(), ad.as_ptr());
	assert_eq!(request.key, &[12; 32]);
	assert_eq!(request.nonce, &[12; 12]);
	let (kernel, opened) = opening.finish(Some([42, 43]));
	let opened = opened.unwrap();
	assert_eq!(opened.plaintext, [42, 43]);
	assert_eq!(opened.seq, 3);
	assert_eq!(opened.key_id, 0x0807_0605_0403_0201);
	assert_eq!(kernel.receive_sequence(), 3);
	assert_eq!(kernel.receive_cache_len(), 2);
}

#[test]
fn hash_and_aead_rejection_preserve_future_and_cached_state() {
	let payload = [0xC5; 81];
	let ad = [0xA3; 281];
	let initial = kernel();
	let before = state(&initial);
	let OpenAfterCommitment::OpenCommitmentRejected(initial) =
		prepare(initial, 3, &payload, &ad).resume(false)
	else {
		panic!("failed commitment exposed an AEAD request");
	};
	assert_eq!(state(&initial), before);
	let OpenAfterCommitment::OpenAeadRequested(opening) =
		prepare(initial, 3, &payload, &ad).resume(true)
	else {
		panic!()
	};
	let (initial, result) = opening.finish::<()>(None);
	assert!(result.is_none());
	assert_eq!(state(&initial), before);
	let OpenAfterCommitment::OpenAeadRequested(opening) =
		prepare(initial, 3, &payload, &ad).resume(true)
	else {
		panic!()
	};
	let (cached, _) = opening.finish(Some(()));
	let before = state(&cached);
	let OpenAfterCommitment::OpenCommitmentRejected(cached) =
		prepare(cached, 1, &payload, &ad).resume(false)
	else {
		panic!()
	};
	assert_eq!(state(&cached), before);
	let OpenAfterCommitment::OpenAeadRequested(opening) =
		prepare(cached, 1, &payload, &ad).resume(true)
	else {
		panic!()
	};
	let (cached, result) = opening.finish::<()>(None);
	assert!(result.is_none());
	assert_eq!(state(&cached), before);
	let OpenAfterCommitment::OpenAeadRequested(opening) =
		prepare(cached, 1, &payload, &ad).resume(true)
	else {
		panic!()
	};
	let (cached, result) = opening.finish(Some(()));
	assert_eq!(result.unwrap().seq, 1);
	assert_eq!(cached.receive_sequence(), 3);
	assert_eq!(cached.receive_cache_len(), 1);
	assert_eq!(cached.receive_entry_at(0).unwrap().0, 2);
	assert!(cached.receive_entry_at(1).is_none());
}
