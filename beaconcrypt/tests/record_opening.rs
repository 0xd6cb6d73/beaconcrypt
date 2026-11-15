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
	ad: &[u8; 151],
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
	let ad = [3; 151];
	for length in 0..=80 {
		assert!(OpenFrameContext::from_frame(&payload[..length], &ad, 2).is_none());
	}
	assert!(OpenFrameContext::from_frame(&payload, &ad, 2).is_some());
}

#[test]
fn selected_request_retains_actual_payload_material_and_plaintext_metadata() {
	let payload = core::array::from_fn::<_, 100, _>(|i| i as u8);
	let mut ad = [0xA3; 151];
	let retained_ad = ad;
	let pending = prepare(kernel(), 3, &payload, &ad);
	ad.fill(0xB4);
	let transcript = pending.transcript().as_bytes();
	assert_eq!(&transcript[..32], &[12; 32]);
	assert_eq!(&transcript[32..44], &[12; 12]);
	assert_eq!(&transcript[44..195], &retained_ad);
	assert_eq!(&transcript[195..211], &payload[20..36]);
	assert_eq!(&transcript[211..219], &3u64.to_le_bytes());
	assert_eq!(&transcript[219..], &0x0807_0605_0403_0201u64.to_le_bytes());
	assert_eq!(pending.supplied_commitment(), &payload[36..]);
	let OpenAfterCommitment::OpenAeadRequested(opening) = pending.resume(true) else {
		panic!("matching commitment rejected");
	};
	let request = opening.request().unwrap();
	assert_eq!(request.ciphertext.as_ptr(), payload.as_ptr());
	assert_eq!(request.ciphertext, &payload[..36]);
	assert_eq!(request.associated_data, &retained_ad);
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
	let ad = [0xA3; 151];
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

#[test]
fn complete_session_ad_binds_both_primitives_under_identical_key_and_nonce() {
	use beaconcrypt_core::authentication::assemble_associated_data;
	use beaconcrypt_crypto::{crypto_aead::chacha20poly1305_ietf as aead, crypto_generichash};
	let first = assemble_associated_data(&[1; 64]);
	let second = assemble_associated_data(&[2; 64]);
	let key = aead::Key::from_bytes(&[10; 32]).unwrap();
	let nonce = aead::Nonce::from_bytes(&[10; 12]).unwrap();
	let (mut payload, tag) =
		aead::encrypt_detached(b"same plaintext", Some(&first), &nonce, &key).unwrap();
	payload.extend_from_slice(&tag);
	payload.extend_from_slice(&[0; 64]);
	let pending = prepare(kernel(), 1, &payload, &first);
	let expected =
		crypto_generichash::generichash(pending.transcript().as_bytes(), None, 64).unwrap();
	drop(pending);
	let end = payload.len() - 64;
	payload[end..].copy_from_slice(&expected);

	let before = state(&kernel());
	let pending = prepare(kernel(), 1, &payload, &second);
	let changed =
		crypto_generichash::generichash(pending.transcript().as_bytes(), None, 64).unwrap();
	assert_ne!(changed, expected);
	let OpenAfterCommitment::OpenCommitmentRejected(rejected) = pending.resume(changed == expected)
	else {
		panic!("different session AD passed CTX");
	};
	assert_eq!(state(&rejected), before);

	// Supply a correctly recomputed CTX for the second AD so the real AEAD check is reached.
	payload[end..].copy_from_slice(&changed);
	let pending = prepare(rejected, 1, &payload, &second);
	assert_eq!(pending.supplied_commitment(), changed.as_slice());
	let OpenAfterCommitment::OpenAeadRequested(opening) = pending.resume(true) else {
		panic!()
	};
	let request = opening.request().unwrap();
	assert_eq!(request.associated_data, &second);
	let plaintext = aead::decrypt(
		request.ciphertext,
		Some(request.associated_data),
		&nonce,
		&key,
	)
	.ok();
	assert!(plaintext.is_none());
	let (rejected, result) = opening.finish(plaintext);
	assert!(result.is_none());
	assert_eq!(state(&rejected), before);

	payload[end..].copy_from_slice(&expected);
	let OpenAfterCommitment::OpenAeadRequested(opening) =
		prepare(rejected, 1, &payload, &first).resume(true)
	else {
		panic!()
	};
	let request = opening.request().unwrap();
	let plaintext = aead::decrypt(
		request.ciphertext,
		Some(request.associated_data),
		&nonce,
		&key,
	)
	.ok();
	let (_, result) = opening.finish(plaintext);
	assert_eq!(result.unwrap().plaintext, b"same plaintext");
}
