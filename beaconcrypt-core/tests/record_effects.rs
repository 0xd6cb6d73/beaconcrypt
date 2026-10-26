// SPDX-License-Identifier: 0BSD

use beaconcrypt_core as boundary;

use boundary::ratchet::{ConcreteRatchetKernel, RatchetChain, RatchetKdfResponse};
use boundary::record_effects::*;

fn kernel() -> ConcreteRatchetKernel {
	ConcreteRatchetKernel::new(
		RatchetChain::from_bytes([3; 32]),
		RatchetChain::from_bytes([4; 32]),
	)
}

fn response() -> RatchetKdfResponse {
	RatchetKdfResponse::from_bytes(std::array::from_fn(|i| {
		if i < 32 {
			7
		} else if i < 64 {
			8
		} else {
			9
		}
	}))
}

type KernelSnapshot = (u64, u64, [u8; 32], [u8; 32], Vec<(u64, [u8; 32], [u8; 12])>);

fn snapshot(kernel: &ConcreteRatchetKernel) -> KernelSnapshot {
	let entries = (0..kernel.receive_cache_len())
		.map(|slot| {
			let (sequence, material) = kernel.receive_entry_at(slot).unwrap();
			(
				sequence,
				*material.key().as_bytes(),
				*material.nonce().as_bytes(),
			)
		})
		.collect();
	(
		kernel.send_sequence(),
		kernel.receive_sequence(),
		*kernel.send_chain().as_bytes(),
		*kernel.receive_chain().as_bytes(),
		entries,
	)
}

fn send(context: SealFrameContext<'_>) -> SealAead<'_> {
	match begin_record_send(kernel(), context) {
		RecordSendStart::KdfRequested(pending) => {
			assert_eq!(pending.request().input(), &[3; 32]);
			pending.resume(response())
		}
		_ => panic!("valid nonempty send"),
	}
}

fn receive_commitment(effect: RecordReceiveEffect<'_>) -> RecordReceiveCommitment<'_> {
	match effect {
		RecordReceiveEffect::KdfRequested(pending) => {
			receive_commitment(pending.resume(response()))
		}
		RecordReceiveEffect::CommitmentRequested(pending) => pending,
		_ => panic!("valid receive reaches commitment"),
	}
}

fn payload() -> Vec<u8> {
	let mut payload = vec![21];
	payload.extend_from_slice(&[10; 16]);
	payload.extend_from_slice(&[11; 64]);
	payload
}

#[test]
fn exact_seal_operands_ordered_frame_parts_and_source_metadata() {
	let ad = [6; 281];
	let aead = send(SealFrameContext::new(
		b"msg",
		77,
		99,
		&ad,
		RecordEncoding::Frame,
	));
	let request = aead.request();
	assert_eq!(request.key, &[7; 32]);
	assert_eq!(request.nonce, &[9; 12]);
	assert_eq!(request.associated_data, &ad);
	match request.plaintext {
		SealPlaintextRequest::Single(plaintext) => assert_eq!(plaintext, b"msg"),
		_ => panic!("ordinary send requests only the exact application bytes"),
	}
	let commitment = match aead.resume(Some((&[21, 22, 23], [10; 16]))) {
		SealAfterAead::CommitmentRequested(pending) => pending,
		_ => panic!("actual detached result"),
	};
	let mut expected = vec![7; 32];
	expected.extend_from_slice(&[9; 12]);
	expected.extend_from_slice(&ad);
	expected.extend_from_slice(&[10; 16]);
	expected.extend_from_slice(&1u64.to_le_bytes());
	expected.extend_from_slice(&99u64.to_le_bytes());
	assert_eq!(commitment.transcript().as_bytes().as_slice(), expected);
	let writer = match commitment.resume(Some([11; 64])) {
		SealAfterCommitment::WriteRequested(writer) => writer,
		_ => panic!("actual hash result"),
	};
	let encoded = match writer.request() {
		RecordWriteRequest::Frame {
			parts,
			sequence,
			sender,
		} => {
			assert_eq!(sequence, 1);
			assert_eq!(sender, 99);
			assert_eq!(parts, [&[21, 22, 23][..], &[10; 16][..], &[11; 64][..]]);
			parts.concat()
		}
		_ => panic!("ordinary frame encoding"),
	};
	let (kernel, sealed) = writer.finish(Some(encoded.clone()));
	let sealed = sealed.unwrap();
	assert_eq!((sealed.key_id, sealed.seq), (77, 1));
	assert_eq!(sealed.ciphertext, encoded);
	assert_eq!(kernel.send_sequence(), 1);
	assert_eq!(kernel.send_chain().as_bytes(), &[8; 32]);
	assert_eq!(kernel.receive_chain().as_bytes(), &[4; 32]);
}

#[test]
fn registration_owns_its_exact_prefix_and_ad_and_requests_raw_output() {
	let aead = {
		let ad = [6; 281];
		send(SealFrameContext::registration(
			b"app",
			0x0807060504030201,
			99,
			&ad,
		))
	};
	assert_eq!(aead.request().associated_data, &[6; 281]);
	match aead.request().plaintext {
		SealPlaintextRequest::Prefixed {
			prefix,
			application,
		} => {
			assert_eq!(prefix, &[1, 2, 3, 4, 5, 6, 7, 8]);
			assert_eq!(application, b"app");
		}
		_ => panic!("registration requests its retained assigned-ID prefix and application"),
	}
	let commitment = match aead.resume(Some((&[21; 11], [10; 16]))) {
		SealAfterAead::CommitmentRequested(pending) => pending,
		_ => panic!("detached result"),
	};
	let writer = match commitment.resume(Some([11; 64])) {
		SealAfterCommitment::WriteRequested(writer) => writer,
		_ => panic!("hash result"),
	};
	assert!(matches!(writer.request(), RecordWriteRequest::Raw { .. }));
	let (_, sealed) = writer.finish(Some(()));
	assert_eq!(sealed.unwrap().key_id, 0x0807060504030201);
}

#[test]
fn admission_and_cancel_preserve_entry_but_each_later_failure_consumes_send_key() {
	let original = snapshot(&kernel());
	let context = SealFrameContext::new(&[], 77, 99, &[6; 281], RecordEncoding::Frame);
	let rejected = match begin_record_send(kernel(), context) {
		RecordSendStart::Rejected(kernel) => kernel,
		_ => panic!("empty send rejects"),
	};
	assert_eq!(snapshot(&rejected), original);
	let context = SealFrameContext::new(b"msg", 77, 99, &[6; 281], RecordEncoding::Frame);
	let canceled = match begin_record_send(kernel(), context) {
		RecordSendStart::KdfRequested(pending) => pending.cancel(),
		_ => panic!("nonempty send"),
	};
	assert_eq!(snapshot(&canceled), original);
	let context = || SealFrameContext::new(b"msg", 77, 99, &[6; 281], RecordEncoding::Frame);
	let failed_aead = match send(context()).resume(None) {
		SealAfterAead::Rejected(kernel) => kernel,
		_ => panic!("AEAD failure"),
	};
	let commitment = match send(context()).resume(Some((&[21; 3], [10; 16]))) {
		SealAfterAead::CommitmentRequested(pending) => pending,
		_ => panic!("AEAD success"),
	};
	let failed_hash = match commitment.resume(None) {
		SealAfterCommitment::Rejected(kernel) => kernel,
		_ => panic!("hash failure"),
	};
	let commitment = match send(context()).resume(Some((&[21; 3], [10; 16]))) {
		SealAfterAead::CommitmentRequested(pending) => pending,
		_ => panic!("AEAD success"),
	};
	let writer = match commitment.resume(Some([11; 64])) {
		SealAfterCommitment::WriteRequested(writer) => writer,
		_ => panic!("hash success"),
	};
	let (failed_write, output) = writer.finish::<()>(None);
	assert!(output.is_none());
	assert_eq!(snapshot(&failed_aead), snapshot(&failed_hash));
	assert_eq!(snapshot(&failed_aead), snapshot(&failed_write));
	assert_eq!(failed_aead.send_sequence(), 1);
	assert_eq!(failed_aead.send_chain().as_bytes(), &[8; 32]);
}

#[test]
fn future_commitment_and_aead_failures_restore_the_complete_entry_kernel() {
	let original = snapshot(&kernel());
	let payload = payload();
	let pending = receive_commitment(begin_record_receive(kernel(), 3, &payload, &[6; 281], 99));
	let rejected = match pending.resume(false) {
		RecordReceiveEffect::Rejected(kernel) => kernel,
		_ => panic!("mismatched commitment"),
	};
	assert_eq!(snapshot(&rejected), original);
	let pending = receive_commitment(begin_record_receive(kernel(), 3, &payload, &[6; 281], 99));
	let aead = match pending.resume(true) {
		RecordReceiveEffect::AeadRequested(pending) => pending,
		_ => panic!("matching commitment"),
	};
	let (rejected, opened) = aead.finish::<()>(None);
	assert!(opened.is_none());
	assert_eq!(snapshot(&rejected), original);
}

#[test]
fn future_success_publishes_once_cached_rejection_stutters_and_replay_rejects() {
	let payload = payload();
	let pending = receive_commitment(begin_record_receive(kernel(), 3, &payload, &[6; 281], 99));
	let aead = match pending.resume(true) {
		RecordReceiveEffect::AeadRequested(pending) => pending,
		_ => panic!("matching commitment"),
	};
	let (kernel, opened) = aead.finish(Some(b"actual plaintext"));
	let opened = opened.unwrap();
	assert_eq!((opened.key_id, opened.seq), (99, 3));
	assert_eq!(opened.plaintext, b"actual plaintext");
	assert_eq!(kernel.receive_sequence(), 3);
	assert_eq!(kernel.receive_cache_len(), 2);
	let before_cached = snapshot(&kernel);
	let pending = receive_commitment(begin_record_receive(kernel, 1, &payload, &[6; 281], 99));
	let rejected = match pending.resume(false) {
		RecordReceiveEffect::Rejected(kernel) => kernel,
		_ => panic!("cached commitment failure"),
	};
	assert_eq!(snapshot(&rejected), before_cached);
	let pending = receive_commitment(begin_record_receive(rejected, 1, &payload, &[6; 281], 99));
	let aead = match pending.resume(true) {
		RecordReceiveEffect::AeadRequested(pending) => pending,
		_ => panic!("cached commitment success"),
	};
	let (kernel, _) = aead.finish(Some(b"cached plaintext"));
	assert_eq!(kernel.receive_cache_len(), 1);
	let before_replay = snapshot(&kernel);
	let rejected = match begin_record_receive(kernel, 1, &payload, &[6; 281], 99) {
		RecordReceiveEffect::Rejected(kernel) => kernel,
		_ => panic!("consumed cached sequence rejects before primitives"),
	};
	assert_eq!(snapshot(&rejected), before_replay);
}
