// SPDX-License-Identifier: 0BSD

use super::*;
use std::{cell::Cell, rc::Rc};
use zeroize::Zeroizing;

fn checked(op: u32, handle: u32, arg: u64, input: &[u8], extra: &[u8]) -> Response {
	let response = dispatch(op, handle, arg, input, extra);
	assert_eq!(response.status, 0, "operation {op}");
	response
}

fn hex<const N: usize>(value: &str) -> [u8; N] {
	assert_eq!(value.len(), 2 * N);
	let mut bytes = [0; N];
	for (index, output) in bytes.iter_mut().enumerate() {
		*output = u8::from_str_radix(&value[2 * index..2 * index + 2], 16).unwrap();
	}
	bytes
}

#[test]
fn seeded_server_matches_rfc8032_ed25519_vector() {
	// RFC 8032 section 7.1, TEST 1: an independent fixed identity vector.
	let seed = hex::<32>("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
	let public_key = hex::<32>("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
	let owner = checked(1, 0, 19, &seed, &[]).handle;
	assert_eq!(checked(3, owner, 0, &[], &[]).data, public_key);
	checked(9, owner, 0, &[], &[]);
	assert_eq!(dispatch(3, owner, 0, &[], &[]).status, INVALID_ARGUMENT);
}

#[test]
fn reply_header_preserves_full_width_metadata_and_independent_lengths() {
	let mut response = Response::message(0x1234_5678, u64::MAX, u64::MAX - 1, vec![1, 2, 3]);
	response.state = br#"{"state":1}"#.to_vec();
	let bytes = response.encode().unwrap();
	assert_eq!(&bytes[..4], &0u32.to_le_bytes());
	assert_eq!(&bytes[4..8], &0x1234_5678u32.to_le_bytes());
	assert_eq!(&bytes[8..16], &u64::MAX.to_le_bytes());
	assert_eq!(&bytes[16..24], &(u64::MAX - 1).to_le_bytes());
	assert_eq!(&bytes[24..28], &3u32.to_le_bytes());
	assert_eq!(&bytes[28..32], &(response.state.len() as u32).to_le_bytes());
	assert_eq!(&bytes[32..35], &[1, 2, 3]);
	assert_eq!(&bytes[35..], response.state);
	let failed = Response::failed(12).encode().unwrap();
	assert_eq!(failed.len(), 32);
	assert!(failed[4..].iter().all(|byte| *byte == 0));
	assert_eq!(bc_abi_version(), 1);
	assert_eq!(bc_max_message_size(), 33_554_432);
}

#[test]
fn input_descriptors_require_owned_exact_allocations_and_free_is_checked() {
	// The registry stores actual linear-memory addresses on wasm32. Synthetic
	// offsets let native tests exercise descriptor checking without unsafe reads.
	abi::ALLOCATIONS.with_borrow_mut(|allocations| {
		allocations.insert(
			4096,
			Zeroizing::new(vec![11, 22, 33, 44].into_boxed_slice()),
		);
	});
	assert_eq!(&*abi::copy_input(4096, 4).unwrap(), &[11, 22, 33, 44]);
	for (ptr, len) in [
		(0, 1),
		(4096, 0),
		(4096, 3),
		(4097, 3),
		(u32::MAX, 1),
		(4096, u32::MAX),
	] {
		assert!(abi::copy_input(ptr, len).is_none(), "({ptr}, {len})");
		assert_eq!(call(1, 0, 19, ptr, len, 0, 0).status, INVALID_ARGUMENT);
	}
	abi::bc_free(4096, 3);
	assert!(abi::copy_input(4096, 4).is_some());
	abi::bc_free(4096, 4);
	assert!(abi::copy_input(4096, 4).is_none());
	abi::bc_free(4096, 4);
	assert!(abi::copy_input(0, 0).unwrap().is_empty());
	assert_eq!(abi::bc_alloc(0), 0);
	assert_eq!(abi::bc_alloc(u32::MAX), 0);
	assert_eq!(call(1, 0, 19, 0, 0, 1, 0).status, INVALID_ARGUMENT);
}

#[test]
fn guest_server_interoperates_with_native_beacon_updates_json_and_checkpoint() {
	let owner = checked(1, 0, 19, &[9; 32], &[]).handle;
	assert_eq!(dispatch(17, owner, u64::MAX, &[], &[]).status, REJECTED);
	let mut beacon = Beacon::try_new(19, &checked(3, owner, 0, &[], &[]).data).unwrap();
	let bundle = beacon.get_registration_bundle().unwrap();
	let registration = checked(5, owner, 0, &bundle, b"hello");
	assert_eq!(
		beacon.finish_registration(&registration.data).unwrap(),
		b"hello"
	);
	let peer = registration.key_id;

	let inbound = beacon.encrypt_message(b"native to guest").unwrap();
	let receive = checked(21, owner, 0, &inbound.ciphertext, &[]);
	assert_eq!(receive.data, b"native to guest");
	assert_eq!(receive.key_id, peer);
	assert_eq!(receive.seq, inbound.seq);
	let state: serde_json::Value = serde_json::from_slice(&receive.state).unwrap();
	assert!(state.get("send_key").is_some() && state.get("recv_key").is_some());
	let before = checked(10, owner, 0, &[], &[]);
	let replay = dispatch(23, owner, 0, &inbound.ciphertext, &[]);
	assert_eq!(replay.status, REJECTED);
	assert!(replay.data.is_empty() && replay.state.is_empty());
	assert_eq!(before.data, checked(10, owner, 0, &[], &[]).data);

	let send = checked(20, owner, peer, b"guest to native", &[]);
	assert_eq!(
		beacon.decrypt_message(&send.data).unwrap().plaintext,
		b"guest to native"
	);
	assert_eq!(send.key_id, peer);
	assert!(!send.state.is_empty());

	let send_json = checked(22, owner, peer, b"JSON send", &[]);
	assert!(send_json.state.is_empty());
	let json: serde_json::Value = serde_json::from_slice(&send_json.data).unwrap();
	assert_eq!(json["kid"], peer);
	let frame: Vec<u8> = serde_json::from_value(json["data"].clone()).unwrap();
	assert_eq!(
		beacon.decrypt_message(&frame).unwrap().plaintext,
		b"JSON send"
	);
	let inbound = beacon.encrypt_message(b"JSON receive").unwrap();
	let receive_json = checked(23, owner, 0, &inbound.ciphertext, &[]);
	let json: serde_json::Value = serde_json::from_slice(&receive_json.data).unwrap();
	assert_eq!(
		serde_json::from_value::<Vec<u8>>(json["data"].clone()).unwrap(),
		b"JSON receive"
	);
	assert_eq!(json["seq"], inbound.seq);
	let skipped = beacon.encrypt_message(b"delayed native frame").unwrap();
	let future = beacon.encrypt_message(b"future native frame").unwrap();
	assert_eq!(
		checked(8, owner, 0, &future.ciphertext, &[]).data,
		b"future native frame"
	);
	let status = checked(17, owner, peer, &[], &[]);
	let remote = beacon.ratchet_status().unwrap();
	assert_eq!(status.handle, owner);
	assert_eq!(status.key_id, peer);
	assert_eq!(status.data.len(), 17);
	assert_eq!(&status.data[..8], &remote.receive_sequence().to_le_bytes());
	assert_eq!(&status.data[8..16], &remote.send_sequence().to_le_bytes());
	assert_eq!(status.data[16], 1);
	assert!(status.state.is_empty());
	assert_eq!(
		checked(8, owner, 0, &skipped.ciphertext, &[]).data,
		b"delayed native frame"
	);
	assert_eq!(checked(17, owner, peer, &[], &[]).data[16], 0);

	let snapshot = checked(10, owner, 0, &[], &[]);
	let head = checked(19, 0, 0, &snapshot.data, &[]);
	assert_eq!(head.data, checked(14, owner, 0, &[], &[]).data);
	checked(9, owner, 0, &[], &[]);
	let restored = checked(11, 0, 0, &snapshot.data, &[]).handle;
	let successor = checked(10, restored, 0, &[], &[]);
	checked(16, 0, 0, &successor.data, &head.data);
	let outbound = checked(7, restored, peer, b"after restore", &[]);
	assert_eq!(
		beacon.decrypt_message(&outbound.data).unwrap().plaintext,
		b"after restore"
	);
	let inbound = beacon.encrypt_message(b"continued native").unwrap();
	assert_eq!(
		checked(8, restored, 0, &inbound.ciphertext, &[]).data,
		b"continued native"
	);
	checked(9, restored, 0, &[], &[]);
}

#[test]
fn guest_beacon_interoperates_with_native_server_and_rejects_wrong_handle_kinds() {
	use beaconcrypt::ProviderServer;
	let mut native = beaconcrypt::Server::try_new(19, Some(&[8; 32])).unwrap();
	let beacon = checked(2, 0, 19, native.identity_pk().as_bytes(), &[]).handle;
	let identity = checked(3, beacon, 0, &[], &[]);
	assert_eq!(identity.data.len(), 32);
	assert_eq!(dispatch(17, beacon, 0, &[], &[]).status, REJECTED);
	let registration = checked(4, beacon, 0, &[], &[]);
	let pending = native.get_shared_secret(&registration.data).unwrap();
	let response = native
		.build_registration_response(pending, Some(b"native hello"))
		.unwrap();
	assert_eq!(
		checked(6, beacon, 0, &response.serialized, &[]).data,
		b"native hello"
	);
	assert_eq!(
		identity.data,
		native.pk_by_kid(response.kid).unwrap().as_bytes()
	);
	let frame = checked(7, beacon, 0, b"guest beacon", &[]);
	assert_eq!(
		native.decrypt_message(&frame.data).unwrap().plaintext,
		b"guest beacon"
	);
	let frame = native
		.encrypt_message(b"native server", response.kid)
		.unwrap();
	assert_eq!(
		checked(8, beacon, 0, &frame.ciphertext, &[]).data,
		b"native server"
	);
	let status = checked(17, beacon, 0, &[], &[]);
	let remote = native.ratchet_status(response.kid).unwrap();
	assert_eq!(status.handle, beacon);
	assert_eq!(status.key_id, 0);
	assert_eq!(status.data.len(), 17);
	assert_eq!(&status.data[..8], &remote.receive_sequence().to_le_bytes());
	assert_eq!(&status.data[8..16], &remote.send_sequence().to_le_bytes());
	assert_eq!(status.data[16], 0);
	assert!(status.state.is_empty());
	for op in [5, 10, 14, 15, 20, 21, 22, 23] {
		assert_eq!(
			dispatch(op, beacon, 0, b"invalid", &[]).status,
			INVALID_ARGUMENT
		);
	}
	assert_eq!(dispatch(1, beacon, 19, &[], &[]).status, INVALID_ARGUMENT);
	checked(9, beacon, 0, &[], &[]);
	assert_eq!(dispatch(9, beacon, 0, &[], &[]).status, INVALID_ARGUMENT);
}

#[derive(Clone)]
struct FailingStore {
	inner: Rc<RefCell<MemoryStore>>,
	fail: Rc<Cell<bool>>,
}

impl SnapshotStore for FailingStore {
	fn load(&self) -> Option<ServerSnapshot> {
		self.inner.borrow().load()
	}
	fn compare_and_swap(
		&mut self,
		expected: Option<&beaconcrypt::SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		!self.fail.get()
			&& self
				.inner
				.borrow_mut()
				.compare_and_swap(expected, replacement)
	}
}

#[test]
fn failed_commit_suppresses_updates_and_poisons_the_live_owner() {
	let store = FailingStore {
		inner: Rc::new(RefCell::new(MemoryStore::default())),
		fail: Rc::new(Cell::new(false)),
	};
	let server = PersistentServer::create(
		19,
		Some(&[7; 32]),
		Box::new(store.clone()) as Box<dyn SnapshotStore>,
	)
	.unwrap();
	let mut beacon = Beacon::try_new(19, server.identity_pk().as_bytes()).unwrap();
	let owner = REGISTRY
		.with_borrow_mut(|registry| registry.server(Ok(server)))
		.handle;
	let registration = checked(
		5,
		owner,
		0,
		&beacon.get_registration_bundle().unwrap(),
		b"hello",
	);
	beacon.finish_registration(&registration.data).unwrap();
	store.fail.set(true);
	let response = dispatch(20, owner, registration.key_id, b"must stay private", &[]);
	assert_eq!(response.status, 6);
	assert!(response.data.is_empty() && response.state.is_empty());
	assert_eq!(checked(15, owner, 0, &[], &[]).data, [1]);
	assert_eq!(
		dispatch(7, owner, registration.key_id, b"next", &[]).status,
		12
	);
	checked(9, owner, 0, &[], &[]);
}

#[test]
fn snapshot_and_constructor_failures_use_production_status_codes() {
	assert_eq!(dispatch(1, 0, 19, &[0; 31], &[]).status, INITIALIZATION);
	assert_eq!(dispatch(19, 0, 0, &[], &[]).status, INVALID_ARGUMENT);
	assert_eq!(dispatch(19, 0, 0, b"not a snapshot", &[]).status, 4);
	assert_eq!(
		dispatch(16, 0, 0, b"not a snapshot", &[0; 71]).status,
		INVALID_ARGUMENT
	);
	assert_eq!(dispatch(18, 0, 19, &[], &[1; 35]).status, INVALID_ARGUMENT);
	assert_eq!(dispatch(13, 0, u64::MAX, &[], &[]).status, INVALID_ARGUMENT);
	assert_eq!(dispatch(u32::MAX, 0, 0, &[], &[]).status, INVALID_ARGUMENT);
	assert_eq!(abi::error_status(PersistenceError::NonCanonicalSnapshot), 5);
	assert_eq!(abi::error_status(PersistenceError::OutputEncoding), 9);
}

#[test]
fn constructors_reject_nonzero_handles_and_unexpected_extra_bytes() {
	let owner = checked(1, 0, 19, &[9; 32], &[]).handle;
	let public_key = checked(3, owner, 0, &[], &[]);
	let snapshot = checked(10, owner, 0, &[], &[]);
	// Each invalid argument must reject independently of the other argument.
	for (handle, extra) in [(owner, &[][..]), (0, &[1][..])] {
		assert_eq!(
			dispatch(2, handle, 19, &public_key.data, extra).status,
			INVALID_ARGUMENT
		);
		assert_eq!(
			dispatch(11, handle, 0, &snapshot.data, extra).status,
			INVALID_ARGUMENT
		);
		assert_eq!(dispatch(13, handle, 0, &[], extra).status, INVALID_ARGUMENT);
	}
	assert_eq!(checked(10, owner, 0, &[], &[]).data, snapshot.data);
	checked(9, owner, 0, &[], &[]);
}

#[test]
fn host_store_constructors_validate_exact_context_length_and_restore_input() {
	// The first four bytes already identify a context; accepting trailing bytes would silently
	// consume that context instead of reporting invalid constructor metadata.
	for length in [5, 6, 36] {
		assert_eq!(
			dispatch(12, 0, 19, &[9; 32], &vec![1; length]).status,
			INVALID_ARGUMENT
		);
	}
	assert_eq!(
		dispatch(13, 0, 0, b"unexpected snapshot bytes", &[]).status,
		INVALID_ARGUMENT
	);
	assert_eq!(
		dispatch(13, 0, 0, &[], &[]).status,
		abi::error_status(PersistenceError::MissingSnapshot)
	);
}

#[test]
fn host_load_failures_match_native_missing_snapshot_status() {
	struct LoadResult(i64);
	impl SnapshotStore for LoadResult {
		fn load(&self) -> Option<ServerSnapshot> {
			let mut calls = 0;
			let snapshot = store::load_snapshot(|ptr, len| {
				calls += 1;
				assert_eq!((ptr, len), (0, 0));
				self.0
			});
			assert_eq!(calls, 1);
			snapshot
		}
		fn compare_and_swap(
			&mut self,
			_: Option<&beaconcrypt::SnapshotHead>,
			_: &ServerSnapshot,
		) -> bool {
			panic!("missing/invalid snapshots must not reach activation CAS")
		}
	}
	for (host_result, expected_status) in [(-1, 3), (-2, 3), (-3, 4), (0, 4)] {
		let restored =
			PersistentServer::restore(Box::new(LoadResult(host_result)) as Box<dyn SnapshotStore>);
		assert_eq!(abi::error_status(restored.err().unwrap()), expected_status);
	}
}
