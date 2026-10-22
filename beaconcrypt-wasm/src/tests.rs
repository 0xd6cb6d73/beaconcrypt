// SPDX-License-Identifier: 0BSD

use super::*;
use std::{cell::Cell, rc::Rc};
use zeroize::Zeroizing;

// Observe live buffers immediately before the system allocator releases them.
// Reading after Response's Vec fields are freed would be an invalid zeroization test.
mod drop_observer {
	use std::{
		alloc::{GlobalAlloc, Layout, System},
		sync::atomic::{AtomicU8, AtomicUsize, Ordering},
	};

	pub static DATA: AtomicUsize = AtomicUsize::new(0);
	pub static STATE: AtomicUsize = AtomicUsize::new(0);
	pub static WIPED: AtomicU8 = AtomicU8::new(0);

	pub struct ObservedAllocator;

	unsafe impl GlobalAlloc for ObservedAllocator {
		unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
			unsafe { System.alloc(layout) }
		}

		unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
			let address = ptr as usize;
			let bit = if DATA
				.compare_exchange(address, 0, Ordering::SeqCst, Ordering::SeqCst)
				.is_ok()
			{
				1
			} else if STATE
				.compare_exchange(address, 0, Ordering::SeqCst, Ordering::SeqCst)
				.is_ok()
			{
				2
			} else {
				0
			};
			if bit != 0 {
				// The allocation is live until System.dealloc below.
				// Both tracked vectors have initialized bytes throughout their exact capacity.
				let bytes = unsafe { std::slice::from_raw_parts(ptr, layout.size()) };
				if bytes.iter().all(|byte| *byte == 0) {
					WIPED.fetch_or(bit, Ordering::SeqCst);
				}
			}
			unsafe { System.dealloc(ptr, layout) }
		}
	}
}

#[global_allocator]
static TEST_ALLOCATOR: drop_observer::ObservedAllocator = drop_observer::ObservedAllocator;

#[test]
fn response_drop_wipes_both_owned_buffers_before_release() {
	use std::sync::atomic::Ordering;
	let mut response = Response::success(7, 11, vec![0x91; 32]);
	response.state = vec![0xe3; 64];
	assert_eq!(response.data.capacity(), response.data.len());
	assert_eq!(response.state.capacity(), response.state.len());
	drop_observer::WIPED.store(0, Ordering::SeqCst);
	drop_observer::DATA.store(response.data.as_ptr() as usize, Ordering::SeqCst);
	drop_observer::STATE.store(response.state.as_ptr() as usize, Ordering::SeqCst);
	drop(response);
	drop_observer::DATA.store(0, Ordering::SeqCst);
	drop_observer::STATE.store(0, Ordering::SeqCst);
	assert_eq!(drop_observer::WIPED.load(Ordering::SeqCst), 3);
}

#[cfg(target_arch = "wasm32")]
#[test]
fn wasm_allocations_and_packed_replies_round_trip_exactly() {
	let ptr = abi::bc_alloc(4);
	assert_ne!(ptr, 0);
	assert_eq!(&*abi::copy_input(ptr, 4).unwrap(), &[0; 4]);
	abi::bc_free(ptr, 3);
	assert!(abi::copy_input(ptr, 4).is_some());
	abi::bc_free(ptr, 4);
	assert!(abi::copy_input(ptr, 4).is_none());

	let mut response = Response::message(0x1234_5678, u64::MAX, u64::MAX - 1, vec![1, 2, 3]);
	response.state = vec![4, 5];
	let expected = response.encode().unwrap();
	let packed = abi::encode_result(response);
	let (ptr, len) = ((packed >> 32) as u32, packed as u32);
	assert_ne!(ptr, 0);
	assert_eq!(len as usize, expected.len());
	assert_eq!(&*abi::copy_input(ptr, len).unwrap(), &*expected);
	abi::bc_free(ptr, len);
	assert!(abi::copy_input(ptr, len).is_none());
}

#[cfg(target_arch = "wasm32")]
mod wasm_store_tests {
	use super::*;

	#[link(wasm_import_module = "beaconcrypt_test")]
	unsafe extern "C" {
		fn configure_store(context: u32, storage: u32, reject: u32);
		fn expected_head(context: u32, ptr: u32, len: u32);
		fn store_count(context: u32, metric: u32) -> u32;
	}

	#[test]
	fn host_store_loads_commits_rejects_and_releases_owned_contexts() {
		const FIRST: u32 = 0xbc00_0001;
		const RESTORED: u32 = 0xbc00_0002;
		const REJECTED: u32 = 0xbc00_0003;
		unsafe { configure_store(FIRST, FIRST, 0) };
		let server =
			PersistentServer::create(19, Some(&[9; 32]), Some(&[10; 32]), HostStore(FIRST))
				.unwrap();
		let head = server.head();
		assert_eq!(server.snapshot().unwrap().head().unwrap(), head);
		assert_eq!(unsafe { store_count(FIRST, 0) }, 2);
		assert_eq!(unsafe { store_count(FIRST, 1) }, 1);
		assert_eq!(unsafe { store_count(FIRST, 2) }, 0);
		drop(server);
		assert_eq!(unsafe { store_count(FIRST, 2) }, 1);

		unsafe { configure_store(RESTORED, FIRST, 0) };
		let encoded_head = encode_head(&head);
		unsafe {
			expected_head(
				RESTORED,
				encoded_head.as_ptr() as u32,
				encoded_head.len() as u32,
			)
		};
		let restored = PersistentServer::restore(HostStore(RESTORED)).unwrap();
		assert_eq!(restored.head().generation(), head.generation() + 1);
		assert_eq!(unsafe { store_count(RESTORED, 0) }, 2);
		assert_eq!(unsafe { store_count(RESTORED, 1) }, 1);
		drop(restored);
		assert_eq!(unsafe { store_count(RESTORED, 2) }, 1);

		unsafe { configure_store(REJECTED, REJECTED, 1) };
		let failure =
			PersistentServer::create(19, Some(&[9; 32]), Some(&[10; 32]), HostStore(REJECTED));
		assert!(matches!(failure, Err(PersistenceError::StaleGeneration)));
		assert_eq!(unsafe { store_count(REJECTED, 1) }, 1);
		assert_eq!(unsafe { store_count(REJECTED, 2) }, 1);
	}

	#[test]
	fn host_store_constructor_dispatch_preserves_both_seeds_and_requested_lineage() {
		let ed_seed = [9; 32];
		let ml_seed = [10; 32];
		let seeds = [ed_seed, ml_seed].concat();
		let expected = beaconcrypt::Server::try_new(19, Some(&ed_seed), Some(&ml_seed)).unwrap();
		let lineage = [0x35; 32];
		for (op, context) in [(12, 0xbc10_0001u32), (18, 0xbc10_0002u32)] {
			unsafe { configure_store(context, context, 0) };
			let mut metadata = context.to_le_bytes().to_vec();
			if op == 18 {
				metadata.extend_from_slice(&lineage);
			}
			metadata.push(3);
			let owner = checked(op, 0, 19, &seeds, &metadata).handle;
			assert_eq!(
				checked(3, owner, 0, &[], &[]).data,
				expected.identity_pk().as_bytes()
			);
			assert_eq!(
				checked(24, owner, 0, &[], &[]).data,
				expected.mldsa_public_key()
			);
			let head = decode_head(&checked(14, owner, 0, &[], &[]).data).unwrap();
			assert_eq!(head.generation(), 0);
			if op == 18 {
				assert_eq!(head.lineage(), SnapshotLineage::from_bytes(lineage));
			}
			assert_eq!(unsafe { store_count(context, 1) }, 1);
			assert_eq!(unsafe { store_count(context, 2) }, 0);
			checked(9, owner, 0, &[], &[]);
			assert_eq!(unsafe { store_count(context, 2) }, 1);
		}
	}

	#[test]
	fn snapshot_load_copies_one_complete_read_and_requires_its_exact_length() {
		let server =
			PersistentServer::create(19, Some(&[9; 32]), Some(&[10; 32]), MemoryStore::default())
				.unwrap();
		let snapshot = server.snapshot().unwrap();
		for correct_length in [true, false] {
			let mut calls = 0;
			let loaded = store::load_snapshot(|ptr, capacity| {
				calls += 1;
				if calls == 1 {
					assert_eq!((ptr, capacity), (0, 0));
					return snapshot.as_bytes().len() as i64;
				}
				assert_eq!(capacity as usize, snapshot.as_bytes().len());
				let output =
					unsafe { std::slice::from_raw_parts_mut(ptr as *mut u8, capacity as usize) };
				output.copy_from_slice(snapshot.as_bytes());
				i64::from(capacity) - i64::from(!correct_length)
			})
			.unwrap();
			assert_eq!(calls, 2);
			if correct_length {
				assert_eq!(loaded.head().unwrap(), snapshot.head().unwrap());
			} else {
				assert!(loaded.as_bytes().is_empty());
				assert!(loaded.head().is_err());
			}
		}
	}

	#[test]
	fn snapshot_load_rejects_unrepresentable_lengths_before_a_second_read() {
		let mut calls = 0;
		let invalid = store::load_snapshot(|ptr, capacity| {
			calls += 1;
			assert_eq!((ptr, capacity), (0, 0));
			i64::from(i32::MAX) + 1
		})
		.unwrap();
		assert_eq!(calls, 1);
		assert!(invalid.as_bytes().is_empty());
	}

	// The WASI runner executes this probe alone and requires the allocation-failure trap.
	// Its 256 MiB limit prevents a real multi-gigabyte allocation.
	// Returning normally would change the guest's observable failure behavior at this bound.
	#[test]
	fn snapshot_load_max_length_allocation_failure_probe() {
		let _ = store::load_snapshot(|ptr, capacity| {
			assert_eq!((ptr, capacity), (0, 0));
			i64::from(i32::MAX)
		});
	}
}

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
	let owner = checked(1, 0, 19, &seed, &[1]).handle;
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
	assert_eq!(bc_abi_version(), 2);
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
	let owner = checked(1, 0, 19, &[9; 64], &[3]).handle;
	let mut beacon = Beacon::try_new(
		19,
		&checked(3, owner, 0, &[], &[]).data,
		&checked(24, owner, 0, &[], &[]).data,
	)
	.unwrap();
	let bundle = beacon.get_registration_bundle().unwrap();
	assert_eq!(&bundle[..3], &[0x88, 2, 0]);
	assert_eq!(bundle.len(), 6_757);
	assert_eq!(&bundle[bundle.len() - 3_312..][..3], &[0x59, 0x0c, 0xed]);
	let registration = checked(5, owner, 0, &bundle, b"hello");
	assert_eq!(&registration.data[..3], &[0x88, 2, 1]);
	assert_eq!(
		&registration.data[registration.data.len() - 3_312..][..3],
		&[0x59, 0x0c, 0xed]
	);
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

	let status = checked(17, owner, peer, &[], &[]);
	let remote_status = beacon.ratchet_status().unwrap();
	assert_eq!(status.data.len(), 17);
	assert_eq!(
		&status.data[..8],
		&remote_status.receive_sequence().to_le_bytes()
	);
	assert_eq!(
		&status.data[8..16],
		&remote_status.send_sequence().to_le_bytes()
	);
	assert_eq!(status.data[16], 0);
	assert_eq!(status.key_id, peer);
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
	let mut native = beaconcrypt::Server::try_new(19, Some(&[8; 32]), Some(&[9; 32])).unwrap();
	let public = [
		native.identity_pk().as_bytes().as_slice(),
		native.mldsa_public_key().as_slice(),
	]
	.concat();
	let beacon = checked(2, 0, 19, &public, &[]).handle;
	assert_eq!(checked(3, beacon, 0, &[], &[]).data.len(), 32);
	let registration = checked(4, beacon, 0, &[], &[]);
	assert_eq!(&registration.data[..3], &[0x88, 2, 0]);
	assert_eq!(registration.data.len(), 6_757);
	assert_eq!(
		&registration.data[registration.data.len() - 3_312..][..3],
		&[0x59, 0x0c, 0xed]
	);
	let pending = native.get_shared_secret(&registration.data).unwrap();
	let response = native
		.build_registration_response(pending, Some(b"native hello"))
		.unwrap();
	assert_eq!(&response.serialized[..3], &[0x88, 2, 1]);
	assert_eq!(
		&response.serialized[response.serialized.len() - 3_312..][..3],
		&[0x59, 0x0c, 0xed]
	);
	assert_eq!(
		checked(6, beacon, 0, &response.serialized, &[]).data,
		b"native hello"
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
	let remote_status = native.ratchet_status(response.kid).unwrap();
	assert_eq!(status.data.len(), 17);
	assert_eq!(
		&status.data[..8],
		&remote_status.receive_sequence().to_le_bytes()
	);
	assert_eq!(
		&status.data[8..16],
		&remote_status.send_sequence().to_le_bytes()
	);
	assert_eq!(status.data[16], 0);
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
		Some(&[8; 32]),
		Box::new(store.clone()) as Box<dyn SnapshotStore>,
	)
	.unwrap();
	let mut beacon = Beacon::try_new(
		19,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)
	.unwrap();
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
fn exported_call_closes_the_requested_owner() {
	let owner = checked(1, 0, 19, &[9; 64], &[3]).handle;
	let packed = bc_call(9, owner, 0, 0, 0, 0, 0);
	if packed != 0 {
		abi::bc_free((packed >> 32) as u32, packed as u32);
	}
	assert_eq!(dispatch(3, owner, 0, &[], &[]).status, INVALID_ARGUMENT);
}

#[test]
fn constructors_reject_nonzero_handles_and_unexpected_extra_bytes() {
	let owner = checked(1, 0, 19, &[9; 64], &[3]).handle;
	let public_key = checked(3, owner, 0, &[], &[]);
	let snapshot = checked(10, owner, 0, &[], &[]);
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
	checked(9, owner, 0, &[], &[]);
}

#[test]
fn host_store_constructors_validate_exact_context_length_and_restore_input() {
	assert_eq!(
		dispatch(12, 0, 19, &[9; 32], &[1; 6]).status,
		INVALID_ARGUMENT
	);
	assert_eq!(
		dispatch(13, 0, 0, b"unexpected", &[]).status,
		INVALID_ARGUMENT
	);
	assert_eq!(
		dispatch(13, 0, 0, &[], &[]).status,
		abi::error_status(PersistenceError::MissingSnapshot)
	);
}

#[test]
fn snapshot_and_constructor_failures_use_production_status_codes() {
	assert_eq!(dispatch(1, 0, 19, &[0; 31], &[1]).status, INITIALIZATION);
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

#[test]
fn seed_presence_flags_keep_the_two_identity_seeds_distinct() {
	let mut input = [0x11; 64];
	input[32..].fill(0x22);
	let (ed, ml) = seeds(&input, 3).unwrap();
	assert_eq!(ed, Some(&input[..32]));
	assert_eq!(ml, Some(&input[32..]));
	assert_eq!(seeds(&input[..32], 1), Some((Some(&input[..32]), None)));
	assert_eq!(seeds(&input[32..], 2), Some((None, Some(&input[32..]))));
	assert_eq!(seeds(&[], 0), Some((None, None)));
	for (bytes, flags) in [
		(&input[..], 0),
		(&input[..31], 1),
		(&input[..32], 3),
		(&input[..], 4),
	] {
		assert!(seeds(bytes, flags).is_none());
	}
}

#[test]
fn beacon_constructor_requires_the_mldsa_pin_after_the_ed25519_key() {
	let server = checked(1, 0, 19, &[9; 64], &[3]).handle;
	let ed = checked(3, server, 0, &[], &[]).data.clone();
	let ml = checked(24, server, 0, &[], &[]).data.clone();
	assert_eq!(ml.len(), 1952);
	assert_eq!(dispatch(2, 0, 19, &ed, &[]).status, INITIALIZATION);
	let public = [ed, ml].concat();
	let beacon = checked(2, 0, 19, &public, &[]).handle;
	assert_eq!(checked(24, beacon, 0, &[], &[]).data.len(), 1952);
	checked(9, beacon, 0, &[], &[]);
	checked(9, server, 0, &[], &[]);
}
