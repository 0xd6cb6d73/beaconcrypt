// SPDX-License-Identifier: 0BSD

use beaconcrypt::{PersistenceError, PersistentServer, ServerSnapshot, SnapshotStore};

use crate::store::{self, MemoryStore};

#[test]
fn snapshot_load_rejects_missing_and_unrepresentable_lengths_without_copying() {
	for length in [-1, -2, -3, 0, i64::from(u32::MAX) + 1, i64::MAX] {
		let mut calls = 0;
		let snapshot = store::load_snapshot(|ptr, capacity| {
			calls += 1;
			assert_eq!((ptr, capacity), (0, 0));
			length
		});
		assert_eq!(calls, 1, "announced length {length}");
		if matches!(length, -1 | -2) {
			assert!(snapshot.is_none());
		} else {
			let snapshot = snapshot.unwrap();
			assert!(snapshot.as_bytes().is_empty());
			assert_eq!(snapshot.head(), Err(PersistenceError::InvalidSnapshot));
		}
	}
}

#[test]
fn memory_store_commits_only_the_expected_head_and_valid_successor() {
	let server = PersistentServer::create(19, Some(&[0x79; 32]), MemoryStore::default()).unwrap();
	let original = server.snapshot().unwrap();
	let previous = original.head().unwrap();
	let mut store = MemoryStore::from_bytes(original.as_bytes().to_vec()).unwrap();
	let restored =
		PersistentServer::restore(MemoryStore::from_bytes(original.as_bytes().to_vec()).unwrap())
			.unwrap();
	let successor = restored.snapshot().unwrap();
	assert!(!store.compare_and_swap(None, &successor));
	assert!(!store.compare_and_swap(Some(&previous), &original));
	assert!(!store.compare_and_swap(Some(&previous), &ServerSnapshot::from_bytes(vec![])));
	assert_eq!(store.load().unwrap().as_bytes(), original.as_bytes());
	assert!(store.compare_and_swap(Some(&previous), &successor));
	assert_eq!(store.load().unwrap().as_bytes(), successor.as_bytes());
	assert!(!store.compare_and_swap(Some(&previous), &successor));
}

#[cfg(target_arch = "wasm32")]
use crate::store::{HostStore, encode_head};

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "beaconcrypt_test")]
unsafe extern "C" {
	fn configure_store(context: u32, storage: u32, reject: u32);
	fn expected_head(context: u32, ptr: u32, len: u32);
	fn store_count(context: u32, metric: u32) -> u32;
}

#[cfg(target_arch = "wasm32")]
#[test]
fn host_store_loads_exact_snapshots_compares_heads_and_releases_contexts() {
	const FIRST: u32 = 0xbc00_0001;
	const RESTORED: u32 = 0xbc00_0002;
	const REJECTED: u32 = 0xbc00_0003;
	const INVALID_SEED: u32 = 0xbc00_0004;
	unsafe { configure_store(FIRST, FIRST, 0) };
	let server = PersistentServer::create(19, Some(&[9; 32]), HostStore(FIRST)).unwrap();
	let head = server.head();
	let snapshot = server.snapshot().unwrap();
	assert_eq!(snapshot.head().unwrap(), head);
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
	assert_eq!(restored.head().lineage(), head.lineage());
	assert_eq!(restored.head().generation(), head.generation() + 1);
	assert_ne!(restored.head().digest(), head.digest());
	assert_eq!(unsafe { store_count(RESTORED, 0) }, 2);
	assert_eq!(unsafe { store_count(RESTORED, 1) }, 1);
	drop(restored);
	assert_eq!(unsafe { store_count(RESTORED, 2) }, 1);

	unsafe { configure_store(REJECTED, REJECTED, 1) };
	assert!(matches!(
		PersistentServer::create(19, Some(&[9; 32]), HostStore(REJECTED)),
		Err(PersistenceError::StaleGeneration)
	));
	assert_eq!(unsafe { store_count(REJECTED, 1) }, 1);
	assert_eq!(unsafe { store_count(REJECTED, 2) }, 1);

	unsafe { configure_store(INVALID_SEED, INVALID_SEED, 0) };
	assert!(matches!(
		PersistentServer::create(19, Some(&[9; 31]), HostStore(INVALID_SEED)),
		Err(PersistenceError::Initialization)
	));
	assert_eq!(unsafe { store_count(INVALID_SEED, 1) }, 0);
	assert_eq!(unsafe { store_count(INVALID_SEED, 2) }, 1);
}

#[cfg(target_arch = "wasm32")]
#[test]
fn snapshot_load_copies_one_complete_read_and_requires_the_exact_returned_length() {
	let server = PersistentServer::create(19, Some(&[9; 32]), MemoryStore::default()).unwrap();
	let snapshot = server.snapshot().unwrap();
	let length = snapshot.as_bytes().len() as i64;
	for copied in [-2, -1, length - 1, length, length + 1] {
		let mut calls = 0;
		let loaded = store::load_snapshot(|ptr, capacity| {
			calls += 1;
			if calls == 1 {
				assert_eq!((ptr, capacity), (0, 0));
				return snapshot.as_bytes().len() as i64;
			}
			assert_ne!(ptr, 0);
			assert_eq!(capacity as usize, snapshot.as_bytes().len());
			// This callback executes in actual wasm32 memory, so the guest pointer is lossless.
			let output =
				unsafe { std::slice::from_raw_parts_mut(ptr as *mut u8, capacity as usize) };
			output.copy_from_slice(snapshot.as_bytes());
			copied
		})
		.unwrap();
		assert_eq!(calls, 2);
		if copied == length {
			assert_eq!(loaded.as_bytes(), snapshot.as_bytes());
			assert_eq!(loaded.head().unwrap(), snapshot.head().unwrap());
		} else {
			assert!(loaded.as_bytes().is_empty());
			assert_eq!(loaded.head(), Err(PersistenceError::InvalidSnapshot));
		}
	}
}

#[cfg(target_arch = "wasm32")]
#[test]
fn snapshot_load_rejects_lengths_above_the_guest_slice_bound_without_copying() {
	for length in [i64::from(i32::MAX) + 1, i64::from(u32::MAX)] {
		let mut calls = 0;
		let invalid = store::load_snapshot(|ptr, capacity| {
			calls += 1;
			assert_eq!((ptr, capacity), (0, 0));
			length
		})
		.unwrap();
		assert_eq!(calls, 1);
		assert!(invalid.as_bytes().is_empty());
	}
}

// The WASI runner executes this probe in isolation and requires an allocation-failure trap.
// Its 256 MiB memory limit makes the largest admissible slice fail without allocating 2 GiB.
#[cfg(target_arch = "wasm32")]
#[test]
fn snapshot_load_max_length_allocation_failure_probe() {
	let _ = store::load_snapshot(|ptr, capacity| {
		assert_eq!((ptr, capacity), (0, 0));
		i64::from(i32::MAX)
	});
}
