// SPDX-License-Identifier: 0BSD

#![cfg(all(
	feature = "pqxdh",
	feature = "beacon",
	feature = "server",
	feature = "std"
))]

use std::sync::{Arc, Mutex};

use beaconcrypt::{
	Beacon, PersistenceError, PersistentServer, ProviderBeacon, ServerSnapshot, SnapshotHead,
	SnapshotStore,
};

#[derive(Default)]
struct State {
	bytes: Option<Vec<u8>>,
	head: Option<SnapshotHead>,
	writes: usize,
	read_error: Option<PersistenceError>,
	write_error: Option<(PersistenceError, bool)>,
}

#[derive(Clone, Default)]
struct Store(Arc<Mutex<State>>);

impl SnapshotStore for Store {
	fn load(&self) -> Result<Option<ServerSnapshot>, PersistenceError> {
		let state = self.0.lock().unwrap();
		if let Some(error) = state.read_error {
			return Err(error);
		}
		Ok(state.bytes.clone().map(ServerSnapshot::from_bytes))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, PersistenceError> {
		let mut state = self.0.lock().unwrap();
		state.writes += 1;
		if state.head.as_ref() != expected {
			return Ok(false);
		}
		let head = replacement.validate_successor(expected)?;
		let failure = state.write_error.take();
		if failure.is_none_or(|(_, published)| published) {
			state.bytes = Some(replacement.as_bytes().to_vec());
			state.head = Some(head);
		}
		match failure {
			Some((error, _)) => Err(error),
			None => Ok(true),
		}
	}
}

fn server(store: Store) -> PersistentServer<Store> {
	PersistentServer::create(19, Some(&[7; 32]), Some(&[8; 32]), store).unwrap()
}

fn beacon(server: &PersistentServer<Store>) -> Beacon {
	Beacon::new(
		19,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)
}

fn register(server: &mut PersistentServer<Store>, beacon: &mut Beacon) -> (Vec<u8>, u64) {
	let request = beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&request).unwrap().unwrap();
	let response = server
		.build_registration_response(pending, None)
		.unwrap()
		.unwrap();
	beacon.finish_registration(&response.serialized).unwrap();
	(request, response.kid)
}

#[test]
fn unchanged_registration_and_send_rejections_do_not_write() {
	let store = Store::default();
	let mut server = server(store.clone());
	let mut peer = beacon(&server);
	let (accepted, kid) = register(&mut server, &mut peer);
	let mut rejected_peer = beacon(&server);
	let rejected_request = rejected_peer.get_registration_bundle().unwrap();
	let pending = server
		.get_shared_secret(&rejected_request)
		.unwrap()
		.unwrap();
	let before = server.head();
	let writes = store.0.lock().unwrap().writes;
	let bytes = server.snapshot().unwrap().as_bytes().to_vec();
	for request in [&[][..], b"invalid registration".as_slice(), &accepted] {
		assert!(server.get_shared_secret(request).unwrap().is_none());
	}
	assert!(
		server
			.build_registration_response(pending, Some(&[]))
			.unwrap()
			.is_none()
	);
	assert!(
		server
			.encrypt_message(b"unknown peer", kid + 100)
			.unwrap()
			.is_none()
	);
	assert!(server.encrypt_message(&[], kid).unwrap().is_none());
	assert!(server.encrypt_and_update(&[], kid).unwrap().is_none());
	assert!(server.encrypt_and_update_json(&[], kid).unwrap().is_none());
	assert_eq!(server.head(), before);
	assert_eq!(store.0.lock().unwrap().writes, writes);
	assert_eq!(server.snapshot().unwrap().as_bytes(), bytes);
	assert!(!server.is_poisoned());
}

#[test]
fn read_and_creation_errors_are_distinct_from_absence_and_conflict() {
	for error in [PersistenceError::Storage, PersistenceError::CommitUnknown] {
		let store = Store::default();
		store.0.lock().unwrap().read_error = Some(error);
		assert_eq!(PersistentServer::restore(store).err(), Some(error));
		let store = Store::default();
		store.0.lock().unwrap().write_error = Some((error, false));
		assert_eq!(
			PersistentServer::create(19, Some(&[7; 32]), Some(&[8; 32]), store).err(),
			Some(error)
		);
	}
	assert_eq!(
		PersistentServer::restore(Store::default()).err(),
		Some(PersistenceError::MissingSnapshot)
	);
	let store = Store::default();
	let server = server(store.clone());
	store.0.lock().unwrap().read_error = Some(PersistenceError::Storage);
	assert_eq!(server.snapshot().err(), Some(PersistenceError::Storage));
	assert!(!server.is_poisoned());
}

#[test]
fn registration_storage_failures_withhold_tokens_and_poison_the_owner() {
	for error in [PersistenceError::Storage, PersistenceError::CommitUnknown] {
		let store = Store::default();
		let mut server = server(store.clone());
		let mut beacon = beacon(&server);
		let request = beacon.get_registration_bundle().unwrap();
		let before = server.head();
		store.0.lock().unwrap().write_error = Some((error, false));
		assert_eq!(server.get_shared_secret(&request).err(), Some(error));
		assert_eq!(server.head(), before);
		assert!(server.is_poisoned());
		assert_eq!(
			server.get_shared_secret(&request).err(),
			Some(PersistenceError::Poisoned)
		);
	}
}

#[test]
fn uncertain_receive_commits_withhold_all_outputs_and_restore_authoritative_consumption() {
	for api in 0..3 {
		for published in [false, true] {
			let store = Store::default();
			let mut server = server(store.clone());
			let mut beacon = beacon(&server);
			register(&mut server, &mut beacon);
			let frame = beacon.encrypt_message(b"withheld private payload").unwrap();
			let before = server.head();
			store.0.lock().unwrap().write_error =
				Some((PersistenceError::CommitUnknown, published));
			let error = match api {
				0 => server.decrypt_message(&frame).err(),
				1 => server.decrypt_and_update(&frame).err(),
				_ => server.decrypt_and_update_json(&frame).err(),
			};
			assert_eq!(error, Some(PersistenceError::CommitUnknown));
			assert_eq!(server.head(), before);
			assert!(server.is_poisoned());
			let mut restored = PersistentServer::restore(store).unwrap();
			let opened = restored.decrypt_message(&frame).unwrap();
			if published {
				assert!(opened.is_none());
			} else {
				assert_eq!(opened.unwrap().plaintext, b"withheld private payload");
			}
		}
	}
}

#[test]
fn consumed_registration_stays_rejected_across_v4_restores_and_old_versions_never_reset_it() {
	let store = Store::default();
	let mut server = server(store.clone());
	let mut peer = beacon(&server);
	let (request, kid) = register(&mut server, &mut peer);
	assert!(server.get_shared_secret(&request).unwrap().is_none());
	drop(server);
	let current = store.0.lock().unwrap().bytes.clone().unwrap();
	assert_eq!(current[16..18], 4u16.to_le_bytes());

	// An envelope from a previous version is refused; it never activates as a fresh ledger.
	for version in [0u16, 1, 2, 3] {
		let mut legacy = current.clone();
		legacy[16..18].copy_from_slice(&version.to_le_bytes());
		let writes = {
			let mut state = store.0.lock().unwrap();
			state.bytes = Some(legacy.clone());
			state.writes
		};
		assert_eq!(
			PersistentServer::restore(store.clone()).err(),
			Some(PersistenceError::InvalidSnapshot),
			"version {version}"
		);
		let state = store.0.lock().unwrap();
		assert_eq!(state.writes, writes);
		assert_eq!(state.bytes.as_deref(), Some(legacy.as_slice()));
	}
	store.0.lock().unwrap().bytes = Some(current);

	for _ in 0..2 {
		let mut restored = PersistentServer::restore(store.clone()).unwrap();
		let head = restored.head();
		let writes = store.0.lock().unwrap().writes;
		assert!(restored.get_shared_secret(&request).unwrap().is_none());
		assert_eq!(restored.head(), head);
		assert_eq!(store.0.lock().unwrap().writes, writes);
		let frame = peer.encrypt_message(b"restored session").unwrap();
		assert_eq!(
			restored.decrypt_message(&frame).unwrap().unwrap().plaintext,
			b"restored session"
		);
	}
	let mut restored = PersistentServer::restore(store).unwrap();
	let mut next = beacon(&restored);
	assert_eq!(register(&mut restored, &mut next).1, kid + 1);
	assert!(restored.get_shared_secret(&request).unwrap().is_none());
}
