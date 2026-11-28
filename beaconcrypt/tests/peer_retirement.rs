use std::{
	num::NonZeroUsize,
	sync::{Arc, Mutex},
};

use beaconcrypt::{
	Beacon, PersistenceError, PersistentServer, ProviderBeacon, ServerSnapshot, SnapshotHead,
	SnapshotStore,
};

#[derive(Default)]
struct StoreState {
	snapshot: Option<Vec<u8>>,
	head: Option<SnapshotHead>,
	fail_next_cas: bool,
}

#[derive(Clone, Default)]
struct MemoryStore(Arc<Mutex<StoreState>>);

impl MemoryStore {
	fn snapshot_len(&self) -> usize {
		self.0.lock().unwrap().snapshot.as_ref().unwrap().len()
	}
	fn fail_next_cas(&self) {
		self.0.lock().unwrap().fail_next_cas = true;
	}
}

impl SnapshotStore for MemoryStore {
	fn load(&self) -> Result<Option<ServerSnapshot>, PersistenceError> {
		Ok(self
			.0
			.lock()
			.unwrap()
			.snapshot
			.clone()
			.map(ServerSnapshot::from_bytes))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, PersistenceError> {
		let mut state = self.0.lock().unwrap();
		if std::mem::take(&mut state.fail_next_cas) || state.head.as_ref() != expected {
			return Ok(false);
		}
		state.head = Some(replacement.head()?);
		state.snapshot = Some(replacement.as_bytes().to_vec());
		Ok(true)
	}
}

fn create() -> (PersistentServer<MemoryStore>, MemoryStore) {
	let store = MemoryStore::default();
	let server =
		PersistentServer::create(7, Some(&[0x41; 32]), Some(&[0x42; 32]), store.clone()).unwrap();
	(server, store)
}

fn beacon(server: &PersistentServer<MemoryStore>) -> Beacon {
	Beacon::new(
		server.identity_key_kid(),
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)
}

fn register(server: &mut PersistentServer<MemoryStore>) -> (Beacon, u64, Vec<u8>) {
	let mut beacon = beacon(server);
	let bundle = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&bundle).unwrap().unwrap();
	let response = server
		.build_registration_response(accepted, Some(b"registered"))
		.unwrap()
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		b"registered"
	);
	(beacon, response.kid, bundle)
}

#[test]
fn retired_peer_is_refused_in_both_directions_and_its_identifier_is_never_reused() {
	let (mut server, store) = create();
	let (mut retired, retired_kid, retired_bundle) = register(&mut server);
	let (mut kept, kept_kid, _) = register(&mut server);
	let inbound = retired
		.encrypt_message(b"after retirement")
		.unwrap()
		.ciphertext;
	let before = server.head();
	let snapshot_before = store.snapshot_len();

	assert_eq!(server.retire_peer(retired_kid), Ok(true));
	assert_eq!(server.head().generation(), before.generation() + 1);
	assert!(store.snapshot_len() < snapshot_before);
	assert_eq!(server.peer_count(), Some(1));
	assert_eq!(server.registration_marker_count(), Some(2));
	assert!(server.pk_by_kid(retired_kid).is_none());

	// Refusals are state-neutral: nothing is committed.
	let retired_head = server.head();
	assert!(server.decrypt_message(&inbound).unwrap().is_none());
	assert!(
		server
			.encrypt_message(b"tasking", retired_kid)
			.unwrap()
			.is_none()
	);
	assert_eq!(server.retire_peer(retired_kid), Ok(false));
	assert_eq!(server.retire_peer(9_999), Ok(false));
	assert_eq!(server.head(), retired_head);

	// The other session is untouched.
	let frame = server.encrypt_message(b"kept", kept_kid).unwrap().unwrap();
	assert_eq!(
		kept.decrypt_message(&frame.ciphertext).unwrap().plaintext,
		b"kept"
	);

	// The replay marker survives, so the retired beacon's registration cannot be replayed.
	assert!(server.get_shared_secret(&retired_bundle).unwrap().is_none());
	let (_, next_kid, _) = register(&mut server);
	assert!(next_kid > kept_kid && next_kid != retired_kid);

	let restored = PersistentServer::restore(store.clone()).unwrap();
	assert_eq!(restored.peer_count(), Some(2));
	assert!(restored.pk_by_kid(retired_kid).is_none());
	assert!(restored.pk_by_kid(kept_kid).is_some());
	assert_eq!(restored.registration_marker_count(), Some(3));
	assert_eq!(restored.server_kid(), next_kid);
	drop(retired);
}

#[test]
fn peer_limit_refuses_acceptance_without_consuming_the_marker() {
	let (mut server, _) = create();
	server.set_max_peers(NonZeroUsize::new(1));
	let (_, first_kid, _) = register(&mut server);
	let mut waiting = beacon(&server);
	let bundle = waiting.get_registration_bundle().unwrap();
	let head = server.head();
	assert!(matches!(
		server.get_shared_secret(&bundle),
		Err(PersistenceError::CapacityExceeded)
	));
	assert!(!server.is_poisoned());
	assert_eq!(server.head(), head);
	assert_eq!(server.registration_marker_count(), Some(1));

	// Retiring frees capacity, and the refused registration can be retried unchanged.
	assert_eq!(server.retire_peer(first_kid), Ok(true));
	let accepted = server.get_shared_secret(&bundle).unwrap().unwrap();
	let response = server
		.build_registration_response(accepted, Some(b"late"))
		.unwrap()
		.unwrap();
	assert_eq!(
		waiting.finish_registration(&response.serialized).unwrap(),
		b"late"
	);
	assert_eq!(server.peer_count(), Some(1));
}

#[test]
fn peer_limit_is_checked_again_at_completion() {
	let (mut server, _) = create();
	assert_eq!(server.max_peers(), None);
	server.set_max_peers(NonZeroUsize::new(1));
	assert_eq!(server.max_peers(), NonZeroUsize::new(1));
	let mut first = beacon(&server);
	let mut second = beacon(&server);
	let first_accepted = server
		.get_shared_secret(&first.get_registration_bundle().unwrap())
		.unwrap()
		.unwrap();
	let second_accepted = server
		.get_shared_secret(&second.get_registration_bundle().unwrap())
		.unwrap()
		.unwrap();
	let response = server
		.build_registration_response(first_accepted, None)
		.unwrap()
		.unwrap();
	first.finish_registration(&response.serialized).unwrap();
	let head = server.head();
	assert!(matches!(
		server.build_registration_response(second_accepted, None),
		Err(PersistenceError::CapacityExceeded)
	));
	assert!(!server.is_poisoned());
	assert_eq!(server.head(), head);
	assert_eq!(server.peer_count(), Some(1));
	assert_eq!(server.registration_marker_count(), Some(2));
	server.set_max_peers(None);
	assert_eq!(server.max_peers(), None);
}

#[test]
fn failed_retirement_commit_poisons_the_owner_and_restore_keeps_the_peer() {
	let (mut server, store) = create();
	let (_, kid, _) = register(&mut server);
	store.fail_next_cas();
	assert_eq!(
		server.retire_peer(kid),
		Err(PersistenceError::StaleGeneration)
	);
	assert!(server.is_poisoned());
	assert_eq!(server.peer_count(), None);
	assert_eq!(server.retire_peer(kid), Err(PersistenceError::Poisoned));
	let restored = PersistentServer::restore(store).unwrap();
	assert!(restored.pk_by_kid(kid).is_some());
	assert_eq!(restored.peer_count(), Some(1));
}
