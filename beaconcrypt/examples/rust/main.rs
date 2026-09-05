// SPDX-License-Identifier: 0BSD

use std::{
	fs::{self, File},
	io::Write,
	path::{Path, PathBuf},
};

use beaconcrypt::{
	Beacon, ED25519_SEED_SIZE, PersistentServer, ProviderBeacon, ServerSnapshot, SnapshotHead,
	SnapshotStore,
};

const SERVER_KID: u64 = 0;
const REGISTRATION_MESSAGE: &[u8] = b"registration ok";

/// Minimal single-process file store for the example.
///
/// A production implementation must additionally coordinate concurrent processes and place the
/// file in a rollback-resistant trust domain. Snapshot bytes are plaintext secret material.
#[derive(Clone)]
struct FileSnapshotStore {
	path: PathBuf,
}

impl SnapshotStore for FileSnapshotStore {
	fn load(&self) -> Option<ServerSnapshot> {
		fs::read(&self.path).ok().map(ServerSnapshot::from_bytes)
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		let current = match fs::read(&self.path) {
			Ok(bytes) => match ServerSnapshot::from_bytes(bytes).head() {
				Ok(head) => Some(head),
				Err(_) => return false,
			},
			Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
			Err(_) => return false,
		};
		if current.as_ref() != expected {
			return false;
		}
		if replacement.validate_successor(expected).is_err() {
			return false;
		}

		let Ok(mut file) = File::create(&self.path) else {
			return false;
		};
		file.write_all(replacement.as_bytes()).is_ok() && file.sync_all().is_ok()
	}
}

#[derive(serde::Deserialize)]
struct StateUpdate {
	kid: u64,
	seq: u64,
	state: String,
	data: Vec<u8>,
}

fn deserialize_state_update(serialized: &str) -> StateUpdate {
	serde_json::from_str(serialized).expect("failed to deserialize state update")
}

fn main() {
	libsodium_rs::ensure_init().expect("failed to initialize libsodium");
	let server_seed = libsodium_rs::random::bytes(ED25519_SEED_SIZE);
	let state_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/rust/server-state.bin");
	let store = FileSnapshotStore {
		path: state_path.clone(),
	};
	let _ = fs::remove_file(&state_path);
	let mut server = PersistentServer::create(SERVER_KID, Some(&server_seed), store.clone())
		.expect("failed to create persistent server");

	// It is assumed that the server's public key is compiled into beacons.
	let mut beacon = Beacon::try_new(SERVER_KID, server.identity_pk().as_bytes())
		.expect("failed to create beacon");
	let transport = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/rust/transport");

	// The beacon is run and registers.
	let b_reg_1 = beacon
		.get_registration_bundle()
		.expect("failed to generate registration");
	// Ship the registration bytes over whichever transport you like.
	fs::write(&transport, b_reg_1).expect("failed to write registration to transport");
	let s_reg_1 = fs::read(&transport).expect("failed to read registration from transport");

	// Now the server has the registration message and can send an initial message if needed.
	let registration = server
		.get_shared_secret(&s_reg_1)
		.expect("failed to save registration state")
		.expect("failed to process registration");
	let s_reg_resp = server
		.build_registration_response(registration, Some(REGISTRATION_MESSAGE))
		.expect("failed to save registration response state")
		.expect("failed to build registration response");
	// Ship the response back over your transport.
	fs::write(&transport, &s_reg_resp.serialized)
		.expect("failed to write registration response to transport");
	let b_reg_1 =
		fs::read(&transport).expect("failed to read registration response from transport");

	// Do whatever you like with the initial message.
	let first_message = beacon
		.finish_registration(&b_reg_1)
		.expect("failed to finish registration");
	println!(
		"Beacon got initial message: {}",
		String::from_utf8_lossy(&first_message)
	);

	// Every PersistentServer mutation above wrote the complete plaintext checkpoint through the
	// store before returning its result. Simulate a restart by dropping the live owner and restoring
	// from that serialized file. Restore itself advances and saves the generation before returning.
	drop(server);
	let mut server = PersistentServer::restore(store.clone())
		.expect("failed to restore server from serialized state");
	println!(
		"Restored server state from {} (generation {})",
		state_path.display(),
		server.head().generation()
	);

	let b_ping = beacon
		.encrypt_message(b"ping")
		.expect("failed to encrypt ping");
	fs::write(&transport, b_ping).expect("failed to write ping to transport");
	let s_ping = fs::read(&transport).expect("failed to read ping from transport");

	// Got the ping, maybe there's a task to send now.
	let ping = server
		.decrypt_and_update_json(&s_ping)
		.expect("failed to save state after decrypting ping")
		.expect("failed to decrypt ping");
	let ping = deserialize_state_update(&ping);
	println!("Server got ping: {}", String::from_utf8_lossy(&ping.data));
	println!("Key ID: {}", ping.kid);
	println!("Consumed key sequence: {}", ping.seq);
	println!("Ratchet state: {}", ping.state);

	// The C2 needs to know what the beacon's ID is so it can encrypt to it.
	let s_task_0 = server
		.encrypt_and_update_json(b"task contents", s_reg_resp.kid)
		.expect("failed to save state after encrypting task")
		.expect("failed to encrypt task");
	let s_task_0 = deserialize_state_update(&s_task_0);
	println!("Key ID: {}", s_task_0.kid);
	println!("Consumed key sequence: {}", s_task_0.seq);
	println!("Ratchet state: {}", s_task_0.state);
	fs::write(&transport, &s_task_0.data).expect("failed to write task to transport");
	let b_task_0 = fs::read(&transport).expect("failed to read task from transport");
	let task_0 = beacon
		.decrypt_message(&b_task_0)
		.expect("failed to decrypt task");
	assert_eq!(task_0.key_id, SERVER_KID);
	println!(
		"Beacon got first task: {}",
		String::from_utf8_lossy(&task_0.plaintext)
	);

	// Process the task and send the response.
	let b_task_1 = beacon
		.encrypt_message(b"task response")
		.expect("failed to encrypt task response");
	fs::write(&transport, b_task_1).expect("failed to write task response to transport");
	let s_task_1 = fs::read(&transport).expect("failed to read task response from transport");
	let task_1 = server
		.decrypt_and_update_json(&s_task_1)
		.expect("failed to save state after decrypting task response")
		.expect("failed to decrypt task response");
	let task_1 = deserialize_state_update(&task_1);
	println!(
		"Server got response to first task: {}",
		String::from_utf8_lossy(&task_1.data)
	);
	println!("Key ID: {}", task_1.kid);
	println!("Consumed key sequence: {}", task_1.seq);
	println!("Ratchet state: {}", task_1.state);

	fs::remove_file(transport).expect("failed to remove transport file");
	fs::remove_file(state_path).expect("failed to remove server state file");
}
