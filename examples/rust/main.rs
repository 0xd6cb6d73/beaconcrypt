// SPDX-License-Identifier: 0BSD

use std::{fs, path::Path};

use beaconcrypt::{
	BeaconCryptPqxdh, CryptoProvider, ED25519_SEED_SIZE, ProviderBeacon, ProviderServer,
};

const SERVER_KID: u64 = 0;
const REGISTRATION_MESSAGE: &[u8] = b"registration ok";

fn main() {
	libsodium_rs::ensure_init().expect("failed to initialize libsodium");
	let server_seed = libsodium_rs::random::bytes(ED25519_SEED_SIZE);
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, Some(&server_seed));

	// It is assumed that the server's public key is compiled into beacons.
	let mut beacon = BeaconCryptPqxdh::new(
		true,
		SERVER_KID,
		Some(server.identity_pk().as_bytes()),
		None,
	);
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
		.expect("failed to process registration");
	let s_reg_resp = server
		.build_registration_response(registration, Some(REGISTRATION_MESSAGE))
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

	let b_ping = beacon
		.encrypt_message(b"ping", SERVER_KID)
		.and_then(|ciphertext| beacon.sign_message(&ciphertext))
		.expect("failed to encrypt and sign ping");
	fs::write(&transport, b_ping).expect("failed to write ping to transport");
	let s_ping = fs::read(&transport).expect("failed to read ping from transport");

	// Got the ping, maybe there's a task to send now.
	let verified_ping = server
		.verify_signature(&s_ping)
		.expect("failed to verify ping signature");
	let ping = server
		.decrypt_message(&verified_ping.data, verified_ping.key_id)
		.expect("failed to decrypt ping");
	println!("Server got ping: {}", String::from_utf8_lossy(&ping));

	// The C2 needs to know what the beacon's ID is so it can encrypt to it.
	let s_task_0 = server
		.encrypt_message(b"task contents", s_reg_resp.kid)
		.and_then(|ciphertext| server.sign_message(&ciphertext))
		.expect("failed to encrypt and sign task");
	fs::write(&transport, s_task_0).expect("failed to write task to transport");
	let b_task_0 = fs::read(&transport).expect("failed to read task from transport");
	let verified_task = beacon
		.verify_signature(&b_task_0)
		.expect("failed to verify task signature");
	let task_0 = beacon
		.decrypt_message(&verified_task.data, verified_task.key_id)
		.expect("failed to decrypt task");
	println!(
		"Beacon got first task: {}",
		String::from_utf8_lossy(&task_0)
	);

	// Process the task and send the response.
	let b_task_1 = beacon
		.encrypt_message(b"task response", SERVER_KID)
		.and_then(|ciphertext| beacon.sign_message(&ciphertext))
		.expect("failed to encrypt and sign task response");
	fs::write(&transport, b_task_1).expect("failed to write task response to transport");
	let s_task_1 = fs::read(&transport).expect("failed to read task response from transport");
	let verified_response = server
		.verify_signature(&s_task_1)
		.expect("failed to verify task response signature");
	let task_1 = server
		.decrypt_message(&verified_response.data, verified_response.key_id)
		.expect("failed to decrypt task response");
	println!(
		"Server got response to first task: {}",
		String::from_utf8_lossy(&task_1)
	);

	fs::remove_file(transport).expect("failed to remove transport file");
}
