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
		.expect("failed to encrypt ping");
	fs::write(&transport, b_ping).expect("failed to write ping to transport");
	let s_ping = fs::read(&transport).expect("failed to read ping from transport");

	// Got the ping, maybe there's a task to send now.
	let ping = server
		.decrypt_and_update(&s_ping)
		.expect("failed to decrypt ping");
	println!("Server got ping: {}", String::from_utf8_lossy(&ping.data));
	println!("Key ID: {}", ping.kid);
	println!("Ratchet state: {:?}", ping.key.as_slice());

	// The C2 needs to know what the beacon's ID is so it can encrypt to it.
	let s_task_0 = server
		.encrypt_and_update(b"task contents", s_reg_resp.kid)
		.expect("failed to encrypt task");
	println!("Key ID: {}", s_task_0.kid);
	println!("Ratchet state: {:?}", s_task_0.key.as_slice());
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
		.encrypt_message(b"task response", SERVER_KID)
		.expect("failed to encrypt task response");
	fs::write(&transport, b_task_1).expect("failed to write task response to transport");
	let s_task_1 = fs::read(&transport).expect("failed to read task response from transport");
	let task_1 = server
		.decrypt_and_update(&s_task_1)
		.expect("failed to decrypt task response");
	println!(
		"Server got response to first task: {}",
		String::from_utf8_lossy(&task_1.data)
	);
	println!("Key ID: {}", task_1.kid);
	println!("Ratchet state: {:?}", task_1.key.as_slice());

	fs::remove_file(transport).expect("failed to remove transport file");
}
