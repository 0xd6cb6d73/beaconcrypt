// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "beacon", feature = "server"))]

use beaconcrypt::{Beacon, ProviderBeacon, ProviderServer, Server};

#[test]
fn fallible_constructors_reject_incorrect_lengths() {
	for length in [0, 1, 31, 33, 64] {
		let bytes = vec![7; length];
		assert!(Server::try_new(19, Some(&bytes)).is_err());
		assert!(Beacon::try_new(19, &bytes).is_err());
	}
}

#[test]
fn fallible_construction_preserves_identity_and_registration() {
	let seed = [9; 32];
	let mut server = Server::try_new(19, Some(&seed)).unwrap();
	let same_identity = Server::try_new(19, Some(&seed)).unwrap();
	assert_eq!(server.identity_pk(), same_identity.identity_pk());
	assert_eq!(server.server_kid(), 19);
	let mut beacon = Beacon::try_new(19, server.identity_pk().as_bytes()).unwrap();
	assert_eq!(beacon.server_kid(), 19);
	assert_eq!(beacon.server_id(), server.identity_pk());
	let bundle = beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&bundle).unwrap();
	let response = server
		.build_registration_response(pending, Some(b"constructor roundtrip"))
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		b"constructor roundtrip"
	);
	assert_ne!(
		Server::try_new(19, None).unwrap().identity_pk(),
		server.identity_pk()
	);
}
