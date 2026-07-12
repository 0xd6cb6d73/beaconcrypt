use beaconcrypt::*;
use libsodium_rs::crypto_sign;

fn test_register_pqxdh_beacon(
	server: &mut BeaconCryptPqxdh,
	beacon: &mut BeaconCryptPqxdh,
) -> Vec<u8> {
	let message = [0xFFu8; 32];

	let phase_1 = beacon.get_registration_bundle().unwrap();
	let reg_out = server.get_shared_secret(&phase_1).unwrap();
	let phase2 = server
		.build_registration_response(reg_out, Some(&message))
		.unwrap();
	beacon.finish_registration(&phase2.serialized).unwrap()
}

#[test]
fn server_from_seed() {
	let empty = [0u8; ED25519_SEED_SIZE];
	let seeded = crypto_sign::KeyPair::from_seed(&empty).unwrap();
	let server = BeaconCryptPqxdh::new(false, 0, None, Some(&empty));
	assert_eq!(
		seeded.secret_key.as_bytes(),
		server.identity_sk().as_bytes()
	);
	assert_eq!(
		seeded.public_key.as_bytes(),
		server.identity_pk().as_bytes()
	);
}

#[test]
fn server_can_register_multiple() {
	let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
	let server_id = server.identity_pk().to_owned();

	let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let b1_reg = test_register_pqxdh_beacon(&mut server, &mut b1);
	let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let b2_reg = test_register_pqxdh_beacon(&mut server, &mut b2);

	assert_eq!(b1_reg, b2_reg);
}
