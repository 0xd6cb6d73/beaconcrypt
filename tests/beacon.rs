use beaconcrypt::*;

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
fn beacon_can_catch_up() {
	let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
	let server_id = server.identity_pk().to_owned();

	let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let _ = test_register_pqxdh_beacon(&mut server, &mut b1);
	assert!(server.pk_by_kid(1).is_some());

	let message = [0xFFu8; 32];
	let b1_m1 = server.encrypt_message(&message, 1).unwrap();
	let b1_m2 = server.encrypt_message(&message, 1).unwrap();
	assert_ne!(b1_m1, b1_m2);

	let dec_b1_m1 = b1.decrypt_message(&b1_m1, 0).unwrap();
	let dec_b1_m2 = b1.decrypt_message(&b1_m2, 0).unwrap();
	assert_eq!(dec_b1_m1, dec_b1_m2);
}
