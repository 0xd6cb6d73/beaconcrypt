// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::authentication::{
	self, AuthRole, InitFields, ResponseFields, bind_associated_data, build_init_transcript,
	build_response_prefix, build_response_transcript, build_signature_input, encode_u64_le,
};

fn patterned<const N: usize>(offset: u8) -> [u8; N] {
	core::array::from_fn(|index| (index as u8).wrapping_mul(29).wrapping_add(offset))
}

// This is the former adapter formula, assembled independently with std's LE64
// conversion. Keep its literal domains separate from the implementation constants.
fn append_field(output: &mut Vec<u8>, field: &[u8]) {
	output.extend_from_slice(&(field.len() as u64).to_le_bytes());
	output.extend_from_slice(field);
}

#[test]
fn constants_and_integer_encoding_match_the_deployed_transcript() {
	assert_eq!(
		authentication::INIT_DOMAIN,
		*b"beaconcrypt ML-DSA-65 init transcript v1\0"
	);
	assert_eq!(
		authentication::RESPONSE_DOMAIN,
		*b"beaconcrypt ML-DSA-65 response transcript v1\0"
	);
	assert_eq!(
		authentication::SIGNING_CONTEXT,
		*b"beaconcrypt registration auth v1"
	);
	assert_eq!(
		authentication::BEACON_LABEL,
		*b"beaconcrypt v1 beacon registration"
	);
	assert_eq!(
		authentication::SERVER_LABEL,
		*b"beaconcrypt v1 server registration"
	);
	assert_eq!(authentication::MLDSA_PUBLIC_KEY_LEN, 1952);
	assert_eq!(authentication::MLDSA_SIGNATURE_LEN, 3309);
	assert_eq!(authentication::TRANSCRIPT_HASH_LEN, 64);
	assert_eq!(authentication::INIT_TRANSCRIPT_LEN, 5495);
	assert_eq!(authentication::RESPONSE_PREFIX_LEN, 1293);
	assert_eq!(authentication::SIGNATURE_INPUT_LEN, 163);
	for value in [
		0,
		1,
		255,
		256,
		u32::MAX as u64,
		0x0123_4567_89ab_cdef,
		u64::MAX,
	] {
		assert_eq!(encode_u64_le(value), value.to_le_bytes());
	}
}

#[test]
fn init_bytes_match_the_prior_adapter_formula_at_every_offset() {
	let identity = patterned::<33>(11);
	let prekey = patterned::<98>(23);
	let one_time = patterned::<98>(47);
	let pq = patterned::<1249>(89);
	let beacon_ml = patterned::<1952>(131);
	let server_ml = patterned::<1952>(173);
	let server_ed = patterned::<32>(211);
	for server_id in [0, 42, 0x0123_4567_89ab_cdef, u64::MAX] {
		let actual = build_init_transcript(
			InitFields {
				identity_key: &identity,
				pre_key: &prekey,
				one_time_key: &one_time,
				pq_key: &pq,
				mldsa_public_key: &beacon_ml,
			},
			server_id,
			&server_ed,
			&server_ml,
		);
		let mut expected = b"beaconcrypt ML-DSA-65 init transcript v1\0".to_vec();
		expected.extend_from_slice(&server_id.to_le_bytes());
		expected.extend_from_slice(&server_ed);
		expected.extend_from_slice(&beacon_ml);
		expected.extend_from_slice(&server_ml);
		for field in [&identity[..], &prekey, &one_time, &pq] {
			append_field(&mut expected, field);
		}
		assert_eq!(expected.len(), 5495);
		assert_eq!(actual.as_slice(), expected);
		assert_eq!(&actual[41..49], &server_id.to_le_bytes());
		assert_eq!(&actual[49..81], &server_ed);
		assert_eq!(&actual[81..2033], &beacon_ml);
		assert_eq!(&actual[2033..3985], &server_ml);
		assert_eq!(&actual[3985..3993], &33_u64.to_le_bytes());
		assert_eq!(&actual[4026..4034], &98_u64.to_le_bytes());
		assert_eq!(&actual[4132..4140], &98_u64.to_le_bytes());
		assert_eq!(&actual[4238..4246], &1249_u64.to_le_bytes());
	}
}

#[test]
fn response_prefix_encodes_all_numeric_application_lengths_without_allocation() {
	let init_hash = patterned::<64>(7);
	let identity = patterned::<32>(19);
	let ephemeral = patterned::<32>(41);
	let kem = patterned::<1088>(83);
	for app_len in [0, 1, 23, 24, 255, 256, 65_535, 65_536, 33_554_432, u64::MAX] {
		let actual = build_response_prefix(&init_hash, &identity, &ephemeral, &kem, app_len);
		let mut expected = b"beaconcrypt ML-DSA-65 response transcript v1\0".to_vec();
		expected.extend_from_slice(&init_hash);
		for field in [&identity[..], &ephemeral, &kem] {
			append_field(&mut expected, field);
		}
		expected.extend_from_slice(&app_len.to_le_bytes());
		assert_eq!(expected.len(), 1293);
		assert_eq!(actual.as_slice(), expected);
		assert_eq!(&actual[45..109], &init_hash);
		assert_eq!(&actual[109..117], &32_u64.to_le_bytes());
		assert_eq!(&actual[149..157], &32_u64.to_le_bytes());
		assert_eq!(&actual[189..197], &1088_u64.to_le_bytes());
		assert_eq!(&actual[1285..1293], &app_len.to_le_bytes());
	}
}

#[test]
fn response_parts_stream_the_original_ciphertext_between_prefix_and_identifier() {
	let init_hash = patterned::<64>(13);
	let identity = patterned::<32>(31);
	let ephemeral = patterned::<32>(61);
	let kem = patterned::<1088>(127);
	for app_len in [0, 1, 23, 24, 255, 256, 65_535, 65_536] {
		let app = (0..app_len)
			.map(|index| (index as u8).wrapping_mul(37))
			.collect::<Vec<_>>();
		for key_id in [0, 42, 0x0123_4567_89ab_cdef, u64::MAX] {
			let transcript = build_response_transcript(
				&init_hash,
				ResponseFields {
					identity_key: &identity,
					ephemeral_key: &ephemeral,
					kem_cipher_text: &kem,
					app_cipher_text: &app,
					key_id,
				},
			)
			.unwrap();
			let parts = transcript.parts();
			assert_eq!(parts[0].len(), 1293);
			assert_eq!(parts[1], app);
			assert_eq!(parts[1].as_ptr(), app.as_ptr());
			assert_eq!(parts[2], key_id.to_le_bytes());
			let mut expected = b"beaconcrypt ML-DSA-65 response transcript v1\0".to_vec();
			expected.extend_from_slice(&init_hash);
			for field in [&identity[..], &ephemeral, &kem, &app] {
				append_field(&mut expected, field);
			}
			expected.extend_from_slice(&key_id.to_le_bytes());
			assert_eq!(parts.concat(), expected);
		}
	}
}

#[test]
fn signature_input_matches_the_prior_tls_style_formula_for_both_roles() {
	let hash = patterned::<64>(197);
	for (role, label) in [
		(AuthRole::Beacon, b"beaconcrypt v1 beacon registration"),
		(AuthRole::Server, b"beaconcrypt v1 server registration"),
	] {
		let actual = build_signature_input(role, &hash);
		let mut expected = vec![b' '; 64];
		expected.extend_from_slice(label);
		expected.push(0);
		expected.extend_from_slice(&hash);
		assert_eq!(expected.len(), 163);
		assert_eq!(actual.as_slice(), expected);
		assert_eq!(&actual[..64], &[b' '; 64]);
		assert_eq!(actual[98], 0);
		assert_eq!(&actual[99..], &hash);
	}
}

#[test]
fn associated_data_preserves_the_prefix_and_replaces_both_reserved_hash_slots() {
	let base = patterned::<281>(17);
	let server_hash = patterned::<64>(71);
	let beacon_hash = patterned::<64>(149);
	let original = base;
	let actual = bind_associated_data(&base, &server_hash, &beacon_hash);
	let mut expected = base[..153].to_vec();
	expected.extend_from_slice(&server_hash);
	expected.extend_from_slice(&beacon_hash);
	assert_eq!(actual.as_slice(), expected);
	assert_eq!(&actual[..153], &base[..153]);
	assert_eq!(&actual[153..217], &server_hash);
	assert_eq!(&actual[217..281], &beacon_hash);
	assert_eq!(base, original);
}
