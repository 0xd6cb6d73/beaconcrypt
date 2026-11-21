// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::authentication::{
	self, AuthRole, InitFields, ResponseFields, assemble_associated_data, build_init_transcript,
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
		*b"beaconcrypt ML-DSA-65 init transcript v2\0"
	);
	assert_eq!(
		authentication::RESPONSE_DOMAIN,
		*b"beaconcrypt ML-DSA-65 response transcript v2\0"
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
	assert_eq!(authentication::INIT_TRANSCRIPT_LEN, 3543);
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
	let server_ml = patterned::<1952>(173);
	let server_ed = patterned::<32>(211);
	for server_id in [0, 42, 0x0123_4567_89ab_cdef, u64::MAX] {
		let actual = build_init_transcript(
			InitFields {
				identity_key: &identity,
				pre_key: &prekey,
				one_time_key: &one_time,
				pq_key: &pq,
			},
			server_id,
			&server_ed,
			&server_ml,
		);
		let mut expected = b"beaconcrypt ML-DSA-65 init transcript v2\0".to_vec();
		expected.extend_from_slice(&server_id.to_le_bytes());
		expected.extend_from_slice(&server_ed);
		expected.extend_from_slice(&server_ml);
		for field in [&identity[..], &prekey, &one_time, &pq] {
			append_field(&mut expected, field);
		}
		assert_eq!(expected.len(), 3543);
		assert_eq!(actual.as_slice(), expected);
		assert_eq!(&actual[41..49], &server_id.to_le_bytes());
		assert_eq!(&actual[49..81], &server_ed);
		assert_eq!(&actual[81..2033], &server_ml);
		assert_eq!(&actual[2033..2041], &33_u64.to_le_bytes());
		assert_eq!(&actual[2074..2082], &98_u64.to_le_bytes());
		assert_eq!(&actual[2180..2188], &98_u64.to_le_bytes());
		assert_eq!(&actual[2286..2294], &1249_u64.to_le_bytes());
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
		let mut expected = b"beaconcrypt ML-DSA-65 response transcript v2\0".to_vec();
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
			let mut expected = b"beaconcrypt ML-DSA-65 response transcript v2\0".to_vec();
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
fn associated_data_retains_the_exact_context_before_the_single_transcript_digest() {
	let hash = patterned::<64>(149);
	let actual = assemble_associated_data(&hash);
	let mut expected = b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768".to_vec();
	expected.extend_from_slice(b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305");
	assert_eq!(expected.len(), 87);
	assert_eq!(&authentication::AD_CONTEXT[..], expected);
	expected.extend_from_slice(&hash);
	assert_eq!(actual.len(), 151);
	assert_eq!(actual.as_slice(), expected);
	assert_eq!(&actual[87..151], &hash);
}

#[test]
fn ratchet_kdf_labels_differ_from_the_retained_ad_context_component() {
	use beaconcrypt_core::{INITIAL_RATCHET_INFO, SYM_RATCHET_INFO, pqxdh::PQXDH_INFO};
	let (pqxdh, old41) = authentication::AD_CONTEXT.split_at(PQXDH_INFO.len());
	assert_eq!(pqxdh, PQXDH_INFO);
	assert_eq!(old41, b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305");
	assert_eq!(old41, &authentication::AD_CONTEXT[46..87]);
	assert_eq!(
		INITIAL_RATCHET_INFO,
		b"SymRatchetInit_HKDF_SHA-512_CHACHA20_POLY1305"
	);
	assert_eq!(
		SYM_RATCHET_INFO,
		b"SymRatchetMessage_HKDF_SHA-512_CHACHA20_POLY1305"
	);
	assert_ne!(INITIAL_RATCHET_INFO.as_slice(), old41);
	assert_ne!(SYM_RATCHET_INFO.as_slice(), old41);
	assert_ne!(INITIAL_RATCHET_INFO.as_slice(), SYM_RATCHET_INFO.as_slice());
	assert_ne!(INITIAL_RATCHET_INFO.as_slice(), PQXDH_INFO.as_slice());
	assert_ne!(SYM_RATCHET_INFO.as_slice(), PQXDH_INFO.as_slice());
}

#[test]
fn record_ad_encoder_preserves_exact_signed_buffers_and_all_fixed_response_fields() {
	use authentication::{AdResponseFields, build_record_ad_transcript};
	let identity = patterned::<33>(11);
	let prekey = patterned::<98>(23);
	let one_time = patterned::<98>(47);
	let pq = patterned::<1249>(89);
	let server_ed = patterned::<32>(173);
	let ephemeral = patterned::<32>(211);
	let kem = patterned::<1088>(137);
	for key_id in [0, 1, 255, 256, 0x0123_4567_89ab_cdef, u64::MAX] {
		let encode = |identity: &[u8; 33],
		              prekey: &[u8; 98],
		              one_time: &[u8; 98],
		              pq: &[u8; 1249],
		              server_ed: &[u8; 32],
		              ephemeral: &[u8; 32],
		              kem: &[u8; 1088],
		              key_id| {
			build_record_ad_transcript(
				InitFields {
					identity_key: identity,
					pre_key: prekey,
					one_time_key: one_time,
					pq_key: pq,
				},
				AdResponseFields {
					identity_key: server_ed,
					ephemeral_key: ephemeral,
					kem_cipher_text: kem,
					key_id,
				},
			)
		};
		let actual = encode(
			&identity, &prekey, &one_time, &pq, &server_ed, &ephemeral, &kem, key_id,
		);
		let mut expected = Vec::new();
		for field in [
			&identity[..],
			&prekey,
			&one_time,
			&pq,
			&server_ed,
			&ephemeral,
			&kem,
		] {
			expected.extend_from_slice(field);
		}
		expected.extend_from_slice(&key_id.to_le_bytes());
		assert_eq!(actual.len(), 2638);
		assert_eq!(expected.len(), 2638);
		assert_eq!(actual.as_slice(), expected);
		assert_eq!(&actual[0..33], &identity);
		assert_eq!(&actual[33..131], &prekey);
		assert_eq!(&actual[131..229], &one_time);
		assert_eq!(&actual[229..1478], &pq);
		assert_eq!(&actual[1478..1510], &server_ed);
		assert_eq!(&actual[1510..1542], &ephemeral);
		assert_eq!(&actual[1542..2630], &kem);
		assert_eq!(&actual[2630..2638], &key_id.to_le_bytes());
		// Every byte, including the attached signatures, must affect the exact encoding.
		for field_index in 0..7 {
			let mut fields = [
				identity.to_vec(),
				prekey.to_vec(),
				one_time.to_vec(),
				pq.to_vec(),
				server_ed.to_vec(),
				ephemeral.to_vec(),
				kem.to_vec(),
			];
			for index in 0..fields[field_index].len() {
				fields[field_index][index] ^= 1;
				let changed = encode(
					fields[0].as_slice().try_into().unwrap(),
					fields[1].as_slice().try_into().unwrap(),
					fields[2].as_slice().try_into().unwrap(),
					fields[3].as_slice().try_into().unwrap(),
					fields[4].as_slice().try_into().unwrap(),
					fields[5].as_slice().try_into().unwrap(),
					fields[6].as_slice().try_into().unwrap(),
					key_id,
				);
				assert_ne!(changed, actual, "field {field_index}, byte {index}");
				assert_eq!(
					changed
						.iter()
						.zip(actual)
						.filter(|(a, b)| **a != *b)
						.count(),
					1
				);
				fields[field_index][index] ^= 1;
			}
		}
		for bit in 0..64 {
			assert_ne!(
				actual,
				encode(
					&identity,
					&prekey,
					&one_time,
					&pq,
					&server_ed,
					&ephemeral,
					&kem,
					key_id ^ (1 << bit)
				)
			);
		}
	}
}
