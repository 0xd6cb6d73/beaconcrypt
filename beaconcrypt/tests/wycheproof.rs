#[cfg(all(windows, target_env = "gnu"))]
#[path = "common/sodium_oracle.rs"]
mod sodium_oracle;

use std::{collections::BTreeSet, fs, path::Path};

use beaconcrypt_crypto::{
	crypto_aead::chacha20poly1305_ietf, crypto_kdf, crypto_kem::mlkem768, crypto_scalarmult,
	crypto_sign,
};
use libsodium_rs::{crypto_kem::mlkem768 as sodium_mlkem, crypto_sign as sodium_sign};
use serde::Deserialize;

const X25519_VECTORS: &str = include_str!("../../wycheproof/testvectors_v1/x25519_test.json");
const ED25519_VECTORS: &str = include_str!("../../wycheproof/testvectors_v1/ed25519_test.json");
const ED25519_TO_X25519_VECTORS: &str =
	include_str!("../../wycheproof/testvectors_v1/ed25519_to_x25519_test.json");
const CHACHA20_POLY1305_VECTORS: &str =
	include_str!("../../wycheproof/testvectors_v1/chacha20_poly1305_test.json");
const HKDF_SHA512_VECTORS: &str =
	include_str!("../../wycheproof/testvectors_v1/hkdf_sha512_test.json");
const MLKEM768_VECTORS: &str = include_str!("../../wycheproof/testvectors_v1/mlkem_768_test.json");
const MLKEM768_ENCAPS_VECTORS: &str =
	include_str!("../../wycheproof/testvectors_v1/mlkem_768_encaps_test.json");
const MLKEM768_KEYGEN_VECTORS: &str =
	include_str!("../../wycheproof/testvectors_v1/mlkem_768_keygen_seed_test.json");
const MLKEM768_IMPORTED_DECAPS_VECTORS: &str =
	include_str!("../../wycheproof/testvectors_v1/mlkem_768_semi_expanded_decaps_test.json");

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TestSet<Group> {
	algorithm: String,
	schema: String,
	number_of_tests: usize,
	test_groups: Vec<Group>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
enum TestResult {
	Valid,
	Invalid,
	Acceptable,
}

#[derive(Debug, Deserialize)]
struct X25519Group {
	curve: String,
	tests: Vec<X25519Test>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct X25519Test {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	public: String,
	private: String,
	shared: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519Group {
	#[serde(rename = "type")]
	group_type: String,
	public_key: Ed25519PublicKey,
	tests: Vec<Ed25519Test>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519PublicKey {
	curve: String,
	key_size: usize,
	pk: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519Test {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	msg: String,
	sig: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519ToX25519Group {
	#[serde(rename = "type")]
	group_type: String,
	edwards_curve: String,
	montgomery_curve: String,
	tests: Vec<Ed25519ToX25519Test>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519ToX25519Test {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	public_key: String,
	converted_public_key: Option<String>,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AeadGroup {
	iv_size: usize,
	key_size: usize,
	tag_size: usize,
	tests: Vec<AeadTest>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AeadTest {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	key: String,
	iv: String,
	aad: String,
	msg: String,
	ct: String,
	tag: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
struct HkdfGroup {
	tests: Vec<HkdfTest>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HkdfTest {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	ikm: String,
	salt: String,
	info: String,
	size: usize,
	okm: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct MlKemGroup<Test> {
	#[serde(rename = "type")]
	group_type: String,
	parameter_set: String,
	tests: Vec<Test>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct MlKemDecapsTest {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	seed: String,
	#[serde(default)]
	ek: String,
	c: String,
	#[serde(rename = "K")]
	shared_secret: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct MlKemEncapsTest {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	m: String,
	ek: String,
	c: String,
	#[serde(rename = "K")]
	shared_secret: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct MlKemKeygenTest {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	seed: String,
	ek: String,
	dk: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct MlKemImportedDecapsTest {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
	dk: String,
	c: String,
	#[serde(rename = "K")]
	shared_secret: Option<String>,
	result: TestResult,
}

fn parse_set<Group>(json: &str, algorithm: &str, schema: &str) -> TestSet<Group>
where
	Group: for<'de> Deserialize<'de>,
{
	let set: TestSet<Group> = serde_json::from_str(json).expect("valid Wycheproof JSON");
	assert_eq!(set.algorithm, algorithm, "unexpected Wycheproof algorithm");
	assert_eq!(set.schema, schema, "unexpected Wycheproof schema");
	set
}

fn assert_test_count(expected: usize, actual: usize) {
	assert_eq!(
		actual, expected,
		"Wycheproof metadata count differs from parsed test count"
	);
}

fn decode_hex(input: &str) -> Vec<u8> {
	fn nibble(byte: u8) -> u8 {
		match byte {
			b'0'..=b'9' => byte - b'0',
			b'a'..=b'f' => byte - b'a' + 10,
			b'A'..=b'F' => byte - b'A' + 10,
			_ => panic!("invalid hex digit in Wycheproof vector"),
		}
	}

	assert_eq!(input.len() % 2, 0, "odd-length hex in Wycheproof vector");
	input
		.as_bytes()
		.as_chunks::<2>()
		.0
		.iter()
		.map(|pair| (nibble(pair[0]) << 4) | nibble(pair[1]))
		.collect()
}

fn case_label(tc_id: usize, comment: &str, flags: &[String]) -> String {
	format!("tcId {tc_id} ({comment}; flags: {})", flags.join(","))
}

#[test]
fn x25519_wycheproof() {
	let set: TestSet<X25519Group> = parse_set(X25519_VECTORS, "XDH", "xdh_comp_schema_v1.json");
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);

	for group in set.test_groups {
		assert_eq!(group.curve, "curve25519");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			let private = decode_hex(&test.private);
			let public = decode_hex(&test.public);
			let expected = decode_hex(&test.shared);
			let actual = crypto_scalarmult::scalarmult(&private, &public);

			match test.result {
				TestResult::Valid => {
					assert_eq!(actual.expect(&label).as_slice(), expected, "{label}");
				}
				TestResult::Acceptable => {
					if let Ok(shared) = actual {
						assert_eq!(shared.as_slice(), expected, "{label}");
					}
				}
				TestResult::Invalid => {
					assert!(actual.is_err(), "{label}");
				}
			}
		}
	}
}

#[test]
fn ed25519_fixture_inventory_wycheproof() {
	let vector_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../wycheproof/testvectors_v1");
	let actual: BTreeSet<_> = fs::read_dir(vector_dir)
		.expect("read Wycheproof fixture directory")
		.map(|entry| {
			entry
				.expect("read Wycheproof fixture entry")
				.file_name()
				.into_string()
				.expect("UTF-8 Wycheproof fixture name")
		})
		.filter(|name| name.starts_with("ed25519_") && name.ends_with("_test.json"))
		.collect();
	let expected = BTreeSet::from([
		"ed25519_test.json".to_owned(),
		"ed25519_to_x25519_test.json".to_owned(),
	]);
	assert_eq!(actual, expected, "unclassified Wycheproof Ed25519 fixture");
}

#[test]
fn ed25519_wycheproof() {
	let set: TestSet<Ed25519Group> =
		parse_set(ED25519_VECTORS, "EDDSA", "eddsa_verify_schema_v1.json");
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);
	assert_eq!(actual_count, 210, "review the pinned Ed25519 corpus count");
	let mut seen_ids = BTreeSet::new();
	let mut detached_cases = 0;
	let mut invalid_signature_widths = 0;

	for group in set.test_groups {
		assert_eq!(group.group_type, "EddsaVerify");
		assert_eq!(group.public_key.curve, "edwards25519");
		assert_eq!(group.public_key.key_size, 255);
		let public_key_bytes = decode_hex(&group.public_key.pk);
		let public_key = crypto_sign::PublicKey::from_bytes(&public_key_bytes)
			.expect("fixed-width Wycheproof Ed25519 public key");
		let native_public_key = sodium_sign::PublicKey::from_bytes(&public_key_bytes)
			.expect("fixed-width Wycheproof Ed25519 native public key");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
			let message = decode_hex(&test.msg);
			let signature_bytes = decode_hex(&test.sig);
			let signature: Result<[u8; crypto_sign::BYTES], _> =
				signature_bytes.as_slice().try_into();
			let Ok(signature) = signature else {
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				invalid_signature_widths += 1;
				// Reject at admission: concatenating a malformed signature would change
				// where an attached verifier finds the message boundary.
				continue;
			};
			detached_cases += 1;
			let verifies = crypto_sign::verify_detached(&signature, &message, &public_key);
			let native_verifies =
				sodium_sign::verify_detached(&signature, &message, &native_public_key);
			assert_eq!(verifies, native_verifies, "detached oracle: {label}");

			let mut signed_message = signature.to_vec();
			signed_message.extend_from_slice(&message);
			let opened = crypto_sign::verify(&signed_message, &public_key);
			let native_opened = sodium_sign::verify(&signed_message, &native_public_key);
			assert_eq!(opened, native_opened, "attached oracle: {label}");
			assert_eq!(
				opened.as_deref(),
				verifies.then_some(message.as_slice()),
				"attached and detached verification disagree: {label}"
			);

			match test.result {
				TestResult::Valid => assert!(verifies, "{label}"),
				TestResult::Invalid => assert!(!verifies, "{label}"),
				TestResult::Acceptable => {
					assert_eq!(test.flags.len(), 1, "unreviewed acceptable flags: {label}");
					if test.flags[0] == "SmallOrderPublicKey" {
						assert!(!verifies, "{label}");
					} else {
						assert_eq!(
							test.flags[0], "MixedOrderPublicKey",
							"unreviewed acceptable Ed25519 policy: {label}"
						);
						assert_eq!(verifies, native_verifies, "mixed-order policy: {label}");
					}
				}
			}
		}
	}
	assert_eq!(seen_ids.len(), actual_count);
	assert_eq!(seen_ids, (1..=210).collect(), "changed Ed25519 case IDs");
	assert_eq!(detached_cases, 198, "review the fixed-width Ed25519 cases");
	assert_eq!(
		invalid_signature_widths, 12,
		"review the Ed25519 width cases"
	);
}

#[test]
fn ed25519_to_x25519_wycheproof() {
	let set: TestSet<Ed25519ToX25519Group> = parse_set(
		ED25519_TO_X25519_VECTORS,
		"EDDSA-to-XDH",
		"eddsa_to_xdh_schema.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);
	assert_eq!(
		actual_count, 34,
		"review the pinned conversion corpus count"
	);
	let mut seen_ids = BTreeSet::new();

	for group in set.test_groups {
		assert_eq!(group.group_type, "EddsaToXdh");
		assert_eq!(group.edwards_curve, "edwards25519");
		assert_eq!(group.montgomery_curve, "curve25519");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
			let public_key = decode_hex(&test.public_key);
			let actual = crypto_sign::PublicKey::from_bytes(&public_key)
				.and_then(|key| crypto_sign::ed25519_pk_to_curve25519(&key));
			let native = sodium_sign::PublicKey::from_bytes(&public_key)
				.and_then(|key| sodium_sign::ed25519_pk_to_curve25519(&key));
			assert_eq!(
				actual.as_ref().ok(),
				native.as_ref().ok(),
				"conversion oracle: {label}"
			);

			match test.result {
				TestResult::Valid => {
					let expected = decode_hex(test.converted_public_key.as_deref().expect(&label));
					assert_eq!(actual.expect(&label).as_slice(), expected, "{label}");
					assert_eq!(native.expect(&label).as_slice(), expected, "native {label}");
				}
				TestResult::Invalid => {
					assert!(actual.is_err(), "{label}");
					assert!(native.is_err(), "native {label}");
				}
				TestResult::Acceptable => {
					panic!("unreviewed acceptable Ed25519 conversion policy: {label}");
				}
			}
		}
	}
	assert_eq!(seen_ids.len(), actual_count);
	assert_eq!(seen_ids, (1..=34).collect(), "changed conversion case IDs");
}

#[test]
fn chacha20_poly1305_wycheproof() {
	let set: TestSet<AeadGroup> = parse_set(
		CHACHA20_POLY1305_VECTORS,
		"CHACHA20-POLY1305",
		"aead_test_schema_v1.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);

	for group in set.test_groups {
		assert_eq!(group.key_size, chacha20poly1305_ietf::KEYBYTES * 8);
		assert_eq!(group.tag_size, chacha20poly1305_ietf::ABYTES * 8);

		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			let key_bytes = decode_hex(&test.key);
			let nonce_bytes = decode_hex(&test.iv);
			let aad = decode_hex(&test.aad);
			let message = decode_hex(&test.msg);
			let ciphertext = decode_hex(&test.ct);
			let tag = decode_hex(&test.tag);

			let key = chacha20poly1305_ietf::Key::from_bytes(&key_bytes).expect(&label);
			let nonce = chacha20poly1305_ietf::Nonce::try_from_slice(&nonce_bytes);
			if group.iv_size != chacha20poly1305_ietf::NPUBBYTES * 8 {
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(nonce.is_err(), "{label}");
				continue;
			}
			let nonce = nonce.expect(&label);
			let mut authenticated_ciphertext = ciphertext.clone();
			authenticated_ciphertext.extend_from_slice(&tag);
			let opened =
				chacha20poly1305_ietf::decrypt(&authenticated_ciphertext, Some(&aad), &nonce, &key);

			match test.result {
				TestResult::Valid => {
					assert_eq!(opened.expect(&label), message, "{label}");
					let (actual_ciphertext, actual_tag) =
						chacha20poly1305_ietf::encrypt_detached(&message, Some(&aad), &nonce, &key)
							.expect(&label);
					assert_eq!(actual_ciphertext, ciphertext, "{label}");
					assert_eq!(actual_tag, tag, "{label}");
				}
				TestResult::Invalid => assert!(opened.is_err(), "{label}"),
				TestResult::Acceptable => {}
			}
		}
	}
}

#[test]
fn hkdf_sha512_wycheproof() {
	let set: TestSet<HkdfGroup> = parse_set(
		HKDF_SHA512_VECTORS,
		"HKDF-SHA-512",
		"hkdf_test_schema_v1.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);

	for group in set.test_groups {
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			let ikm = decode_hex(&test.ikm);
			let salt = decode_hex(&test.salt);
			let info = decode_hex(&test.info);
			let expected = decode_hex(&test.okm);
			let actual = crypto_kdf::hkdf::sha512::extract(Some(&salt), &ikm)
				.and_then(|prk| crypto_kdf::hkdf::sha512::expand(test.size, Some(&info), &prk));

			match test.result {
				TestResult::Valid => {
					assert_eq!(actual.expect(&label), expected, "{label}");
				}
				TestResult::Invalid => assert!(actual.is_err(), "{label}"),
				TestResult::Acceptable => {}
			}
		}
	}
}

fn assert_mlkem_keypair(
	portable: &mlkem768::KeyPair,
	native: &sodium_mlkem::KeyPair,
	expected_public: &[u8],
	expected_secret: Option<&[u8]>,
	label: &str,
) {
	assert_eq!(
		portable.public_key.as_bytes().as_slice(),
		expected_public,
		"{label}"
	);
	assert_eq!(
		native.public_key.as_bytes().as_slice(),
		expected_public,
		"native {label}"
	);
	assert_eq!(
		portable.secret_key.as_bytes().as_slice(),
		native.secret_key.as_bytes().as_slice(),
		"expanded secret encoding oracle: {label}"
	);
	if let Some(expected_secret) = expected_secret {
		assert_eq!(
			portable.secret_key.as_bytes().as_slice(),
			expected_secret,
			"{label}"
		);
		assert_eq!(
			native.secret_key.as_bytes().as_slice(),
			expected_secret,
			"native {label}"
		);
	}
}

fn assert_mlkem_shared_secret(
	portable: &mlkem768::SharedSecret,
	native: &sodium_mlkem::SharedSecret,
	expected: &[u8],
	label: &str,
) {
	assert_eq!(portable.as_bytes().as_slice(), expected, "{label}");
	assert_eq!(native.as_bytes().as_slice(), expected, "native {label}");
	assert_eq!(
		portable.as_bytes().as_slice(),
		native.as_bytes().as_slice(),
		"{label}"
	);
}

#[test]
fn mlkem768_fixture_inventory_wycheproof() {
	let vector_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../wycheproof/testvectors_v1");
	let actual: BTreeSet<_> = fs::read_dir(vector_dir)
		.expect("read Wycheproof fixture directory")
		.map(|entry| {
			entry
				.expect("read Wycheproof fixture entry")
				.file_name()
				.into_string()
				.expect("UTF-8 Wycheproof fixture name")
		})
		.filter(|name| name.starts_with("mlkem_768_") && name.ends_with("_test.json"))
		.collect();
	let expected = BTreeSet::from([
		"mlkem_768_test.json".to_owned(),
		"mlkem_768_encaps_test.json".to_owned(),
		"mlkem_768_keygen_seed_test.json".to_owned(),
		"mlkem_768_semi_expanded_decaps_test.json".to_owned(),
	]);
	assert_eq!(
		actual, expected,
		"unclassified Wycheproof ML-KEM-768 fixture"
	);
}

#[test]
fn mlkem768_keygen_and_decapsulation_wycheproof() {
	let set: TestSet<MlKemGroup<MlKemDecapsTest>> =
		parse_set(MLKEM768_VECTORS, "ML-KEM", "mlkem_test_schema.json");
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);
	assert_eq!(actual_count, 201, "review the seeded ML-KEM corpus count");
	let mut seen_ids = BTreeSet::new();
	let mut rejected_seeds = 0;
	let mut rejected_ciphertexts = 0;
	let mut valid_decapsulations = 0;

	for group in set.test_groups {
		assert_eq!(group.group_type, "MLKEMTest");
		assert_eq!(group.parameter_set, "ML-KEM-768");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
			let seed = decode_hex(&test.seed);
			let ciphertext_bytes = decode_hex(&test.c);
			let keypair = mlkem768::KeyPair::from_seed(&seed);
			let native_keypair = sodium_mlkem::KeyPair::from_seed(&seed);
			let ciphertext = mlkem768::Ciphertext::from_bytes(&ciphertext_bytes);
			let native_ciphertext = sodium_mlkem::Ciphertext::from_bytes(&ciphertext_bytes);
			assert_eq!(
				keypair.is_ok(),
				native_keypair.is_ok(),
				"seed admission: {label}"
			);
			assert_eq!(
				ciphertext.is_ok(),
				native_ciphertext.is_ok(),
				"ciphertext admission: {label}"
			);
			if seed.len() != mlkem768::SEEDBYTES {
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(keypair.is_err(), "{label}");
				assert!(native_keypair.is_err(), "native {label}");
				rejected_seeds += 1;
				continue;
			}
			let keypair = keypair.expect(&label);
			let native_keypair = native_keypair.expect(&label);
			assert_mlkem_keypair(
				&keypair,
				&native_keypair,
				&decode_hex(&test.ek),
				None,
				&label,
			);
			if ciphertext_bytes.len() != mlkem768::CIPHERTEXTBYTES {
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(ciphertext.is_err(), "{label}");
				assert!(native_ciphertext.is_err(), "native {label}");
				rejected_ciphertexts += 1;
				continue;
			}
			assert_eq!(
				test.result,
				TestResult::Valid,
				"unreviewed full-width decapsulation: {label}"
			);
			let shared = mlkem768::decapsulate(&ciphertext.expect(&label), &keypair.secret_key)
				.expect(&label);
			let native_shared = sodium_mlkem::decapsulate(
				&native_ciphertext.expect(&label),
				&native_keypair.secret_key,
			)
			.expect(&label);
			assert_mlkem_shared_secret(
				&shared,
				&native_shared,
				&decode_hex(&test.shared_secret),
				&label,
			);
			valid_decapsulations += 1;
		}
	}
	assert_eq!(
		seen_ids,
		(1..=201).collect(),
		"changed seeded ML-KEM case IDs"
	);
	assert_eq!(
		(valid_decapsulations, rejected_seeds, rejected_ciphertexts),
		(161, 20, 20)
	);
}

#[test]
fn mlkem768_encapsulation_wycheproof() {
	let set: TestSet<MlKemGroup<MlKemEncapsTest>> = parse_set(
		MLKEM768_ENCAPS_VECTORS,
		"ML-KEM",
		"mlkem_encaps_test_schema.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);
	assert_eq!(
		actual_count, 265,
		"review the ML-KEM encapsulation corpus count"
	);
	let mut seen_ids = BTreeSet::new();
	let mut valid_encapsulations = 0;
	let mut rejected_key_widths = 0;
	let mut rejected_key_encodings = 0;

	for group in set.test_groups {
		assert_eq!(group.group_type, "MLKEMEncapsTest");
		assert_eq!(group.parameter_set, "ML-KEM-768");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
			let public_bytes = decode_hex(&test.ek);
			let randomness = decode_hex(&test.m);
			let seed = mlkem768::EncapsulationSeed::from_bytes(&randomness).expect(&label);
			let native_seed =
				sodium_mlkem::EncapsulationSeed::from_bytes(&randomness).expect(&label);
			assert_eq!(
				seed.as_bytes().as_slice(),
				native_seed.as_bytes().as_slice(),
				"{label}"
			);
			let public = mlkem768::PublicKey::from_bytes(&public_bytes);
			let native_public = sodium_mlkem::PublicKey::from_bytes(&public_bytes);
			assert_eq!(
				public.is_ok(),
				native_public.is_ok(),
				"public key admission: {label}"
			);
			if public_bytes.len() != mlkem768::PUBLICKEYBYTES {
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(public.is_err(), "{label}");
				assert!(native_public.is_err(), "native {label}");
				rejected_key_widths += 1;
				continue;
			}
			let public = public.expect(&label);
			let native_public = native_public.expect(&label);
			assert_eq!(public.as_bytes().as_slice(), public_bytes, "{label}");
			assert_eq!(
				native_public.as_bytes().as_slice(),
				public_bytes,
				"native {label}"
			);
			let actual = mlkem768::encapsulate_deterministic(&public, &seed);
			let native = sodium_mlkem::encapsulate_deterministic(&native_public, &native_seed);
			assert_eq!(
				actual.is_ok(),
				native.is_ok(),
				"encapsulation oracle: {label}"
			);
			match test.result {
				TestResult::Valid => {
					let (ciphertext, shared) = actual.expect(&label);
					let (native_ciphertext, native_shared) = native.expect(&label);
					let expected_ciphertext = decode_hex(&test.c);
					assert_eq!(
						ciphertext.as_bytes().as_slice(),
						expected_ciphertext,
						"{label}"
					);
					assert_eq!(
						native_ciphertext.as_bytes().as_slice(),
						expected_ciphertext,
						"native {label}"
					);
					assert_mlkem_shared_secret(
						&shared,
						&native_shared,
						&decode_hex(&test.shared_secret),
						&label,
					);
					valid_encapsulations += 1;
				}
				TestResult::Invalid => {
					assert!(actual.is_err(), "{label}");
					assert!(native.is_err(), "native {label}");
					rejected_key_encodings += 1;
				}
				TestResult::Acceptable => {
					panic!("unreviewed acceptable ML-KEM encapsulation: {label}")
				}
			}
		}
	}
	assert_eq!(
		seen_ids,
		(2..=266).collect(),
		"changed ML-KEM encapsulation case IDs"
	);
	assert_eq!(
		(
			valid_encapsulations,
			rejected_key_widths,
			rejected_key_encodings
		),
		(133, 20, 112)
	);
}

#[test]
fn mlkem768_expanded_keygen_wycheproof() {
	let set: TestSet<MlKemGroup<MlKemKeygenTest>> = parse_set(
		MLKEM768_KEYGEN_VECTORS,
		"ML-KEM",
		"mlkem_keygen_seed_test_schema.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);
	assert_eq!(
		actual_count, 100,
		"review the expanded ML-KEM keygen corpus count"
	);
	let mut seen_ids = BTreeSet::new();
	for group in set.test_groups {
		assert_eq!(group.group_type, "MLKEMKeyGen");
		assert_eq!(group.parameter_set, "ML-KEM-768");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
			assert_eq!(test.result, TestResult::Valid, "{label}");
			let seed = decode_hex(&test.seed);
			let keypair = mlkem768::KeyPair::from_seed(&seed).expect(&label);
			let native_keypair = sodium_mlkem::KeyPair::from_seed(&seed).expect(&label);
			assert_mlkem_keypair(
				&keypair,
				&native_keypair,
				&decode_hex(&test.ek),
				Some(&decode_hex(&test.dk)),
				&label,
			);
		}
	}
	assert_eq!(
		seen_ids,
		(1..=100).collect(),
		"changed expanded ML-KEM keygen case IDs"
	);
}

#[test]
fn mlkem768_imported_decapsulation_wycheproof() {
	let set: TestSet<MlKemGroup<MlKemImportedDecapsTest>> = parse_set(
		MLKEM768_IMPORTED_DECAPS_VECTORS,
		"ML-KEM",
		"mlkem_semi_expanded_decaps_test_schema.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);
	assert_eq!(
		actual_count, 9,
		"review the imported ML-KEM decapsulation corpus count"
	);
	let mut seen_ids = BTreeSet::new();
	let mut native_validation_differences = BTreeSet::new();
	const REVIEWED_NATIVE_EXPANDED_KEY_VALIDATION_DIFFERENCES: [usize; 2] = [6, 7];

	for group in set.test_groups {
		assert_eq!(group.group_type, "MLKEMDecapsValidationTest");
		assert_eq!(group.parameter_set, "ML-KEM-768");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
			let secret_bytes = decode_hex(&test.dk);
			let ciphertext_bytes = decode_hex(&test.c);
			let secret_key = mlkem768::SecretKey::from_bytes(&secret_bytes);
			let native_secret_key = sodium_mlkem::SecretKey::from_bytes(&secret_bytes);
			let ciphertext = mlkem768::Ciphertext::from_bytes(&ciphertext_bytes);
			let native_ciphertext = sodium_mlkem::Ciphertext::from_bytes(&ciphertext_bytes);
			assert_eq!(
				secret_key.is_ok(),
				native_secret_key.is_ok(),
				"secret admission: {label}"
			);
			assert_eq!(
				ciphertext.is_ok(),
				native_ciphertext.is_ok(),
				"ciphertext admission: {label}"
			);
			if test
				.flags
				.iter()
				.any(|flag| flag == "IncorrectDecapsulationKeyLength")
			{
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(secret_key.is_err(), "{label}");
				assert!(native_secret_key.is_err(), "native {label}");
				continue;
			}
			if test
				.flags
				.iter()
				.any(|flag| flag == "IncorrectCiphertextLength")
			{
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(ciphertext.is_err(), "{label}");
				assert!(native_ciphertext.is_err(), "native {label}");
				continue;
			}
			let secret_key = secret_key.expect(&label);
			let native_secret_key = native_secret_key.expect(&label);
			assert_eq!(secret_key.as_bytes().as_slice(), secret_bytes, "{label}");
			assert_eq!(
				native_secret_key.as_bytes().as_slice(),
				secret_bytes,
				"native {label}"
			);
			let actual = mlkem768::decapsulate(&ciphertext.expect(&label), &secret_key);
			let native =
				sodium_mlkem::decapsulate(&native_ciphertext.expect(&label), &native_secret_key);
			match test.result {
				TestResult::Valid => {
					// Modified ciphertexts have exact implicit-rejection secrets in both backends.
					assert_mlkem_shared_secret(
						&actual.expect(&label),
						&native.expect(&label),
						&decode_hex(test.shared_secret.as_deref().expect(&label)),
						&label,
					);
				}
				TestResult::Invalid => {
					assert!(actual.is_err(), "{label}");
					if REVIEWED_NATIVE_EXPANDED_KEY_VALIDATION_DIFFERENCES.contains(&test.tc_id) {
						assert_eq!(test.flags, ["InvalidDecapsulationKey"], "{label}");
						// The installed libsodium decapsulator omits expanded-key hash validation.
						// Preserve the vector's rejection rule for the portable implementation.
						assert!(
							native.is_ok(),
							"review changed native expanded-key validation: {label}"
						);
						assert!(
							native_validation_differences.insert(test.tc_id),
							"duplicate {label}"
						);
					} else {
						assert!(native.is_err(), "native {label}");
					}
				}
				TestResult::Acceptable => {
					panic!("unreviewed acceptable ML-KEM decapsulation: {label}")
				}
			}
		}
	}
	assert_eq!(
		seen_ids,
		(1..=9).collect(),
		"changed imported ML-KEM case IDs"
	);
	assert_eq!(
		native_validation_differences,
		BTreeSet::from(REVIEWED_NATIVE_EXPANDED_KEY_VALIDATION_DIFFERENCES)
	);
}
