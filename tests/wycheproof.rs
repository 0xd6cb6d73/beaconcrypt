use libsodium_rs::{
	crypto_aead::chacha20poly1305_ietf, crypto_kdf, crypto_kem::mlkem768, crypto_scalarmult,
	crypto_sign, ensure_init,
};
use serde::Deserialize;

const X25519_VECTORS: &str = include_str!("../wycheproof/testvectors_v1/x25519_test.json");
const ED25519_VECTORS: &str = include_str!("../wycheproof/testvectors_v1/ed25519_test.json");
const CHACHA20_POLY1305_VECTORS: &str =
	include_str!("../wycheproof/testvectors_v1/chacha20_poly1305_test.json");
const HKDF_SHA512_VECTORS: &str =
	include_str!("../wycheproof/testvectors_v1/hkdf_sha512_test.json");
const MLKEM768_VECTORS: &str = include_str!("../wycheproof/testvectors_v1/mlkem_768_test.json");
const MLKEM768_ENCAPS_VECTORS: &str =
	include_str!("../wycheproof/testvectors_v1/mlkem_768_encaps_test.json");

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

fn initialize_test_runtime() {
	ensure_init().expect("initialize libsodium");

	// Direct libsodium use would otherwise let Cargo omit Beaconcrypt's Windows
	// GNU compatibility symbols from this integration-test executable.
	#[cfg(all(windows, target_env = "gnu"))]
	{
		std::hint::black_box(
			beaconcrypt::memset_explicit
				as unsafe extern "C" fn(
					*mut std::ffi::c_void,
					std::ffi::c_int,
					usize,
				) -> *mut std::ffi::c_void,
		);
		std::hint::black_box(
			beaconcrypt::SystemFunction036
				as unsafe extern "system" fn(*mut std::ffi::c_void, u32) -> u8,
		);
	}
}

#[test]
fn x25519_wycheproof() {
	initialize_test_runtime();
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
fn ed25519_wycheproof() {
	initialize_test_runtime();
	let set: TestSet<Ed25519Group> =
		parse_set(ED25519_VECTORS, "EDDSA", "eddsa_verify_schema_v1.json");
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);

	for group in set.test_groups {
		assert_eq!(group.public_key.curve, "edwards25519");
		assert_eq!(group.public_key.key_size, 255);
		let public_key = crypto_sign::PublicKey::from_bytes(&decode_hex(&group.public_key.pk));
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			let message = decode_hex(&test.msg);
			let mut signed_message = decode_hex(&test.sig);
			signed_message.extend_from_slice(&message);
			let verifies = public_key
				.as_ref()
				.ok()
				.and_then(|public_key| crypto_sign::verify(&signed_message, public_key))
				.is_some_and(|opened| opened == message);

			match test.result {
				TestResult::Valid => assert!(verifies, "{label}"),
				TestResult::Invalid => assert!(!verifies, "{label}"),
				TestResult::Acceptable => {}
			}
		}
	}
}

#[test]
fn chacha20_poly1305_wycheproof() {
	initialize_test_runtime();
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
	initialize_test_runtime();
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

#[test]
fn mlkem768_keygen_and_decapsulation_wycheproof() {
	initialize_test_runtime();
	let set: TestSet<MlKemGroup<MlKemDecapsTest>> =
		parse_set(MLKEM768_VECTORS, "ML-KEM", "mlkem_test_schema.json");
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);

	for group in set.test_groups {
		assert_eq!(group.parameter_set, "ML-KEM-768");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			let seed = decode_hex(&test.seed);
			let ciphertext = decode_hex(&test.c);

			match test.result {
				TestResult::Valid => {
					let keypair = mlkem768::KeyPair::from_seed(&seed).expect(&label);
					assert_eq!(
						keypair.public_key.as_bytes().as_slice(),
						decode_hex(&test.ek),
						"{label}"
					);
					let ciphertext = mlkem768::Ciphertext::from_bytes(&ciphertext).expect(&label);
					let shared =
						mlkem768::decapsulate(&ciphertext, &keypair.secret_key).expect(&label);
					assert_eq!(
						shared.as_bytes().as_slice(),
						decode_hex(&test.shared_secret),
						"{label}"
					);
				}
				TestResult::Invalid => {
					assert!(
						mlkem768::KeyPair::from_seed(&seed).is_err()
							|| mlkem768::Ciphertext::from_bytes(&ciphertext).is_err(),
						"{label}"
					);
				}
				TestResult::Acceptable => {}
			}
		}
	}
}

#[test]
fn mlkem768_encapsulation_wycheproof() {
	initialize_test_runtime();
	let set: TestSet<MlKemGroup<MlKemEncapsTest>> = parse_set(
		MLKEM768_ENCAPS_VECTORS,
		"ML-KEM",
		"mlkem_encaps_test_schema.json",
	);
	let actual_count = set.test_groups.iter().map(|group| group.tests.len()).sum();
	assert_test_count(set.number_of_tests, actual_count);

	for group in set.test_groups {
		assert_eq!(group.parameter_set, "ML-KEM-768");
		for test in group.tests {
			let label = case_label(test.tc_id, &test.comment, &test.flags);
			let public_key = decode_hex(&test.ek);
			let randomness = decode_hex(&test.m);
			assert_eq!(randomness.len(), 32, "{label}");

			// ML-KEM Encaps_internal consumes a 32-byte m. libsodium-rs currently
			// exposes that native function through its 64-byte keygen Seed type;
			// the native function consumes the first 32 bytes.
			let mut deterministic_seed = [0u8; mlkem768::SEEDBYTES];
			deterministic_seed[..randomness.len()].copy_from_slice(&randomness);
			let deterministic_seed = mlkem768::Seed::from(deterministic_seed);
			let actual = mlkem768::PublicKey::from_bytes(&public_key).and_then(|public_key| {
				mlkem768::encapsulate_deterministic(&public_key, &deterministic_seed)
			});

			match test.result {
				TestResult::Valid => {
					let (ciphertext, shared) = actual.expect(&label);
					assert_eq!(
						ciphertext.as_bytes().as_slice(),
						decode_hex(&test.c),
						"{label}"
					);
					assert_eq!(
						shared.as_bytes().as_slice(),
						decode_hex(&test.shared_secret),
						"{label}"
					);
				}
				TestResult::Invalid => assert!(actual.is_err(), "{label}"),
				TestResult::Acceptable => {}
			}
		}
	}
}
