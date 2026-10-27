#[cfg(all(windows, target_env = "gnu"))]
#[path = "common/sodium_oracle.rs"]
mod sodium_oracle;

use std::{collections::BTreeSet, fs, path::Path};

use beaconcrypt_crypto::{
	crypto_aead::chacha20poly1305_ietf, crypto_generichash, crypto_kdf, crypto_scalarmult,
	crypto_sign,
};
use libsodium_rs as sodium;
use serde::Deserialize;

const ROOTERBERG_VERSION: &str = "0.65";
const X25519_VECTOR: &str = "xdh/x25519.json";
const ED25519_VERIFY_VECTOR: &str = "eddsa/ed25519.json";
const ED25519_SIGN_VECTOR: &str = "eddsa/ed25519_sign.json";
const CHACHA20_POLY1305_VECTOR: &str = "aead/chacha20_poly1305.json";
const HKDF_SHA512_VECTOR: &str = "kdf/hkdf_sha512.json";
const HMAC_SHA512_VECTOR: &str = "mac/hmac_sha512_512.json";
const BLAKE2B_VECTOR: &str = "message_digest/blake2b.json";

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TestSet<Algorithm, Test> {
	test_type: String,
	algorithm: Algorithm,
	version: String,
	num_tests: usize,
	tests: Vec<Test>,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct X25519Algorithm {
	algorithm_type: String,
	primitive: String,
	curve: String,
	encoding: String,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct Ed25519Algorithm {
	algorithm_type: String,
	curve: String,
	cofactored: bool,
	encoding: String,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct AeadAlgorithm {
	algorithm_type: String,
	primitive: String,
	key_size: usize,
	iv_size: usize,
	tag_size: usize,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct HkdfAlgorithm {
	algorithm_type: String,
	primitive: String,
	sha: String,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct HmacAlgorithm {
	algorithm_type: String,
	primitive: String,
	mac_size: usize,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct HashAlgorithm {
	algorithm_type: String,
	primitive: String,
	digest_size: usize,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct X25519Test {
	tc_id: usize,
	private_key: String,
	public_key: String,
	shared: String,
	valid: bool,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519VerifyTest {
	tc_id: usize,
	public_key: String,
	msg: String,
	sig: String,
	valid: bool,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Ed25519SignTest {
	tc_id: usize,
	private_key: String,
	msg: String,
	sig: String,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AeadTest {
	tc_id: usize,
	key: String,
	iv: String,
	aad: String,
	msg: String,
	ct: String,
	tag: String,
	valid: bool,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HkdfTest {
	tc_id: usize,
	ikm: String,
	salt: String,
	info: String,
	out_len: usize,
	okm: String,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HmacTest {
	tc_id: usize,
	key: String,
	msg: String,
	mac: String,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HashTest {
	tc_id: usize,
	msg: String,
	digest: String,
	#[serde(default)]
	flags: Vec<String>,
	#[serde(default)]
	comment: String,
}

fn load_vector(relative_path: &str) -> String {
	let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
	let path = manifest_dir
		.join("../rooterberg")
		.join("test_vectors")
		.join(relative_path);
	fs::read_to_string(&path).unwrap_or_else(|error| {
		if manifest_dir.join(".cargo_vcs_info.json").is_file() {
			panic!(
				"read Rooterberg vector {}: {error}; Rooterberg vectors are intentionally \
				 excluded from published crate archives, so run this test from a repository \
				 checkout instead",
				path.display()
			);
		}
		panic!(
			"read Rooterberg vector {}: {error}; initialize submodules with \
			 `git submodule update --init --recursive`",
			path.display()
		);
	})
}

fn parse_set<Algorithm, Test>(json: &str, test_type: &str) -> TestSet<Algorithm, Test>
where
	Algorithm: for<'de> Deserialize<'de>,
	Test: for<'de> Deserialize<'de>,
{
	let set: TestSet<Algorithm, Test> = serde_json::from_str(json).expect("valid Rooterberg JSON");
	assert_eq!(set.test_type, test_type, "unexpected Rooterberg test type");
	assert_eq!(
		set.version, ROOTERBERG_VERSION,
		"unexpected Rooterberg format version"
	);
	assert_eq!(
		set.num_tests,
		set.tests.len(),
		"Rooterberg metadata count differs from parsed test count"
	);
	set
}

fn decode_hex(input: &str) -> Vec<u8> {
	fn nibble(byte: u8) -> u8 {
		match byte {
			b'0'..=b'9' => byte - b'0',
			b'a'..=b'f' => byte - b'a' + 10,
			b'A'..=b'F' => byte - b'A' + 10,
			_ => panic!("invalid hex digit in Rooterberg vector"),
		}
	}

	assert_eq!(input.len() % 2, 0, "odd-length hex in Rooterberg vector");
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
fn x25519_rooterberg() {
	let json = load_vector(X25519_VECTOR);
	let set: TestSet<X25519Algorithm, X25519Test> = parse_set(&json, "Xdh");
	assert_eq!(
		set.algorithm,
		X25519Algorithm {
			algorithm_type: "Xdh".into(),
			primitive: "x25519".into(),
			curve: "curve25519".into(),
			encoding: "RAW".into(),
		},
		"unexpected Rooterberg X25519 algorithm metadata"
	);

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let private_key = decode_hex(&test.private_key);
		let public_key = decode_hex(&test.public_key);
		let expected = decode_hex(&test.shared);
		let actual = crypto_scalarmult::scalarmult(&private_key, &public_key);

		if test.valid {
			assert_eq!(actual.expect(&label).as_slice(), expected, "{label}");
		} else {
			assert!(actual.is_err(), "{label}");
		}
	}
}

#[test]
fn ed25519_fixture_inventory_rooterberg() {
	let vector_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../rooterberg/test_vectors/eddsa");
	let actual: BTreeSet<_> = fs::read_dir(vector_dir)
		.expect("read Rooterberg fixture directory")
		.map(|entry| {
			entry
				.expect("read Rooterberg fixture entry")
				.file_name()
				.into_string()
				.expect("UTF-8 Rooterberg fixture name")
		})
		.filter(|name| name.starts_with("ed25519") && name.ends_with(".json"))
		.collect();
	// Pure raw signing and verification are consumed. JWK and cofactored files repeat
	// those raw inputs; ph and BLAKE2b files specify signature algorithms we do not use.
	let classified = BTreeSet::from([
		"ed25519.json".to_owned(),
		"ed25519_sign.json".to_owned(),
		"ed25519_jwk.json".to_owned(),
		"ed25519_cofactored.json".to_owned(),
		"ed25519ph.json".to_owned(),
		"ed25519ph_sign.json".to_owned(),
		"ed25519_blake2b.json".to_owned(),
		"ed25519_blake2b_sign.json".to_owned(),
	]);
	assert_eq!(
		actual, classified,
		"unclassified Rooterberg Ed25519 fixture"
	);
}

#[test]
fn ed25519_verification_rooterberg() {
	let json = load_vector(ED25519_VERIFY_VECTOR);
	let set: TestSet<Ed25519Algorithm, Ed25519VerifyTest> = parse_set(&json, "EddsaVerify");
	assert_eq!(
		set.algorithm,
		Ed25519Algorithm {
			algorithm_type: "Eddsa".into(),
			curve: "edwards25519".into(),
			cofactored: false,
			encoding: "RAW".into(),
		},
		"unexpected Rooterberg Ed25519 verification algorithm metadata"
	);
	assert_eq!(set.num_tests, 84, "review changed Ed25519 fixture coverage");

	let mut seen_ids = BTreeSet::new();
	let mut full_width_cases = 0;
	let mut invalid_width_cases = 0;
	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
		let public_bytes = decode_hex(&test.public_key);
		let public_key = crypto_sign::PublicKey::from_bytes(&public_bytes).expect(&label);
		let native_public =
			sodium::crypto_sign::PublicKey::from_bytes(&public_bytes).expect(&label);
		let message = decode_hex(&test.msg);
		let signature = decode_hex(&test.sig);
		let verifies = <&[u8; crypto_sign::BYTES]>::try_from(signature.as_slice())
			.is_ok_and(|signature| crypto_sign::verify_detached(signature, &message, &public_key));
		let native_verifies = <&[u8; sodium::crypto_sign::BYTES]>::try_from(signature.as_slice())
			.is_ok_and(|signature| {
				sodium::crypto_sign::verify_detached(signature, &message, &native_public)
			});
		assert_eq!(verifies, test.valid, "{label}");
		assert_eq!(native_verifies, test.valid, "native oracle: {label}");
		assert_eq!(
			crypto_sign::ed25519_pk_to_curve25519(&public_key).ok(),
			sodium::crypto_sign::ed25519_pk_to_curve25519(&native_public).ok(),
			"public-key conversion: {label}"
		);

		if signature.len() != crypto_sign::BYTES {
			assert!(!test.valid, "{label}");
			invalid_width_cases += 1;
			// A detached signature with the wrong width is rejected at admission;
			// concatenation would change the attached message boundary.
			continue;
		}
		full_width_cases += 1;
		let mut signed_message = signature;
		signed_message.extend_from_slice(&message);
		let expected_opened = test.valid.then_some(message);
		assert_eq!(
			crypto_sign::verify(&signed_message, &public_key),
			expected_opened,
			"attached verification: {label}"
		);
		assert_eq!(
			sodium::crypto_sign::verify(&signed_message, &native_public),
			expected_opened,
			"native attached verification: {label}"
		);
	}
	assert_eq!(
		seen_ids,
		(1..=set.num_tests).collect(),
		"changed Ed25519 case IDs"
	);
	assert_eq!(full_width_cases, 80, "review the fixed-width Ed25519 cases");
	assert_eq!(invalid_width_cases, 4, "review the Ed25519 width cases");
}

#[test]
fn ed25519_signing_rooterberg() {
	let json = load_vector(ED25519_SIGN_VECTOR);
	let set: TestSet<Ed25519Algorithm, Ed25519SignTest> = parse_set(&json, "EddsaSign");
	assert_eq!(
		set.algorithm,
		Ed25519Algorithm {
			algorithm_type: "Eddsa".into(),
			curve: "edwards25519".into(),
			cofactored: false,
			encoding: "RAW".into(),
		},
		"unexpected Rooterberg Ed25519 signing algorithm metadata"
	);
	assert_eq!(
		set.num_tests, 133,
		"review changed Ed25519 fixture coverage"
	);

	let mut seen_ids = BTreeSet::new();
	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		assert!(seen_ids.insert(test.tc_id), "duplicate {label}");
		let private_key = decode_hex(&test.private_key);
		let keypair = crypto_sign::KeyPair::from_seed(&private_key).expect(&label);
		let native_keypair = sodium::crypto_sign::KeyPair::from_seed(&private_key).expect(&label);
		assert_eq!(
			keypair.public_key.as_bytes(),
			native_keypair.public_key.as_bytes(),
			"public-key encoding: {label}"
		);
		assert_eq!(
			keypair.secret_key.as_bytes(),
			native_keypair.secret_key.as_bytes(),
			"secret-key encoding: {label}"
		);
		assert_eq!(
			crypto_sign::secret_key_to_seed(&keypair.secret_key)
				.expect(&label)
				.as_slice(),
			private_key,
			"seed recovery: {label}"
		);
		assert_eq!(
			sodium::crypto_sign::secret_key_to_seed(&native_keypair.secret_key)
				.expect(&label)
				.as_slice(),
			private_key,
			"native seed recovery: {label}"
		);
		let curve_public =
			crypto_sign::ed25519_pk_to_curve25519(&keypair.public_key).expect(&label);
		let curve_secret =
			crypto_sign::ed25519_sk_to_curve25519(&keypair.secret_key).expect(&label);
		assert_eq!(
			curve_public,
			sodium::crypto_sign::ed25519_pk_to_curve25519(&native_keypair.public_key)
				.expect(&label),
			"public-key conversion: {label}"
		);
		assert_eq!(
			curve_secret,
			sodium::crypto_sign::ed25519_sk_to_curve25519(&native_keypair.secret_key)
				.expect(&label),
			"secret-key conversion: {label}"
		);
		let mut basepoint = [0; 32];
		basepoint[0] = 9;
		assert_eq!(
			crypto_scalarmult::scalarmult(&curve_secret, &basepoint).expect(&label),
			curve_public,
			"converted keypair consistency: {label}"
		);
		let message = decode_hex(&test.msg);
		let expected_signature = decode_hex(&test.sig);
		let actual = crypto_sign::sign_detached(&message, &keypair.secret_key).expect(&label);
		let native_signature =
			sodium::crypto_sign::sign_detached(&message, &native_keypair.secret_key).expect(&label);
		assert_eq!(actual.as_slice(), expected_signature, "{label}");
		assert_eq!(
			native_signature.as_slice(),
			expected_signature,
			"native oracle: {label}"
		);
		assert!(
			crypto_sign::verify_detached(&native_signature, &message, &keypair.public_key),
			"native signature verified by portable backend: {label}"
		);
		assert!(
			sodium::crypto_sign::verify_detached(&actual, &message, &native_keypair.public_key),
			"portable signature verified by native backend: {label}"
		);

		let mut expected_signed_message = expected_signature;
		expected_signed_message.extend_from_slice(&message);
		let signed_message = crypto_sign::sign(&message, &keypair.secret_key).expect(&label);
		let native_signed =
			sodium::crypto_sign::sign(&message, &native_keypair.secret_key).expect(&label);
		assert_eq!(signed_message, expected_signed_message, "{label}");
		assert_eq!(
			native_signed, expected_signed_message,
			"native oracle: {label}"
		);
		assert_eq!(
			crypto_sign::verify(&native_signed, &keypair.public_key).expect(&label),
			message,
			"native attached signature verified by portable backend: {label}"
		);
		assert_eq!(
			sodium::crypto_sign::verify(&signed_message, &native_keypair.public_key).expect(&label),
			message,
			"portable attached signature verified by native backend: {label}"
		);
	}
	assert_eq!(
		seen_ids,
		(1..=set.num_tests).collect(),
		"changed Ed25519 case IDs"
	);
}

#[test]
fn chacha20_poly1305_rooterberg() {
	let json = load_vector(CHACHA20_POLY1305_VECTOR);
	let set: TestSet<AeadAlgorithm, AeadTest> = parse_set(&json, "Aead");
	assert_eq!(
		set.algorithm,
		AeadAlgorithm {
			algorithm_type: "Aead".into(),
			primitive: "Chacha20Poly1305".into(),
			key_size: chacha20poly1305_ietf::KEYBYTES * 8,
			iv_size: chacha20poly1305_ietf::NPUBBYTES * 8,
			tag_size: chacha20poly1305_ietf::ABYTES * 8,
		},
		"unexpected Rooterberg ChaCha20-Poly1305 algorithm metadata"
	);

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let key = chacha20poly1305_ietf::Key::from_bytes(&decode_hex(&test.key)).expect(&label);
		let nonce =
			chacha20poly1305_ietf::Nonce::try_from_slice(&decode_hex(&test.iv)).expect(&label);
		let aad = decode_hex(&test.aad);
		let message = decode_hex(&test.msg);
		let ciphertext = decode_hex(&test.ct);
		let tag = decode_hex(&test.tag);
		let mut authenticated_ciphertext = ciphertext.clone();
		authenticated_ciphertext.extend_from_slice(&tag);
		let opened =
			chacha20poly1305_ietf::decrypt(&authenticated_ciphertext, Some(&aad), &nonce, &key);

		if test.valid {
			assert_eq!(opened.expect(&label), message, "{label}");
			let (actual_ciphertext, actual_tag) =
				chacha20poly1305_ietf::encrypt_detached(&message, Some(&aad), &nonce, &key)
					.expect(&label);
			assert_eq!(actual_ciphertext, ciphertext, "{label}");
			assert_eq!(actual_tag.as_slice(), tag, "{label}");
		} else {
			assert!(opened.is_err(), "{label}");
		}
	}
}

#[test]
fn hkdf_sha512_rooterberg() {
	let json = load_vector(HKDF_SHA512_VECTOR);
	let set: TestSet<HkdfAlgorithm, HkdfTest> = parse_set(&json, "Hkdf");
	assert_eq!(
		set.algorithm,
		HkdfAlgorithm {
			algorithm_type: "Hkdf".into(),
			primitive: "HkdfSha512".into(),
			sha: "SHA-512".into(),
		},
		"unexpected Rooterberg HKDF-SHA-512 algorithm metadata"
	);

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let ikm = decode_hex(&test.ikm);
		let salt = decode_hex(&test.salt);
		let info = decode_hex(&test.info);
		let expected = decode_hex(&test.okm);
		assert_eq!(expected.len(), test.out_len, "{label}");
		let actual = crypto_kdf::hkdf::sha512::extract(Some(&salt), &ikm)
			.and_then(|prk| crypto_kdf::hkdf::sha512::expand(test.out_len, Some(&info), &prk))
			.expect(&label);
		assert_eq!(actual, expected, "{label}");
	}
}

#[test]
fn blake2b_rooterberg() {
	let json = load_vector(BLAKE2B_VECTOR);
	let set: TestSet<HashAlgorithm, HashTest> = parse_set(&json, "Hash");
	assert_eq!(
		set.algorithm,
		HashAlgorithm {
			algorithm_type: "MessageDigest".into(),
			primitive: "blake2b".into(),
			digest_size: 512,
		},
		"unexpected Rooterberg BLAKE2b algorithm metadata"
	);
	let output_len = set.algorithm.digest_size / 8;

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let message = decode_hex(&test.msg);
		let expected = decode_hex(&test.digest);
		assert_eq!(expected.len(), output_len, "{label}");
		let actual = crypto_generichash::generichash(&message, None, output_len).expect(&label);
		assert_eq!(actual, expected, "{label}");

		for chunk_size in [1, 7, 127, 128, 129] {
			let mut state = crypto_generichash::State::new(None, output_len).expect(&label);
			state.update(&[]);
			for chunk in message.chunks(chunk_size) {
				state.update(chunk);
				state.update(&[]);
			}
			state.update(&[]);
			assert_eq!(
				state.finalize(),
				expected,
				"{label}; chunk size {chunk_size}"
			);
		}
	}
}

#[test]
fn hkdf_sha512_extract_hmac_rooterberg() {
	let json = load_vector(HMAC_SHA512_VECTOR);
	let set: TestSet<HmacAlgorithm, HmacTest> = parse_set(&json, "Mac");
	assert_eq!(
		set.algorithm,
		HmacAlgorithm {
			algorithm_type: "Mac".into(),
			primitive: "HmacSha512".into(),
			mac_size: 512,
		},
		"unexpected Rooterberg HMAC-SHA-512 algorithm metadata"
	);

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let key = decode_hex(&test.key);
		let message = decode_hex(&test.msg);
		let expected = decode_hex(&test.mac);
		assert_eq!(expected.len(), set.algorithm.mac_size / 8, "{label}");
		// HKDF-Extract(salt, IKM) is HMAC-SHA-512(salt, IKM).
		let actual = crypto_kdf::hkdf::sha512::extract(Some(&key), &message).expect(&label);
		assert_eq!(actual.as_bytes().as_slice(), expected, "{label}");
	}
}
