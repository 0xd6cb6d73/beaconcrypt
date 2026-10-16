use std::{fs, path::Path};

use libsodium_rs::{
	crypto_aead::chacha20poly1305_ietf, crypto_generichash, crypto_kdf, crypto_scalarmult,
	crypto_sign, ensure_init,
};
use serde::Deserialize;

const ROOTERBERG_VERSION: &str = "0.65";
const X25519_VECTOR: &str = "xdh/x25519.json";
const ED25519_VERIFY_VECTOR: &str = "eddsa/ed25519.json";
const ED25519_SIGN_VECTOR: &str = "eddsa/ed25519_sign.json";
const CHACHA20_POLY1305_VECTOR: &str = "aead/chacha20_poly1305.json";
const HKDF_SHA512_VECTOR: &str = "kdf/hkdf_sha512.json";
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
fn x25519_rooterberg() {
	initialize_test_runtime();
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
fn ed25519_verification_rooterberg() {
	initialize_test_runtime();
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

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let public_key =
			crypto_sign::PublicKey::from_bytes(&decode_hex(&test.public_key)).expect(&label);
		let message = decode_hex(&test.msg);
		let signature = decode_hex(&test.sig);
		let verifies = <&[u8; crypto_sign::BYTES]>::try_from(signature.as_slice())
			.is_ok_and(|signature| crypto_sign::verify_detached(signature, &message, &public_key));
		assert_eq!(verifies, test.valid, "{label}");
	}
}

#[test]
fn ed25519_signing_rooterberg() {
	initialize_test_runtime();
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

	for test in set.tests {
		let label = case_label(test.tc_id, &test.comment, &test.flags);
		let private_key = decode_hex(&test.private_key);
		let keypair = crypto_sign::KeyPair::from_seed(&private_key).expect(&label);
		let message = decode_hex(&test.msg);
		let actual = crypto_sign::sign_detached(&message, &keypair.secret_key).expect(&label);
		assert_eq!(actual.as_slice(), decode_hex(&test.sig), "{label}");
	}
}

#[test]
fn chacha20_poly1305_rooterberg() {
	initialize_test_runtime();
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
	initialize_test_runtime();
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
	initialize_test_runtime();
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
	}
}
