// SPDX-License-Identifier: 0BSD

#![cfg(feature = "pqxdh")]

//! External ML-DSA-65 vectors exercise the primitive operations used by the authentication adapter.
//! Their arbitrary messages and contexts do not pass through the protocol's fixed transcript request types.
//! Seed-derived public keys additionally exercise the public `MldsaIdentity` wrapper.
//! Invalid seed widths are checked at admission to its fixed-size seed argument.
//! Expanded-key signing additionally exercises the dependency's deprecated import API, which production does not expose.
//! Its malformed-coefficient panics are caught and accounted for explicitly; they are not clean production rejections.

use std::{collections::BTreeSet, fs, panic::catch_unwind, path::Path};

use beaconcrypt::MldsaIdentity;
use ml_dsa::{
	EncodedVerifyingKey, ExpandedSigningKey, ExpandedSigningKeyBytes, MlDsa65, Signature,
	SigningKey, VerifyingKey,
};
use serde::Deserialize;

const WYCHEPROOF_VERIFY: &str =
	include_str!("../../wycheproof/testvectors_v1/mldsa_65_verify_test.json");
const WYCHEPROOF_SIGN_SEED: &str =
	include_str!("../../wycheproof/testvectors_v1/mldsa_65_sign_seed_test.json");
const WYCHEPROOF_SIGN_EXPANDED: &str =
	include_str!("../../wycheproof/testvectors_v1/mldsa_65_sign_noseed_test.json");
const ROOTERBERG_VERSION: &str = "0.65";
const ROOTERBERG_VERIFY: &str = "ml_dsa/ml_dsa_65.json";
const ROOTERBERG_SIGN: &str = "ml_dsa/ml_dsa_65_sign.json";
const ROOTERBERG_SEED_PKCS8_PREFIX: &str = "3034020100300b060960864801650304031204228020";

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Case {
	tc_id: usize,
	#[serde(default)]
	comment: String,
	#[serde(default)]
	flags: Vec<String>,
}

impl Case {
	fn label(&self) -> String {
		format!(
			"tcId {} ({}; flags: {})",
			self.tc_id,
			self.comment,
			self.flags.join(",")
		)
	}

	fn has_flag(&self, flag: &str) -> bool {
		self.flags.iter().any(|actual| actual == flag)
	}
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
enum TestResult {
	Valid,
	Invalid,
	Acceptable,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct WycheproofSet<Group> {
	algorithm: String,
	schema: String,
	number_of_tests: usize,
	test_groups: Vec<Group>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct VerifyGroup {
	#[serde(rename = "type")]
	group_type: String,
	public_key: String,
	tests: Vec<WycheproofVerifyCase>,
}

#[derive(Debug, Deserialize)]
struct WycheproofVerifyCase {
	#[serde(flatten)]
	case: Case,
	msg: String,
	#[serde(default)]
	ctx: String,
	sig: String,
	result: TestResult,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SignSeedGroup {
	#[serde(rename = "type")]
	group_type: String,
	private_seed: String,
	public_key: Option<String>,
	tests: Vec<WycheproofSignCase>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SignExpandedGroup {
	#[serde(rename = "type")]
	group_type: String,
	private_key: String,
	public_key: Option<String>,
	tests: Vec<WycheproofSignCase>,
}

#[derive(Debug, Deserialize)]
struct WycheproofSignCase {
	#[serde(flatten)]
	case: Case,
	msg: Option<String>,
	ctx: Option<String>,
	mu: Option<String>,
	rnd: Option<String>,
	sig: String,
	result: TestResult,
}

#[derive(Debug, Default, Eq, PartialEq)]
struct SigningCounts {
	deterministic_message: usize,
	internal_mu: usize,
	randomized_message: usize,
	invalid_context: usize,
	invalid_key_width: usize,
	invalid_key_coefficients: usize,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RooterbergSet<Test> {
	test_type: String,
	algorithm: RooterbergAlgorithm,
	version: String,
	num_tests: usize,
	tests: Vec<Test>,
}

#[derive(Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
struct RooterbergAlgorithm {
	algorithm_type: String,
	primitive: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RooterbergVerifyCase {
	#[serde(flatten)]
	case: Case,
	public_key: String,
	msg: String,
	sig: String,
	valid: bool,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RooterbergSignCase {
	#[serde(flatten)]
	case: Case,
	private_key: String,
	private_key_pkcs8: String,
	msg: String,
	sig: String,
}

fn decode_hex(input: &str, label: &str) -> Vec<u8> {
	fn nibble(byte: u8, label: &str) -> u8 {
		match byte {
			b'0'..=b'9' => byte - b'0',
			b'a'..=b'f' => byte - b'a' + 10,
			b'A'..=b'F' => byte - b'A' + 10,
			_ => panic!("invalid hex digit: {label}"),
		}
	}

	assert_eq!(input.len() % 2, 0, "odd-length vector hex: {label}");
	input
		.as_bytes()
		.as_chunks::<2>()
		.0
		.iter()
		.map(|pair| (nibble(pair[0], label) << 4) | nibble(pair[1], label))
		.collect()
}

fn assert_case_inventory(
	ids: impl Iterator<Item = usize>,
	declared_count: usize,
	reviewed_count: usize,
	label: &str,
) {
	let mut seen = BTreeSet::new();
	let mut count = 0;
	for id in ids {
		assert!(seen.insert(id), "duplicate vector tcId {id}: {label}");
		count += 1;
	}
	assert_eq!(
		count, declared_count,
		"metadata differs from parsed test count: {label}"
	);
	assert_eq!(
		count, reviewed_count,
		"reviewed vector count changed: {label}"
	);
}

fn corpus_files(directory: &Path, parameter_set: &str) -> BTreeSet<String> {
	fs::read_dir(directory)
		.unwrap_or_else(|error| panic!("read vector directory {}: {error}", directory.display()))
		.map(|entry| entry.expect("read vector directory entry").file_name())
		.filter_map(|name| name.into_string().ok())
		.filter(|name| {
			name.strip_suffix(".json").is_some_and(|stem| {
				stem == parameter_set
					|| stem
						.strip_prefix(parameter_set)
						.is_some_and(|suffix| suffix.starts_with('_'))
			})
		})
		.collect()
}

fn parse_wycheproof<Group>(json: &str, schema: &str) -> WycheproofSet<Group>
where
	Group: for<'de> Deserialize<'de>,
{
	let set: WycheproofSet<Group> = serde_json::from_str(json).expect("valid Wycheproof JSON");
	assert_eq!(
		set.algorithm, "ML-DSA-65",
		"unexpected Wycheproof algorithm"
	);
	assert_eq!(set.schema, schema, "unexpected Wycheproof schema");
	set
}

fn load_rooterberg<Test>(relative_path: &str, test_type: &str) -> RooterbergSet<Test>
where
	Test: for<'de> Deserialize<'de>,
{
	let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
	let path = manifest_dir
		.join("../rooterberg/test_vectors")
		.join(relative_path);
	let json = fs::read_to_string(&path).unwrap_or_else(|error| {
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
	});
	let set: RooterbergSet<Test> = serde_json::from_str(&json).expect("valid Rooterberg JSON");
	assert_eq!(set.test_type, test_type, "unexpected Rooterberg test type");
	assert_eq!(
		set.version, ROOTERBERG_VERSION,
		"unexpected Rooterberg format version"
	);
	assert_eq!(
		set.algorithm,
		RooterbergAlgorithm {
			algorithm_type: "MlDsa".into(),
			primitive: "ML-DSA-65".into(),
		},
		"unexpected Rooterberg algorithm metadata"
	);
	assert_eq!(
		set.num_tests,
		set.tests.len(),
		"Rooterberg metadata count differs from parsed test count"
	);
	set
}

fn verify(public: &[u8], message: &[u8], context: &[u8], signature: &[u8]) -> bool {
	let Ok(encoded) = <&EncodedVerifyingKey<MlDsa65>>::try_from(public) else {
		return false;
	};
	let Ok(signature) = Signature::<MlDsa65>::try_from(signature) else {
		return false;
	};
	VerifyingKey::decode(encoded).verify_with_context(message, context, &signature)
}

fn assert_wycheproof_signature(
	key: &ExpandedSigningKey<MlDsa65>,
	test: WycheproofSignCase,
	counts: &mut SigningCounts,
) {
	let label = test.case.label();
	let expected = decode_hex(&test.sig, &label);
	let actual = if test.case.has_flag("Internal") {
		counts.internal_mu += 1;
		assert!(!test.case.has_flag("Randomized"), "{label}");
		assert!(
			test.msg.is_none() && test.ctx.is_none() && test.rnd.is_none(),
			"{label}"
		);
		let mu = decode_hex(test.mu.as_deref().expect(&label), &label);
		let mu: [u8; 64] = mu.try_into().expect(&label);
		Some(key.sign_mu_deterministic(&mu.into()))
	} else {
		let message = decode_hex(test.msg.as_deref().expect(&label), &label);
		let context = decode_hex(test.ctx.as_deref().unwrap_or_default(), &label);
		if test.case.has_flag("Randomized") {
			counts.randomized_message += 1;
			assert!(context.len() <= 255, "{label}");
			let random = decode_hex(test.rnd.as_deref().expect(&label), &label);
			let random: [u8; 32] = random.try_into().expect(&label);
			// Supply the vector's entropy to the FIPS 204 external message domain encoding.
			let prefix = [0, context.len() as u8];
			Some(key.sign_internal(&[&prefix, &context, &message], &random.into()))
		} else {
			assert!(test.rnd.is_none(), "unreviewed signing randomness: {label}");
			if test.result == TestResult::Invalid {
				counts.invalid_context += 1;
				assert!(test.case.has_flag("InvalidContext"), "{label}");
				assert!(context.len() > 255, "{label}");
			} else {
				counts.deterministic_message += 1;
			}
			key.sign_deterministic(&message, &context).ok()
		}
	};
	match test.result {
		TestResult::Valid => {
			let actual = actual.expect(&label);
			assert_eq!(actual.encode().as_slice(), expected, "{label}");
			let public_key = key.verifying_key();
			let verifies = if test.case.has_flag("Internal") {
				let mu = decode_hex(test.mu.as_deref().expect(&label), &label);
				let mu: [u8; 64] = mu.try_into().expect(&label);
				public_key.verify_mu(&mu.into(), &actual)
			} else {
				let message = decode_hex(test.msg.as_deref().expect(&label), &label);
				let context = decode_hex(test.ctx.as_deref().unwrap_or_default(), &label);
				public_key.verify_with_context(&message, &context, &actual)
			};
			assert!(verifies, "generated signature did not verify: {label}");
		}
		TestResult::Invalid => assert!(actual.is_none(), "{label}"),
		TestResult::Acceptable => panic!("unreviewed acceptable ML-DSA result: {label}"),
	}
}

#[test]
fn mldsa65_corpus_inventory() {
	let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
	// A new file requires an explicit relevance review before changing this raw-primitive inventory.
	assert_eq!(
		corpus_files(
			&manifest_dir.join("../wycheproof/testvectors_v1"),
			"mldsa_65"
		),
		[
			"mldsa_65_sign_seed_test.json".to_owned(),
			"mldsa_65_sign_noseed_test.json".to_owned(),
			"mldsa_65_verify_test.json".to_owned(),
		]
		.into_iter()
		.collect(),
		"reviewed Wycheproof ML-DSA-65 corpus changed"
	);
	assert_eq!(
		corpus_files(
			&manifest_dir.join("../rooterberg/test_vectors/ml_dsa"),
			"ml_dsa_65"
		),
		[
			"ml_dsa_65.json".to_owned(),
			"ml_dsa_65_sign.json".to_owned()
		]
		.into_iter()
		.collect(),
		"reviewed Rooterberg ML-DSA-65 corpus changed"
	);
}

#[test]
fn mldsa65_verification_wycheproof() {
	let set: WycheproofSet<VerifyGroup> =
		parse_wycheproof(WYCHEPROOF_VERIFY, "mldsa_verify_schema.json");
	assert_case_inventory(
		set.test_groups
			.iter()
			.flat_map(|group| group.tests.iter().map(|test| test.case.tc_id)),
		set.number_of_tests,
		210,
		"Wycheproof ML-DSA-65 verification",
	);
	for group in set.test_groups {
		assert_eq!(
			group.group_type, "MlDsaVerify",
			"unexpected Wycheproof group type"
		);
		for test in group.tests {
			let label = test.case.label();
			let public_key = decode_hex(&group.public_key, &label);
			let message = decode_hex(&test.msg, &label);
			let context = decode_hex(&test.ctx, &label);
			let signature = decode_hex(&test.sig, &label);
			let verifies = verify(&public_key, &message, &context, &signature);
			match test.result {
				TestResult::Valid => assert!(verifies, "{label}"),
				TestResult::Invalid => assert!(!verifies, "{label}"),
				TestResult::Acceptable => panic!("unreviewed acceptable ML-DSA result: {label}"),
			}
		}
	}
}

#[test]
fn mldsa65_seed_signing_wycheproof() {
	let set: WycheproofSet<SignSeedGroup> =
		parse_wycheproof(WYCHEPROOF_SIGN_SEED, "mldsa_sign_seed_schema.json");
	assert_case_inventory(
		set.test_groups
			.iter()
			.flat_map(|group| group.tests.iter().map(|test| test.case.tc_id)),
		set.number_of_tests,
		105,
		"Wycheproof ML-DSA-65 seed signing",
	);
	let mut counts = SigningCounts::default();
	let mut public_key_count = 0;
	for group in set.test_groups {
		assert_eq!(
			group.group_type, "MlDsaSign",
			"unexpected Wycheproof group type"
		);
		let group_label = group
			.tests
			.first()
			.expect("nonempty Wycheproof signing group")
			.case
			.label();
		let seed = decode_hex(&group.private_seed, &group_label);
		let key = <[u8; 32]>::try_from(seed.as_slice()).ok().map(|seed| {
			let public_key = decode_hex(
				group.public_key.as_deref().expect(&group_label),
				&group_label,
			);
			assert_eq!(
				MldsaIdentity::from_seed(seed).public_key().as_slice(),
				public_key,
				"{group_label}"
			);
			public_key_count += 1;
			SigningKey::<MlDsa65>::from_seed(&seed.into())
		});
		for test in group.tests {
			let label = test.case.label();
			let Some(key) = key.as_ref() else {
				counts.invalid_key_width += 1;
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(test.case.has_flag("IncorrectPrivateKeyLength"), "{label}");
				assert!(group.public_key.is_none(), "{label}");
				continue;
			};
			assert_wycheproof_signature(key.expanded_key(), test, &mut counts);
		}
	}
	assert_eq!(
		public_key_count, 39,
		"Wycheproof seed public-key inventory changed"
	);
	assert_eq!(
		counts,
		SigningCounts {
			deterministic_message: 83,
			internal_mu: 17,
			randomized_message: 1,
			invalid_context: 1,
			invalid_key_width: 3,
			invalid_key_coefficients: 0,
		},
		"Wycheproof seed signing category inventory changed"
	);
}

#[test]
fn mldsa65_expanded_key_signing_wycheproof() {
	let set: WycheproofSet<SignExpandedGroup> =
		parse_wycheproof(WYCHEPROOF_SIGN_EXPANDED, "mldsa_sign_noseed_schema.json");
	assert_case_inventory(
		set.test_groups
			.iter()
			.flat_map(|group| group.tests.iter().map(|test| test.case.tc_id)),
		set.number_of_tests,
		78,
		"Wycheproof ML-DSA-65 expanded-key signing",
	);
	let mut counts = SigningCounts::default();
	let mut public_key_count = 0;
	for group in set.test_groups {
		assert_eq!(
			group.group_type, "MlDsaSign",
			"unexpected Wycheproof group type"
		);
		let group_label = group
			.tests
			.first()
			.expect("nonempty Wycheproof signing group")
			.case
			.label();
		let private_key = decode_hex(&group.private_key, &group_label);
		let encoded = <&ExpandedSigningKeyBytes<MlDsa65>>::try_from(private_key.as_slice());
		let Ok(encoded) = encoded else {
			assert!(group.public_key.is_none(), "{group_label}");
			for test in group.tests {
				let label = test.case.label();
				counts.invalid_key_width += 1;
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(test.case.has_flag("IncorrectPrivateKeyLength"), "{label}");
			}
			continue;
		};
		// The dependency's deprecated raw importer panics on malformed s1/s2 coefficients.
		// Catch and assert that actual importer behavior; production accepts seed keys only.
		#[allow(deprecated)]
		let key = catch_unwind(|| ExpandedSigningKey::<MlDsa65>::from_expanded(encoded));
		let Ok(key) = key else {
			for test in group.tests {
				let label = test.case.label();
				counts.invalid_key_coefficients += 1;
				assert_eq!(test.result, TestResult::Invalid, "{label}");
				assert!(test.case.has_flag("InvalidPrivateKey"), "{label}");
			}
			continue;
		};
		let public_key = decode_hex(
			group.public_key.as_deref().expect(&group_label),
			&group_label,
		);
		assert_eq!(
			key.verifying_key().encode().as_slice(),
			public_key,
			"{group_label}"
		);
		public_key_count += 1;
		for test in group.tests {
			assert_wycheproof_signature(&key, test, &mut counts);
		}
	}
	assert_eq!(
		public_key_count, 19,
		"Wycheproof expanded public-key inventory changed"
	);
	assert_eq!(
		counts,
		SigningCounts {
			deterministic_message: 62,
			internal_mu: 10,
			randomized_message: 1,
			invalid_context: 1,
			invalid_key_width: 2,
			invalid_key_coefficients: 2,
		},
		"Wycheproof expanded signing category inventory changed"
	);
}

#[test]
fn mldsa65_verification_rooterberg() {
	let set: RooterbergSet<RooterbergVerifyCase> =
		load_rooterberg(ROOTERBERG_VERIFY, "MlDsaVerify");
	assert_case_inventory(
		set.tests.iter().map(|test| test.case.tc_id),
		set.num_tests,
		64,
		"Rooterberg ML-DSA-65 verification",
	);
	for test in set.tests {
		let label = test.case.label();
		let public_key = decode_hex(&test.public_key, &label);
		let message = decode_hex(&test.msg, &label);
		let signature = decode_hex(&test.sig, &label);
		assert_eq!(
			verify(&public_key, &message, &[], &signature),
			test.valid,
			"{label}"
		);
	}
}

#[test]
fn mldsa65_seed_signing_rooterberg() {
	let set: RooterbergSet<RooterbergSignCase> = load_rooterberg(ROOTERBERG_SIGN, "MlDsa");
	assert_case_inventory(
		set.tests.iter().map(|test| test.case.tc_id),
		set.num_tests,
		34,
		"Rooterberg ML-DSA-65 seed signing",
	);
	for test in set.tests {
		let label = test.case.label();
		let encoded_seed = decode_hex(&test.private_key_pkcs8, &label);
		let prefix = decode_hex(ROOTERBERG_SEED_PKCS8_PREFIX, &label);
		assert_eq!(encoded_seed.len(), prefix.len() + 32, "{label}");
		assert!(
			encoded_seed.starts_with(&prefix),
			"unexpected seed PKCS#8 encoding: {label}"
		);
		let seed: [u8; 32] = encoded_seed[prefix.len()..].try_into().expect(&label);
		let key = SigningKey::<MlDsa65>::from_seed(&seed.into());
		#[allow(deprecated)]
		let expanded = key.expanded_key().to_expanded();
		assert_eq!(
			expanded.as_slice(),
			decode_hex(&test.private_key, &label),
			"{label}"
		);
		let message = decode_hex(&test.msg, &label);
		let actual = key
			.expanded_key()
			.sign_deterministic(&message, &[])
			.expect(&label);
		assert_eq!(
			actual.encode().as_slice(),
			decode_hex(&test.sig, &label),
			"{label}"
		);
	}
}
