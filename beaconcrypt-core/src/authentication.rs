// SPDX-License-Identifier: 0BSD

//! Exact ML-DSA registration authentication inputs, without hashing or signing.
//!
//! The adapter streams these bytes into BLAKE2b-512 and supplies the resulting digest to ML-DSA.
//! Keeping the layout here makes the production construction available to Hax extraction.

pub const INIT_DOMAIN: [u8; 41] = *b"beaconcrypt ML-DSA-65 init transcript v1\0";
pub const RESPONSE_DOMAIN: [u8; 45] = *b"beaconcrypt ML-DSA-65 response transcript v1\0";
pub const SIGNING_CONTEXT: [u8; 32] = *b"beaconcrypt registration auth v1";
pub const BEACON_LABEL: [u8; 34] = *b"beaconcrypt v1 beacon registration";
pub const SERVER_LABEL: [u8; 34] = *b"beaconcrypt v1 server registration";

pub const MLDSA_PUBLIC_KEY_LEN: usize = 1952;
pub const MLDSA_SIGNATURE_LEN: usize = 3309;
pub const TRANSCRIPT_HASH_LEN: usize = 64;
pub const INIT_TRANSCRIPT_LEN: usize = 5495;
pub const RESPONSE_PREFIX_LEN: usize = 1293;
pub const SIGNATURE_INPUT_LEN: usize = 163;

// Tie the literal offsets exposed by Hax to the production sizes.
const _: () = assert!(MLDSA_PUBLIC_KEY_LEN == 1952);
const _: () = assert!(TRANSCRIPT_HASH_LEN == 64);
const _: () = assert!(crate::constants::ASSOCIATED_DATA_SIZE == 281);

#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub enum AuthRole {
	Beacon,
	Server,
}

/// The unsigned, decoded request fields; the authentication signature is deliberately absent.
pub struct InitFields<'a> {
	pub identity_key: &'a [u8; 33],
	pub pre_key: &'a [u8; 98],
	pub one_time_key: &'a [u8; 98],
	pub pq_key: &'a [u8; 1249],
	pub mldsa_public_key: &'a [u8; MLDSA_PUBLIC_KEY_LEN],
}

pub const fn encode_u64_le(value: u64) -> [u8; 8] {
	[
		value as u8,
		(value >> 8) as u8,
		(value >> 16) as u8,
		(value >> 24) as u8,
		(value >> 32) as u8,
		(value >> 40) as u8,
		(value >> 48) as u8,
		(value >> 56) as u8,
	]
}

/// Build the domain, server pins, both ML-DSA keys, and LE64-framed request key material.
pub fn build_init_transcript(
	fields: InitFields<'_>,
	server_id: u64,
	server_ed: &[u8; 32],
	server_mldsa: &[u8; MLDSA_PUBLIC_KEY_LEN],
) -> [u8; INIT_TRANSCRIPT_LEN] {
	let server_id = encode_u64_le(server_id);
	let identity_len = encode_u64_le(33);
	let signed_key_len = encode_u64_le(98);
	let pq_key_len = encode_u64_le(1249);
	core::array::from_fn(|i| {
		if i < 41 {
			INIT_DOMAIN[i]
		} else if i < 49 {
			server_id[i - 41]
		} else if i < 81 {
			server_ed[i - 49]
		} else if i < 2033 {
			fields.mldsa_public_key[i - 81]
		} else if i < 3985 {
			server_mldsa[i - 2033]
		} else if i < 3993 {
			identity_len[i - 3985]
		} else if i < 4026 {
			fields.identity_key[i - 3993]
		} else if i < 4034 {
			signed_key_len[i - 4026]
		} else if i < 4132 {
			fields.pre_key[i - 4034]
		} else if i < 4140 {
			signed_key_len[i - 4132]
		} else if i < 4238 {
			fields.one_time_key[i - 4140]
		} else if i < 4246 {
			pq_key_len[i - 4238]
		} else {
			fields.pq_key[i - 4246]
		}
	})
}

/// The unsigned, decoded response fields, including the complete application ciphertext.
pub struct ResponseFields<'a> {
	pub identity_key: &'a [u8; 32],
	pub ephemeral_key: &'a [u8; 32],
	pub kem_cipher_text: &'a [u8; 1088],
	pub app_cipher_text: &'a [u8],
	pub key_id: u64,
}

/// The fixed prefix through the LE64 application-ciphertext length.
pub fn build_response_prefix(
	init_hash: &[u8; TRANSCRIPT_HASH_LEN],
	identity: &[u8; 32],
	ephemeral: &[u8; 32],
	kem: &[u8; 1088],
	app_len: u64,
) -> [u8; RESPONSE_PREFIX_LEN] {
	let public_key_len = encode_u64_le(32);
	let kem_len = encode_u64_le(1088);
	let app_len = encode_u64_le(app_len);
	core::array::from_fn(|i| {
		if i < 45 {
			RESPONSE_DOMAIN[i]
		} else if i < 109 {
			init_hash[i - 45]
		} else if i < 117 {
			public_key_len[i - 109]
		} else if i < 149 {
			identity[i - 117]
		} else if i < 157 {
			public_key_len[i - 149]
		} else if i < 189 {
			ephemeral[i - 157]
		} else if i < 197 {
			kem_len[i - 189]
		} else if i < 1285 {
			kem[i - 197]
		} else {
			app_len[i - 1285]
		}
	})
}

/// Ordered transcript parts that borrow the application ciphertext without copying it.
pub struct ResponseTranscript<'a> {
	prefix: [u8; RESPONSE_PREFIX_LEN],
	application: &'a [u8],
	assigned_id: [u8; 8],
}

impl ResponseTranscript<'_> {
	pub fn parts(&self) -> [&[u8]; 3] {
		[&self.prefix, self.application, &self.assigned_id]
	}
}

/// Bind the length and ordering to the same borrowed ciphertext that will be hashed.
pub fn build_response_transcript<'a>(
	init_hash: &[u8; TRANSCRIPT_HASH_LEN],
	fields: ResponseFields<'a>,
) -> Option<ResponseTranscript<'a>> {
	let app_len = match u64::try_from(fields.app_cipher_text.len()) {
		Ok(len) => len,
		Err(_) => return None,
	};
	Some(ResponseTranscript {
		prefix: build_response_prefix(
			init_hash,
			fields.identity_key,
			fields.ephemeral_key,
			fields.kem_cipher_text,
			app_len,
		),
		application: fields.app_cipher_text,
		assigned_id: encode_u64_le(fields.key_id),
	})
}

/// Build the TLS CertificateVerify-style role-separated ML-DSA message.
pub fn build_signature_input(
	role: AuthRole,
	digest: &[u8; TRANSCRIPT_HASH_LEN],
) -> [u8; SIGNATURE_INPUT_LEN] {
	let label = match role {
		AuthRole::Beacon => BEACON_LABEL,
		AuthRole::Server => SERVER_LABEL,
	};
	core::array::from_fn(|i| {
		if i < 64 {
			b' '
		} else if i < 98 {
			label[i - 64]
		} else if i == 98 {
			0
		} else {
			digest[i - 99]
		}
	})
}

/// Replace both reserved fingerprint slots after the classical 153-byte AD prefix.
pub fn bind_associated_data(
	base: &[u8; crate::constants::ASSOCIATED_DATA_SIZE],
	server_hash: &[u8; TRANSCRIPT_HASH_LEN],
	beacon_hash: &[u8; TRANSCRIPT_HASH_LEN],
) -> [u8; crate::constants::ASSOCIATED_DATA_SIZE] {
	core::array::from_fn(|i| {
		if i < 153 {
			base[i]
		} else if i < 217 {
			server_hash[i - 153]
		} else {
			beacon_hash[i - 217]
		}
	})
}
