// SPDX-License-Identifier: 0BSD

//! Exact registration authentication and record-context inputs, without hashing or signing.
//!
//! The adapter streams these bytes into BLAKE2b-512 and supplies the resulting digest to ML-DSA.
//! Keeping the layout here makes the production construction available to Hax extraction.

pub const INIT_DOMAIN: [u8; 41] = *b"beaconcrypt ML-DSA-65 init transcript v2\0";
pub const RESPONSE_DOMAIN: [u8; 45] = *b"beaconcrypt ML-DSA-65 response transcript v2\0";
pub const SIGNING_CONTEXT: [u8; 32] = *b"beaconcrypt registration auth v1";
pub const BEACON_LABEL: [u8; 34] = *b"beaconcrypt v1 beacon registration";
pub const SERVER_LABEL: [u8; 34] = *b"beaconcrypt v1 server registration";

pub const MLDSA_PUBLIC_KEY_LEN: usize = 1952;
pub const MLDSA_SIGNATURE_LEN: usize = 3309;
pub const TRANSCRIPT_HASH_LEN: usize = 64;
pub const INIT_TRANSCRIPT_LEN: usize = 3543;
pub const RESPONSE_PREFIX_LEN: usize = 1293;
pub const SIGNATURE_INPUT_LEN: usize = 163;

// Tie the literal offsets exposed by Hax to the production sizes.
const _: () = assert!(MLDSA_PUBLIC_KEY_LEN == 1952);
const _: () = assert!(TRANSCRIPT_HASH_LEN == 64);
const _: () = assert!(crate::constants::ASSOCIATED_DATA_SIZE == 151);

#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub enum AuthRole {
	Beacon,
	Server,
}

/// The exact remaining decoded InitKex fields, including their attached Ed25519 signatures.
pub struct InitFields<'a> {
	pub identity_key: &'a [u8; 33],
	pub pre_key: &'a [u8; 98],
	pub one_time_key: &'a [u8; 98],
	pub pq_key: &'a [u8; 1249],
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

/// Build the versioned request digest input with the Server pin and LE64-framed key fields.
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
			server_mldsa[i - 81]
		} else if i < 2041 {
			identity_len[i - 2033]
		} else if i < 2074 {
			fields.identity_key[i - 2041]
		} else if i < 2082 {
			signed_key_len[i - 2074]
		} else if i < 2180 {
			fields.pre_key[i - 2082]
		} else if i < 2188 {
			signed_key_len[i - 2180]
		} else if i < 2286 {
			fields.one_time_key[i - 2188]
		} else if i < 2294 {
			pq_key_len[i - 2286]
		} else {
			fields.pq_key[i - 2294]
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

/// Public InitKex buffers retained unchanged until the response public fields exist.
///
/// These include all three attached Ed25519 signatures; opened public keys are insufficient.
pub struct OwnedInitFields {
	identity_key: [u8; 33],
	pre_key: [u8; 98],
	one_time_key: [u8; 98],
	pq_key: [u8; 1249],
}

impl OwnedInitFields {
	pub fn new(fields: InitFields<'_>) -> Self {
		Self {
			identity_key: *fields.identity_key,
			pre_key: *fields.pre_key,
			one_time_key: *fields.one_time_key,
			pq_key: *fields.pq_key,
		}
	}

	pub const fn fields(&self) -> InitFields<'_> {
		InitFields {
			identity_key: &self.identity_key,
			pre_key: &self.pre_key,
			one_time_key: &self.one_time_key,
			pq_key: &self.pq_key,
		}
	}

	pub fn identity_public_key(&self) -> [u8; 32] {
		core::array::from_fn(|i| self.identity_key[i + 1])
	}
}

pub const INIT_FIELDS_LEN: usize = 1478;
pub const RECORD_AD_TRANSCRIPT_LEN: usize = 2638;
pub const AD_CONTEXT_LEN: usize = 87;
/// The context retained outside the transcript digest, independent of either ratchet KDF label.
pub const AD_CONTEXT: [u8; AD_CONTEXT_LEN] =
	*b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305";

/// Only response fields available before the first protected record is sealed.
pub struct AdResponseFields<'a> {
	pub identity_key: &'a [u8; 32],
	pub ephemeral_key: &'a [u8; 32],
	pub kem_cipher_text: &'a [u8; 1088],
	pub key_id: u64,
}

/// Allocation-free, exact-width encoding; field positions are role framing.
pub fn build_record_ad_transcript(
	init: InitFields<'_>,
	response: AdResponseFields<'_>,
) -> [u8; RECORD_AD_TRANSCRIPT_LEN] {
	let key_id = encode_u64_le(response.key_id);
	core::array::from_fn(|i| {
		if i < 33 {
			init.identity_key[i]
		} else if i < 131 {
			init.pre_key[i - 33]
		} else if i < 229 {
			init.one_time_key[i - 131]
		} else if i < 1478 {
			init.pq_key[i - 229]
		} else if i < 1510 {
			response.identity_key[i - 1478]
		} else if i < 1542 {
			response.ephemeral_key[i - 1510]
		} else if i < 2630 {
			response.kem_cipher_text[i - 1542]
		} else {
			key_id[i - 2630]
		}
	})
}

/// Assemble the one authoritative public context for AEAD and CTX in this session.
pub fn assemble_associated_data(
	transcript_hash: &[u8; TRANSCRIPT_HASH_LEN],
) -> [u8; crate::constants::ASSOCIATED_DATA_SIZE] {
	core::array::from_fn(|i| {
		if i < 87 {
			AD_CONTEXT[i]
		} else {
			transcript_hash[i - 87]
		}
	})
}
