// SPDX-License-Identifier: 0BSD

//! Mandatory prototype envelope around the existing registration codecs.
//! Transcript hashes use decoded fields, independently of this envelope and CBOR.

use crate::auth::{MLDSA_PUBLIC_KEY_LEN, MLDSA_SIGNATURE_LEN};

const MAGIC: &[u8] = b"beaconcrypt/ml-dsa-65/v1\0";
const INIT: u8 = 0;
const RESPONSE: u8 = 1;

#[cfg(any(feature = "server", test))]
pub(crate) const INIT_OVERHEAD: usize =
	MAGIC.len() + 1 + MLDSA_PUBLIC_KEY_LEN + MLDSA_SIGNATURE_LEN;
pub(crate) const RESPONSE_OVERHEAD: usize = MAGIC.len() + 1 + MLDSA_SIGNATURE_LEN;

#[cfg(any(feature = "server", test))]
pub(crate) fn response_fits(payload_len: usize) -> bool {
	payload_len
		.checked_add(RESPONSE_OVERHEAD)
		.is_some_and(|len| len <= crate::MAX_MESSAGE_SIZE)
}

fn encode(kind: u8, key: &[u8], signature: &[u8], payload: &[u8]) -> Option<Vec<u8>> {
	if signature.len() != MLDSA_SIGNATURE_LEN {
		return None;
	}
	let len = MAGIC
		.len()
		.checked_add(1)?
		.checked_add(key.len())?
		.checked_add(signature.len())?
		.checked_add(payload.len())?;
	if len > crate::MAX_MESSAGE_SIZE {
		return None;
	}
	let mut output = Vec::new();
	output.try_reserve_exact(len).ok()?;
	output.extend_from_slice(MAGIC);
	output.push(kind);
	output.extend_from_slice(key);
	output.extend_from_slice(signature);
	output.extend_from_slice(payload);
	Some(output)
}

#[cfg(any(feature = "beacon", test))]
pub(crate) fn encode_init(
	key: &[u8; MLDSA_PUBLIC_KEY_LEN],
	signature: &[u8],
	payload: &[u8],
) -> Option<Vec<u8>> {
	encode(INIT, key, signature, payload)
}

#[cfg(any(feature = "server", test))]
pub(crate) fn encode_response(signature: &[u8], payload: &[u8]) -> Option<Vec<u8>> {
	encode(RESPONSE, &[], signature, payload)
}

fn decode(bytes: &[u8], kind: u8, overhead: usize) -> Option<&[u8]> {
	if bytes.len() <= overhead || bytes.len() > crate::MAX_MESSAGE_SIZE {
		return None;
	}
	let body = bytes.strip_prefix(MAGIC)?;
	let (&actual_kind, body) = body.split_first()?;
	(actual_kind == kind).then_some(body)
}

#[cfg(any(feature = "server", test))]
pub(crate) fn decode_init(bytes: &[u8]) -> Option<(&[u8; MLDSA_PUBLIC_KEY_LEN], &[u8], &[u8])> {
	let body = decode(bytes, INIT, INIT_OVERHEAD)?;
	let (key, body) = body.split_at(MLDSA_PUBLIC_KEY_LEN);
	let (signature, payload) = body.split_at(MLDSA_SIGNATURE_LEN);
	Some((key.try_into().ok()?, signature, payload))
}

#[cfg(any(feature = "beacon", test))]
pub(crate) fn decode_response(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
	let body = decode(bytes, RESPONSE, RESPONSE_OVERHEAD)?;
	Some(body.split_at(MLDSA_SIGNATURE_LEN))
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn envelopes_preserve_fields_and_reject_every_header_only_prefix() {
		let key = [0x57; MLDSA_PUBLIC_KEY_LEN];
		let signature = [0xa3; MLDSA_SIGNATURE_LEN];
		let payload = [0x80];
		let init = encode_init(&key, &signature, &payload).unwrap();
		let init_header = init.len() - payload.len();
		assert_eq!(INIT_OVERHEAD, init_header);
		assert_eq!(
			decode_init(&init),
			Some((&key, signature.as_slice(), payload.as_slice()))
		);
		for end in 0..=init_header {
			assert!(
				decode_init(&init[..end]).is_none(),
				"accepted init prefix {end}"
			);
		}

		let response = encode_response(&signature, &payload).unwrap();
		let response_header = response.len() - payload.len();
		assert_eq!(RESPONSE_OVERHEAD, response_header);
		assert_eq!(
			decode_response(&response),
			Some((signature.as_slice(), payload.as_slice()))
		);
		for end in 0..=response_header {
			assert!(
				decode_response(&response[..end]).is_none(),
				"accepted response prefix {end}"
			);
		}
	}

	#[test]
	fn response_size_admission_counts_the_complete_envelope_and_rejects_overflow() {
		let payload = [0x80];
		let encoded = encode_response(&[0xa3; MLDSA_SIGNATURE_LEN], &payload).unwrap();
		let actual_header = encoded.len() - payload.len();
		let maximum_payload = crate::MAX_MESSAGE_SIZE - actual_header;
		assert!(response_fits(0));
		assert!(response_fits(maximum_payload));
		assert!(!response_fits(maximum_payload + 1));
		assert!(!response_fits(usize::MAX));
	}
}
