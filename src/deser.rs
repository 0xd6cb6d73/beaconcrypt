// SPDX-License-Identifier: 0BSD

use super::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, KeyMaterial, Ratchet, RatchetManager, RecvChain, SecretArr,
	SendChain, roles, systems,
};
#[cfg(feature = "server")]
use super::{RemotePrincipal, SignType, decode_sign};
#[cfg(feature = "server")]
use libsodium_rs::crypto_sign;
#[cfg(feature = "server")]
use serde::de::MapAccess;
use serde::{
	Deserialize, Deserializer,
	de::{self, Error as _, IgnoredAny, SeqAccess, Visitor},
};
use std::{collections::HashMap, fmt, marker::PhantomData};
use zeroize::{Zeroize, Zeroizing};

struct SecretBytes<const N: usize>(Zeroizing<[u8; N]>);

struct SecretBytesVisitor<const N: usize>;

impl<const N: usize> SecretBytesVisitor<N> {
	fn copy_from_slice<E>(value: &[u8]) -> Result<SecretBytes<N>, E>
	where
		E: de::Error,
	{
		if value.len() != N {
			return Err(E::custom(format!(
				"expected a {N}-byte buffer, got {} bytes",
				value.len()
			)));
		}

		let mut protected = Zeroizing::new([0; N]);
		protected.copy_from_slice(value);
		Ok(SecretBytes(protected))
	}
}

impl<'de, const N: usize> Visitor<'de> for SecretBytesVisitor<N> {
	type Value = SecretBytes<N>;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		write!(formatter, "a byte buffer containing exactly {N} bytes")
	}

	fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
	where
		E: de::Error,
	{
		Self::copy_from_slice(value)
	}

	fn visit_byte_buf<E>(self, mut value: Vec<u8>) -> Result<Self::Value, E>
	where
		E: de::Error,
	{
		let result = Self::copy_from_slice(&value);
		value.zeroize();
		result
	}

	fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
	where
		A: SeqAccess<'de>,
	{
		let mut protected = Zeroizing::new([0; N]);
		for index in 0..N {
			protected[index] = sequence.next_element()?.ok_or_else(|| {
				A::Error::custom(format!("expected a {N}-byte buffer, got {index} bytes"))
			})?;
		}

		if sequence.next_element::<IgnoredAny>()?.is_some() {
			return Err(A::Error::custom(format!(
				"expected a {N}-byte buffer, got more than {N} bytes"
			)));
		}

		Ok(SecretBytes(protected))
	}
}

impl<'de, const N: usize> Deserialize<'de> for SecretBytes<N> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_bytes(SecretBytesVisitor::<N>)
	}
}

struct TypedArray<const N: usize, System, Role> {
	buffer: SecretBytes<N>,
	_type: PhantomData<(System, Role)>,
}

struct TypedArrayVisitor<const N: usize, System, Role>(PhantomData<(System, Role)>);

impl<'de, const N: usize, System, Role> Visitor<'de> for TypedArrayVisitor<N, System, Role>
where
	System: systems::Identified,
	Role: roles::Identified,
{
	type Value = TypedArray<N, System, Role>;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str(
			"a typed array containing an algorithm identifier, role identifier, and byte buffer",
		)
	}

	fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
	where
		A: SeqAccess<'de>,
	{
		let algorithm: u8 = sequence
			.next_element()?
			.ok_or_else(|| A::Error::invalid_length(0, &self))?;
		let expected_algorithm = u8::from(System::IDENTIFIER);
		if systems::Identifier::from(algorithm) != System::IDENTIFIER {
			return Err(A::Error::custom(format!(
				"unexpected algorithm identifier {algorithm}; expected {expected_algorithm}"
			)));
		}

		let role: u8 = sequence
			.next_element()?
			.ok_or_else(|| A::Error::invalid_length(1, &self))?;
		let expected_role = u8::from(Role::IDENTIFIER);
		if roles::Identifier::from(role) != Role::IDENTIFIER {
			return Err(A::Error::custom(format!(
				"unexpected role identifier {role}; expected {expected_role}"
			)));
		}

		let buffer = sequence
			.next_element()?
			.ok_or_else(|| A::Error::invalid_length(2, &self))?;
		if sequence.next_element::<IgnoredAny>()?.is_some() {
			return Err(A::Error::invalid_length(4, &self));
		}

		Ok(TypedArray {
			buffer,
			_type: PhantomData,
		})
	}
}

impl<'de, const N: usize, System, Role> Deserialize<'de> for TypedArray<N, System, Role>
where
	System: systems::Identified,
	Role: roles::Identified,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_tuple(3, TypedArrayVisitor::<N, System, Role>(PhantomData))
	}
}

impl<'de, const N: usize, System, Role> Deserialize<'de> for SecretArr<N, System, Role>
where
	System: systems::Identified,
	Role: roles::Identified,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let typed = TypedArray::<N, System, Role>::deserialize(deserializer)?;
		Ok(Self {
			data: typed.buffer.0,
			_system: PhantomData,
			_role: PhantomData,
		})
	}
}

impl<'de, Role> Deserialize<'de> for Ratchet<Role> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		Ok(Self {
			state: Deserialize::deserialize(deserializer)?,
			_role: PhantomData,
		})
	}
}

#[derive(Deserialize)]
#[serde(rename = "KeyMaterial")]
struct KeyMaterialData {
	key: TypedArray<AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, roles::EncryptionKey>,
	nonce: TypedArray<AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, roles::Nonce>,
}

impl<'de> Deserialize<'de> for KeyMaterial {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = KeyMaterialData::deserialize(deserializer)?;
		Ok(Self {
			key: (*data.key.buffer.0).into(),
			nonce: (*data.nonce.buffer.0).into(),
		})
	}
}

#[derive(Deserialize)]
#[serde(rename = "RatchetManager")]
struct RatchetManagerData {
	send_key: SendChain,
	recv_key: RecvChain,
	send_past: HashMap<u64, KeyMaterial>,
	send_ctr: u64,
	recv_past: HashMap<u64, KeyMaterial>,
	recv_ctr: u64,
}

impl<'de> Deserialize<'de> for RatchetManager {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = RatchetManagerData::deserialize(deserializer)?;
		if data
			.send_past
			.keys()
			.any(|seq| *seq == 0 || *seq > data.send_ctr)
		{
			return Err(D::Error::custom(
				"send_past contains a sequence outside 1..=send_ctr",
			));
		}
		if data
			.recv_past
			.keys()
			.any(|seq| *seq == 0 || *seq > data.recv_ctr)
		{
			return Err(D::Error::custom(
				"recv_past contains a sequence outside 1..=recv_ctr",
			));
		}
		Ok(Self {
			send_key: data.send_key,
			recv_key: data.recv_key,
			send_past: data.send_past,
			send_ctr: data.send_ctr,
			recv_past: data.recv_past,
			recv_ctr: data.recv_ctr,
		})
	}
}

#[cfg(feature = "server")]
#[derive(Deserialize)]
#[serde(rename = "RemotePrincipal")]
struct RemotePrincipalData {
	pk: Vec<u8>,
	ratchet: RatchetManager,
}

#[cfg(feature = "server")]
impl<'de> Deserialize<'de> for RemotePrincipal<crypto_sign::PublicKey> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = RemotePrincipalData::deserialize(deserializer)?;
		let decoded = decode_sign(&data.pk, SignType::Ed25519)
			.map_err(|error| D::Error::custom(error.to_string()))?;
		let pk = crypto_sign::PublicKey::from_bytes(&decoded)
			.map_err(|_| D::Error::custom("invalid Ed25519 public key"))?;
		Ok(Self::new(pk, data.ratchet))
	}
}

#[cfg(feature = "server")]
struct DeserializedKnownIds(HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>);

#[cfg(feature = "server")]
pub(crate) fn deserialize_known_ids(
	state: &str,
) -> Option<HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>> {
	let DeserializedKnownIds(known_ids) = serde_json::from_str(state).ok()?;
	Some(known_ids)
}

#[cfg(feature = "server")]
struct KnownIdsVisitor;

#[cfg(feature = "server")]
impl<'de> Visitor<'de> for KnownIdsVisitor {
	type Value = DeserializedKnownIds;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str("a map from key IDs to remote principals")
	}

	fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
	where
		A: MapAccess<'de>,
	{
		let mut known_ids = HashMap::with_capacity(map.size_hint().unwrap_or(0));
		while let Some(kid) = map.next_key()? {
			if known_ids.contains_key(&kid) {
				return Err(A::Error::custom(format!("duplicate key ID {kid}")));
			}
			let principal = map.next_value()?;
			known_ids.insert(kid, principal);
		}
		Ok(DeserializedKnownIds(known_ids))
	}
}

#[cfg(feature = "server")]
impl<'de> Deserialize<'de> for DeserializedKnownIds {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_map(KnownIdsVisitor)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::shared::{KDF_STATE_SIZE, SYM_RATCHET_INFO};
	use serde::Serialize;
	use serde_json::{Value, json};

	fn assert_serde_traits<T>()
	where
		T: Serialize + for<'de> Deserialize<'de>,
	{
	}

	fn assert_key_material_eq(left: &KeyMaterial, right: &KeyMaterial) {
		assert_eq!(left.key.as_bytes(), right.key.as_bytes());
		assert_eq!(left.nonce.as_bytes(), right.nonce.as_bytes());
	}

	fn assert_manager_eq(left: &RatchetManager, right: &RatchetManager) {
		assert_eq!(
			left.send_key.state.as_slice(),
			right.send_key.state.as_slice()
		);
		assert_eq!(
			left.recv_key.state.as_slice(),
			right.recv_key.state.as_slice()
		);
		assert_eq!(left.send_ctr, right.send_ctr);
		assert_eq!(left.recv_ctr, right.recv_ctr);
		assert_eq!(left.send_past.len(), right.send_past.len());
		assert_eq!(left.recv_past.len(), right.recv_past.len());

		for (seq, key) in &left.send_past {
			assert_key_material_eq(key, right.send_past.get(seq).unwrap());
		}
		for (seq, key) in &left.recv_past {
			assert_key_material_eq(key, right.recv_past.get(seq).unwrap());
		}
	}

	fn populated_manager() -> RatchetManager {
		let mut manager = RatchetManager::default();
		manager.init_ratchets(&[0x42; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);

		for _ in 0..3 {
			manager.ratchet_send(SYM_RATCHET_INFO).unwrap();
		}
		manager.delete_send_key(2);
		manager.ratchet_recv_until(SYM_RATCHET_INFO, 4).unwrap();
		manager.delete_recv_key(1);
		manager.delete_recv_key(3);
		manager
	}

	#[test]
	fn ratchet_manager_implements_serde_traits() {
		assert_serde_traits::<RatchetManager>();
	}

	#[test]
	fn default_ratchet_manager_round_trips() {
		let manager = RatchetManager::default();
		let serialized = serde_json::to_string(&manager).unwrap();
		let restored = serde_json::from_str(&serialized).unwrap();

		assert_manager_eq(&manager, &restored);
	}

	#[test]
	fn populated_ratchet_manager_round_trips_and_continues() {
		let mut manager = populated_manager();
		let serialized = serde_json::to_string(&manager).unwrap();
		let mut restored = serde_json::from_str(&serialized).unwrap();

		assert_manager_eq(&manager, &restored);

		let next_send = manager.ratchet_send(SYM_RATCHET_INFO).unwrap();
		assert_eq!(restored.ratchet_send(SYM_RATCHET_INFO), Some(next_send));
		assert_key_material_eq(
			manager.send_key(next_send).unwrap(),
			restored.send_key(next_send).unwrap(),
		);

		let next_recv = manager.ratchet_recv(SYM_RATCHET_INFO).unwrap();
		assert_eq!(restored.ratchet_recv(SYM_RATCHET_INFO), Some(next_recv));
		assert_key_material_eq(
			manager.recv_key(next_recv).unwrap(),
			restored.recv_key(next_recv).unwrap(),
		);
	}

	#[test]
	fn serialized_keys_and_nonces_include_their_type_identifiers() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();
		let cases = [
			(
				&serialized["send_key"],
				systems::Identifier::HkdfSha512,
				roles::Identifier::ChainKey,
				KDF_STATE_SIZE,
			),
			(
				&serialized["recv_key"],
				systems::Identifier::HkdfSha512,
				roles::Identifier::ChainKey,
				KDF_STATE_SIZE,
			),
			(
				&serialized["send_past"]["1"]["key"],
				systems::Identifier::Chacha20Poly1305Ietf,
				roles::Identifier::EncryptionKey,
				AEAD_KEY_LEN,
			),
			(
				&serialized["recv_past"]["2"]["nonce"],
				systems::Identifier::Chacha20Poly1305Ietf,
				roles::Identifier::Nonce,
				AEAD_NONCE_LEN,
			),
		];

		for (typed, algorithm, role, buffer_len) in cases {
			let typed = typed.as_array().unwrap();
			assert_eq!(typed.len(), 3);
			assert_eq!(typed[0], json!(u8::from(algorithm)));
			assert_eq!(typed[1], json!(u8::from(role)));
			assert_eq!(typed[2].as_array().unwrap().len(), buffer_len);
		}
	}

	#[test]
	fn malformed_secret_lengths_are_rejected() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();

		for (path, invalid_len) in [
			(&["send_key"][..], KDF_STATE_SIZE - 1),
			(&["recv_key"][..], KDF_STATE_SIZE + 1),
			(&["send_past", "1", "key"][..], AEAD_KEY_LEN - 1),
			(&["recv_past", "2", "nonce"][..], AEAD_NONCE_LEN + 1),
		] {
			let mut malformed = serialized.clone();
			let mut typed = &mut malformed;
			for segment in path {
				typed = &mut typed[*segment];
			}
			typed[2] = Value::Array(vec![json!(0); invalid_len]);

			assert!(serde_json::from_value::<RatchetManager>(malformed).is_err());
		}
	}

	#[test]
	fn unknown_and_mismatched_type_identifiers_are_rejected() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();
		let mutations = [
			(
				&["send_key"][..],
				0,
				u8::from(systems::Identifier::Chacha20Poly1305Ietf),
			),
			(
				&["recv_key"][..],
				1,
				u8::from(roles::Identifier::EncryptionKey),
			),
			(&["send_past", "1", "key"][..], 0, 0),
			(&["send_past", "1", "key"][..], 1, u8::MAX),
			(
				&["recv_past", "2", "nonce"][..],
				0,
				u8::from(systems::Identifier::HkdfSha512),
			),
			(
				&["recv_past", "2", "nonce"][..],
				1,
				u8::from(roles::Identifier::EncryptionKey),
			),
		];

		for (path, identifier_index, replacement) in mutations {
			let mut malformed = serialized.clone();
			let mut typed = &mut malformed;
			for segment in path {
				typed = &mut typed[*segment];
			}
			typed[identifier_index] = json!(replacement);

			assert!(serde_json::from_value::<RatchetManager>(malformed).is_err());
		}
	}

	#[test]
	fn legacy_and_malformed_typed_arrays_are_rejected() {
		let serialized = serde_json::to_value(RatchetManager::default()).unwrap();

		let mut legacy = serialized.clone();
		legacy["send_key"] = json!(vec![0; KDF_STATE_SIZE]);
		assert!(serde_json::from_value::<RatchetManager>(legacy).is_err());

		let mut missing = serialized.clone();
		missing["send_key"].as_array_mut().unwrap().pop();
		assert!(serde_json::from_value::<RatchetManager>(missing).is_err());

		let mut extra = serialized;
		extra["send_key"].as_array_mut().unwrap().push(json!(0));
		assert!(serde_json::from_value::<RatchetManager>(extra).is_err());
	}

	#[test]
	fn missing_and_duplicate_fields_are_rejected() {
		let mut missing = serde_json::to_value(RatchetManager::default()).unwrap();
		missing.as_object_mut().unwrap().remove("recv_ctr");
		assert!(serde_json::from_value::<RatchetManager>(missing).is_err());

		let serialized = serde_json::to_string(&RatchetManager::default()).unwrap();
		let duplicate = serialized.replacen("\"send_ctr\":0", "\"send_ctr\":0,\"send_ctr\":1", 1);
		assert!(serde_json::from_str::<RatchetManager>(&duplicate).is_err());
	}

	#[test]
	fn type_identifiers_follow_the_undefined_zero_convention() {
		assert_eq!(u8::from(systems::Identifier::Undefined), 0);
		assert_eq!(u8::from(systems::Identifier::HkdfSha512), 6);
		assert_eq!(u8::from(systems::Identifier::Chacha20Poly1305Ietf), 7);
		assert!(matches!(
			systems::Identifier::from(0),
			systems::Identifier::Undefined
		));
		assert!(matches!(
			systems::Identifier::from(u8::MAX),
			systems::Identifier::Undefined
		));

		assert_eq!(u8::from(roles::Identifier::Undefined), 0);
		assert_eq!(u8::from(roles::Identifier::ChainKey), 8);
		assert_eq!(u8::from(roles::Identifier::EncryptionKey), 9);
		assert_eq!(u8::from(roles::Identifier::Nonce), 10);
		assert!(matches!(
			roles::Identifier::from(0),
			roles::Identifier::Undefined
		));
		assert!(matches!(
			roles::Identifier::from(u8::MAX),
			roles::Identifier::Undefined
		));
	}

	#[test]
	fn impossible_cached_key_sequences_are_rejected() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();

		let mut zero_sequence = serialized.clone();
		let cached_key = zero_sequence["send_past"]["1"].clone();
		zero_sequence["send_past"]
			.as_object_mut()
			.unwrap()
			.insert("0".into(), cached_key);
		assert!(serde_json::from_value::<RatchetManager>(zero_sequence).is_err());

		let mut future_sequence = serialized;
		let cached_key = future_sequence["recv_past"]["2"].clone();
		future_sequence["recv_past"]
			.as_object_mut()
			.unwrap()
			.insert("5".into(), cached_key);
		assert!(serde_json::from_value::<RatchetManager>(future_sequence).is_err());
	}
}
