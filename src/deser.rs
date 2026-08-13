// SPDX-License-Identifier: 0BSD

#[cfg(feature = "server")]
use super::{EstablishedRemote, SignType, decode_sign};
use crate::ratchet::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, KDF_STATE_SIZE, KeyMaterial, RatchetManager, ratchet_hkdf,
};
use crate::shared::{roles, systems};
use beaconcrypt_protocol_core::ratchet as verified_ratchet;
#[cfg(feature = "server")]
use libsodium_rs::crypto_sign;
use serde::de::MapAccess;
use serde::{
	Deserialize, Deserializer,
	de::{self, Error as _, IgnoredAny, SeqAccess, Visitor},
};
use std::{
	collections::{HashMap, HashSet, hash_map::Entry},
	fmt,
	marker::PhantomData,
};
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

struct DirectionalRatchetChain<Role> {
	chain: verified_ratchet::RatchetChain,
	_role: PhantomData<Role>,
}

impl<'de, Role> Deserialize<'de> for DirectionalRatchetChain<Role>
where
	Role: roles::ChainKey + roles::Identified,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let typed =
			TypedArray::<KDF_STATE_SIZE, systems::HkdfSha512, Role>::deserialize(deserializer)?;
		Ok(Self {
			chain: verified_ratchet::RatchetChain::from_bytes(*typed.buffer.0),
			_role: PhantomData,
		})
	}
}

struct CanonicalU64(u64);

impl<'de> Deserialize<'de> for CanonicalU64 {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let encoded = String::deserialize(deserializer)?;
		let value = encoded.parse::<u64>().map_err(|_| {
			D::Error::custom(format!("invalid unsigned integer map key `{encoded}`"))
		})?;
		if encoded != value.to_string() {
			return Err(D::Error::custom(format!(
				"non-canonical unsigned integer map key `{encoded}`; expected `{value}`"
			)));
		}
		Ok(Self(value))
	}
}

struct DuplicateRejectingU64Map<V>(HashMap<u64, V>);

struct DuplicateRejectingU64MapVisitor<V>(PhantomData<V>);

impl<'de, V> Visitor<'de> for DuplicateRejectingU64MapVisitor<V>
where
	V: Deserialize<'de>,
{
	type Value = DuplicateRejectingU64Map<V>;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str("a map with unique canonical unsigned integer keys")
	}

	fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
	where
		A: MapAccess<'de>,
	{
		let mut values = HashMap::with_capacity(map.size_hint().unwrap_or(0));
		while let Some(CanonicalU64(key)) = map.next_key()? {
			match values.entry(key) {
				Entry::Occupied(_) => {
					return Err(A::Error::custom(format!(
						"duplicate unsigned integer map key {key}"
					)));
				}
				Entry::Vacant(entry) => {
					entry.insert(map.next_value()?);
				}
			}
		}
		Ok(DuplicateRejectingU64Map(values))
	}
}

impl<'de, V> Deserialize<'de> for DuplicateRejectingU64Map<V>
where
	V: Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_map(DuplicateRejectingU64MapVisitor(PhantomData))
	}
}

#[derive(Deserialize)]
#[serde(rename = "KeyMaterial", deny_unknown_fields)]
struct KeyMaterialData<Key, Nonce> {
	key: Key,
	nonce: Nonce,
}

struct DirectionalKeyMaterial<KeyRole, NonceRole> {
	material: KeyMaterial,
	_roles: PhantomData<(KeyRole, NonceRole)>,
}

impl<'de, KeyRole, NonceRole> Deserialize<'de> for DirectionalKeyMaterial<KeyRole, NonceRole>
where
	KeyRole: roles::Identified,
	NonceRole: roles::Identified,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = KeyMaterialData::<
			TypedArray<AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, KeyRole>,
			TypedArray<AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, NonceRole>,
		>::deserialize(deserializer)?;
		Ok(Self {
			material: KeyMaterial::from_bytes(*data.key.buffer.0, *data.nonce.buffer.0),
			_roles: PhantomData,
		})
	}
}

#[derive(Deserialize)]
#[serde(rename = "RatchetManager", deny_unknown_fields)]
struct RatchetManagerData {
	send_key: DirectionalRatchetChain<roles::ChainSendKey>,
	recv_key: DirectionalRatchetChain<roles::ChainRecvKey>,
	send_ctr: u64,
	recv_past: DuplicateRejectingU64Map<
		DirectionalKeyMaterial<roles::EncryptionRecvKey, roles::RecvNonce>,
	>,
	recv_ctr: u64,
}

impl<'de> Deserialize<'de> for RatchetManager {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = RatchetManagerData::deserialize(deserializer)?;
		let mut receive_entries = data.recv_past.0.into_iter().collect::<Vec<_>>();
		receive_entries.sort_unstable_by_key(|(sequence, _)| *sequence);
		let mut restore = verified_ratchet::start_concrete_restore(
			data.send_ctr,
			data.recv_ctr,
			data.send_key.chain,
			data.recv_key.chain,
			ratchet_hkdf,
		);
		for (sequence, directed) in receive_entries {
			if !verified_ratchet::concrete_restore_receive_key(
				&mut restore,
				sequence,
				directed.material,
			) {
				return Err(D::Error::custom(
					"recv_past exceeds the refined cache capacity or contains an invalid sequence",
				));
			}
		}
		let manager = Self {
			refined: verified_ratchet::finish_concrete_restore(restore),
		};
		Ok(manager)
	}
}

#[cfg(feature = "server")]
#[derive(Deserialize)]
#[serde(rename = "RemotePrincipal", deny_unknown_fields)]
struct RemotePrincipalData {
	pk: Vec<u8>,
	ratchet: RatchetManager,
}

#[cfg(feature = "server")]
impl<'de> Deserialize<'de> for EstablishedRemote<crypto_sign::PublicKey> {
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
#[derive(Deserialize)]
#[serde(rename = "BeaconCryptPqxdh", deny_unknown_fields)]
struct ServerStateData {
	identity_key: TypedArray<{ crypto_sign::SEEDBYTES }, systems::Ed25519, roles::IdentityKey>,
	identity_key_kid: u64,
	server_kid: u64,
	known_ids: DuplicateRejectingU64Map<EstablishedRemote<crypto_sign::PublicKey>>,
	consumed_registrations: Vec<Vec<u8>>,
}

#[cfg(feature = "server")]
type DeserializedServerState = (
	crypto_sign::KeyPair,
	u64,
	u64,
	HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>,
	HashSet<[u8; beaconcrypt_protocol_core::pqxdh::REGISTRATION_ID_SIZE]>,
);

#[cfg(feature = "server")]
pub(crate) fn deserialize_server_state(state: &str) -> Option<DeserializedServerState> {
	let ServerStateData {
		identity_key,
		identity_key_kid,
		server_kid,
		known_ids: DuplicateRejectingU64Map(known_ids),
		consumed_registrations,
	} = serde_json::from_str(state).ok()?;

	if identity_key_kid > server_kid
		|| known_ids.keys().any(|kid| *kid > server_kid)
		|| consumed_registrations.len() < known_ids.len()
	{
		return None;
	}
	let mut consumed = HashSet::with_capacity(consumed_registrations.len());
	for registration_id in consumed_registrations {
		let registration_id = registration_id.as_slice().try_into().ok()?;
		if !consumed.insert(registration_id) {
			return None;
		}
	}

	let keypair = crypto_sign::KeyPair::from_seed(identity_key.buffer.0.as_slice()).ok()?;

	Some((keypair, identity_key_kid, server_kid, known_ids, consumed))
}
#[cfg(test)]
mod tests {
	use super::*;
	use crate::pqxdh::AD_SIZE;
	use crate::ratchet::{KDF_STATE_SIZE, encrypt_message_with_ratchet};
	use serde::Serialize;
	use serde_json::{Value, json};

	fn assert_serde_traits<T>()
	where
		T: Serialize + for<'de> Deserialize<'de>,
	{
	}

	fn assert_key_material_eq(left: &KeyMaterial, right: &KeyMaterial) {
		assert_eq!(left.key().as_bytes(), right.key().as_bytes());
		assert_eq!(left.nonce().as_bytes(), right.nonce().as_bytes());
	}

	fn receive_slot(manager: &RatchetManager, sequence: u64) -> Option<u8> {
		(0..manager.receive_cache_len()).find(|slot| {
			manager
				.receive_entry_at(*slot)
				.is_some_and(|entry| entry.0 == sequence)
		})
	}

	fn assert_manager_eq(left: &RatchetManager, right: &RatchetManager) {
		assert_eq!(left.send_state().as_slice(), right.send_state().as_slice());
		assert_eq!(left.recv_state().as_slice(), right.recv_state().as_slice());
		assert_eq!(left.send_sequence(), right.send_sequence());
		assert_eq!(left.receive_sequence(), right.receive_sequence());
		assert_eq!(left.receive_cache_len(), right.receive_cache_len());
		let mut left_logical = (0..left.receive_cache_len())
			.map(|slot| left.receive_entry_at(slot).unwrap().0)
			.collect::<Vec<_>>();
		let mut right_logical = (0..right.receive_cache_len())
			.map(|slot| right.receive_entry_at(slot).unwrap().0)
			.collect::<Vec<_>>();
		left_logical.sort_unstable();
		right_logical.sort_unstable();
		assert_eq!(left_logical, right_logical);

		for slot in 0..left.receive_cache_len() {
			let (sequence, material) = left.receive_entry_at(slot).unwrap();
			assert_key_material_eq(material, right.recv_key(sequence).unwrap());
		}
	}

	#[test]
	fn byte_and_tuple_visitors_describe_and_enforce_their_input_shapes() {
		assert!(
			SecretBytesVisitor::<4>::copy_from_slice::<serde_json::Error>(&[1, 2, 3, 4]).is_ok()
		);
		let borrowed = SecretBytesVisitor::<4>
			.visit_bytes::<serde_json::Error>(&[1, 2, 3, 4])
			.unwrap();
		assert_eq!(borrowed.0.as_slice(), &[1, 2, 3, 4]);
		let owned = SecretBytesVisitor::<4>
			.visit_byte_buf::<serde_json::Error>(vec![4, 3, 2, 1])
			.unwrap();
		assert_eq!(owned.0.as_slice(), &[4, 3, 2, 1]);
		let wrong_length =
			SecretBytesVisitor::<4>::copy_from_slice::<serde_json::Error>(&[1, 2, 3])
				.err()
				.unwrap();
		assert!(
			wrong_length
				.to_string()
				.contains("expected a 4-byte buffer")
		);

		let bytes_error = serde_json::from_str::<SecretBytes<4>>("null")
			.err()
			.unwrap();
		assert!(
			bytes_error
				.to_string()
				.contains("a byte buffer containing exactly 4 bytes")
		);

		type TestTypedArray = TypedArray<4, systems::HkdfSha512, roles::ChainSendKey>;
		let typed_error = serde_json::from_str::<TestTypedArray>("null")
			.err()
			.unwrap();
		assert!(typed_error.to_string().contains(
			"a typed array containing an algorithm identifier, role identifier, and byte buffer"
		));

		#[cfg(feature = "server")]
		{
			type DeserializedKnownIds =
				DuplicateRejectingU64Map<EstablishedRemote<crypto_sign::PublicKey>>;
			let known_ids_error = serde_json::from_str::<DeserializedKnownIds>("[]")
				.err()
				.unwrap();
			assert!(
				known_ids_error
					.to_string()
					.contains("a map with unique canonical unsigned integer keys")
			);
		}
	}

	fn populated_manager() -> RatchetManager {
		libsodium_rs::ensure_init().unwrap();
		let mut manager = RatchetManager::default();
		manager.init_ratchets(
			&[0x42; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		for message in [
			b"first".as_slice(),
			b"second".as_slice(),
			b"third".as_slice(),
		] {
			assert!(
				encrypt_message_with_ratchet(message, 1, 0, &[0x24; AD_SIZE], &mut manager)
					.is_some()
			);
		}
		manager.ratchet_recv_until(4).unwrap();
		manager.delete_recv_key(1);
		manager.delete_recv_key(3);
		manager
	}

	fn ratchet_json_with_recv_past(manager: &RatchetManager, recv_past: &str) -> String {
		let serialized = serde_json::to_value(manager).unwrap();
		format!(
			"{{\"send_key\":{},\"recv_key\":{},\"send_ctr\":{},\"recv_past\":{{{recv_past}}},\"recv_ctr\":{}}}",
			serialized["send_key"],
			serialized["recv_key"],
			serialized["send_ctr"],
			serialized["recv_ctr"],
		)
	}

	fn assert_unknown_field_rejected<T>()
	where
		T: for<'de> Deserialize<'de>,
	{
		let error = serde_json::from_str::<T>(r#"{"unexpected":null}"#)
			.err()
			.unwrap();
		assert!(
			error.to_string().contains("unknown field `unexpected`"),
			"unexpected error: {error}"
		);
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
	fn ratchet_manager_schema_is_five_fields_and_receive_cache_is_sequence_keyed() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();
		let object = serialized.as_object().unwrap();
		let mut fields = object.keys().map(String::as_str).collect::<Vec<_>>();
		fields.sort_unstable();
		assert_eq!(
			fields,
			vec!["recv_ctr", "recv_key", "recv_past", "send_ctr", "send_key"]
		);

		let receive_map = object["recv_past"].as_object().unwrap();
		let mut sequences = receive_map.keys().map(String::as_str).collect::<Vec<_>>();
		sequences.sort_unstable();
		assert_eq!(sequences, vec!["2", "4"]);
	}

	#[test]
	fn post_swap_round_trip_preserves_receive_material_by_sequence() {
		let mut manager = RatchetManager::default();
		manager.init_ratchets(
			&[0x74; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(manager.ratchet_recv_until(4), Some(4));
		let target_slot = receive_slot(&manager, 2).unwrap();
		let old_last_slot = receive_slot(&manager, 4).unwrap();
		assert_ne!(target_slot, old_last_slot);
		assert_eq!(
			manager.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert_eq!(receive_slot(&manager, 4), Some(target_slot));

		let serialized_text = serde_json::to_string(&manager).unwrap();
		let recv_past = serialized_text.split_once("\"recv_past\":{").unwrap().1;
		let positions = [1, 3, 4].map(|sequence| {
			recv_past
				.find(&format!("\"{sequence}\":"))
				.unwrap_or_else(|| panic!("missing receive sequence {sequence}"))
		});
		assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));

		let serialized: Value = serde_json::from_str(&serialized_text).unwrap();
		let receive_map = serialized["recv_past"].as_object().unwrap();
		let mut sequences = receive_map.keys().map(String::as_str).collect::<Vec<_>>();
		sequences.sort_unstable();
		assert_eq!(sequences, vec!["1", "3", "4"]);
		let restored: RatchetManager = serde_json::from_str(&serialized_text).unwrap();

		assert_manager_eq(&manager, &restored);
		assert_eq!(serde_json::to_string(&restored).unwrap(), serialized_text);
		let restored_last_slot = receive_slot(&restored, 4).unwrap();
		assert_ne!(restored_last_slot, target_slot);
		for sequence in [1, 3, 4] {
			assert_key_material_eq(
				manager.recv_key(sequence).unwrap(),
				restored.recv_key(sequence).unwrap(),
			);
		}
	}

	#[test]
	fn populated_ratchet_manager_round_trips_and_continues() {
		let mut manager = populated_manager();
		let serialized = serde_json::to_string(&manager).unwrap();
		let mut restored = serde_json::from_str(&serialized).unwrap();

		assert_manager_eq(&manager, &restored);

		let original_send =
			encrypt_message_with_ratchet(b"continued send", 1, 0, &[0x25; AD_SIZE], &mut manager)
				.unwrap();
		let restored_send =
			encrypt_message_with_ratchet(b"continued send", 1, 0, &[0x25; AD_SIZE], &mut restored)
				.unwrap();
		assert_eq!(original_send.seq, 4);
		assert_eq!(restored_send.seq, original_send.seq);
		assert_eq!(restored_send.ciphertext, original_send.ciphertext);
		assert_manager_eq(&manager, &restored);

		let next_recv = manager.ratchet_recv().unwrap();
		assert_eq!(restored.ratchet_recv(), Some(next_recv));
		assert_key_material_eq(
			manager.recv_key(next_recv).unwrap(),
			restored.recv_key(next_recv).unwrap(),
		);
	}

	#[test]
	fn serialized_keys_and_nonces_include_their_directional_type_identifiers() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();
		let cases = [
			(
				&serialized["send_key"],
				systems::Identifier::HkdfSha512,
				roles::Identifier::ChainSendKey,
				KDF_STATE_SIZE,
			),
			(
				&serialized["recv_key"],
				systems::Identifier::HkdfSha512,
				roles::Identifier::ChainRecvKey,
				KDF_STATE_SIZE,
			),
			(
				&serialized["recv_past"]["2"]["key"],
				systems::Identifier::Chacha20Poly1305Ietf,
				roles::Identifier::EncryptionRecvKey,
				AEAD_KEY_LEN,
			),
			(
				&serialized["recv_past"]["2"]["nonce"],
				systems::Identifier::Chacha20Poly1305Ietf,
				roles::Identifier::RecvNonce,
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
				u8::from(roles::Identifier::ChainSendKey),
			),
			(
				&["recv_past", "2", "nonce"][..],
				0,
				u8::from(systems::Identifier::HkdfSha512),
			),
			(
				&["recv_past", "2", "nonce"][..],
				1,
				u8::from(roles::Identifier::SendNonce),
			),
			(&["recv_past", "2", "key"][..], 1, u8::MAX),
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
	fn send_and_recv_key_arrays_cannot_be_substituted() {
		let serialized = serde_json::to_value(populated_manager()).unwrap();
		let substitutions = [
			(&["send_key"][..], &["recv_key"][..]),
			(&["recv_key"][..], &["send_key"][..]),
			(&["send_key"][..], &["recv_past", "2", "key"][..]),
			(&["recv_past", "2", "key"][..], &["send_key"][..]),
		];

		for (destination, source) in substitutions {
			let mut replacement = &serialized;
			for segment in source {
				replacement = &replacement[*segment];
			}
			let replacement = replacement.clone();

			let mut malformed = serialized.clone();
			let mut destination_value = &mut malformed;
			for segment in destination {
				destination_value = &mut destination_value[*segment];
			}
			*destination_value = replacement;

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
	fn duplicate_receive_keys_are_rejected_before_hash_map_insertion() {
		let manager = populated_manager();
		let serialized = serde_json::to_value(&manager).unwrap();
		let material = serde_json::to_string(&serialized["recv_past"]["2"]).unwrap();

		for recv_past in [
			format!(r#""2":{material},"2":{material}"#),
			format!(r#""2":{material},"\u0032":{material}"#),
		] {
			let duplicate = ratchet_json_with_recv_past(&manager, &recv_past);
			let error = serde_json::from_str::<RatchetManager>(&duplicate)
				.err()
				.unwrap();
			assert!(
				error
					.to_string()
					.contains("duplicate unsigned integer map key 2"),
				"unexpected error: {error}"
			);
		}
	}

	#[test]
	fn noncanonical_unsigned_integer_map_keys_are_rejected() {
		let manager = populated_manager();
		let serialized = serde_json::to_value(&manager).unwrap();
		let material = serde_json::to_string(&serialized["recv_past"]["2"]).unwrap();
		let noncanonical = ratchet_json_with_recv_past(&manager, &format!(r#""02":{material}"#));
		let error = serde_json::from_str::<RatchetManager>(&noncanonical)
			.err()
			.unwrap();

		assert!(
			error
				.to_string()
				.contains("non-canonical unsigned integer map key `02`; expected `2`"),
			"unexpected error: {error}"
		);
	}

	#[test]
	fn every_persistence_object_rejects_unknown_fields() {
		type ReceiveKeyMaterialData = KeyMaterialData<
			TypedArray<AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, roles::EncryptionRecvKey>,
			TypedArray<AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, roles::RecvNonce>,
		>;

		assert_unknown_field_rejected::<ReceiveKeyMaterialData>();
		assert_unknown_field_rejected::<RatchetManagerData>();
		assert_unknown_field_rejected::<RemotePrincipalData>();
		assert_unknown_field_rejected::<ServerStateData>();
	}

	#[test]
	fn cached_receive_entries_serialize_in_numeric_order() {
		let mut manager = RatchetManager::default();
		manager.init_ratchets(
			&[0x75; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(manager.ratchet_recv_until(10), Some(10));
		assert_eq!(
			manager.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);

		let serialized = serde_json::to_string(&manager).unwrap();
		let recv_past = serialized.split_once("\"recv_past\":{").unwrap().1;
		let sequences = [1, 3, 4, 5, 6, 7, 8, 9, 10];
		let positions = sequences.map(|sequence| {
			recv_past
				.find(&format!("\"{sequence}\":"))
				.unwrap_or_else(|| panic!("missing receive sequence {sequence}"))
		});
		assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));

		let restored: RatchetManager = serde_json::from_str(&serialized).unwrap();
		assert_eq!(serde_json::to_string(&restored).unwrap(), serialized);
	}

	#[test]
	fn legacy_send_past_field_is_rejected() {
		let mut legacy = serde_json::to_value(RatchetManager::default()).unwrap();
		legacy["send_past"] = json!({});
		let error = serde_json::from_value::<RatchetManager>(legacy)
			.err()
			.unwrap();
		assert!(error.to_string().contains("unknown field `send_past`"));
	}

	#[test]
	fn type_identifiers_follow_the_undefined_zero_convention() {
		assert_eq!(u8::from(systems::Identifier::Undefined), 0);
		assert_eq!(u8::from(systems::Identifier::Ed25519), 1);
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
		for (identifier, encoded) in [
			(roles::Identifier::ChainSendKey, 8),
			(roles::Identifier::ChainRecvKey, 9),
			(roles::Identifier::EncryptionSendKey, 10),
			(roles::Identifier::EncryptionRecvKey, 11),
			(roles::Identifier::SendNonce, 12),
			(roles::Identifier::RecvNonce, 13),
			(roles::Identifier::IdentityKey, 14),
		] {
			assert_eq!(u8::from(identifier), encoded);
			assert_eq!(roles::Identifier::from(encoded), identifier);
		}
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
	fn impossible_cached_receive_sequence_is_rejected() {
		let mut future_sequence = serde_json::to_value(populated_manager()).unwrap();
		let cached_key = future_sequence["recv_past"]["2"].clone();
		future_sequence["recv_past"]
			.as_object_mut()
			.unwrap()
			.insert("5".into(), cached_key);
		assert!(serde_json::from_value::<RatchetManager>(future_sequence).is_err());
	}

	#[test]
	fn receive_cache_restoration_accepts_the_bound_and_rejects_overflow() {
		let mut manager = RatchetManager::default();
		manager.init_ratchets(
			&[0x73; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		manager
			.ratchet_recv_until(verified_ratchet::RECEIVE_CACHE_CAPACITY as u64)
			.unwrap();
		let mut at_capacity = serde_json::to_value(manager).unwrap();

		let restored: RatchetManager = serde_json::from_value(at_capacity.clone()).unwrap();
		assert_eq!(
			restored.receive_cache_len() as usize,
			verified_ratchet::RECEIVE_CACHE_CAPACITY
		);
		for slot in 0..restored.receive_cache_len() {
			assert!(restored.receive_entry_at(slot).is_some());
		}
		for sequence in 1..=verified_ratchet::RECEIVE_CACHE_CAPACITY as u64 {
			assert!(restored.recv_key(sequence).is_some());
		}

		let overflow_sequence = verified_ratchet::RECEIVE_CACHE_CAPACITY as u64 + 1;
		let template =
			at_capacity["recv_past"][verified_ratchet::RECEIVE_CACHE_CAPACITY.to_string()].clone();
		at_capacity["recv_past"]
			.as_object_mut()
			.unwrap()
			.insert(overflow_sequence.to_string(), template);
		at_capacity["recv_ctr"] = json!(overflow_sequence);
		assert!(serde_json::from_value::<RatchetManager>(at_capacity).is_err());
	}
}
