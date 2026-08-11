// SPDX-License-Identifier: 0BSD

use super::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, KDF_STATE_SIZE, KeyMaterial, Ratchet, RatchetManager, RecvChain,
	SendChain, roles, systems, verified_ratchet,
};
#[cfg(feature = "server")]
use super::{RemotePrincipal, SignType, decode_sign};
#[cfg(feature = "server")]
use crate::server::StateUpdate;
#[cfg(feature = "server")]
use libsodium_rs::crypto_sign;
#[cfg(feature = "server")]
use serde::de::MapAccess;
use serde::{
	Deserialize, Deserializer,
	de::{self, Error as _, IgnoredAny, SeqAccess, Visitor},
};
use std::{
	collections::{HashMap, HashSet},
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

impl<'de> Deserialize<'de> for Ratchet<roles::ChainSendKey> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let typed =
			TypedArray::<KDF_STATE_SIZE, systems::HkdfSha512, roles::ChainSendKey>::deserialize(
				deserializer,
			)?;
		Ok(Self {
			state: (*typed.buffer.0).into(),
		})
	}
}

impl<'de> Deserialize<'de> for Ratchet<roles::ChainRecvKey> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let typed =
			TypedArray::<KDF_STATE_SIZE, systems::HkdfSha512, roles::ChainRecvKey>::deserialize(
				deserializer,
			)?;
		Ok(Self {
			state: (*typed.buffer.0).into(),
		})
	}
}

#[derive(Deserialize)]
#[serde(rename = "KeyMaterial")]
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
			material: KeyMaterial {
				key: (*data.key.buffer.0).into(),
				nonce: (*data.nonce.buffer.0).into(),
			},
			_roles: PhantomData,
		})
	}
}

#[derive(Deserialize)]
#[serde(rename = "RatchetManager", deny_unknown_fields)]
struct RatchetManagerData {
	send_key: SendChain,
	recv_key: RecvChain,
	send_ctr: u64,
	recv_past: HashMap<u64, DirectionalKeyMaterial<roles::EncryptionRecvKey, roles::RecvNonce>>,
	recv_ctr: u64,
}

impl<'de> Deserialize<'de> for RatchetManager {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = RatchetManagerData::deserialize(deserializer)?;
		let mut receive_entries = data.recv_past.into_iter().collect::<Vec<_>>();
		receive_entries.sort_unstable_by_key(|(sequence, _)| *sequence);
		let mut restore = verified_ratchet::start_refined_restore(
			data.send_ctr,
			data.recv_ctr,
			data.send_key,
			data.recv_key,
		);
		for (sequence, directed) in receive_entries {
			if !verified_ratchet::refined_restore_receive_key(
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
			refined: verified_ratchet::finish_refined_restore(restore),
		};
		Ok(manager)
	}
}

#[cfg(feature = "server")]
#[derive(Deserialize)]
#[serde(rename = "StateUpdate")]
struct StateUpdateData {
	kid: u64,
	seq: u64,
	state: RatchetManager,
	data: Vec<u8>,
}

#[cfg(feature = "server")]
impl<'de, Role: roles::ChainKey> Deserialize<'de> for StateUpdate<Role> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let data = StateUpdateData::deserialize(deserializer)?;
		Ok(Self {
			kid: data.kid,
			seq: data.seq,
			state: data.state,
			data: data.data,
			_role: PhantomData,
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
#[derive(Deserialize)]
#[serde(rename = "BeaconCryptPqxdh")]
struct ServerStateData {
	identity_key: TypedArray<{ crypto_sign::SEEDBYTES }, systems::Ed25519, roles::IdentityKey>,
	identity_key_kid: u64,
	server_kid: u64,
	known_ids: DeserializedKnownIds,
	consumed_registrations: Vec<Vec<u8>>,
}

#[cfg(feature = "server")]
type DeserializedServerState = (
	crypto_sign::KeyPair,
	u64,
	u64,
	HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
	HashSet<[u8; beaconcrypt_protocol_core::pqxdh::REGISTRATION_ID_SIZE]>,
);

#[cfg(feature = "server")]
pub(crate) fn deserialize_server_state(state: &str) -> Option<DeserializedServerState> {
	let ServerStateData {
		identity_key,
		identity_key_kid,
		server_kid,
		known_ids: DeserializedKnownIds(known_ids),
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
	use crate::shared::{AD_SIZE, KDF_STATE_SIZE, SYM_RATCHET_INFO, encrypt_message_with_ratchet};
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
			let known_ids_error = serde_json::from_str::<DeserializedKnownIds>("[]")
				.err()
				.unwrap();
			assert!(
				known_ids_error
					.to_string()
					.contains("a map from key IDs to remote principals")
			);
		}
	}

	fn populated_manager() -> RatchetManager {
		libsodium_rs::ensure_init().unwrap();
		let mut manager = RatchetManager::default();
		manager.init_ratchets(
			&[0x42; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
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
		manager.ratchet_recv_until(SYM_RATCHET_INFO, 4).unwrap();
		manager.delete_recv_key(1);
		manager.delete_recv_key(3);
		manager
	}

	#[test]
	fn ratchet_manager_implements_serde_traits() {
		assert_serde_traits::<RatchetManager>();
	}

	#[cfg(feature = "server")]
	#[test]
	fn state_updates_round_trip_the_complete_ratchet_state() {
		use crate::server::{RecvState, SendState};

		assert_serde_traits::<SendState>();
		assert_serde_traits::<RecvState>();

		let state = populated_manager();
		let update = SendState {
			kid: 7,
			seq: 3,
			state: state.clone(),
			data: vec![0x31, 0x32],
			_role: PhantomData,
		};
		let serialized = serde_json::to_string(&update).unwrap();
		let restored: SendState = serde_json::from_str(&serialized).unwrap();

		assert_eq!(restored.kid, update.kid);
		assert_eq!(restored.seq, update.seq);
		assert_eq!(restored.data, update.data);
		assert_manager_eq(&restored.state, &state);
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
		assert!(manager.init_ratchets(
			&[0x74; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		));
		assert_eq!(manager.ratchet_recv_until(SYM_RATCHET_INFO, 4), Some(4));
		let target_slot = receive_slot(&manager, 2).unwrap();
		let old_last_slot = receive_slot(&manager, 4).unwrap();
		assert_ne!(target_slot, old_last_slot);
		assert_eq!(
			manager.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert_eq!(receive_slot(&manager, 4), Some(target_slot));

		let serialized = serde_json::to_value(&manager).unwrap();
		let receive_map = serialized["recv_past"].as_object().unwrap();
		let mut sequences = receive_map.keys().map(String::as_str).collect::<Vec<_>>();
		sequences.sort_unstable();
		assert_eq!(sequences, vec!["1", "3", "4"]);
		let restored: RatchetManager = serde_json::from_value(serialized).unwrap();

		assert_manager_eq(&manager, &restored);
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

		let next_recv = manager.ratchet_recv(SYM_RATCHET_INFO).unwrap();
		assert_eq!(restored.ratchet_recv(SYM_RATCHET_INFO), Some(next_recv));
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
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		manager
			.ratchet_recv_until(
				SYM_RATCHET_INFO,
				verified_ratchet::RECEIVE_CACHE_CAPACITY as u64,
			)
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
