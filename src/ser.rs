// SPDX-License-Identifier: 0BSD

#[cfg(feature = "server")]
use super::{EstablishedRemote, SignType, encode_sign};
use crate::ratchet::{AEAD_KEY_LEN, AEAD_NONCE_LEN, KDF_STATE_SIZE, KeyMaterial, RatchetManager};
#[cfg(test)]
use crate::ratchet::{RatchetKernel, ratchet_hkdf};
#[cfg(feature = "server")]
use crate::server::{RatchetSnapshot, StateUpdate};
use crate::shared::{roles, systems};
#[cfg(feature = "server")]
use libsodium_rs::crypto_sign;
#[cfg(feature = "server")]
use serde::ser::Error as _;
use serde::{
	Serialize, Serializer,
	ser::{SerializeMap, SerializeSeq, SerializeStruct, SerializeTuple},
};
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
#[cfg(feature = "server")]
use zeroize::Zeroizing;

struct ByteBuffer<'a>(&'a [u8]);

impl Serialize for ByteBuffer<'_> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		// A Serde byte buffer carries its length separately from its contents.
		serializer.serialize_bytes(self.0)
	}
}

struct TypedArray<'a, const N: usize, System, Role> {
	buffer: &'a [u8; N],
	_type: PhantomData<(System, Role)>,
}

impl<'a, const N: usize, System, Role> TypedArray<'a, N, System, Role> {
	fn new(buffer: &'a [u8; N]) -> Self {
		Self {
			buffer,
			_type: PhantomData,
		}
	}
}

impl<const N: usize, System, Role> Serialize for TypedArray<'_, N, System, Role>
where
	System: systems::Identified,
	Role: roles::Identified,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut tuple = serializer.serialize_tuple(3)?;
		tuple.serialize_element(&u8::from(System::IDENTIFIER))?;
		tuple.serialize_element(&u8::from(Role::IDENTIFIER))?;
		tuple.serialize_element(&ByteBuffer(self.buffer.as_slice()))?;
		tuple.end()
	}
}

struct DirectionalRatchetChainRef<'a, Role> {
	chain: &'a beaconcrypt_protocol_core::ratchet::RatchetChain,
	_role: PhantomData<Role>,
}

impl<'a, Role> DirectionalRatchetChainRef<'a, Role> {
	fn new(chain: &'a beaconcrypt_protocol_core::ratchet::RatchetChain) -> Self {
		Self {
			chain,
			_role: PhantomData,
		}
	}
}

impl<Role: roles::ChainKey + roles::Identified> Serialize for DirectionalRatchetChainRef<'_, Role> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		TypedArray::<KDF_STATE_SIZE, systems::HkdfSha512, Role>::new(self.chain.as_bytes())
			.serialize(serializer)
	}
}

#[cfg(feature = "server")]
impl<Role: roles::ChainKey> Serialize for StateUpdate<Role> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut state = serializer.serialize_struct("StateUpdate", 4)?;
		state.serialize_field("kid", &self.kid)?;
		state.serialize_field("seq", &self.seq)?;
		state.serialize_field("state", &self.state)?;
		state.serialize_field("data", &ByteBuffer(&self.data))?;
		state.end()
	}
}

#[cfg(feature = "server")]
impl Serialize for RatchetSnapshot {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(self.as_str())
	}
}

struct DirectionalKeyMaterialRef<'a, KeyRole, NonceRole> {
	material: &'a KeyMaterial,
	_roles: PhantomData<(KeyRole, NonceRole)>,
}

impl<'a, KeyRole, NonceRole> DirectionalKeyMaterialRef<'a, KeyRole, NonceRole> {
	fn new(material: &'a KeyMaterial) -> Self {
		Self {
			material,
			_roles: PhantomData,
		}
	}
}

impl<KeyRole, NonceRole> Serialize for DirectionalKeyMaterialRef<'_, KeyRole, NonceRole>
where
	KeyRole: roles::Identified,
	NonceRole: roles::Identified,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let key = TypedArray::<AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, KeyRole>::new(
			self.material.key().as_bytes(),
		);
		let nonce = TypedArray::<AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, NonceRole>::new(
			self.material.nonce().as_bytes(),
		);
		let mut state = serializer.serialize_struct("KeyMaterial", 2)?;
		state.serialize_field("key", &key)?;
		state.serialize_field("nonce", &nonce)?;
		state.end()
	}
}

struct DirectionalReceiveKeySlotsRef<'a, KeyRole, NonceRole> {
	ratchet: &'a RatchetManager,
	_roles: PhantomData<(KeyRole, NonceRole)>,
}

impl<'a, KeyRole, NonceRole> DirectionalReceiveKeySlotsRef<'a, KeyRole, NonceRole> {
	fn new(ratchet: &'a RatchetManager) -> Self {
		Self {
			ratchet,
			_roles: PhantomData,
		}
	}
}

impl<KeyRole, NonceRole> Serialize for DirectionalReceiveKeySlotsRef<'_, KeyRole, NonceRole>
where
	KeyRole: roles::Identified,
	NonceRole: roles::Identified,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let len = self.ratchet.receive_cache_len();
		let mut entries = Vec::with_capacity(len as usize);
		for slot in 0..len {
			entries.push(self.ratchet.receive_entry_at(slot).ok_or_else(|| {
				S::Error::custom("refined receive cache contains an invalid entry")
			})?);
		}
		entries.sort_unstable_by_key(|(sequence, _)| *sequence);

		let mut map = serializer.serialize_map(Some(len as usize))?;
		for (sequence, material) in entries {
			map.serialize_entry(
				&sequence,
				&DirectionalKeyMaterialRef::<KeyRole, NonceRole>::new(material),
			)?;
		}
		map.end()
	}
}

impl Serialize for RatchetManager {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let recv_past =
			DirectionalReceiveKeySlotsRef::<roles::EncryptionRecvKey, roles::RecvNonce>::new(self);
		let send_chain =
			DirectionalRatchetChainRef::<roles::ChainSendKey>::new(self.refined.send_chain());
		let receive_chain =
			DirectionalRatchetChainRef::<roles::ChainRecvKey>::new(self.refined.receive_chain());
		let mut state = serializer.serialize_struct("RatchetManager", 5)?;
		state.serialize_field("send_key", &send_chain)?;
		state.serialize_field("recv_key", &receive_chain)?;
		state.serialize_field("send_ctr", &self.send_sequence())?;
		state.serialize_field("recv_past", &recv_past)?;
		state.serialize_field("recv_ctr", &self.receive_sequence())?;
		state.end()
	}
}

#[cfg(feature = "server")]
struct EncodedSignaturePublicKey<'a>(&'a crypto_sign::PublicKey);

#[cfg(feature = "server")]
impl Serialize for EncodedSignaturePublicKey<'_> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let encoded = encode_sign(SignType::Ed25519, self.0.as_bytes())
			.map_err(|error| S::Error::custom(error.to_string()))?;
		ByteBuffer(&encoded).serialize(serializer)
	}
}

#[cfg(feature = "server")]
impl Serialize for EstablishedRemote<crypto_sign::PublicKey> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut state = serializer.serialize_struct("RemotePrincipal", 2)?;
		state.serialize_field("pk", &EncodedSignaturePublicKey(self.pk()))?;
		state.serialize_field("ratchet", self.ratchet())?;
		state.end()
	}
}

#[cfg(feature = "server")]
struct SerializableKnownIds<'a>(&'a HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>);

#[cfg(feature = "server")]
struct SerializableConsumedRegistrations<'a>(
	&'a HashSet<[u8; beaconcrypt_protocol_core::pqxdh::REGISTRATION_ID_SIZE]>,
);

#[cfg(feature = "server")]
struct SerializableServerState<'a> {
	identity_key: &'a crypto_sign::KeyPair,
	identity_key_kid: u64,
	server_kid: u64,
	known_ids: &'a HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>,
	consumed_registrations:
		&'a HashSet<[u8; beaconcrypt_protocol_core::pqxdh::REGISTRATION_ID_SIZE]>,
}

#[cfg(feature = "server")]
pub(crate) fn serialize_server_state(
	identity_key: &crypto_sign::KeyPair,
	identity_key_kid: u64,
	server_kid: u64,
	known_ids: &HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>,
	consumed_registrations: &HashSet<[u8; beaconcrypt_protocol_core::pqxdh::REGISTRATION_ID_SIZE]>,
) -> Option<String> {
	serde_json::to_string(&SerializableServerState {
		identity_key,
		identity_key_kid,
		server_kid,
		known_ids,
		consumed_registrations,
	})
	.ok()
}

#[cfg(feature = "server")]
impl Serialize for SerializableServerState<'_> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let identity_seed = Zeroizing::new(
			crypto_sign::secret_key_to_seed(&self.identity_key.secret_key)
				.map_err(|error| S::Error::custom(error.to_string()))?,
		);
		let identity_seed_buffer = identity_seed
			.as_slice()
			.try_into()
			.expect("Ed25519 seed always contains SEEDBYTES bytes");
		let typed_identity_seed =
			TypedArray::<{ crypto_sign::SEEDBYTES }, systems::Ed25519, roles::IdentityKey>::new(
				identity_seed_buffer,
			);
		let mut state = serializer.serialize_struct("BeaconCryptPqxdh", 5)?;
		state.serialize_field("identity_key", &typed_identity_seed)?;
		state.serialize_field("identity_key_kid", &self.identity_key_kid)?;
		state.serialize_field("server_kid", &self.server_kid)?;
		state.serialize_field("known_ids", &SerializableKnownIds(self.known_ids))?;
		state.serialize_field(
			"consumed_registrations",
			&SerializableConsumedRegistrations(self.consumed_registrations),
		)?;
		state.end()
	}
}

#[cfg(feature = "server")]
impl Serialize for SerializableKnownIds<'_> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut entries: Vec<_> = self.0.iter().collect();
		entries.sort_unstable_by_key(|(kid, _)| **kid);

		let mut map = serializer.serialize_map(Some(entries.len()))?;
		for (kid, principal) in entries {
			map.serialize_entry(kid, principal)?;
		}
		map.end()
	}
}

#[cfg(feature = "server")]
impl Serialize for SerializableConsumedRegistrations<'_> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut entries: Vec<_> = self.0.iter().collect();
		entries.sort_unstable();

		let mut sequence = serializer.serialize_seq(Some(entries.len()))?;
		for registration_id in entries {
			sequence.serialize_element(&ByteBuffer(registration_id.as_slice()))?;
		}
		sequence.end()
	}
}

#[cfg(all(test, feature = "server"))]
mod tests {
	use super::*;
	use crate::server::{RecvState, SendState};
	use serde_json::json;

	#[test]
	fn state_updates_include_an_inert_serialized_ratchet_snapshot() {
		let send_bytes = [0x21; KDF_STATE_SIZE];
		let mut send_state = RatchetManager::default();
		send_state.refined = RatchetKernel::new(
			beaconcrypt_protocol_core::ratchet::RatchetChain::from_bytes(send_bytes),
			beaconcrypt_protocol_core::ratchet::RatchetChain::from_bytes([0; KDF_STATE_SIZE]),
			ratchet_hkdf,
		);
		let expected_send_state = serde_json::to_string(&send_state).unwrap();
		let send_update = SendState {
			kid: 7,
			seq: 11,
			state: RatchetSnapshot::capture(&send_state).unwrap(),
			data: vec![0x31, 0x32],
			_role: PhantomData,
		};

		let recv_bytes = [0x41; KDF_STATE_SIZE];
		let mut recv_state = RatchetManager::default();
		recv_state.refined = RatchetKernel::new(
			beaconcrypt_protocol_core::ratchet::RatchetChain::from_bytes([0; KDF_STATE_SIZE]),
			beaconcrypt_protocol_core::ratchet::RatchetChain::from_bytes(recv_bytes),
			ratchet_hkdf,
		);
		let expected_recv_state = serde_json::to_string(&recv_state).unwrap();
		let recv_update = RecvState {
			kid: 9,
			seq: 13,
			state: RatchetSnapshot::capture(&recv_state).unwrap(),
			data: vec![0x51, 0x52],
			_role: PhantomData,
		};

		let send = serde_json::to_value(send_update).unwrap();
		let recv = serde_json::to_value(recv_update).unwrap();

		assert_eq!(
			send,
			json!({
				"kid": 7,
				"seq": 11,
				"state": expected_send_state,
				"data": [0x31, 0x32],
			})
		);
		assert_eq!(
			recv,
			json!({
				"kid": 9,
				"seq": 13,
				"state": expected_recv_state,
				"data": [0x51, 0x52],
			})
		);
	}
}
