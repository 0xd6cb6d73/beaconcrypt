// SPDX-License-Identifier: 0BSD

use super::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, KDF_STATE_SIZE, KdfState, KeyMaterial, Ratchet, RatchetManager,
	roles, systems,
};
#[cfg(feature = "server")]
use super::{RemotePrincipal, SignType, encode_sign};
#[cfg(feature = "server")]
use crate::server::StateUpdate;
#[cfg(feature = "server")]
use libsodium_rs::crypto_sign;
#[cfg(feature = "server")]
use serde::ser::Error as _;
use serde::{
	Serialize, Serializer,
	ser::{SerializeMap, SerializeStruct, SerializeTuple},
};
use std::collections::HashMap;
use std::marker::PhantomData;

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

struct KdfStateRef<'a, Role: roles::ChainKey>(&'a KdfState<Role>);

impl<Role: roles::ChainKey + roles::Identified> Serialize for KdfStateRef<'_, Role> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let buffer = self
			.0
			.as_slice()
			.try_into()
			.expect("KDF state always contains KDF_STATE_SIZE bytes");
		TypedArray::<KDF_STATE_SIZE, systems::HkdfSha512, Role>::new(buffer).serialize(serializer)
	}
}

impl<Role: roles::ChainKey + roles::Identified> Serialize for Ratchet<Role> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		KdfStateRef(&self.state).serialize(serializer)
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
		let key_buffer = self
			.material
			.key
			.as_bytes()
			.try_into()
			.expect("AeadKey always contains AEAD_KEY_LEN bytes");
		let key =
			TypedArray::<AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, KeyRole>::new(key_buffer);
		let nonce = TypedArray::<AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, NonceRole>::new(
			self.material.nonce.as_bytes(),
		);
		let mut state = serializer.serialize_struct("KeyMaterial", 2)?;
		state.serialize_field("key", &key)?;
		state.serialize_field("nonce", &nonce)?;
		state.end()
	}
}

struct DirectionalKeyMapRef<'a, KeyRole, NonceRole> {
	keys: &'a HashMap<u64, KeyMaterial>,
	_roles: PhantomData<(KeyRole, NonceRole)>,
}

impl<'a, KeyRole, NonceRole> DirectionalKeyMapRef<'a, KeyRole, NonceRole> {
	fn new(keys: &'a HashMap<u64, KeyMaterial>) -> Self {
		Self {
			keys,
			_roles: PhantomData,
		}
	}
}

impl<KeyRole, NonceRole> Serialize for DirectionalKeyMapRef<'_, KeyRole, NonceRole>
where
	KeyRole: roles::Identified,
	NonceRole: roles::Identified,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut map = serializer.serialize_map(Some(self.keys.len()))?;
		for (sequence, material) in self.keys {
			map.serialize_entry(
				sequence,
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
		let send_past = DirectionalKeyMapRef::<roles::EncryptionSendKey, roles::SendNonce>::new(
			&self.send_past,
		);
		let recv_past = DirectionalKeyMapRef::<roles::EncryptionRecvKey, roles::RecvNonce>::new(
			&self.recv_past,
		);
		let mut state = serializer.serialize_struct("RatchetManager", 6)?;
		state.serialize_field("send_key", &self.send_key)?;
		state.serialize_field("recv_key", &self.recv_key)?;
		state.serialize_field("send_past", &send_past)?;
		state.serialize_field("send_ctr", &self.send_ctr)?;
		state.serialize_field("recv_past", &recv_past)?;
		state.serialize_field("recv_ctr", &self.recv_ctr)?;
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
impl Serialize for RemotePrincipal<crypto_sign::PublicKey> {
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
struct SerializableKnownIds<'a>(&'a HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>);

#[cfg(feature = "server")]
pub(crate) fn serialize_known_ids(
	known_ids: &HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
) -> Option<String> {
	serde_json::to_string(&SerializableKnownIds(known_ids)).ok()
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

#[cfg(all(test, feature = "server"))]
mod tests {
	use super::*;
	use crate::server::{RecvState, SendState};
	use serde_json::json;

	#[test]
	fn state_updates_include_the_complete_ratchet_state() {
		let send_bytes = [0x21; KDF_STATE_SIZE];
		let mut send_state = RatchetManager::default();
		send_state.send_key = Ratchet::<roles::ChainSendKey>::from(send_bytes);
		let send_update = SendState {
			kid: 7,
			seq: 11,
			state: send_state.clone(),
			data: vec![0x31, 0x32],
			_role: PhantomData,
		};

		let recv_bytes = [0x41; KDF_STATE_SIZE];
		let mut recv_state = RatchetManager::default();
		recv_state.recv_key = Ratchet::<roles::ChainRecvKey>::from(recv_bytes);
		let recv_update = RecvState {
			kid: 9,
			seq: 13,
			state: recv_state.clone(),
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
				"state": serde_json::to_value(send_state).unwrap(),
				"data": [0x31, 0x32],
			})
		);
		assert_eq!(
			recv,
			json!({
				"kid": 9,
				"seq": 13,
				"state": serde_json::to_value(recv_state).unwrap(),
				"data": [0x51, 0x52],
			})
		);
	}
}
