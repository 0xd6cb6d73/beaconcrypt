// SPDX-License-Identifier: 0BSD

use super::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, AeadKey, AeadNonce, KeyMaterial, Ratchet, RatchetManager,
	SecretArr, roles, systems,
};
#[cfg(feature = "server")]
use super::{RemotePrincipal, SignType, encode_sign};
#[cfg(feature = "server")]
use libsodium_rs::crypto_sign;
#[cfg(feature = "server")]
use serde::ser::{Error as _, SerializeMap};
use serde::{
	Serialize, Serializer,
	ser::{SerializeStruct, SerializeTuple},
};
#[cfg(feature = "server")]
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

impl<'a, const N: usize, System, Role> From<&'a SecretArr<N, System, Role>>
	for TypedArray<'a, N, System, Role>
{
	fn from(value: &'a SecretArr<N, System, Role>) -> Self {
		Self {
			buffer: value
				.as_slice()
				.try_into()
				.expect("SecretArr always contains exactly N bytes"),
			_type: PhantomData,
		}
	}
}

impl<'a> From<&'a AeadKey>
	for TypedArray<'a, AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, roles::EncryptionKey>
{
	fn from(value: &'a AeadKey) -> Self {
		Self {
			buffer: value
				.as_bytes()
				.try_into()
				.expect("AeadKey always contains AEAD_KEY_LEN bytes"),
			_type: PhantomData,
		}
	}
}

impl<'a> From<&'a AeadNonce>
	for TypedArray<'a, AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, roles::Nonce>
{
	fn from(value: &'a AeadNonce) -> Self {
		Self {
			buffer: value.as_bytes(),
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

impl<const N: usize, System, Role> Serialize for SecretArr<N, System, Role>
where
	System: systems::Identified,
	Role: roles::Identified,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		TypedArray::<N, System, Role>::from(self).serialize(serializer)
	}
}

impl<Role> Serialize for Ratchet<Role> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		self.state.serialize(serializer)
	}
}

impl Serialize for KeyMaterial {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let key =
			TypedArray::<AEAD_KEY_LEN, systems::Chacha20Poly1305Ietf, roles::EncryptionKey>::from(
				&self.key,
			);
		let nonce = TypedArray::<AEAD_NONCE_LEN, systems::Chacha20Poly1305Ietf, roles::Nonce>::from(
			&self.nonce,
		);
		let mut state = serializer.serialize_struct("KeyMaterial", 2)?;
		state.serialize_field("key", &key)?;
		state.serialize_field("nonce", &nonce)?;
		state.end()
	}
}

impl Serialize for RatchetManager {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut state = serializer.serialize_struct("RatchetManager", 6)?;
		state.serialize_field("send_key", &self.send_key)?;
		state.serialize_field("recv_key", &self.recv_key)?;
		state.serialize_field("send_past", &self.send_past)?;
		state.serialize_field("send_ctr", &self.send_ctr)?;
		state.serialize_field("recv_past", &self.recv_past)?;
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
