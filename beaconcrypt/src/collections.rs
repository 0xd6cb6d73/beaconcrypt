// SPDX-License-Identifier: 0BSD

//! Hash tables retain fallible reservation and use identity-secret-derived SipHash keys.

use core::hash::BuildHasher;

use beaconcrypt_crypto::crypto_generichash;
use siphasher::sip::SipHasher13;
use zeroize::{Zeroize, ZeroizeOnDrop};

#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub(crate) struct KeyedHasher([u8; 16]);

impl BuildHasher for KeyedHasher {
	type Hasher = SipHasher13;

	fn build_hasher(&self) -> Self::Hasher {
		SipHasher13::new_with_key(&self.0)
	}
}

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, KeyedHasher>;
pub(crate) type HashSet<K> = hashbrown::HashSet<K, KeyedHasher>;

fn hasher(secret: &[u8]) -> KeyedHasher {
	let mut hash =
		crypto_generichash::State::new(None, 16).expect("the fixed BLAKE2b output length is valid");
	hash.update(b"beaconcrypt private hash table key v1\0");
	hash.update(secret);
	let mut key = hash.finalize();
	let hasher = KeyedHasher(key.as_slice().try_into().expect("fixed hash output width"));
	key.zeroize();
	hasher
}

pub(crate) fn map_with_key<K, V>(secret: &[u8]) -> HashMap<K, V> {
	HashMap::with_hasher(hasher(secret))
}

pub(crate) fn set_with_key<K>(secret: &[u8]) -> HashSet<K> {
	HashSet::with_hasher(hasher(secret))
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn table_hashes_depend_on_the_private_identity_and_survive_restore() {
		let original = map_with_key::<u64, ()>(&[0x31; 64]);
		let restored = map_with_key::<u64, ()>(&[0x31; 64]);
		let other_identity = set_with_key::<u64>(&[0x32; 64]);
		for registration in [0, 1, 17, u64::MAX] {
			let hash = original.hasher().hash_one(registration);
			assert_eq!(hash, restored.hasher().hash_one(registration));
			assert_ne!(hash, other_identity.hasher().hash_one(registration));
		}
	}
}
