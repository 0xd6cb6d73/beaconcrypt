// SPDX-License-Identifier: 0BSD

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;
#[cfg(test)]
extern crate std;

/// The portable primitive suite and caller-supplied entropy traits.
pub use beaconcrypt_crypto as crypto;

#[cfg(feature = "server")]
mod collections;

#[cfg(feature = "pqxdh")]
mod auth;
#[cfg(feature = "beacon")]
mod beacon;
mod error;
#[cfg(feature = "server")]
mod persistence;
#[cfg(feature = "pqxdh")]
mod pqxdh;
mod ratchet;
#[cfg(feature = "server")]
mod row_persistence;
#[cfg(feature = "server")]
mod server;
mod shared;
mod wire;

/// Maximum complete encoded transport message size in bytes, including all framing.
pub const MAX_MESSAGE_SIZE: usize = 33_554_432;
const _: () = assert!(MAX_MESSAGE_SIZE == beaconcrypt_parse::MAX_MESSAGE_SIZE);

#[cfg(feature = "pqxdh")]
pub use auth::{MLDSA_PUBLIC_KEY_LEN, MLDSA_SIGNATURE_LEN, MldsaIdentity};
#[cfg(all(feature = "pqxdh", feature = "beacon"))]
pub use beacon::Beacon;
#[cfg(feature = "beacon")]
pub use beacon::ProviderBeacon;
pub use error::{
	CipherTextError, DecodingError, DecryptionError, EncodingError, KeyGenError, SignatureError,
};
#[cfg(feature = "server")]
pub use persistence::{
	PersistenceError, PersistentServer, ServerSnapshot, SnapshotHead, SnapshotLineage,
	SnapshotStore,
};
pub use ratchet::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, KDF_RATCHET_OUTPUT_LEN, KDF_STATE_SIZE, RatchetStatus,
};
#[cfg(feature = "server")]
pub use row_persistence::{
	CachedRowServer, RowError, RowMessage, RowRegistrationDecision, RowRegistrationError,
	RowRegistrationPhase, RowServer, RowSession, RowStore, RowTransaction, RowTransition,
};
#[cfg(all(feature = "pqxdh", feature = "server"))]
pub use server::Server;
#[cfg(feature = "server")]
pub use server::{
	ProviderServer, RatchetSnapshot, RecvState, RegResponse, RegistrationOutput, SendState,
};
#[cfg(feature = "pqxdh")]
pub use shared::{DH_OUT_LEN, ED25519_SEED_SIZE};
pub use shared::{Decrypted, Encrypted, KEX_KDF_OUT_LEN, SignType};

#[cfg(any(feature = "cbinds", feature = "gobinds"))]
mod cbinds;

#[cfg(feature = "pybinds")]
mod pybinds;

#[cfg(any(feature = "cbinds", feature = "gobinds", feature = "pybinds"))]
mod row_binding_server;
#[cfg(any(feature = "cbinds", feature = "gobinds"))]
mod row_cbinds;
#[cfg(feature = "pybinds")]
mod row_pybinds;

#[cfg(feature = "pybinds")]
#[pyo3::pymodule]
mod beaconcrypt {
	/// Maximum complete encoded transport message in bytes; snapshots and JSON state are uncapped.
	#[pymodule_export]
	const MAX_MESSAGE_SIZE: usize = crate::MAX_MESSAGE_SIZE;

	#[pymodule_export]
	use crate::pybinds::{
		Beacon, EncryptStatePy, PersistenceError, RegResponsePy, Server, SnapshotHeadPy,
		snapshot_head, validate_snapshot_successor,
	};

	#[pymodule_export]
	use crate::row_pybinds::{
		CachedRowServerPy, RowMessagePy, RowPersistenceError, RowRegistrationDecisionPy,
		RowRegistrationError, RowServerPy, RowSessionPy, RowTransitionPy,
	};
}
