// SPDX-License-Identifier: 0BSD

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

/// # Safety
/// This is a horrible hack to compensate for the fact that libsodium 0.2.4 fails to link to `memset_explicit` on Windows when using the GNU toolchain. You probably should not use this
#[cfg(all(windows, target_env = "gnu"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset_explicit(
	dest: *mut std::ffi::c_void,
	ch: std::ffi::c_int,
	count: usize,
) -> *mut std::ffi::c_void {
	unsafe { std::ptr::write_bytes(dest, ch as u8, count) };
	std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
	dest
}

#[cfg(all(windows, target_env = "gnu"))]
#[link(name = "bcrypt")]
unsafe extern "system" {
	fn BCryptGenRandom(
		algorithm: *mut std::ffi::c_void,
		buffer: *mut u8,
		buffer_len: u32,
		flags: u32,
	) -> i32;
}

/// # Safety
/// This is a horrible hack to compensate for the fact that libsodium 0.2.4 fails to link to `SystemFunction036` on Windows when using the GNU toolchain. You probably should not use this
#[cfg(all(windows, target_env = "gnu"))]
#[unsafe(no_mangle)]
pub unsafe extern "system" fn SystemFunction036(
	buffer: *mut std::ffi::c_void,
	buffer_len: u32,
) -> u8 {
	const BCRYPT_USE_SYSTEM_PREFERRED_RNG: u32 = 0x00000002;
	let status = unsafe {
		BCryptGenRandom(
			std::ptr::null_mut(),
			buffer.cast::<u8>(),
			buffer_len,
			BCRYPT_USE_SYSTEM_PREFERRED_RNG,
		)
	};
	u8::from(status >= 0)
}

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
pub use shared::{DH_OUT_LEN, Decrypted, ED25519_SEED_SIZE, Encrypted, KEX_KDF_OUT_LEN, SignType};

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
