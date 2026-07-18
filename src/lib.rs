// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
mod beacon;
mod error;
#[cfg(feature = "pqxdh")]
mod pqxdh;
#[cfg(feature = "server")]
mod server;
mod shared;

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

#[cfg(feature = "beacon")]
pub use beacon::ProviderBeacon;
pub use error::{
	CipherTextError, DecodingError, DecryptionError, EncodingError, KeyGenError, SignatureError,
};
#[cfg(feature = "pqxdh")]
pub use pqxdh::BeaconCryptPqxdh;
#[cfg(feature = "server")]
pub use server::{ProviderServer, RegResponse, RegistrationOutput};
pub use shared::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, CryptoProvider, DH_OUT_LEN, ED25519_SEED_SIZE,
	KDF_RATCHET_OUTPUT_LEN, KDF_STATE_SIZE, KEX_KDF_OUT_LEN, SignType,
};

capnp::generated_code!(pub mod phase1_capnp);
capnp::generated_code!(pub mod phase2_capnp);
capnp::generated_code!(pub mod cryptoframe_capnp);
capnp::generated_code!(pub mod protogram_capnp);

#[cfg(feature = "gobinds")]
mod gobinds;

#[cfg(feature = "cbinds")]
mod cbinds;

#[cfg(feature = "pybinds")]
mod pybinds;

#[cfg(feature = "pybinds")]
#[pyo3::pymodule(name = "beaconcrypt")]
fn beaconcrypt_py(m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> pyo3::PyResult<()> {
	pybinds::register(m)
}
