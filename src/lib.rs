// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
mod beacon;
#[cfg(feature = "cnsa2")]
mod cnsa2;
mod error;
#[cfg(feature = "pqxdh")]
mod pqxdh;
#[cfg(feature = "server")]
mod server;
mod shared;

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
