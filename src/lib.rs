// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
mod beacon;
mod error;
#[cfg(feature = "server")]
mod server;
mod shared;

#[cfg(feature = "beacon")]
pub use beacon::{
	decrypt_server_message, decrypt_server_message_signed, encrypt_to_server,
	encrypt_to_server_signed, generate_registration, init_for_server, process_initial_message,
	process_initial_message_signed,
};
pub use error::{
	CipherTextError, DecodingError, DecryptionError, EncodingError, KeyGenError, SignatureError,
};
#[cfg(feature = "server")]
pub use server::{
	decrypt_beacon_message, decrypt_beacon_message_signed, encrypt_to_beacon,
	encrypt_to_beacon_signed, register_beacon,
};
pub use shared::{
	BeaconCryptPqxdh, CryptoProvider, free_vec, init, set_identity_seq, sign_message,
	verify_signature,
};

capnp::generated_code!(pub mod phase1_capnp);
capnp::generated_code!(pub mod phase2_capnp);
capnp::generated_code!(pub mod cryptoframe_capnp);
capnp::generated_code!(pub mod protogram_capnp);
