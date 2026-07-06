// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
mod beacon;
mod error;
#[cfg(feature = "server")]
mod server;
mod shared;

#[cfg(feature = "beacon")]
pub use beacon::{decrypt_server_message, encrypt_to_server, process_initial_message};
pub use error::{
	CipherTextError, DecodingError, DecryptionError, EncodingError, KeyGenError, SignatureError,
};
#[cfg(feature = "server")]
pub use server::{decrypt_beacon_message, encrypt_to_beacon, register_beacon};
pub use shared::{build_additional_data, init};

capnp::generated_code!(mod phase1_capnp);
capnp::generated_code!(mod phase2_capnp);
capnp::generated_code!(mod cryptoframe_capnp);
capnp::generated_code!(mod protogram_capnp);

#[cfg(test)]
mod tests {
	#[test]
	fn it_works() {}
}
