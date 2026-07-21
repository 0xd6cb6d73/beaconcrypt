// SPDX-License-Identifier: 0BSD

use crate::shared::{CryptoProvider, INITIALIZED, Provider, STATE};
use libsodium_rs::crypto_sign;
use std::{ptr::slice_from_raw_parts, sync::atomic::Ordering, vec};

pub trait ProviderBeacon {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>>;
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>>;
}

/// This function is safe to call multiple times. It is used to initialize beacons with a hardcoded server public key. You should always use this on beacons
/// ## Arguments
///
/// * `is_beacon` - Whether the current instance is a beacon
/// * `server_kid` - The ID of the server's identity key for the campaign
#[unsafe(no_mangle)]
pub extern "C" fn init_for_server(
	is_beacon: bool,
	server_kid: u64,
	server_pk: *const u8,
	server_pk_len: u64,
) {
	if !INITIALIZED.swap(true, Ordering::AcqRel) {
		let mut state = STATE.lock().unwrap();
		let pk_slice = slice_from_raw_parts(server_pk, server_pk_len.try_into().unwrap());
		let mut pk_vec = vec![0u8; crypto_sign::PUBLICKEYBYTES];
		pk_vec.copy_from_slice(unsafe { pk_slice.as_ref().unwrap() });
		*state = Provider::new(is_beacon, server_kid, Some(&pk_vec), None);
	}
}
