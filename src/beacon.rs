// SPDX-License-Identifier: 0BSD

use std::{mem, ptr::slice_from_raw_parts, sync::atomic::Ordering, vec};

use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libcrux_ml_dsa::ml_dsa_87;
use libcrux_ml_kem::mlkem1024;
use libsodium_rs::{crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign};

use crate::{
	phase1_capnp, phase2_capnp,
	shared::{
		BeaconCryptCnsa2, BeaconCryptPqxdh, CryptoProvider, CurveType, DhSecret, INITIALIZED,
		KemType, ML_DSA_87_PUBKEY_SIZE, ML_KEM_1024_CT_SIZE, STATE, SYM_RATCHET_INFO,
		build_additional_data, derive_root_key, encode_ec, encode_kem,
	},
};

pub trait ProviderBeacon {
	fn get_registration_bundle(&self) -> Option<Vec<u8>>;
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>>;
}

impl ProviderBeacon for BeaconCryptPqxdh {
	fn get_registration_bundle(&self) -> Option<Vec<u8>> {
		let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut bundle = msg.init_root();

		let encoded_id = encode_ec(CurveType::Ed25519, self.get_identity_pk().as_bytes()).ok()?;
		bundle.set_identity_key(&encoded_id);

		let encoded_prekey = encode_ec(CurveType::X25519, self.get_prekey_pk().as_bytes()).ok()?;
		let prekey_sig = crypto_sign::sign(&encoded_prekey, self.get_identity_sk()).ok()?;
		bundle.set_pre_key(&prekey_sig);

		let encoded_onetime =
			encode_ec(CurveType::X25519, self.get_onetime_pk().as_bytes()).ok()?;
		let onetime_sig = crypto_sign::sign(&encoded_onetime, self.get_identity_sk()).ok()?;
		bundle.set_one_time_key(&onetime_sig);

		let encoded_pq = encode_kem(KemType::MlKem768, self.get_pq_pk().as_bytes()).ok()?;
		let pq_sig = crypto_sign::sign(&encoded_pq, self.get_identity_sk()).ok()?;
		bundle.set_pq_key(&pq_sig);

		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).unwrap();
		Some(buffer)
	}

	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let reader = capnp::serialize_packed::read_message(bytes, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
		let response = typed_reader.get().ok()?;

		let kem_ciphertext =
			crypto_kem::mlkem768::Ciphertext::from_bytes(response.get_kem_cipher_text().ok()?)
				.ok()?;
		let ephemeral =
			crypto_kx::PublicKey::from_bytes(response.get_ephemeral_key().ok()?).ok()?;
		let server_id =
			crypto_sign::PublicKey::from_bytes(response.get_identity_key().ok()?).ok()?;
		let server_kex_id = crypto_sign::ed25519_pk_to_curve25519(&server_id).ok()?;
		let beacon_kex_id = crypto_sign::ed25519_sk_to_curve25519(self.get_identity_sk()).ok()?;
		let shared_secret =
			crypto_kem::mlkem768::decapsulate(&kem_ciphertext, self.get_pq_sk()).ok()?;
		let dh1: DhSecret =
			crypto_scalarmult::scalarmult(self.get_prekey_sk().as_bytes(), &server_kex_id)
				.ok()?
				.into();
		let dh2: DhSecret = crypto_scalarmult::scalarmult(&beacon_kex_id, ephemeral.as_bytes())
			.ok()?
			.into();
		let dh3: DhSecret =
			crypto_scalarmult::scalarmult(self.get_prekey_sk().as_bytes(), ephemeral.as_bytes())
				.ok()?
				.into();
		let dh4: DhSecret =
			crypto_scalarmult::scalarmult(self.get_onetime_sk().as_bytes(), ephemeral.as_bytes())
				.ok()?
				.into();
		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, shared_secret).ok()?;
		self.delete_onetime_keypair();

		self.add_server_pk(server_id.clone());
		self.set_identity_kid(response.get_key_id());
		let id = self.get_identity_pk().clone();
		self.set_associated_data(build_additional_data(server_id.clone(), id));
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let srv_key_id = self.get_server_kid();
		self.init_ratchets(&derived_secret, &info_str, true, srv_key_id);

		match response.get_app_cipher_text() {
			Ok(ciphertext) => match self.decrypt_message(ciphertext, srv_key_id, true) {
				Some(plaintext) => Some(plaintext),
				None => None,
			},
			Err(_) => Some(vec![0u8; 0]),
		}
	}
}

impl ProviderBeacon for BeaconCryptCnsa2 {
	fn get_registration_bundle(&self) -> Option<Vec<u8>> {
		let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut bundle = msg.init_root();

		bundle.set_identity_key(self.get_identity_pk().as_slice());
		bundle.set_pq_key(self.get_pq_pk().as_slice());
		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).unwrap();
		Some(buffer)
	}
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let reader = capnp::serialize_packed::read_message(bytes, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
		let response = typed_reader.get().ok()?;

		let mldsa_buf = response
			.get_identity_key()
			.ok()?
			.as_array::<ML_DSA_87_PUBKEY_SIZE>()
			.unwrap();
		let mldsa = ml_dsa_87::MLDSA87VerificationKey::new(*mldsa_buf);

		let kem_ct_buf = response
			.get_kem_cipher_text()
			.ok()?
			.as_array::<ML_KEM_1024_CT_SIZE>()
			.unwrap();
		let kem_ct = mlkem1024::MlKem1024Ciphertext::from(kem_ct_buf);

		None
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn process_initial_message(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut net_vec = vec![0u8; bytes_len];
	let net_slice = slice_from_raw_parts(bytes, bytes_len);
	net_vec.copy_from_slice(unsafe { net_slice.as_ref().unwrap() });
	let mut state = STATE.lock().unwrap();
	match state.finish_registration(net_vec.as_slice()) {
		Some(mut plaintext) => {
			unsafe {
				_out = plaintext.as_mut_ptr();
				*out_len = plaintext.len();
				*out_capa = plaintext.capacity();
				mem::forget(plaintext);
			};
			0i32
		}
		None => -1i32,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn process_initial_message_signed(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut net_vec = vec![0u8; bytes_len];
	let net_slice = slice_from_raw_parts(bytes, bytes_len);
	net_vec.copy_from_slice(unsafe { net_slice.as_ref().unwrap() });

	let mut state = STATE.lock().unwrap();
	match state.verify_signature(net_vec.as_slice()) {
		Some(verified) => match state.finish_registration(&verified) {
			Some(mut plaintext) => {
				unsafe {
					_out = plaintext.as_mut_ptr();
					*out_len = plaintext.len();
					*out_capa = plaintext.capacity();
					mem::forget(plaintext);
				};
				0i32
			}
			None => -1i32,
		},
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_server_message(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };

	let srv_seq = state.get_server_kid();
	match state.decrypt_message(&data_vec, srv_seq, true) {
		Some(mut plaintext) => {
			unsafe {
				_out = plaintext.as_mut_ptr();
				*out_len = plaintext.len();
				*out_capa = plaintext.capacity();
				mem::forget(plaintext);
			};
			0
		}
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_server_message_signed(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };

	match state.verify_signature(data_vec.as_slice()) {
		Some(verified) => {
			let srv_seq = state.get_server_kid();
			match state.decrypt_message(&verified, srv_seq, true) {
				Some(mut plaintext) => {
					unsafe {
						_out = plaintext.as_mut_ptr();
						*out_len = plaintext.len();
						*out_capa = plaintext.capacity();
						mem::forget(plaintext);
					};
					0
				}
				None => -1,
			}
		}
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_server(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let srv_seq = state.get_server_kid();
	match state.encrypt_message(data_vec.as_slice(), false, srv_seq) {
		Some(mut ciphertext) => {
			unsafe {
				_out = ciphertext.as_mut_ptr();
				*out_len = ciphertext.len();
				*out_capa = ciphertext.capacity();
				mem::forget(ciphertext);
			};
			0
		}
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_server_signed(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let srv_seq = state.get_server_kid();
	match state.encrypt_message(data_vec.as_slice(), false, srv_seq) {
		Some(ciphertext) => match state.sign_message(ciphertext.as_slice()) {
			Some(mut signed) => {
				unsafe {
					_out = signed.as_mut_ptr();
					*out_len = signed.len();
					*out_capa = signed.capacity();
					mem::forget(signed);
				};
				0
			}
			None => -1,
		},
		None => -1,
	}
}

/// # Safety
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn generate_registration(
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	let state = STATE.lock().unwrap();
	match state.get_registration_bundle() {
		Some(mut data) => {
			unsafe {
				_out = data.as_mut_ptr();
				*out_len = data.len();
				*out_capa = data.capacity();
				mem::forget(data);
			};
			0
		}
		None => -1,
	}
}

/// This function is safe to call multiple times. It is used to initialize beacons with a hardcoded server public key. You should always use this on beacons
/// ## Arguments
///
/// * `is_beacon` - Whether the current instance is a beacon
/// * `server_seq` - The ID of the server's identity key for the campaign
#[unsafe(no_mangle)]
pub extern "C" fn init_for_server(
	is_beacon: bool,
	server_seq: u64,
	server_pk: *const u8,
	server_pk_len: u64,
) {
	if !INITIALIZED.swap(true, Ordering::AcqRel) {
		let mut state = STATE.lock().unwrap();
		let pk_slice = slice_from_raw_parts(server_pk, server_pk_len.try_into().unwrap());
		let mut pk_vec = vec![0u8; crypto_sign::PUBLICKEYBYTES];
		pk_vec.copy_from_slice(unsafe { pk_slice.as_ref().unwrap() });
		*state = BeaconCryptPqxdh::new(is_beacon, server_seq, Some(&pk_vec));
	}
}

#[cfg(test)]
mod tests {
	use libsodium_rs::crypto_kx;

	use crate::{
		beacon::ProviderBeacon,
		server::ProviderServer,
		shared::{BeaconCryptPqxdh, CryptoProvider},
	};

	fn test_register_beacon(
		server: &mut BeaconCryptPqxdh,
		beacon: &mut BeaconCryptPqxdh,
	) -> Vec<u8> {
		let message = [0xFFu8; 32];

		let phase_1 = beacon.get_registration_bundle().unwrap();
		let reg_out = server.get_shared_secret(&phase_1).unwrap();
		let phase2 = server
			.build_registration_response(reg_out, Some(&message))
			.unwrap();
		beacon.finish_registration(&phase2.serialized).unwrap()
	}

	#[test]
	fn beacon_sign_can_check() {
		let server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk();
		let beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let message = [0xFFu8; 32];
		let signed = server.sign_message(&message).unwrap();

		assert!(beacon.verify_signature(signed.as_slice()).is_some());
	}

	#[test]
	fn beacon_can_register() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk();
		let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let message = [0xFFu8; 32];
		let phase_1 = beacon.get_registration_bundle().unwrap();
		let reg_out = server.get_shared_secret(&phase_1).unwrap();
		let phase2 = server
			.build_registration_response(reg_out, Some(&message))
			.unwrap();
		let plaintext = beacon.finish_registration(&phase2.serialized).unwrap();
		assert!(plaintext.len() == message.len());
		assert_eq!(plaintext.as_array::<32>().unwrap().to_owned(), message);
	}

	#[test]
	fn beacon_can_sign() {
		let beacon = BeaconCryptPqxdh::new(true, 0, None);
		let message = [0xFFu8; 32];
		assert!(beacon.sign_message(&message).is_some());
	}

	#[test]
	fn beacon_can_catch_up() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(server.get_id_by_seq(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, true, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);

		let dec_b1_m1 = b1.decrypt_message(&b1_m1, 0, true).unwrap();
		let dec_b1_m2 = b1.decrypt_message(&b1_m2, 0, true).unwrap();
		assert_eq!(dec_b1_m1, dec_b1_m2);
	}

	#[test]
	fn beacon_delete_onetime() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let empty = [0u8; crypto_kx::PUBLICKEYBYTES];
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		assert!(b1.get_onetime_pk().as_bytes() != empty);
		assert!(b1.get_onetime_sk().as_bytes() != empty);
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(b1.get_onetime_pk().as_bytes() == empty);
		assert!(b1.get_onetime_sk().as_bytes() == empty);
	}
}
