// SPDX-License-Identifier: 0BSD

use std::{mem, slice::from_raw_parts, vec};

use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign};

use crate::{
	build_additional_data, phase1_capnp, phase2_capnp,
	shared::{
		BeaconCryptAgent, DhSecret, RegistrationOutput, STATE, SYM_RATCHET_INFO, decode_ec,
		decode_kem, derive_root_key,
	},
};

pub struct RegResponse {
	pub serialized: Vec<u8>,
	kid: u64,
}

impl BeaconCryptAgent {
	pub fn get_shared_secret(
		&mut self,
		buffer: &[u8],
	) -> Result<RegistrationOutput, Box<dyn std::error::Error>> {
		let reader = capnp::serialize::read_message(buffer, ReaderOptions::new()).unwrap();
		let typed_reader = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(reader);
		let registration = typed_reader.get().unwrap();

		let decoded_beacon_id = decode_ec(registration.get_identity_key()?)?;
		let remote_id = crypto_sign::PublicKey::from_bytes(&decoded_beacon_id)?;
		let pq_verified = crypto_sign::verify(registration.get_pq_key()?, &remote_id).unwrap();
		let prekey_verified = crypto_sign::verify(registration.get_pre_key()?, &remote_id).unwrap();
		let onetime_verified =
			crypto_sign::verify(registration.get_one_time_key()?, &remote_id).unwrap();

		let beacon_prekey = crypto_kx::PublicKey::from_bytes(&decode_ec(&prekey_verified)?)?;
		let beacon_onetime = crypto_kx::PublicKey::from_bytes(&decode_ec(&onetime_verified)?)?;
		let ephemeral = crypto_kx::KeyPair::generate()?;
		let pq_pub = crypto_kem::mlkem768::PublicKey::from_bytes(&decode_kem(&pq_verified)?)?;
		let (kem_ciphertext, kem_shared) = crypto_kem::mlkem768::encapsulate(&pq_pub)?;

		let remote_id_kex = crypto_sign::ed25519_pk_to_curve25519(&remote_id)?;
		let id_kex_sk = crypto_sign::ed25519_sk_to_curve25519(self.get_identity_sk())?;
		let dh1: DhSecret =
			crypto_scalarmult::scalarmult(&id_kex_sk, beacon_prekey.as_bytes())?.into();
		let dh2: DhSecret =
			crypto_scalarmult::scalarmult(ephemeral.secret_key.as_bytes(), &remote_id_kex)?.into();
		let dh3: DhSecret = crypto_scalarmult::scalarmult(
			ephemeral.secret_key.as_bytes(),
			beacon_prekey.as_bytes(),
		)?
		.into();
		let dh4: DhSecret = crypto_scalarmult::scalarmult(
			ephemeral.secret_key.as_bytes(),
			beacon_onetime.as_bytes(),
		)?
		.into();

		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, kem_shared)?;
		let server_id = self.get_identity_pk().clone();
		self.set_associated_data(build_additional_data(server_id, remote_id.clone()));

		Ok(RegistrationOutput {
			kem_ciphertext,
			derived_secret: derived_secret.into(),
			ephemeral: ephemeral.public_key,
			public_key: remote_id,
		})
	} // ephemeral and kem_shared are deleted and zeroized here

	pub fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse> {
		// create the session on our end
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let remote_kid = self.new_remote_kid();
		self.add_known_kid(remote_kid, reg_out.public_key);
		self.init_ratchets(
			reg_out.derived_secret.inner().as_slice(),
			&info_str,
			false,
			remote_kid,
		);

		let mut msg = TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default();
		let mut bundle = msg.init_root();
		bundle.set_key_id(self.get_server_kid());
		bundle.set_ephemeral_key(reg_out.ephemeral.as_bytes());
		bundle.set_identity_key(self.get_identity_pk().as_bytes());
		bundle.set_kem_cipher_text(reg_out.kem_ciphertext.as_bytes());

		let mut buffer = vec![];
		if let Some(plaintext) = data {
			let ciphertext = self.encrypt_message(plaintext, true, remote_kid)?;
			let _ = bundle.set_app_cipher_text(&ciphertext);
			capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner()).ok()?;
		} else {
			capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner()).ok()?;
		};

		Some(RegResponse {
			serialized: buffer,
			kid: remote_kid,
		})
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
///
/// * `bytes` - A serialized `phase1_capnp::init_kex` from the network
/// * `bytes_len` - The size of the `bytes` buffer
/// * `data` - The contents of the initial message to send back to the agent, as bytes
/// * `data_len` - The size of the `data` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
/// ## Returns
///
/// * i32 - Values other than 0 indicate failure
///
#[unsafe(no_mangle)]
pub unsafe extern "C" fn register_beacon(
	bytes: *const u8,
	bytes_len: usize,
	data: *const u8,
	data_len: usize,
	mut _response: *mut u8,
	response_len: *mut usize,
	response_capa: *mut usize,
	mut _pk: *mut u8,
	pk_len: *mut usize,
	pk_capa: *mut usize,
	key_id: *mut u64,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let bytes_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let mut state = STATE.lock().unwrap();
	match state.get_shared_secret(bytes_vec.as_slice()) {
		Ok(secrets) => {
			let to_encrypt = if data.is_null() || data_len == 0 {
				None
			} else {
				Some(unsafe { from_raw_parts(data, data_len) })
			};
			match state.build_registration_response(secrets.clone(), to_encrypt) {
				Some(mut response) => {
					let beacon_key_id = response.kid;
					unsafe {
						_response = response.serialized.as_mut_ptr();
						*response_len = response.serialized.len();
						*response_capa = response.serialized.capacity();
						mem::forget(response);
						let mut pk = secrets.public_key.as_bytes().to_vec();
						_pk = pk.as_mut_ptr();
						*pk_len = pk.len();
						*pk_capa = pk.capacity();
						mem::forget(pk);
						*key_id = beacon_key_id;
					};
					0
				}
				None => -1i32,
			}
		}
		Err(_) => -1i32,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `seq` - The sequence number for the beacon to encypt to
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_beacon_message(
	seq: u64,
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

	match state.decrypt_message(&data_vec, seq, false) {
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
/// * `seq` - The sequence number for the beacon to encypt to
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_beacon_message_signed(
	seq: u64,
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
		Some(verified) => match state.decrypt_message(&verified, seq, false) {
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
/// * `seq` - The sequence number for the beacon to encypt to
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_beacon(
	seq: u64,
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
	match state.encrypt_message(data_vec.as_slice(), true, seq) {
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
/// * `seq` - The sequence number for the beacon to encypt to
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_beacon_signed(
	seq: u64,
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
	match state.encrypt_message(data_vec.as_slice(), false, seq) {
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

#[cfg(test)]
mod tests {
	use crate::shared::BeaconCryptAgent;

	fn test_register_beacon(
		server: &mut BeaconCryptAgent,
		beacon: &mut BeaconCryptAgent,
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
	fn server_can_register_multiple() {
		let mut server = BeaconCryptAgent::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptAgent::new(true, 0, Some(server_id.as_bytes()));
		let b1_reg = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptAgent::new(true, 0, Some(server_id.as_bytes()));
		let b2_reg = test_register_beacon(&mut server, &mut b2);

		assert_eq!(b1_reg, b2_reg);
	}

	#[test]
	fn server_encrypt_to_multiple() {
		let mut server = BeaconCryptAgent::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptAgent::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptAgent::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b2);

		assert!(server.get_id_by_seq(1).is_some());
		assert!(server.get_id_by_seq(2).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b2_m1 = server.encrypt_message(&message, true, 2).unwrap();
		assert_ne!(b1_m1, b2_m1);
	}

	#[test]
	fn server_encrypt_multiple() {
		let mut server = BeaconCryptAgent::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptAgent::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b1);

		assert!(server.get_id_by_seq(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, true, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);
	}
}
