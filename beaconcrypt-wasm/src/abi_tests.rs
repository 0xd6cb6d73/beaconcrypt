// SPDX-License-Identifier: 0BSD

use super::*;

// Inspect only the two tracked live allocations immediately before System releases them.
// Observing dangling Vec pointers after drop would not be a valid zeroization test.
mod drop_observer {
	use std::{
		alloc::{GlobalAlloc, Layout, System},
		sync::{
			Mutex,
			atomic::{AtomicU8, AtomicUsize, Ordering},
		},
	};

	pub static LOCK: Mutex<()> = Mutex::new(());
	pub static DATA: AtomicUsize = AtomicUsize::new(0);
	pub static STATE: AtomicUsize = AtomicUsize::new(0);
	pub static WIPED: AtomicU8 = AtomicU8::new(0);

	pub struct ObservedAllocator;

	unsafe impl GlobalAlloc for ObservedAllocator {
		unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
			unsafe { System.alloc(layout) }
		}

		unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
			let address = ptr as usize;
			let bit = if DATA
				.compare_exchange(address, 0, Ordering::SeqCst, Ordering::SeqCst)
				.is_ok()
			{
				1
			} else if STATE
				.compare_exchange(address, 0, Ordering::SeqCst, Ordering::SeqCst)
				.is_ok()
			{
				2
			} else {
				0
			};
			if bit != 0 {
				// The tracked buffers are initialized throughout their asserted exact capacities.
				// The allocation remains live until the System.dealloc call below.
				let bytes = unsafe { std::slice::from_raw_parts(ptr, layout.size()) };
				if bytes.iter().all(|byte| *byte == 0) {
					WIPED.fetch_or(bit, Ordering::SeqCst);
				}
			}
			unsafe { System.dealloc(ptr, layout) }
		}
	}
}

#[global_allocator]
static TEST_ALLOCATOR: drop_observer::ObservedAllocator = drop_observer::ObservedAllocator;

#[test]
fn response_drop_wipes_owned_data_and_state_before_deallocation() {
	use std::sync::atomic::Ordering;
	let _guard = drop_observer::LOCK.lock().unwrap();
	let mut response = Response::success(7, 11, vec![0x91; 32]);
	response.state = vec![0xe3; 64];
	assert_eq!(response.data.capacity(), response.data.len());
	assert_eq!(response.state.capacity(), response.state.len());
	drop_observer::WIPED.store(0, Ordering::SeqCst);
	drop_observer::DATA.store(response.data.as_ptr() as usize, Ordering::SeqCst);
	drop_observer::STATE.store(response.state.as_ptr() as usize, Ordering::SeqCst);
	drop(response);
	assert_eq!(drop_observer::DATA.load(Ordering::SeqCst), 0);
	assert_eq!(drop_observer::STATE.load(Ordering::SeqCst), 0);
	assert_eq!(drop_observer::WIPED.load(Ordering::SeqCst), 3);
}

#[test]
fn exported_call_dispatches_the_requested_close_operation() {
	let created = dispatch(1, 0, 19, &[9; 64], &[3]);
	assert_eq!(created.status, abi::OK);
	let packed = bc_call(9, created.handle, 0, 0, 0, 0, 0);
	// Native pointers need not fit this wasm32 descriptor. Dispatch must still occur.
	if packed != 0 {
		abi::bc_free((packed >> 32) as u32, packed as u32);
	}
	assert_eq!(
		dispatch(3, created.handle, 0, &[], &[]).status,
		INVALID_ARGUMENT
	);
}

#[test]
fn invalid_input_or_extra_descriptors_do_not_dispatch_or_close_the_owner() {
	let created = dispatch(1, 0, 19, &[9; 64], &[3]);
	assert_eq!(created.status, abi::OK);
	for (ptr, len) in [(0, 1), (1, 0), (u32::MAX, 1), (1, u32::MAX)] {
		for (input_ptr, input_len, extra_ptr, extra_len) in [(ptr, len, 0, 0), (0, 0, ptr, len)] {
			assert_eq!(
				call(
					9,
					created.handle,
					0,
					input_ptr,
					input_len,
					extra_ptr,
					extra_len
				)
				.status,
				INVALID_ARGUMENT
			);
			assert_eq!(dispatch(3, created.handle, 0, &[], &[]).status, abi::OK);
		}
	}
	assert_eq!(call(9, created.handle, 0, 0, 0, 0, 0).status, abi::OK);
}

#[cfg(target_arch = "wasm32")]
mod wasm {
	use super::*;
	use std::sync::atomic::Ordering;

	fn input(bytes: &[u8]) -> u32 {
		if bytes.is_empty() {
			return 0;
		}
		let len = u32::try_from(bytes.len()).unwrap();
		let ptr = abi::bc_alloc(len);
		assert_ne!(ptr, 0, "valid bounded input allocation");
		// bc_alloc returned a live writable allocation of exactly this length.
		unsafe { std::slice::from_raw_parts_mut(ptr as *mut u8, bytes.len()) }
			.copy_from_slice(bytes);
		ptr
	}

	fn reply(packed: u64) -> Vec<u8> {
		let (ptr, len) = ((packed >> 32) as u32, packed as u32);
		assert_ne!(ptr, 0, "reply pointer must occupy the upper 32 bits");
		assert!(len >= 32, "reply must include its complete header");
		let bytes = abi::copy_input(ptr, len)
			.expect("reply must be one registered allocation")
			.to_vec();
		abi::bc_free(ptr, len);
		assert!(abi::copy_input(ptr, len).is_none());
		bytes
	}

	fn invoke(op: u32, handle: u32, arg: u64, bytes: &[u8], extra: &[u8]) -> Response {
		let input_ptr = input(bytes);
		let extra_ptr = input(extra);
		let packed = bc_call(
			op,
			handle,
			arg,
			input_ptr,
			bytes.len() as u32,
			extra_ptr,
			extra.len() as u32,
		);
		abi::bc_free(input_ptr, bytes.len() as u32);
		abi::bc_free(extra_ptr, extra.len() as u32);
		let reply = reply(packed);
		let data_len = u32::from_le_bytes(reply[24..28].try_into().unwrap()) as usize;
		let state_len = u32::from_le_bytes(reply[28..32].try_into().unwrap()) as usize;
		assert_eq!(reply.len(), 32 + data_len + state_len);
		Response {
			status: u32::from_le_bytes(reply[..4].try_into().unwrap()),
			handle: u32::from_le_bytes(reply[4..8].try_into().unwrap()),
			key_id: u64::from_le_bytes(reply[8..16].try_into().unwrap()),
			seq: u64::from_le_bytes(reply[16..24].try_into().unwrap()),
			data: reply[32..32 + data_len].to_vec(),
			state: reply[32 + data_len..].to_vec(),
		}
	}

	#[test]
	fn exported_allocations_require_exact_descriptors_and_wipe_before_free() {
		let _guard = drop_observer::LOCK.lock().unwrap();
		let ptr = input(&[11, 22, 33, 44]);
		assert_eq!(&*abi::copy_input(ptr, 4).unwrap(), &[11, 22, 33, 44]);
		for (bad_ptr, bad_len) in [(ptr, 0), (ptr, 3), (ptr, 5), (ptr + 1, 3), (0, 4)] {
			assert!(abi::copy_input(bad_ptr, bad_len).is_none());
			abi::bc_free(bad_ptr, bad_len);
			assert!(abi::copy_input(ptr, 4).is_some());
		}
		drop_observer::WIPED.store(0, Ordering::SeqCst);
		drop_observer::DATA.store(ptr as usize, Ordering::SeqCst);
		abi::bc_free(ptr, 4);
		assert!(abi::copy_input(ptr, 4).is_none());
		assert_eq!(drop_observer::DATA.load(Ordering::SeqCst), 0);
		assert_eq!(drop_observer::WIPED.load(Ordering::SeqCst), 1);
		abi::bc_free(ptr, 4);
		assert_eq!(abi::bc_alloc(0), 0);
		assert_eq!(abi::bc_alloc(u32::MAX), 0);
	}

	#[test]
	fn packed_replies_preserve_full_width_metadata_and_complete_payloads() {
		let mut response = Response::message(u32::MAX, u64::MAX, u64::MAX - 1, vec![1, 2, 3]);
		response.state = vec![4, 5];
		let bytes = reply(abi::encode_result(response));
		assert_eq!(bytes.len(), 37);
		assert_eq!(&bytes[..4], &abi::OK.to_le_bytes());
		assert_eq!(&bytes[4..8], &u32::MAX.to_le_bytes());
		assert_eq!(&bytes[8..16], &u64::MAX.to_le_bytes());
		assert_eq!(&bytes[16..24], &(u64::MAX - 1).to_le_bytes());
		assert_eq!(&bytes[24..28], &3u32.to_le_bytes());
		assert_eq!(&bytes[28..32], &2u32.to_le_bytes());
		assert_eq!(&bytes[32..], &[1, 2, 3, 4, 5]);
	}

	#[test]
	fn exported_call_returns_failure_descriptors_without_dispatching_invalid_inputs() {
		let created = invoke(1, 0, 19, &[9; 64], &[3]);
		assert_eq!(created.status, abi::OK);
		let owner = created.handle;
		for (input_ptr, input_len, extra_ptr, extra_len) in [(0, 1, 0, 0), (0, 0, 1, 0)] {
			let bytes = reply(bc_call(
				9, owner, 0, input_ptr, input_len, extra_ptr, extra_len,
			));
			assert_eq!(bytes.len(), 32);
			assert_eq!(&bytes[..4], &INVALID_ARGUMENT.to_le_bytes());
			assert!(bytes[4..].iter().all(|&byte| byte == 0));
			assert_eq!(invoke(3, owner, 0, &[], &[]).status, abi::OK);
		}
		assert_eq!(invoke(9, owner, 0, &[], &[]).status, abi::OK);
	}

	#[test]
	fn exported_call_copies_registered_input_and_extra_and_returns_protocol_metadata() {
		const SERVER_KID: u64 = u64::MAX - 5;
		let created = invoke(1, 0, SERVER_KID, &[9; 64], &[3]);
		assert_eq!(created.status, abi::OK);
		assert_ne!(created.handle, 0);
		let owner = created.handle;
		let identity = invoke(3, owner, 0, &[], &[]);
		assert_eq!(identity.status, abi::OK);
		assert_eq!(identity.key_id, SERVER_KID);
		let mldsa_identity = invoke(24, owner, 0, &[], &[]);
		assert_eq!(mldsa_identity.status, abi::OK);
		let mut beacon = Beacon::try_new(SERVER_KID, &identity.data, &mldsa_identity.data).unwrap();
		let bundle = beacon.get_registration_bundle().unwrap();
		let registration = invoke(5, owner, 0, &bundle, b"initial plaintext from extra");
		assert_eq!(registration.status, abi::OK);
		assert_eq!(registration.handle, owner);
		assert_eq!(
			beacon.finish_registration(&registration.data).unwrap(),
			b"initial plaintext from extra"
		);
		let outbound = invoke(7, owner, registration.key_id, b"guest to beacon", &[]);
		assert_eq!(outbound.status, abi::OK);
		assert_eq!(outbound.key_id, registration.key_id);
		assert_eq!(outbound.seq, 2);
		assert_eq!(
			beacon.decrypt_message(&outbound.data).unwrap().plaintext,
			b"guest to beacon"
		);
		let inbound = beacon.encrypt_message(b"beacon to guest").unwrap();
		let received = invoke(8, owner, 0, &inbound.ciphertext, &[]);
		assert_eq!(received.status, abi::OK);
		assert_eq!(received.handle, owner);
		assert_eq!(received.key_id, registration.key_id);
		assert_eq!(received.seq, 1);
		assert_eq!(received.data, b"beacon to guest");
		let closed = invoke(9, owner, 0, &[], &[]);
		assert_eq!(closed.status, abi::OK);
		assert_eq!(closed.handle, owner);
		let invalid = invoke(3, owner, 0, &[], &[]);
		assert_eq!(invalid.status, INVALID_ARGUMENT);
		assert_eq!(invalid.handle, 0);
		assert!(invalid.data.is_empty() && invalid.state.is_empty());
	}
}
