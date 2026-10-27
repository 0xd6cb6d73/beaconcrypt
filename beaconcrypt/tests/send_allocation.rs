// SPDX-License-Identifier: 0BSD

#![cfg(all(
	feature = "std",
	feature = "beacon",
	feature = "server",
	feature = "pqxdh"
))]

use std::{
	alloc::{GlobalAlloc, Layout, System},
	cell::Cell,
};

use beaconcrypt::{Beacon, ProviderBeacon, ProviderServer, Server};

const PAYLOAD_LENGTH: usize = 1024 * 1024;

#[derive(Clone, Copy, Default)]
struct Buffers {
	current: usize,
	peak: usize,
	allocations: usize,
}

thread_local! {
	static BUFFERS: Cell<Option<Buffers>> = const { Cell::new(None) };
}

fn record_allocation(size: usize, allocated: bool) {
	if size < PAYLOAD_LENGTH {
		return;
	}
	let _ = BUFFERS.try_with(|buffers| {
		if let Some(mut record) = buffers.get() {
			if allocated {
				record.current += size;
				record.peak = record.peak.max(record.current);
				record.allocations += 1;
			} else {
				record.current -= size;
			}
			buffers.set(Some(record));
		}
	});
}

struct BufferAllocator;

unsafe impl GlobalAlloc for BufferAllocator {
	unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
		let pointer = unsafe { System.alloc(layout) };
		if !pointer.is_null() {
			record_allocation(layout.size(), true);
		}
		pointer
	}

	unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
		let pointer = unsafe { System.alloc_zeroed(layout) };
		if !pointer.is_null() {
			record_allocation(layout.size(), true);
		}
		pointer
	}

	unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
		record_allocation(layout.size(), false);
		unsafe { System.dealloc(pointer, layout) }
	}

	unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
		let new_pointer = unsafe { System.realloc(pointer, layout, size) };
		if !new_pointer.is_null() {
			record_allocation(layout.size(), false);
			record_allocation(size, true);
		}
		new_pointer
	}
}

#[global_allocator]
static ALLOCATOR: BufferAllocator = BufferAllocator;

#[test]
fn framed_send_needs_only_ciphertext_and_final_frame_payload_buffers() {
	let mut server = Server::new(7, Some(&[7; 32]), Some(&[8; 32]));
	let mut beacon = Beacon::new(
		7,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let request = beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&request).unwrap();
	let response = server.build_registration_response(pending, None).unwrap();
	beacon.finish_registration(&response.serialized).unwrap();
	let payload = vec![0x5a; PAYLOAD_LENGTH];
	// No existing large allocation is released in this window: the payload is borrowed and both endpoints remain live.
	BUFFERS.with(|buffers| buffers.set(Some(Buffers::default())));
	let frame = server.encrypt_message(&payload, response.kid);
	let buffers = BUFFERS.with(|buffers| buffers.replace(None).unwrap());
	let frame = frame.unwrap();
	assert_eq!(buffers.allocations, 2);
	assert_eq!(buffers.current, frame.ciphertext.capacity());
	assert_eq!(buffers.peak, PAYLOAD_LENGTH + frame.ciphertext.capacity());
	assert!(buffers.peak <= 2 * PAYLOAD_LENGTH + 128);
	println!(
		"payload bytes: {PAYLOAD_LENGTH}; peak payload-buffer bytes: {}",
		buffers.peak
	);
	assert_eq!(
		beacon.decrypt_message(&frame.ciphertext).unwrap().plaintext,
		payload
	);
}
