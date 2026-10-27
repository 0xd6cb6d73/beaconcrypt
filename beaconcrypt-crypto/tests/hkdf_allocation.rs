// SPDX-License-Identifier: 0BSD

use std::{
	alloc::{GlobalAlloc, Layout, System},
	cell::Cell,
};

use beaconcrypt_crypto::crypto_kdf::hkdf::sha512;

struct CountingAllocator;

thread_local! {
	static COUNT: Cell<Option<usize>> = const { Cell::new(None) };
}

fn record_allocation() {
	COUNT.with(|count| {
		if let Some(value) = count.get() {
			count.set(Some(value + 1));
		}
	});
}

unsafe impl GlobalAlloc for CountingAllocator {
	unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
		record_allocation();
		unsafe { System.alloc(layout) }
	}

	unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
		record_allocation();
		unsafe { System.alloc_zeroed(layout) }
	}

	unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
		unsafe { System.dealloc(pointer, layout) }
	}

	unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
		record_allocation();
		unsafe { System.realloc(pointer, layout, size) }
	}
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

#[test]
fn fixed_ratchet_hkdf_extraction_and_expansion_do_not_allocate() {
	let mut initialization = [0; 64];
	let mut advancement = [0; 76];
	COUNT.with(|count| count.set(Some(0)));
	let key = sha512::extract(None, &[0x37; 32]).unwrap();
	sha512::expand_into(&mut initialization, Some(b"initialization"), &key).unwrap();
	sha512::expand_into(&mut advancement, Some(b"symmetric ratchet"), &key).unwrap();
	drop(key);
	let allocations = COUNT.with(|count| count.replace(None).unwrap());
	assert_eq!(allocations, 0);
	assert_ne!(initialization, advancement[..64]);
}
