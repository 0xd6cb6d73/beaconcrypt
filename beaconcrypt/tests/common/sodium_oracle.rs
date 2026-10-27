// SPDX-License-Identifier: 0BSD

// Only the development oracle needs these compatibility symbols on Windows GNU.
// They are absent from the production RustCrypto library.
use core::ffi::{c_int, c_void};

#[unsafe(no_mangle)]
unsafe extern "C" fn memset_explicit(dest: *mut c_void, value: c_int, count: usize) -> *mut c_void {
	unsafe { core::ptr::write_bytes(dest, value as u8, count) };
	core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
	dest
}

#[link(name = "bcrypt")]
unsafe extern "system" {
	fn BCryptGenRandom(algorithm: *mut c_void, output: *mut u8, length: u32, flags: u32) -> i32;
}

#[allow(non_snake_case)]
#[unsafe(no_mangle)]
unsafe extern "system" fn SystemFunction036(output: *mut c_void, length: u32) -> u8 {
	let status = unsafe { BCryptGenRandom(core::ptr::null_mut(), output.cast(), length, 2) };
	u8::from(status >= 0)
}
