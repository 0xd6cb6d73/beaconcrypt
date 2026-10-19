// SPDX-License-Identifier: 0BSD

use std::{cell::RefCell, collections::BTreeMap};

use beaconcrypt::PersistenceError;
use zeroize::{Zeroize, Zeroizing};

pub(crate) const OK: u32 = 0;
pub(crate) const REJECTED: u32 = 1;
pub(crate) const INVALID_ARGUMENT: u32 = 2;
pub(crate) const INITIALIZATION: u32 = 10;

pub(crate) fn error_status(error: PersistenceError) -> u32 {
	match error {
		PersistenceError::MissingSnapshot => 3,
		PersistenceError::InvalidSnapshot => 4,
		PersistenceError::NonCanonicalSnapshot => 5,
		PersistenceError::StaleGeneration => 6,
		PersistenceError::GenerationExhausted => 7,
		PersistenceError::Encoding => 8,
		PersistenceError::OutputEncoding => 9,
		PersistenceError::Initialization => INITIALIZATION,
		PersistenceError::Digest => 11,
		PersistenceError::Poisoned => 12,
	}
}

#[derive(Default)]
pub(crate) struct Response {
	pub status: u32,
	pub handle: u32,
	pub key_id: u64,
	pub seq: u64,
	pub data: Vec<u8>,
	pub state: Vec<u8>,
}

impl Response {
	pub fn success(handle: u32, key_id: u64, data: Vec<u8>) -> Self {
		Self {
			status: OK,
			handle,
			key_id,
			seq: 0,
			data,
			state: Vec::new(),
		}
	}

	pub fn failed(status: u32) -> Self {
		Self {
			status,
			handle: 0,
			key_id: 0,
			seq: 0,
			data: Vec::new(),
			state: Vec::new(),
		}
	}

	pub fn message(handle: u32, key_id: u64, seq: u64, data: Vec<u8>) -> Self {
		let mut response = Self::success(handle, key_id, data);
		response.seq = seq;
		response
	}

	pub fn persistence(error: PersistenceError) -> Self {
		Self::failed(error_status(error))
	}

	pub fn encode(&self) -> Option<Zeroizing<Vec<u8>>> {
		let data_len = u32::try_from(self.data.len()).ok()?;
		let state_len = u32::try_from(self.state.len()).ok()?;
		let len = 32usize
			.checked_add(self.data.len())?
			.checked_add(self.state.len())?;
		let mut bytes = Zeroizing::new(Vec::new());
		bytes.try_reserve_exact(len).ok()?;
		bytes.extend_from_slice(&self.status.to_le_bytes());
		bytes.extend_from_slice(&self.handle.to_le_bytes());
		bytes.extend_from_slice(&self.key_id.to_le_bytes());
		bytes.extend_from_slice(&self.seq.to_le_bytes());
		bytes.extend_from_slice(&data_len.to_le_bytes());
		bytes.extend_from_slice(&state_len.to_le_bytes());
		bytes.extend_from_slice(&self.data);
		bytes.extend_from_slice(&self.state);
		Some(bytes)
	}
}

impl Drop for Response {
	fn drop(&mut self) {
		self.data.zeroize();
		self.state.zeroize();
	}
}

thread_local! {
	pub(crate) static ALLOCATIONS: RefCell<BTreeMap<usize, Zeroizing<Box<[u8]>>>> = RefCell::new(BTreeMap::new());
}

fn allocate(mut bytes: Zeroizing<Vec<u8>>) -> Option<u32> {
	let bytes = Zeroizing::new(std::mem::take(&mut *bytes).into_boxed_slice());
	let ptr = bytes.as_ptr() as usize;
	let ptr32 = u32::try_from(ptr).ok()?;
	ALLOCATIONS.with_borrow_mut(|allocations| {
		allocations.insert(ptr, bytes);
	});
	Some(ptr32)
}

pub(crate) fn copy_input(ptr: u32, len: u32) -> Option<Zeroizing<Vec<u8>>> {
	if len == 0 {
		return (ptr == 0).then(|| Zeroizing::new(Vec::new()));
	}
	if ptr == 0 {
		return None;
	}
	ALLOCATIONS.with_borrow(|allocations| {
		let bytes = allocations.get(&(ptr as usize))?;
		(bytes.len() == len as usize).then(|| Zeroizing::new(bytes.to_vec()))
	})
}

/// Allocate one host-owned input buffer. Zero denotes invalid length or allocation failure.
#[unsafe(no_mangle)]
pub extern "C" fn bc_alloc(len: u32) -> u32 {
	// Rust wasm32 slices cannot exceed i32::MAX bytes. Keep that ABI boundary
	// even when this crate is compiled natively for descriptor tests.
	if len == 0 || len > i32::MAX as u32 {
		return 0;
	}
	let mut bytes = Zeroizing::new(Vec::new());
	if bytes.try_reserve_exact(len as usize).is_err() {
		return 0;
	}
	bytes.resize(len as usize, 0);
	allocate(bytes).unwrap_or(0)
}

/// Wipe and release exactly one registered buffer. Incorrect descriptors do not release memory.
#[unsafe(no_mangle)]
pub extern "C" fn bc_free(ptr: u32, len: u32) {
	ALLOCATIONS.with_borrow_mut(|allocations| {
		if allocations
			.get(&(ptr as usize))
			.is_some_and(|bytes| bytes.len() == len as usize)
		{
			allocations.remove(&(ptr as usize));
		}
	});
}

pub(crate) fn encode_result(response: Response) -> u64 {
	let Some(bytes) = response.encode() else {
		return 0;
	};
	let Ok(len) = u32::try_from(bytes.len()) else {
		return 0;
	};
	allocate(bytes).map_or(0, |ptr| (u64::from(ptr) << 32) | u64::from(len))
}
