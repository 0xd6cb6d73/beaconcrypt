// SPDX-License-Identifier: 0BSD

use beaconcrypt::{PersistenceError, ServerSnapshot, SnapshotHead, SnapshotLineage, SnapshotStore};
use zeroize::Zeroizing;

/// Checkpoint semantics match the native binding's BindingSnapshotStore.
/// These snapshots require trusted manual saving; this is not durable storage.
#[derive(Default)]
pub(crate) struct MemoryStore {
	snapshot: Option<Zeroizing<Vec<u8>>>,
	head: Option<SnapshotHead>,
}

impl MemoryStore {
	pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, PersistenceError> {
		let snapshot = ServerSnapshot::from_bytes(bytes);
		let head = snapshot.head()?;
		Ok(Self {
			snapshot: Some(Zeroizing::new(snapshot.as_bytes().to_vec())),
			head: Some(head),
		})
	}
}

impl SnapshotStore for MemoryStore {
	fn load(&self) -> Result<Option<ServerSnapshot>, PersistenceError> {
		Ok(self
			.snapshot
			.as_ref()
			.map(|bytes| ServerSnapshot::from_bytes(bytes.to_vec())))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, PersistenceError> {
		if self.head.as_ref() != expected {
			return Ok(false);
		}
		let Ok(head) = replacement.validate_successor(expected) else {
			return Ok(false);
		};
		self.snapshot = Some(Zeroizing::new(replacement.as_bytes().to_vec()));
		self.head = Some(head);
		Ok(true)
	}
}

pub(crate) struct HostStore(pub u32);

// Load's first call captures one owned host read and returns its size (-1 absent,
// -2 error). The second copies that exact cached read and clears it. CAS compares
// the complete expected head (72 bytes; empty means no head), validates the
// successor and durably publishes before returning 1; 0 means a conflict,
// 2 a known storage failure, and 3 an uncertain commit. Destroy releases the
// context once, including constructor failure. Host code must copy borrowed
// arguments synchronously and may not reenter the owning handle.
#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "beaconcrypt_host")]
unsafe extern "C" {
	fn snapshot_load(context: u32, output: u32, capacity: u32) -> i64;
	fn snapshot_cas(
		context: u32,
		expected: u32,
		expected_len: u32,
		replacement: u32,
		replacement_len: u32,
	) -> u32;
	fn snapshot_destroy(context: u32);
}

#[cfg(any(target_arch = "wasm32", test))]
pub(crate) fn load_snapshot(
	mut load: impl FnMut(u32, u32) -> i64,
) -> Result<Option<ServerSnapshot>, PersistenceError> {
	let len = load(0, 0);
	if len == -1 {
		return Ok(None);
	}
	if len == -2 {
		return Err(PersistenceError::Storage);
	}
	let len = u32::try_from(len).map_err(|_| PersistenceError::InvalidSnapshot)?;
	if len == 0 || len > i32::MAX as u32 {
		return Err(PersistenceError::InvalidSnapshot);
	}
	let mut bytes = Zeroizing::new(vec![0; len as usize]);
	let copied = load(bytes.as_mut_ptr() as u32, len);
	if copied == -2 {
		return Err(PersistenceError::Storage);
	}
	if copied != i64::from(len) {
		return Err(PersistenceError::InvalidSnapshot);
	}
	Ok(Some(ServerSnapshot::from_bytes(std::mem::take(
		&mut *bytes,
	))))
}

#[cfg(any(target_arch = "wasm32", test))]
pub(crate) fn cas_result(status: u32) -> Result<bool, PersistenceError> {
	match status {
		0 => Ok(false),
		1 => Ok(true),
		2 => Err(PersistenceError::Storage),
		_ => Err(PersistenceError::CommitUnknown),
	}
}

impl SnapshotStore for HostStore {
	fn load(&self) -> Result<Option<ServerSnapshot>, PersistenceError> {
		#[cfg(target_arch = "wasm32")]
		{
			load_snapshot(|ptr, len| unsafe { snapshot_load(self.0, ptr, len) })
		}
		#[cfg(not(target_arch = "wasm32"))]
		Err(PersistenceError::Storage)
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, PersistenceError> {
		#[cfg(target_arch = "wasm32")]
		{
			let head = expected.map(encode_head);
			let (ptr, len) = head
				.as_ref()
				.map_or((0, 0), |bytes| (bytes.as_ptr() as u32, bytes.len() as u32));
			cas_result(unsafe {
				snapshot_cas(
					self.0,
					ptr,
					len,
					replacement.as_bytes().as_ptr() as u32,
					replacement.as_bytes().len() as u32,
				)
			})
		}
		#[cfg(not(target_arch = "wasm32"))]
		{
			let _ = (expected, replacement);
			Err(PersistenceError::Storage)
		}
	}
}

impl Drop for HostStore {
	fn drop(&mut self) {
		#[cfg(target_arch = "wasm32")]
		unsafe {
			snapshot_destroy(self.0)
		};
		#[cfg(not(target_arch = "wasm32"))]
		let _ = self.0;
	}
}

pub(crate) fn encode_head(head: &SnapshotHead) -> Vec<u8> {
	let mut bytes = Vec::with_capacity(72);
	bytes.extend_from_slice(head.lineage().as_bytes());
	bytes.extend_from_slice(&head.generation().to_le_bytes());
	bytes.extend_from_slice(&head.digest());
	bytes
}

pub(crate) fn decode_head(bytes: &[u8]) -> Option<SnapshotHead> {
	if bytes.len() != 72 {
		return None;
	}
	Some(SnapshotHead::from_parts(
		SnapshotLineage::from_bytes(bytes[..32].try_into().ok()?),
		u64::from_le_bytes(bytes[32..40].try_into().ok()?),
		bytes[40..].try_into().ok()?,
	))
}
