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
	fn load(&self) -> Option<ServerSnapshot> {
		self.snapshot
			.as_ref()
			.map(|bytes| ServerSnapshot::from_bytes(bytes.to_vec()))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		if self.head.as_ref() != expected {
			return false;
		}
		let Ok(head) = replacement.validate_successor(expected) else {
			return false;
		};
		self.snapshot = Some(Zeroizing::new(replacement.as_bytes().to_vec()));
		self.head = Some(head);
		true
	}
}

pub(crate) struct HostStore(pub u32);

// Load's first call captures one owned host read and returns its size (-1 absent,
// -2 error). The second copies that exact cached read and clears it. CAS compares
// the complete expected head (72 bytes; empty means no head), validates the
// successor and durably publishes before returning 1. Destroy releases the
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
pub(crate) fn load_snapshot(mut load: impl FnMut(u32, u32) -> i64) -> Option<ServerSnapshot> {
	let len = load(0, 0);
	// Native callback failure returns false without delivering snapshot bytes.
	// The Go host retains its error/panic as the resulting error's cause.
	if matches!(len, -1 | -2) {
		return None;
	}
	let Ok(len) = u32::try_from(len) else {
		return Some(ServerSnapshot::from_bytes(Vec::new()));
	};
	if len == 0 || len > i32::MAX as u32 {
		return Some(ServerSnapshot::from_bytes(Vec::new()));
	}
	let mut bytes = Zeroizing::new(vec![0; len as usize]);
	if load(bytes.as_mut_ptr() as u32, len) != i64::from(len) {
		return Some(ServerSnapshot::from_bytes(Vec::new()));
	}
	Some(ServerSnapshot::from_bytes(std::mem::take(&mut *bytes)))
}

impl SnapshotStore for HostStore {
	fn load(&self) -> Option<ServerSnapshot> {
		#[cfg(target_arch = "wasm32")]
		{
			load_snapshot(|ptr, len| unsafe { snapshot_load(self.0, ptr, len) })
		}
		#[cfg(not(target_arch = "wasm32"))]
		None
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		#[cfg(target_arch = "wasm32")]
		{
			let head = expected.map(encode_head);
			let (ptr, len) = head
				.as_ref()
				.map_or((0, 0), |bytes| (bytes.as_ptr() as u32, bytes.len() as u32));
			unsafe {
				snapshot_cas(
					self.0,
					ptr,
					len,
					replacement.as_bytes().as_ptr() as u32,
					replacement.as_bytes().len() as u32,
				) == 1
			}
		}
		#[cfg(not(target_arch = "wasm32"))]
		{
			let _ = (expected, replacement);
			false
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
