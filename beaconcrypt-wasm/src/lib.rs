// SPDX-License-Identifier: 0BSD

//! WASI reactor for the Go bindings. Crypto, codecs and persistence execute in
//! the existing Rust adapter; this crate only owns the guest ABI and handles.
//!
//! `bc_call(op, handle, arg, input_ptr, input_len, extra_ptr, extra_len)` returns
//! `(ptr << 32) | len`. Reply bytes are little endian:
//! `[status:u32, handle:u32, key_id:u64, seq:u64, data_len:u32, state_len:u32]`,
//! followed by data and optional observational ratchet JSON. Status values
//! match the production PersistenceStatus enum (0..12). Failures carry no data.
//! Inputs must describe entire allocations returned by bc_alloc, or (0,0).
//! Hosts copy reply data before bc_free, which wipes the complete allocation.
//! A zero packed reply indicates allocation failure and invalidates the guest.
//!
//! Operations: 1 checkpoint server (arg=kid,input=seed concatenation,extra=presence flags), 2 beacon
//! (arg=server kid,input=Ed25519 public key || ML-DSA-65 public key), 3 identity, 4 registration bundle,
//! 5 register (input=bundle,extra=optional first plaintext), 6 finish registration,
//! 7 encrypt (arg=peer kid for server), 8 decrypt, 9 close, 10 export checkpoint,
//! 11 restore trusted checkpoint, 12 host-store server (extra=context u32 + seed flags),
//! 13 restore host store (arg=context), 14 owner head, 15 poisoned flag,
//! 16 validate snapshot successor (extra=optional 72-byte head), 17 ratchet status,
//! 18 host-store server with lineage (extra=context u32 + lineage[32] + seed flags),
//! 19 parse snapshot head, 20 encrypt and update, 21 decrypt and update,
//! 22 encrypt and update JSON, 23 decrypt and update JSON, 24 ML-DSA-65 public key. Seed flags select Ed25519
//! (bit0) and ML-DSA (bit1), whose supplied 32-byte seeds appear in that order. Operations 7,8 and
//! 20,21 return key_id/seq metadata; JSON operations return JSON in data only.
//! Store-backed constructors take ownership of a valid supplied host context.
//! All access to one instance must be serialized. Store callbacks must not
//! reenter the owning handle. Snapshot helpers can use a separate instance.

mod abi;
mod store;

use std::{cell::RefCell, collections::BTreeMap};

use abi::{INITIALIZATION, INVALID_ARGUMENT, REJECTED, Response};
use beaconcrypt::{
	Beacon, PersistenceError, PersistentServer, ProviderBeacon, ServerSnapshot, SnapshotLineage,
	SnapshotStore,
};
use store::{HostStore, MemoryStore, decode_head, encode_head};

type Server = PersistentServer<Box<dyn SnapshotStore>>;

enum Handle {
	Server(Box<Server>),
	Beacon(Box<Beacon>),
}

#[derive(Default)]
struct Registry {
	next: u32,
	handles: BTreeMap<u32, Handle>,
}

impl Registry {
	fn insert(&mut self, owner: Handle) -> Response {
		let Some(id) = self.next.checked_add(1) else {
			return Response::failed(INITIALIZATION);
		};
		self.next = id;
		self.handles.insert(id, owner);
		Response::success(id, 0, Vec::new())
	}

	fn server(&mut self, result: Result<Server, PersistenceError>) -> Response {
		match result {
			Ok(server) => self.insert(Handle::Server(Box::new(server))),
			Err(error) => Response::persistence(error),
		}
	}
}

thread_local! { static REGISTRY: RefCell<Registry> = RefCell::new(Registry::default()); }

#[unsafe(no_mangle)]
pub extern "C" fn bc_abi_version() -> u32 {
	2
}

#[unsafe(no_mangle)]
pub extern "C" fn bc_max_message_size() -> u32 {
	beaconcrypt::MAX_MESSAGE_SIZE as u32
}

fn optional(input: &[u8]) -> Option<&[u8]> {
	(!input.is_empty()).then_some(input)
}

type IdentitySeeds<'a> = (Option<&'a [u8]>, Option<&'a [u8]>);

fn seeds(input: &[u8], flags: u8) -> Option<IdentitySeeds<'_>> {
	let ed_len = usize::from(flags & 1 != 0) * 32;
	let ml_len = usize::from(flags & 2 != 0) * 32;
	if flags > 3 || input.len() != ed_len + ml_len {
		return None;
	}
	let (ed, ml) = input.split_at(ed_len);
	Some((optional(ed), optional(ml)))
}

fn protocol<T>(
	result: Result<Option<T>, PersistenceError>,
	success: impl FnOnce(T) -> Response,
) -> Response {
	match result {
		Ok(Some(value)) => success(value),
		Ok(None) => Response::failed(REJECTED),
		Err(error) => Response::persistence(error),
	}
}

fn dispatch(op: u32, handle: u32, arg: u64, input: &[u8], extra: &[u8]) -> Response {
	if matches!(op, 16 | 19) {
		if handle != 0 || input.is_empty() {
			return Response::failed(INVALID_ARGUMENT);
		}
		let snapshot = ServerSnapshot::from_bytes(input.to_vec());
		let result = if op == 19 {
			if !extra.is_empty() {
				return Response::failed(INVALID_ARGUMENT);
			}
			snapshot.head()
		} else {
			let expected = if extra.is_empty() {
				None
			} else {
				let Some(head) = decode_head(extra) else {
					return Response::failed(INVALID_ARGUMENT);
				};
				Some(head)
			};
			snapshot.validate_successor(expected.as_ref())
		};
		return match result {
			Ok(head) => Response::success(0, 0, encode_head(&head)),
			Err(error) => Response::persistence(error),
		};
	}
	REGISTRY.with(|cell| {
		let Ok(mut registry) = cell.try_borrow_mut() else {
			return Response::failed(INVALID_ARGUMENT);
		};
		match op {
			1 | 12 | 18 => {
				if handle != 0 {
					return Response::failed(INVALID_ARGUMENT);
				}
				let store: Box<dyn SnapshotStore> = if op == 1 {
					if extra.len() != 1 {
						return Response::failed(INVALID_ARGUMENT);
					}
					Box::<MemoryStore>::default()
				} else {
					let Some(context) = extra
						.get(..4)
						.and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
					else {
						return Response::failed(INVALID_ARGUMENT);
					};
					Box::new(HostStore(u32::from_le_bytes(context)))
				};
				let metadata_len = match op {
					1 => 1,
					12 => 5,
					_ => 37,
				};
				if extra.len() != metadata_len {
					return Response::failed(INVALID_ARGUMENT);
				}
				let Some((ed_seed, ml_seed)) = seeds(input, extra[metadata_len - 1]) else {
					return Response::failed(INITIALIZATION);
				};
				return if op == 18 {
					let Some(lineage) = extra
						.get(4..36)
						.and_then(|bytes| <[u8; 32]>::try_from(bytes).ok())
					else {
						return Response::failed(INVALID_ARGUMENT);
					};
					registry.server(PersistentServer::create_with_lineage(
						arg,
						ed_seed,
						ml_seed,
						store,
						SnapshotLineage::from_bytes(lineage),
					))
				} else {
					registry.server(PersistentServer::create(arg, ed_seed, ml_seed, store))
				};
			}
			2 => {
				if handle != 0 || !extra.is_empty() {
					return Response::failed(INVALID_ARGUMENT);
				}
				let Some((ed_public, ml_public)) = input.split_at_checked(32) else {
					return Response::failed(INITIALIZATION);
				};
				return match Beacon::try_new(arg, ed_public, ml_public) {
					Ok(beacon) => registry.insert(Handle::Beacon(Box::new(beacon))),
					Err(_) => Response::failed(INITIALIZATION),
				};
			}
			11 | 13 => {
				if handle != 0 || !extra.is_empty() {
					return Response::failed(INVALID_ARGUMENT);
				}
				let store: Box<dyn SnapshotStore> = if op == 13 {
					let Ok(context) = u32::try_from(arg) else {
						return Response::failed(INVALID_ARGUMENT);
					};
					if !input.is_empty() {
						return Response::failed(INVALID_ARGUMENT);
					}
					Box::new(HostStore(context))
				} else {
					if input.is_empty() {
						return Response::failed(INVALID_ARGUMENT);
					}
					match MemoryStore::from_bytes(input.to_vec()) {
						Ok(store) => Box::new(store),
						Err(error) => return Response::persistence(error),
					}
				};
				return registry.server(PersistentServer::restore(store));
			}
			_ => {}
		}
		if !extra.is_empty() && op != 5 {
			return Response::failed(INVALID_ARGUMENT);
		}
		if matches!(op, 3 | 4 | 9 | 10 | 14 | 15 | 17 | 24) && !input.is_empty() {
			return Response::failed(INVALID_ARGUMENT);
		}
		if matches!(op, 5..=8 | 20..=23) && input.is_empty() {
			return Response::failed(INVALID_ARGUMENT);
		}
		if op == 9 {
			return if registry.handles.remove(&handle).is_some() {
				Response::success(handle, 0, Vec::new())
			} else {
				Response::failed(INVALID_ARGUMENT)
			};
		}
		let Some(owner) = registry.handles.get_mut(&handle) else {
			return Response::failed(INVALID_ARGUMENT);
		};
		match (op, owner) {
			(3, Handle::Server(server)) => Response::success(
				handle,
				server.identity_key_kid(),
				server.identity_pk().as_bytes().to_vec(),
			),
			(3, Handle::Beacon(beacon)) => Response::success(
				handle,
				beacon.identity_key_kid(),
				beacon.identity_pk().as_bytes().to_vec(),
			),
			(24, Handle::Server(server)) => Response::success(
				handle,
				server.identity_key_kid(),
				server.mldsa_public_key().to_vec(),
			),
			(24, Handle::Beacon(beacon)) => Response::success(
				handle,
				beacon.identity_key_kid(),
				beacon.mldsa_public_key().to_vec(),
			),
			(4, Handle::Beacon(beacon)) => match beacon.get_registration_bundle() {
				Some(data) => Response::success(handle, 0, data),
				None => Response::failed(REJECTED),
			},
			(5, Handle::Server(server)) => {
				let pending = match server.get_shared_secret(input) {
					Ok(Some(pending)) => pending,
					Ok(None) => return Response::failed(REJECTED),
					Err(error) => return Response::persistence(error),
				};
				protocol(
					server.build_registration_response(pending, optional(extra)),
					|registration| {
						Response::success(handle, registration.kid, registration.serialized)
					},
				)
			}
			(6, Handle::Beacon(beacon)) => match beacon.finish_registration(input) {
				Some(data) => Response::success(handle, 0, data),
				None => Response::failed(REJECTED),
			},
			(7, Handle::Server(server)) => {
				protocol(server.encrypt_message(input, arg), |message| {
					Response::message(handle, message.key_id, message.seq, message.ciphertext)
				})
			}
			(7, Handle::Beacon(beacon)) => match beacon.encrypt_message(input) {
				Some(message) => {
					Response::message(handle, message.key_id, message.seq, message.ciphertext)
				}
				None => Response::failed(REJECTED),
			},
			(8, Handle::Server(server)) => protocol(server.decrypt_message(input), |message| {
				Response::message(handle, message.key_id, message.seq, message.plaintext)
			}),
			(8, Handle::Beacon(beacon)) => match beacon.decrypt_message(input) {
				Some(message) => {
					Response::message(handle, message.key_id, message.seq, message.plaintext)
				}
				None => Response::failed(REJECTED),
			},
			(10, Handle::Server(server)) => match server.snapshot() {
				Ok(snapshot) => Response::success(handle, 0, snapshot.as_bytes().to_vec()),
				Err(error) => Response::persistence(error),
			},
			(14, Handle::Server(server)) => {
				Response::success(handle, 0, encode_head(&server.head()))
			}
			(15, Handle::Server(server)) => {
				Response::success(handle, 0, vec![u8::from(server.is_poisoned())])
			}
			(17, owner) => {
				let status = match owner {
					Handle::Server(server) => server.ratchet_status(arg),
					Handle::Beacon(beacon) => beacon.ratchet_status(),
				};
				match status {
					Some(status) => {
						let mut data = Vec::with_capacity(17);
						data.extend_from_slice(&status.send_sequence().to_le_bytes());
						data.extend_from_slice(&status.receive_sequence().to_le_bytes());
						data.push(status.receive_cache_len());
						Response::success(handle, arg, data)
					}
					None => Response::failed(REJECTED),
				}
			}
			(20, Handle::Server(server)) => {
				protocol(server.encrypt_and_update(input, arg), |update| {
					let mut result = Response::success(handle, update.kid, update.data);
					result.seq = update.seq;
					result.state = update.state.as_str().as_bytes().to_vec();
					result
				})
			}
			(21, Handle::Server(server)) => protocol(server.decrypt_and_update(input), |update| {
				let mut result = Response::success(handle, update.kid, update.data);
				result.seq = update.seq;
				result.state = update.state.as_str().as_bytes().to_vec();
				result
			}),
			(22, Handle::Server(server)) => {
				protocol(server.encrypt_and_update_json(input, arg), |json| {
					Response::success(handle, 0, json.into_bytes())
				})
			}
			(23, Handle::Server(server)) => {
				protocol(server.decrypt_and_update_json(input), |json| {
					Response::success(handle, 0, json.into_bytes())
				})
			}
			_ => Response::failed(INVALID_ARGUMENT),
		}
	})
}

fn call(
	op: u32,
	handle: u32,
	arg: u64,
	input_ptr: u32,
	input_len: u32,
	extra_ptr: u32,
	extra_len: u32,
) -> Response {
	match (
		abi::copy_input(input_ptr, input_len),
		abi::copy_input(extra_ptr, extra_len),
	) {
		(Some(input), Some(extra)) => dispatch(op, handle, arg, &input, &extra),
		_ => Response::failed(INVALID_ARGUMENT),
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn bc_call(
	op: u32,
	handle: u32,
	arg: u64,
	input_ptr: u32,
	input_len: u32,
	extra_ptr: u32,
	extra_len: u32,
) -> u64 {
	abi::encode_result(call(
		op, handle, arg, input_ptr, input_len, extra_ptr, extra_len,
	))
}

#[cfg(test)]
mod tests;
