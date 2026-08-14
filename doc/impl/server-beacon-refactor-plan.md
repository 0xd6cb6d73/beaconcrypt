# Refactor specification: split `BeaconCryptPqxdh` into `Server` and `Beacon`

## Status and baseline

This document is an implementation specification for the `proof` branch of `0xd6cb6d73/beaconcrypt`. It is written against commit `e3d3ec0d749dbcf8072b75bf0e1924fcb979d65b` on the `proof` branch.

The implementation MUST encode the server/beacon role distinction in Rust types instead of in a runtime enum. The patch MUST remain a storage/API refactor: it MUST NOT change the verified protocol state machine, cryptographic transcript, wire format, ratchet algorithm, server-state persistence format, or the public Python and Go APIs. The C API is intentionally breaking: it MUST expose distinct opaque server and beacon handle types instead of the current role-erased `beaconcrypt_BeaconCryptPqxdh` handle.

## Objective

Replace the public Rust type `BeaconCryptPqxdh`, which currently contains `ProviderRole::{Beacon, Server}`, with two public Rust types named `Server` and `Beacon`.

The resulting types MUST satisfy these invariants:

- A `Server` stores only server-owned state. It MUST NOT contain `BeaconState`, an X25519 prekey, an X25519 one-time key, an ML-KEM keypair, beacon associated data, or any field whose only purpose is supporting beacon registration.
- A `Beacon` is configured for exactly one server. It MUST NOT contain a map of remotes and MUST NOT expose APIs for adding, deleting, resetting, allocating, or selecting arbitrary remote identities.
- Only `Server` owns the `HashMap<u64, RemotePrincipal<_>>` and remote-KID-selection APIs.
- Registration key material remains in `BeaconState` and disappears according to the existing state transitions.
- Server-side ML-KEM encapsulation continues to use the beacon public key from the registration message as temporary input; a `Server` owns no persistent ML-KEM key.
- The role-specific `ProviderBeacon` and `ProviderServer` traits remain, while the generic `CryptoProvider` trait is removed.
- The C boundary exposes incompatible `beaconcrypt_Server *` and `beaconcrypt_Beacon *` handles with no common provider handle.

## Non-goals

- Do not modify `crates/protocol-core`, proof artifacts, Cap'n Proto schemas, or generated message layouts.
- Do not alter transcript construction, signatures, KDF inputs, associated data, commitments, ratchet behavior, or persistence format.
- Do not redesign `RemotePrincipal`, `RatchetManager`, `BeaconState`, `ProviderBeacon`, or `ProviderServer` beyond mechanical changes required by the split.
- Keep both concrete implementations in `src/pqxdh.rs`; do not introduce a shared `Identity` struct.
- Preserve the serialized `server_kid` field and serialized struct name.
- Preserve Python-visible and Go-visible APIs.
- Intentionally remove the role-erased C handle; do not add compatibility aliases, tagged unions, `void *` wrappers, or runtime role discriminators.
- Preserve the names of already role-specific C functions. Only `beaconcrypt_free` and `beaconcrypt_identity_pk` are replaced with role-specific variants.
- Do not retain a production abstraction solely so tests can treat both roles as interchangeable.

## Required Rust data model

Under `feature = "beacon"`, define:

```rust
pub struct Beacon {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	state: BeaconState,
	server: RemotePrincipal<crypto_sign::PublicKey>,
}
```

The configured `server` owns the public identity key and the sole `RatchetManager`. A valid `Beacon` always has this server. `BeaconState` retains the verified control state and registration-only key material; remove its obsolete dead-code workaround.

Under `feature = "server"`, define:

```rust
pub struct Server {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	control: verified_pqxdh::ServerState,
	known_ids: HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
	consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>,
}
```

`Server` has no `BeaconState` and no separately stored `server_kid`. `control.last_key_id()` is the only in-memory source of truth, while `server_kid()` remains a compatibility accessor returning that value.

Delete `ProviderRole`, its large-enum annotation and comment, `BeaconCryptPqxdh`, and every `is_beacon()` runtime discriminator. Beacon matches operate directly on `self.state`; server code accesses `self.control` directly.

## Constructors and identity access

Add `Server::new(server_kid: u64, id_seed: Option<&[u8]>)`. It initializes libsodium, restores or generates the Ed25519 identity as today, sets `identity_key_kid`, creates `ServerState::new(server_kid)`, and starts with empty remote and replay sets. It MUST NOT create ML-KEM state.

Add `Beacon::new(server_kid: u64, server_id_pk: &[u8])`. It initializes libsodium, always generates a fresh Ed25519 identity, parses the mandatory server public key with the existing panic behavior, creates the single `RemotePrincipal`, and creates `BeaconState::Fresh` with the existing binding, X25519 prekey, and ML-KEM-768 keypair. Its pre-registration `identity_key_kid` remains `server_kid`.

Remove the generic constructor and `Default`. Do not add `Default` to either concrete type.

Both types expose inherent `identity_key_kid`, `identity_pk`, and `identity_sk` getters. Only `Server` retains `set_identity_kid`; beacon identity assignment remains controlled by registration transitions.

## Beacon registration and key material

Implement `ProviderBeacon` for `Beacon`. Preserve control calls, generation, serialization, signatures, and transitions while replacing role matches with direct `BeaconState` matches.

Move `abort_registration` to `Beacon`. It restores the identity KID from the control state, resets the sole server ratchet directly, and installs the verified aborted state.

Keep the existing response decoding, authentication, candidate-ratchet construction, initial-message decryption, and verified transitions in `finish_registration`. Validate the authenticated binding directly against `self.server_kid()` and `self.server.pk()`. On mismatch, abort and return `None`; on success, install the candidate ratchet in `self.server`, set the assigned beacon identity KID, and commit the established state and associated data. No remote-map lookup is permitted.

Move the existing prekey, one-time-key, and PQ-key getters and transition helpers to `Beacon`, preserving their semantics. `pq_pk()` and `pq_sk()` remain optional because protocol phases discard PQ material. Temporary replacement states use `self.server_kid()`. None of these methods exist on `Server`.

## Role-specific messaging

Keep the common helper bodies in `src/shared.rs` and call them with explicit ratchets and associated data.

`Beacon::encrypt_message(&mut self, bytes: &[u8])` obtains the configured server KID, beacon sender KID, established associated data, and sole server ratchet. `Beacon::decrypt_message(&mut self, data: &[u8])` passes the configured server KID as the expected sender to `decrypt_message_with_ratchet`. Neither API accepts an arbitrary remote KID.

`Server::encrypt_message(&mut self, bytes: &[u8], kid: u64)` selects a registered beacon, builds associated data from the server and remote identities, and calls the existing encryption helper. `Server::decrypt_message(&mut self, data: &[u8])` parses the frame sender KID, selects that registered beacon, builds associated data, and passes the same KID as the expected sender. Clone the server public identity before the mutable map borrow if required.

## Role-specific remote and ratchet APIs

`Beacon` exposes non-optional `server_id`, state-derived `server_kid`, and singular `ratchet_manager` and `ratchet_manager_mut` accessors. Its `associated_data` and `set_associated_data` methods are singular and operate only on established state.

`Beacon` MUST NOT expose multi-remote operations such as `add_known_kid`, `delete_known_kid`, `reset_known_kid`, `new_remote_kid`, `pk_by_kid`, KID-taking ratchet access, `add_server_pk`, KID-taking associated-data access, or KID-taking encryption.

`Server` retains the existing remote-management methods: `add_known_kid`, `delete_known_kid`, `reset_known_kid`, `new_remote_kid`, `pk_by_kid`, `ratchet_manager(kid)`, and `ratchet_manager_mut(kid)`. `new_remote_kid` advances only `self.control`, rejects collisions, and never updates duplicate counter storage.

Move the test-exercised low-level ratchet delegation methods to inherent `Server` methods with their existing KID-based signatures: `ratchet_recv_until`, `ratchet_send`, `send_key`, `recv_key`, `delete_send_key`, `consume_send_key`, `delete_recv_key`, and `complete_recv_key`. Do not add these KID-taking methods to `Beacon`.

## Traits, exports, and feature gates

Implement `ProviderServer` for `Server` with no runtime role guards. Preserve registration verification, collision checks, replay prevention, response generation, witness verification, and state updates. On success, update only `self.control` and `known_ids`; ML-KEM encapsulation remains local to registration.

Delete `CryptoProvider` from `src/shared.rs` and its `src/lib.rs` export without replacing it. Retain `RemotePrincipal`, `RatchetManager`, `KeyMaterial`, message helpers, frame parsing, constants, and public result types.

Export `Beacon` under `feature = "beacon"` and `Server` under `feature = "server"`. Gate role-specific imports, fields, implementations, collections, and serialization dependencies so both supported single-role builds compile without dead state from the other role.

## Persistence compatibility

Do not change `SerializableServerState`, `ServerStateData`, serde names, or fields. Export using `self.control.last_key_id()` as the value of the existing `server_kid` JSON field. Restore a concrete `Server` with `control: ServerState::new(server_kid)`. Existing snapshots and assertions must pass without migration.

## Python bindings

Alias imported Rust types as `PqxdhServer` and `PqxdhBeacon` to avoid wrapper name collisions. Store them in the existing Python classes `BeaconCryptServer` and `BeaconCryptBeacon`, use their role-specific constructors, restore `PqxdhServer` through `ProviderServer`, and call beacon encryption without a remote KID. Preserve every Python-visible class name, constructor, method, argument, return type, and stub signature.

## C API

Use concrete Rust `Server` and `Beacon` pointers as opaque handles without `repr(C)`. Generated declarations must contain incomplete `beaconcrypt_Server` and `beaconcrypt_Beacon` types and no `beaconcrypt_BeaconCryptPqxdh`.

Keep constructor names but return typed pointers. `beaconcrypt_beacon_new` requires non-null, non-empty server-key input, returns null when input extraction fails, and otherwise preserves malformed-key panic behavior.

Replace `beaconcrypt_free` with null-safe `beaconcrypt_server_free` and `beaconcrypt_beacon_free`. Replace `beaconcrypt_identity_pk` with `beaconcrypt_server_identity_pk` and `beaconcrypt_beacon_identity_pk`, preserving empty-buffer behavior for null handles. Do not expose a generic destructor or identity accessor.

Keep already role-specific names while changing handle parameters to their concrete types. Registration generation and completion and server messaging use `Beacon *`; registration acceptance, beacon messaging, state updates, and export use `Server *`. Specifically, server-to-beacon encryption calls `Server::encrypt_message(data, key_id)`, beacon-to-server encryption calls `Beacon::encrypt_message(data)`, and each decryption function calls the matching concrete method.

Every C function checks null and invalid byte input as today and dereferences only its concrete role. Remove generic private encrypt/decrypt helpers if they require role erasure; duplication is limited to small FFI plumbing.

Regenerate `bindings.h`. The typed handles, typed constructors and methods, split destructors, and split identity functions are an intentional C source and ABI break. Buffer structures, registration and update structures, constants, byte ownership, and non-handle layouts remain unchanged.

## Go bindings

Keep the public Go API unchanged. In the cgo preamble, declare incomplete `beaconcrypt_Server` and `beaconcrypt_Beacon` types and use typed pointers for every handle parameter and return value; no provider handle remains `void *`.

Replace the shared native holder with private `serverNativeHandle` and `beaconNativeHandle` types containing typed C pointers. Add role-specific constructors and `withServerHandle`/`withBeaconHandle` helpers. Preserve mutexes, finalizers, `runtime.KeepAlive`, nil and closed checks, concurrency semantics, and unrelated buffer-copy `unsafe` usage. Each holder calls its typed C destructor.

All `Server` methods use the server helper and all `Beacon` methods use the beacon helper. `Server.IdentityPK` calls the server-specific C function. Do not add a public Go `Beacon.IdentityPK` method.

## Examples and documentation

Update `examples/rust/main.rs` to construct `Server::new(SERVER_KID, Some(&server_seed))` and `Beacon::new(SERVER_KID, server.identity_pk().as_bytes())`. Server-to-beacon encryption retains the beacon KID; beacon-to-server encryption drops the remote-KID argument. Update only the README Rust usage that refers to `CryptoProvider` or the old type.

## Test migration

Migrate Rust tests to concrete `Server` and `Beacon` constructors and role-specific messaging, associated-data, and ratchet APIs. Keep remote-map tests server-only. Preserve registration, authentication-failure, replay, malformed-input, state-rollback, persistence, and key-lifecycle coverage.

In `tests/protocol.rs`, keep direction-generic helpers through a test-only `TestEndpoint` trait exposing `encrypt_for_test`, `decrypt_for_test`, `receive_state_for_test`, and `has_recv_key_for_test`. The `Server` adapter forwards its remote KID; the `Beacon` adapter asserts that the supplied test KID equals `server_kid()` and then uses singular production APIs. Do not export this adapter or add a production equivalent.

Delete the test that mutates the beacon peer map, since that state is no longer representable. Retain wrong-server authentication coverage and assert in a normal registration test that `Beacon::server_id()` equals the constructor-provided identity before and after registration.

Update `src/pqxdh.rs` unit tests to cover fresh beacon registration material, fresh server identity and counter state, server-only mutators, beacon key-material transitions, singular associated-data replacement, and equivalent singular/per-KID ratchet advancement. Do not add compile-fail infrastructure solely to prove absent server methods.

## Implementation order

1. Introduce the concrete structs, constructors, identity accessors, and role-specific state accessors in `src/pqxdh.rs`.
2. Move `ProviderBeacon` to `Beacon` and replace role matches with direct state access.
3. Move `ProviderServer` to `Server`, use direct control access, and export `control.last_key_id()`.
4. Add concrete messaging methods using the shared helpers.
5. Migrate Rust tests and the Rust example.
6. Migrate Python bindings.
7. Migrate the C API to typed opaque pointers and regenerate `bindings.h`.
8. Migrate Go cgo declarations and native holders while preserving its public API.
9. Remove `CryptoProvider`, `ProviderRole`, and `BeaconCryptPqxdh` after all callers migrate.
10. Update crate exports and README text.
11. Run formatting, linting, feature checks, and all Rust, Go, and Python tests.

## Required validation

Run:

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo check --no-default-features --features pqxdh,beacon --lib
cargo check --no-default-features --features pqxdh,server --lib
cargo build --release --features gobinds
go test -race ./...
uv run maturin develop --uv
uv run pytest tests
```

Proof verification is not required because this refactor must not touch protocol-core. If protocol-core changes become necessary, stop and treat that work as a scope expansion requiring the repository proof process.

After generating bindings, verify:

```sh
grep -q 'typedef struct beaconcrypt_Server beaconcrypt_Server;' bindings.h
grep -q 'typedef struct beaconcrypt_Beacon beaconcrypt_Beacon;' bindings.h
! grep -q 'beaconcrypt_BeaconCryptPqxdh' bindings.h
! grep -q 'beaconcrypt_free(' bindings.h
! grep -q 'beaconcrypt_identity_pk(' bindings.h
grep -q 'beaconcrypt_server_free' bindings.h
grep -q 'beaconcrypt_beacon_free' bindings.h
grep -q 'beaconcrypt_server_identity_pk' bindings.h
grep -q 'beaconcrypt_beacon_identity_pk' bindings.h
```

Inspect every exported prototype to ensure provider parameters are never `void *`, server operations never accept beacon handles, and beacon operations never accept server handles.

## Completion criteria

- `Server` owns only its Ed25519 identity, verified server control/counter, registered beacon map, and consumed-registration set.
- `Beacon` owns its Ed25519 identity, `BeaconState`, and exactly one server `RemotePrincipal`.
- No server duplicate counter or beacon remote map exists.
- Beacon messaging is singular; server messaging remains KID-addressed.
- Registration behavior and key-material lifetimes are unchanged.
- Existing server JSON restores and exports with the unchanged `server_kid` field.
- Python and Go public APIs are unchanged.
- C exposes only the two incompatible opaque handles and typed operations.
- Both single-role Rust feature builds compile.
- No protocol-core or proof artifact changes are present.

## Review guidance

Review ownership and impossible states first. The declarations should visibly encode a server identity, verified server control and last allocated remote ID, a beacon map, and replay history in `Server`; and a beacon identity, phase-specific `BeaconState`, and exactly one configured server ratchet in `Beacon`. Boxing the old role enum, retaining a role-erased public API, or adding compatibility peer-selection APIs does not satisfy this specification.
