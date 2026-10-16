# Overview

This document describes the way beaconcrypt exposes state persistence to the server. This breaks forward secrecy, but is required to be useful in a server context. Additionally, the [threat model](threat_model.md) specifies that we already assume that server compromise is game over.

Snapshots contain the server identity seed and all ratchet state in plaintext. They are not encrypted or authenticated by beaconcrypt, so applications must treat them as secret data and obtain integrity, provenance, and rollback protection from the server's trusted storage.

# Usage

Rust, C, Go, and Python can all use an application-supplied snapshot store. Its load operation returns only the trusted current snapshot, or no snapshot when the store is empty. Its compare-and-swap operation atomically compares the complete expected head and durably stores the replacement before reporting success. An absent expected head means that creation must fail if the store is already occupied. The store must provide integrity, provenance, rollback resistance, durability, and coordination between concurrent owners; snapshot parsing and successor validation do not supply these properties.

Python storage objects implement `load() -> bytes | None` and `compare_and_swap(expected: SnapshotHead | None, replacement: bytes) -> bool`:

```python
from beaconcrypt import BeaconCryptServer

# store implements the trusted storage contract described above.
server = BeaconCryptServer.create_with_store(server_kid, seed, store)
response = server.register_beacon(registration, initial_message)
# The store has committed the registration before response is returned.

del server
server = BeaconCryptServer.restore(store)
# Restoration commits its activation generation before returning.
```

Go provides `SnapshotStore`, `NewServerWithStore`, `NewServerWithStoreAndLineage`, and `RestoreServer`. Go store methods return errors as well as their load or CAS result. Python's optional `lineage` argument and Go's lineage constructor correspond to Rust's `create_with_lineage`; applications must provision each lineage to exactly one authoritative store head.

C provides `beaconcrypt_server_create_with_store`, `beaconcrypt_server_create_with_store_and_lineage`, and `beaconcrypt_server_restore_with_store`. A `beaconcrypt_SnapshotStoreCallbacks` value carries an application context, load and compare-and-swap callbacks, and an optional destructor. The constructor consumes this context immediately: a supplied destructor runs exactly once when the server is freed or construction fails. Without a destructor, the application must keep the context alive for the server's complete lifetime.

The C load callback synchronously calls its supplied sink exactly once with a nonempty snapshot and returns `true`, or omits the sink and returns `false` for an empty store. The sink copies the bytes during that call. The load callback must not retain the sink or its context. The CAS callback receives a borrowed expected head, or a null pointer for initial creation, and borrowed replacement bytes; it must copy bytes it retains and complete its durable transaction before returning `true`. Callback arguments are valid only for the duration of the callback. Callbacks must not unwind through the C ABI or reenter their owning server. Calls on one C handle, including status inspection and destruction, must be serialized by the application. A store shared by several owners must independently synchronize its transactions.

All bindings expose the owner's current snapshot head and poisoned state. Python provides `snapshot_head` and `validate_snapshot_successor`, Go provides `ParseSnapshotHead` and `ValidateSnapshotSuccessor`, and C provides `beaconcrypt_snapshot_head` and `beaconcrypt_snapshot_validate_successor`. These helpers use the same native Rust implementation, so applications can compare lineage, generation, and complete-snapshot digest without implementing the envelope codec themselves. Successor validation belongs inside the same transaction that compares the authoritative head and saves the replacement. Exporting a snapshot remains a trusted read and does not replace that transaction; an owner whose stored head has changed receives a stale-generation error.

Persistence failures are distinct from ordinary protocol rejection. C server operations retain a `STATUS_*` code readable through `beaconcrypt_server_last_status`; durable constructors return their status through an output pointer. Head and snapshot-validation helpers return their status directly. Status inspection does not clear the operation status. Go exposes typed persistence errors and Python raises `PersistenceError` with a native error code; callback errors are retained as error context. A false or failed CAS suppresses the operation's output and poisons the local owner. Restore from the trusted current store before using it again. `OutputEncoding` is different: an accepted receive has already committed and consumed its key, but projecting the returned update failed; that owner remains usable. A normal rejected receive returns `None` in Python, an empty result with `STATUS_REJECTED` in C, and nil output with `ErrCrypto` in Go; it does not call CAS and leaves the owner's snapshot and generation unchanged. Invalid arguments are separate: for example, empty Go input returns `ErrEmptyData`, and absent C input reports `STATUS_INVALID_ARGUMENT`.

The following checkpoint-only APIs remain available for single-owner compatibility. They use an in-memory store and require the application to save exported state itself:

```python
state = server.export_state()
with open("server-state.bin", "wb") as state_file:
    state_file.write(state)

del server
with open("server-state.bin", "rb") as state_file:
    server = BeaconCryptServer.from_state(state_file.read())

# Restoration advances the snapshot generation, so save the activated state.
with open("server-state.bin", "wb") as state_file:
    state_file.write(server.export_state())
```

Go uses `Server.ExportState` and `NewServerFromState`. C uses `beaconcrypt_server_export_state` and `beaconcrypt_server_new_from_state`. Complete runnable save-and-restore examples are available for [Python](../examples/python/main.py), [Go](../examples/go/main.go), and [C](../examples/c/main.c).

The exported value is a binary version-2 snapshot envelope, not a bare JSON document. It contains a format identifier, a lineage identifier, a monotonic generation, the previous snapshot's digest, a payload length, and the canonical JSON server-state payload. The digest identifies exact snapshot bytes and links generations; because it is unkeyed, it does not authenticate snapshots obtained outside trusted storage.

Store implementations can call `replacement.validate_successor(expected)` to validate the envelope, exact next generation, same lineage and complete parent digest before accepting a replacement. The in-memory binding store uses this check. It must run in the same transaction as comparison with the authoritative current head; it supplies neither payload authentication nor external freshness, durability or linearizability. The application must separately provide storage integrity, freshness, durability, and linearizability; buffer wiping does not protect copies retained by the application or storage system.

The decoded JSON payload has the following shape:

```json
{
    "identity_key": [1,14,[65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65]],
    "identity_key_kid": 0,
    "server_kid": 2,
    "known_ids": {
      "1": {
        "pk": [1,179,176,97,56,138,132,165,3,79,7,190,144,179,105,2,187,3,165,119,87,142,123,131,59,254,117,167,156,41,125,254,56],
        "ratchet": {
            "send_key": [6,8,[1,79,112,132,98,47,6,118,212,221,235,120,149,156,87,172,106,157,248,36,135,198,191,207,243,65,83,183,57,110,161,213]],
            "recv_key": [6,9,[171,11,55,200,145,194,88,3,54,90,129,116,208,31,217,146,194,6,40,38,184,222,233,43,198,132,151,204,51,182,233,11]],
            "send_ctr": 2,
            "recv_past": {},
            "recv_ctr": 1
        }
      },
      "2": {
        "pk": [1,198,247,65,172,172,76,66,155,64,140,90,73,162,40,247,225,134,162,239,15,149,105,64,89,167,171,159,125,28,56,207,166],
        "ratchet": {
            "send_key": [6,8,[62,234,153,109,200,24,60,67,197,43,127,175,32,40,158,53,61,233,196,100,226,72,64,51,164,91,186,161,85,15,211,144]],
            "recv_key": [6,9,[102,95,139,78,169,159,72,133,153,83,238,26,138,13,31,122,136,212,63,38,104,40,239,153,128,61,177,149,28,80,14,79]],
            "send_ctr": 2,
            "recv_past": {},
            "recv_ctr": 1
        }
      }
    },
    "consumed_registrations": [
      [179,176,97,56,138,132,165,3,79,7,190,144,179,105,2,187,3,165,119,87,142,123,131,59,254,117,167,156,41,125,254,56,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],
      [198,247,65,172,172,76,66,155,64,140,90,73,162,40,247,225,134,162,239,15,149,105,64,89,167,171,159,125,28,56,207,166,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20]
    ]
}
```

`identity_key` contains the server's 32-byte Ed25519 seed as a strongly typed array. `identity_key_kid` is the server identity's key ID, `server_kid` is the last allocated remote-ID counter, and `known_ids` contains the known beacons' public keys and ratchet states. In this example the server knows two beacons, with key IDs 1 and 2.

Each serialized ratchet has exactly five fields: `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`. Send-message keys and their logical capabilities exist only during one encryption call and are never persisted. Objects from the former six-field format, including objects with an empty `send_past`, are rejected.

`consumed_registrations` is the persistent replay history. Each sorted 64-byte entry is the decoded beacon identity followed by the decoded signed one-time X25519 public key from one accepted `InitKex`. An identifier is retained even when response construction fails. Restoration rejects a missing history, entries of the wrong length, duplicates, or fewer entries than committed peers.

The canonical codec serializes peer IDs and cached receive sequences in numeric order and rejects duplicate or noncanonical map keys before inserting them into a `HashMap`. Restoration also checks field names, typed-array roles, counter bounds, cache capacity, and cached sequence alignment. These structural checks do not establish that arbitrary supplied chain bytes came from the canonical HKDF history, which is why restoration must receive the current snapshot from trusted storage.

Version-2 snapshots permit up to 50 receive-cache entries. Restoration accepts structurally valid state with all 50 entries occupied, including a target retained by an older failed-receive implementation. An invalid retry against an imported cached target is neutral; an authentic retry consumes it. A full restored cache can still process the next no-skip future target because the target is consumed separately and never occupies a cache slot; a farther target that would require retaining another skipped key is rejected until an authentic cached frame frees capacity. A fresh maximum-gap success can now retain all 50 skipped keys without changing the snapshot format or cache capacity.

Rust applications use `PersistentServer<S>` with an implementation of `SnapshotStore` instead of exporting from a raw `Server`:

```rust
pub trait SnapshotStore {
    fn load(&self) -> Option<ServerSnapshot>;

    fn compare_and_swap(
        &mut self,
        expected: Option<&SnapshotHead>,
        replacement: &ServerSnapshot,
    ) -> bool;
}

let mut server = PersistentServer::create(server_kid, Some(&seed), store.clone())?;

// Drop the only live owner before restoring it from the store.
drop(server);
let mut server = PersistentServer::restore(store)?;
```

`compare_and_swap` must atomically compare the complete current `SnapshotHead` and durably store the replacement before returning `true`. `load` must return only the current snapshot previously accepted by that store. The store must protect the snapshot and authoritative head against modification and rollback, and one lineage must not be made current in independent stores. `PersistentServer` commits the next generation before returning an accepted receive or any other state-changing result; a failed CAS fences the local server so that a losing branch cannot continue. A normally rejected receive is different: it leaves the in-memory server, snapshot head, generation, and authoritative snapshot unchanged and returns without encoding a successor, loading the store, or invoking CAS. This can delay detection that an owner is stale, but the stale owner releases no plaintext and its next state-changing operation must still win the normal CAS. See the [Rust example](../beaconcrypt/examples/rust/main.rs) for a complete single-process save-and-restart flow and the additional requirements placed on a production store.

The compatibility binding checkpoint APIs use an in-memory store. The application must therefore save `export_state` immediately after every accepted or otherwise state-changing call and before using that call's ciphertext, plaintext, registration token, or response. Save after registration and encryption attempts even when they report failure: once such an operation reaches `PersistentServer`, its commit advances the generation even if the operation returns `None`, and a failed registration can also retain consumed-registration history. A normal rejected receive is state-neutral and leaves exported checkpoint bytes unchanged, so it does not require another save. Import trusts the supplied bytes as the current state, so a standalone checkpoint file cannot detect stale rollback or prevent two independent restorations. Applications that require crash-atomic persistence, coordination between processes, or rollback detection should use the store-backed constructors in their language binding or Rust's `PersistentServer<S>` interface.

The three persistent receive methods decrypt once and commit the same accepted transition before releasing plaintext or constructing a receive update. `decrypt_and_update` and `decrypt_and_update_json` render their output only after durable acceptance. If that post-commit projection fails, they return `PersistenceError::OutputEncoding`; the target remains durably consumed, the owner remains usable, and the failure is not reported as a rejected frame. A process crash after CAS but before result delivery can likewise lose delivery while retaining consumption. Panics, external callback side effects, and physical erasure remain outside the normal-return state-neutrality contract.

For operations that need the updated state of one beacon, the server still exposes the following interface:

```rust
/// Encrypt bytes to `kid` and return the ciphertext, key ID, consumed sequence, and an inert serialized view of that peer's ratchet.
fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState>;

/// Decrypt a message and return the plaintext, sender key ID, consumed sequence, and an inert serialized view of that peer's ratchet.
fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState>;
```

The returned type looks like this:

```rust
pub struct StateUpdate<Role: roles::ChainKey> {
    pub kid: u64,
    /// The sequence number of the key consumed by this operation.
    pub seq: u64,
    pub state: RatchetSnapshot,
    pub data: Vec<u8>,
    pub(crate) _role: PhantomData<Role>,
}

pub type SendState = StateUpdate<roles::ChainSendKey>;
pub type RecvState = StateUpdate<roles::ChainRecvKey>;
```

`RatchetSnapshot` is an inert, serialization-only JSON string. It cannot be deserialized or converted into a live ratchet. This prevents the per-peer update API from creating another operational ratchet owner, but it does not make the string public: it still contains secret ratchet state.

The JSON wrappers return the same update as a JSON object:

```rust
fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String>;
fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String>;
```

Its output has the following shape:

```json
{
    "kid": 1,
    "seq": 2,
    "state": "{\"send_key\":[6,8,[...]],\"recv_key\":[6,9,[...]],\"send_ctr\":2,\"recv_past\":{},\"recv_ctr\":1}",
    "data": [0,0,0,0,19,0,0,0]
}
```

The Python and Go wrappers expose the inert ratchet JSON through `EncryptState.state()` and `EncryptState.State`, respectively. It is useful for observing or indexing one peer's resulting state, but it is not a complete server checkpoint and cannot replace full persistence through `PersistentServer` or the binding checkpoint APIs.
