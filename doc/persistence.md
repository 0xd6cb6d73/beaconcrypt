# Overview

This document describes the way beaconcrypt exposes state persistence to the server. This breaks forward secrecy, but is required to be useful in a server context. Additionally, the [threat model](threat_model.md) specifies that we already assume that server compromise is game over.

Snapshots contain the server identity seeds and all ratchet state in plaintext. They are not encrypted or authenticated by beaconcrypt, so applications must treat them as secret data and obtain integrity, provenance, and rollback protection from the server's trusted storage.

# Usage

Applications with a database can use `RowServer<S>` and the database-independent `RowStore` interface described below. `PersistentServer<S>` and the binding snapshot constructors remain available for applications that want a complete checkpoint. Row storage and snapshot storage are separate formats and ownership models; a row server never reconstructs the complete peer map for a message operation.

## Database row API

`RowServer` retains immutable identity keys and an application-supplied store. Each message operation reads one peer row inside a database transaction, executes the existing ratchet transition, and saves only that peer when its state changes. The peer includes its Ed25519 public key, ML-DSA public-key hash, both ratchet chains, counters, and bounded skipped-key cache. Peer state is discarded after every operation. Different handles can operate on the same lineage through separate connections to the same authoritative database; no global generation is updated for ordinary messages. `open` loads only the immutable identity row and performs no activation write.

The library has no database driver dependency. An application implements these interfaces using its own connection or pool:

```rust
pub trait RowTransaction {
    fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError>;
    fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError>;
}

pub trait RowStore {
    fn transaction(
        &mut self,
        operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
    ) -> Result<(), RowError>;
}

let mut server = RowServer::create(server_kid, Some(&ed25519_seed), Some(&mldsa_seed), store, lineage)?;
let response = server.register_beacon(registration, Some(initial_message))?;
let plaintext = server.decrypt_message(frame)?;
let ciphertext = server.encrypt_message(message, peer_kid)?;
// Another worker/restart supplies a new connection to the same authoritative database.
let server = RowServer::open(another_store, lineage)?;
```

`transaction` invokes the callback exactly once, rolls back on its error, and returns success only after the outer transaction commits durably. Do not retry the callback or return success for a savepoint whose enclosing transaction can still roll back. Use serializable isolation with conflict detection, or equivalent locking and conditional insertion that protects every read, including absent rows. A normal read followed by an unconditional upsert at read-committed isolation is insufficient: two workers could both accept an absent replay marker or overwrite the same peer predecessor. A serialization failure is an error for this attempt; a new message attempt reloads current state. Database errors must not be mapped to missing rows.

The following logical records use opaque byte keys and versioned byte values:

| Record | Scope | Write behaviour |
| --- | --- | --- |
| Identity | One per lineage | Created once; includes both identity seeds |
| Allocator | One per lineage | Updated with the new peer at registration completion |
| Peer | One per assigned peer ID and lineage | Replaced only for that peer's state-changing operation |
| Consumed registration | One per accepted registration ID and lineage | Inserted once and retained permanently |

Keys and values must be stored byte-for-byte, for example in binary columns. Values bind their complete storage key, format version, independent generation, and identity digest. Peer payloads reuse the canonical checked codec, including the ML-DSA hash and receive-cache validation. Generations are storage revisions, not protocol sequence numbers: a cached receive can remove a key without advancing the receive counter. These checks do not authenticate untrusted storage or detect restoration of a stale database backup. The application must protect the database, WAL, replicas and backups as secret state and provide the same integrity, provenance, freshness and durability guarantees as snapshot storage. A lineage must never be made authoritative in two independent databases.

Registration deliberately uses two transactions. The first commits the consumed registration marker before the pending cryptographic material can be used to build a response. The second reads the allocator, checks the next peer ID is absent, constructs the response, and atomically writes the allocator and new peer. A dropped pending attempt, failed response, transaction conflict, or crash does not remove the first marker. A rejected or interrupted registration therefore needs a fresh beacon registration attempt. Ordinary messages never read the allocator or replay history.

An authentic receive commits consumption before releasing plaintext. A rejected receive writes no row. Send failure after key consumption still saves the advanced chain. On a database error, including a lost commit acknowledgement, the method releases no output and discards its tentative peer state; the next attempt reads the authoritative row. The handle remains usable because it retains no mutable ratchet cache. The convenience methods commit only cryptographic state, so a crash after commit can still lose result delivery. Applications needing a durable result use the composition API below. Do not return success from `RowStore` before an enclosing application transaction commits.

The [SQLite example](../beaconcrypt/examples/sqlite/main.rs) implements the storage interface entirely in application code and can be run with `cargo run -p beaconcrypt --example sqlite -- /path/to/server.sqlite`. Its file-backed integration tests cover restart, transaction rollback, lost commit acknowledgement, concurrent workers, replay, and bounded receive-cache recovery. SQLite is a development-only dependency for this example and tests. Its database-wide writer lock is a backend property; a database with row locking can let unrelated peers commit independently through the same interface.

Existing full-snapshot exports cannot be passed to `RowServer::open`, and inert `RatchetSnapshot` values cannot be activated as peers. This API creates new row lineages; snapshot import tooling is not provided. A future migration API would need to fence all old snapshot writers, validate the authoritative snapshot, transfer its identities, allocator, every peer and all consumed registrations, and establish the new store as the sole authority before serving requests. Applications must not reimplement private row encodings to bypass this boundary or keep both stores operational.

## Composing application transactions

`RowServer::transaction` runs an application callback with a temporary `RowSession` and releases its return value only after the same durable outer transaction commits. The session exposes `load_application` and `store_application` for opaque application records in a separate namespace bound to the server lineage. It also exposes `encrypt_message` and `decrypt_message`, permitting zero or one native attempt per callback. A cached-result lookup can therefore finish without advancing a ratchet. A fresh request can validate authorization and its input fingerprint, perform cryptography, and store the exact application response and associated metadata together with the peer update.

Native session methods return a `RowTransition` with `message` and `changed`. Its optional `RowMessage` exposes only bytes, authenticated peer ID, and sequence through read-only accessors; its owned buffer is wiped on drop. `changed` distinguishes an ordinary rejection from a failed send that consumed a key. A storage/native error, wrong-phase method, or second native attempt makes the session fail permanently; swallowing the error in the callback cannot publish partial work. Application values distinguish absence from a present empty byte string.

These callbacks form part of the trusted persistence boundary. They may encode pending plaintext/ciphertext and save it inside the active transaction, but must not send it, acknowledge delivery, or perform irreversible external work before the outer call succeeds. The library confines its return value and wipes its own pending native buffers on failure; it cannot erase arbitrary copies made by application code. Use wiping buffers for secret callback results where applicable. Callback-scoped access does not make untrusted application code safe.

Registration composition uses `RowServer::registration_transaction` with acceptance and completion callbacks. Both receive a session with application-row access. The acceptance callback can return `RowRegistrationDecision::Return(result)` for a cached or terminal application result, or call `accept_registration` and return `Continue(context)` after staging an application-owned incomplete receipt. Only a confirmed first commit permits the library's private pending token to reach the completion transaction. The completion callback can recheck authorization, call `complete_registration`, and atomically store its exact reply and session mapping with the allocator and peer. It may instead commit an application-owned terminal result without completing cryptography. No pending token is exported or persisted.

`RowRegistrationError` identifies the failed phase. A completion-phase error means acceptance was already confirmed committed; an acceptance-phase error may include an uncertain first commit. A crash between phases leaves the accepted marker and any application incomplete receipt. The application must inspect its authoritative receipts after uncertainty, preserve compact tombstones when result payloads expire, and avoid repeating cryptography for an already completed or incomplete request. Request identifiers, fingerprints, authorization, retention, inbox/outbox records, and delivery policy remain entirely application-defined. See [the integration design](impl/row-delivery-design.md) for the Mythic example and its remote storage requirements.

## Database row bindings

Python exposes `BeaconCryptRowServer` and a separate `RowPersistenceError`. Supply a database object with `begin()`, `load(key) -> bytes | None`, `store(key, value)`, `commit()`, and `rollback()` methods. Methods other than `load` return `None`; failures must raise an exception. `begin` starts the outer transaction, `commit` durably completes it, and `rollback` must safely clean up after a begin, operation or commit failure, including when no transaction is active. The original callback exception is retained as `__cause__`. The [Python row tests](../tests/test_row_persistence.py) contain a complete file-backed `sqlite3` adapter.

```python
from beaconcrypt import BeaconCryptRowServer

server = BeaconCryptRowServer.create(server_kid, ed25519_seed, mldsa_seed, database, lineage)
response = server.register_beacon(registration, initial_message)
ciphertext = server.encrypt_to_beacon(message, response.key_id())
server.close()
server = BeaconCryptRowServer.open(another_database_connection, lineage)
plaintext = server.decrypt_beacon_message(frame)
```

Go exposes `RowStore` with `Begin() error`, `Load(key []byte) ([]byte, error)`, `Store(key, value []byte) error`, `Commit() error`, and `Rollback() error`. An absent row is `nil, nil`, and a database failure is an error. `NewRowServer(kid, seed, mldsaSeed, store, lineage)` creates the namespace; `OpenRowServer(store, lineage)` opens it. Handles provide `IdentityPK`, `MLDSAPublicKey`, `RegisterBeacon`, `EncryptToBeacon`, `DecryptBeaconMessage`, and `Close`. Operations use the existing `PersistenceError` status codes; callback failures carry `StatusStorage` and their original error as `Cause`. Calls on one Go handle are serialized. Use separate handles and transaction connections for independent concurrent workers. The WASM backend currently supports snapshot storage only; its row constructors return `ErrPersistenceUnsupported` without calling the store.

Use metadata-bearing methods when authorizing the authenticated peer or tracking the consumed sequence. Go's `EncryptToBeaconWithMetadata` and `DecryptBeaconMessageWithMetadata` return `*RowMessage` with `Data`, `KeyID`, and `Seq`. Python's `encrypt_to_beacon_with_metadata` and `decrypt_beacon_message_with_metadata` return an immutable `RowMessage` with `data`, `key_id`, and `seq` properties. C's `beaconcrypt_row_server_encrypt_with_metadata` and `beaconcrypt_row_server_decrypt_with_metadata` return `beaconcrypt_RowMessageBuffer` with `data`, `key_id`, and `seq`; free its data buffer with `beaconcrypt_free_buffer`. Metadata describes the consumed key, so receiving an older cached key returns its original sequence. These methods release metadata and bytes together after commit and expose no ratchet snapshot.

C exposes `beaconcrypt_row_server_create`, `beaconcrypt_row_server_open`, and `beaconcrypt_row_server_free` with a separate opaque `RowServerHandle`. `RowStoreCallbacks` supplies `begin`, `load`, `store`, `commit`, `rollback`, and optional `destroy` callbacks. The load callback returns `0` for absence, `1` after calling its borrowed sink exactly once, or `-1` for a storage error. The other fallible callbacks return a Boolean success flag. Constructors consume the callback context immediately; `destroy` runs exactly once on construction failure or handle destruction. Read operation status with `beaconcrypt_row_server_last_status`; `ROW_STATUS_STORAGE` denotes a database callback failure or uncertain commit. A row-encoding failure uses `STATUS_ENCODING` and occurs before commit; Python reports its code as `encoding`. Other codes retain their snapshot equivalents: missing identity uses `STATUS_MISSING_SNAPSHOT`, invalid row uses `STATUS_INVALID_SNAPSHOT`, and conflict uses `STATUS_STALE_GENERATION`. All calls on one C handle must be serialized, and callbacks must not reenter it or retain borrowed pointers. Release returned buffers with `beaconcrypt_free_buffer`.

Across these row bindings, an omitted registration response payload uses the protocol witness. An explicitly empty payload rejects response construction after registration acceptance: Python uses `b""`, Go uses a non-nil empty slice, and C uses a non-null pointer with zero length. The consumed registration marker remains committed. Rejected messages return `None` in Python, `ErrCrypto` in Go, or empty output with `STATUS_REJECTED` in C. Database failure never releases tentative output, and subsequent calls load current peer state again rather than continuing a failed tentative ratchet.

### Composing application transactions

Use a trusted transaction callback when cryptographic rows must commit with application authorization, metadata, or an exact result. Go exposes `server.Transaction(func(*RowSession) ([]byte, error))`; Python exposes `server.transaction(callback)` where the callback receives a `RowSession` and returns `bytes`; C exposes `beaconcrypt_row_server_transaction` with a callback and copied result sink. These interfaces define no request identifiers, digests, journals, response formats, or database drivers. The application can load its cached result before invoking any native transition, or store its exact new response before returning it. The outer method releases the callback's opaque bytes only after durable commit. An empty result is valid.

Session `Load`/`load` and `Store`/`store` address application keys isolated from beaconcrypt's native records. An absent value is Go `nil`, Python `None`, or a null C buffer with `STATUS_REJECTED`; a present empty value is a non-nil empty slice, `b""`, or a non-null zero-length C buffer. Native encrypt/decrypt session methods return `RowTransition` containing an optional `RowMessage` and `Changed`/`changed`. The C equivalent is `beaconcrypt_RowTransitionBuffer`. A transition can change native state without producing a message. Each session allows zero or one attempted native operation, including rejection; a native or storage method error aborts the transaction even if the application catches it.

Callbacks are part of the trusted persistence boundary. Their native message bytes are pending and must not be sent to a network, broker, or another irreversible effect before the outer method succeeds. Foreign code can copy these bytes; the library cannot revoke those copies or guarantee their erasure. The result returned by the outer call is suppressed on failure. Use sessions synchronously on the callback thread or goroutine; do not share them with concurrent work. C session pointers and sinks must not escape the callback; Go and Python wrappers reject calls after callback return. Recursive session calls are rejected, and Go rejects overlapping session calls. Do not reenter the owning server from any callback; its Go mutex remains held, while Python rejects a second mutable borrow.

Registration uses `RegistrationTransaction` in Go, `registration_transaction` in Python, and `beaconcrypt_row_server_registration_transaction` in C. The acceptance callback can return a cached application result, or call `AcceptRegistration`/`accept_registration`, stage an incomplete application record, and choose to continue with opaque context bytes. Go returns `RowRegistrationDecision{Continue: true, Data: context}` or `{Data: result}`; Python returns `RowRegistrationDecision.continue_registration(context)` or `.return_result(result)`; C returns 1 or 0 and invokes its sink exactly once. Completion runs only after the first transaction is durably confirmed. It receives the application context, revalidates application authorization, invokes `CompleteRegistration`/`complete_registration`, and saves its exact response and routing metadata in the second transaction.

A completion failure retains the first transaction's replay marker and application rows. Go's `RowRegistrationError.Phase`, Python's `RowRegistrationError.phase`, and C's phase output distinguish acceptance from completion errors. Completion means acceptance definitely committed; either failed phase can still have an uncertain commit outcome. Inspect authoritative application records to distinguish a completed result from an accepted incomplete operation. The library retains no resumable pending registration token after the call. Callback errors remain the original Go error or Python exception cause; panics in Go callbacks become errors. Generic session misuse has `StatusInvalidSession`/`ROW_STATUS_INVALID_SESSION` or Python code `invalid_session`.

The [Go composition tests](../row_session_cgo_test.go) and [Python database composition tests](../tests/test_row_transactions.py) demonstrate exact application-result recovery after lost commit acknowledgement, rollback of application and native writes, and registration phase handling. The [integration design](impl/row-delivery-design.md) explains how an application can build authorization-aware deduplication and result retention around these generic primitives.

## Snapshot API

Rust, C, Go, and Python can all use an application-supplied snapshot store. Its load operation returns only the trusted current snapshot, or no snapshot when the store is empty. Its compare-and-swap operation atomically compares the complete expected head and durably stores the replacement before reporting success. An absent expected head means that creation must fail if the store is already occupied. The store must provide integrity, provenance, rollback resistance, durability, and coordination between concurrent owners; snapshot parsing and successor validation do not supply these properties.

Python storage objects implement `load() -> bytes | None` and `compare_and_swap(expected: SnapshotHead | None, replacement: bytes) -> bool`:

```python
from beaconcrypt import BeaconCryptServer

# store implements the trusted storage contract described above.
server = BeaconCryptServer.create_with_store(server_kid, ed25519_seed, mldsa_seed, store)
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

The exported value is a binary version-3 snapshot envelope, not a bare JSON document. It contains a format identifier, a lineage identifier, a monotonic generation, the previous snapshot's digest, a payload length, and the canonical JSON server-state payload. The digest identifies exact snapshot bytes and links generations; because it is unkeyed, it does not authenticate snapshots obtained outside trusted storage.

Store implementations can call `replacement.validate_successor(expected)` to validate the envelope, exact next generation, same lineage and complete parent digest before accepting a replacement. The in-memory binding store uses this check. It must run in the same transaction as comparison with the authoritative current head; it supplies neither payload authentication nor external freshness, durability or linearizability. The application must separately provide storage integrity, freshness, durability, and linearizability; buffer wiping does not protect copies retained by the application or storage system. [The deployment boundary](deployment-boundary.md) describes the separate requirements and the limits of buffer erasure and fallible construction.

The decoded JSON payload has the following shape:

```json
{
    "identity_key": [1,14,[65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65]],
    "mldsa_identity_seed": [66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66],
    "identity_key_kid": 0,
    "server_kid": 2,
    "known_ids": {
      "1": {
        "pk": [1,179,176,97,56,138,132,165,3,79,7,190,144,179,105,2,187,3,165,119,87,142,123,131,59,254,117,167,156,41,125,254,56],
        "mldsa_public_key_hash": [67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67],
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
        "mldsa_public_key_hash": [67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67,67],
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

`identity_key` contains the server's 32-byte Ed25519 seed as a strongly typed array. `mldsa_identity_seed` contains its independent 32-byte ML-DSA-65 seed, and each peer requires its 64-byte `mldsa_public_key_hash` to reconstruct the authenticated AD. Version-one and version-two snapshots, missing fields, and incorrect seed or hash lengths are rejected. `identity_key_kid` is the server identity's key ID, `server_kid` is the last allocated remote-ID counter, and `known_ids` contains the known beacons' public keys and ratchet states. In this example the server knows two beacons, with key IDs 1 and 2.

Registration transport messages use CBOR version two, with the agent ML-DSA public key and both parties' signatures carried as array fields. The persisted peer hash is BLAKE2b-512 of the decoded 1,952-byte agent ML-DSA public key. Registration CBOR headers and signature bytes are excluded from that hash. Snapshot version three stores the same identity seeds, peer hashes, and ratchets independently of registration encoding.

Each serialized ratchet has exactly five fields: `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`. Send-message keys and their logical capabilities exist only during one encryption call and are never persisted. Objects from the former six-field format, including objects with an empty `send_past`, are rejected.

`consumed_registrations` is the persistent replay history. Each sorted 64-byte entry is the decoded beacon identity followed by the decoded signed one-time X25519 public key from one accepted `InitKex`. An identifier is retained even when response construction fails. Restoration rejects a missing history, entries of the wrong length, duplicates, or fewer entries than committed peers.

The canonical codec serializes peer IDs and cached receive sequences in numeric order and rejects duplicate or noncanonical map keys before inserting them into a `HashMap`. Restoration also checks field names, typed-array roles, counter bounds, cache capacity, and cached sequence alignment. These structural checks do not establish that arbitrary supplied chain bytes came from the canonical HKDF history, which is why restoration must receive the current snapshot from trusted storage.

Version-3 snapshots permit up to 50 receive-cache entries. Restoration accepts structurally valid state with all 50 entries occupied, including a target retained by an older failed-receive implementation. An invalid retry against an imported cached target is neutral; an authentic retry consumes it. A full restored cache can still process the next no-skip future target because the target is consumed separately and never occupies a cache slot; a farther target that would require retaining another skipped key is rejected until an authentic cached frame frees capacity. A fresh maximum-gap success can now retain all 50 skipped keys without changing the snapshot format or cache capacity.

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

let mut server = PersistentServer::create(server_kid, Some(&ed25519_seed), Some(&mldsa_seed), store.clone())?;

// Drop the only live owner before restoring it from the store.
drop(server);
let mut server = PersistentServer::restore(store)?;
```

`compare_and_swap` must atomically compare the complete current `SnapshotHead` and durably store the replacement before returning `true`. `load` must return only the current snapshot previously accepted by that store. The store must protect the snapshot and authoritative head against modification and rollback, and one lineage must not be made current in independent stores. `PersistentServer` commits the next generation before returning an accepted receive or any other state-changing result; a failed CAS fences the local server so that a losing branch cannot continue. A normally rejected receive is different: it leaves the in-memory server, snapshot head, generation, and authoritative snapshot unchanged and returns without encoding a successor, loading the store, or invoking CAS. This can delay detection that an owner is stale, but the stale owner releases no plaintext and its next state-changing operation must still win the normal CAS. See the [Rust example](../beaconcrypt/examples/rust/main.rs) for a complete single-process save-and-restart flow and the additional requirements placed on a production store.

The compatibility binding checkpoint APIs use an in-memory store. The application must therefore save `export_state` immediately after every accepted or otherwise state-changing call and before using that call's ciphertext, plaintext, registration token, or response. Save after registration and encryption attempts even when they report failure: a successful commit advances the generation even on `None`, and a failed registration can retain consumed-registration history. Transport-size rejection before commit leaves the head unchanged, but a combined binding registration helper may already have committed `InitKex` acceptance before rejecting its response size. A normal rejected receive is state-neutral and leaves exported checkpoint bytes unchanged, so it does not require another save. Import trusts the supplied bytes as the current state, so a standalone checkpoint file cannot detect stale rollback or prevent two independent restorations. Applications that require crash-atomic persistence, coordination between processes, or rollback detection should use the store-backed constructors in their language binding or Rust's `PersistentServer<S>` interface.

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
