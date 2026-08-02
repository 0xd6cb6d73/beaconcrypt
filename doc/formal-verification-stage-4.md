<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 4 implementation

## Status and scope

Stage 4 moves PQXDH composition and registration control into role-specific
typestates in `beaconcrypt-protocol-core`, then makes the production
`BeaconCryptPqxdh` implementation delegate to those transitions. The work was
based on commit `a748f323d0fb17b3aa929e468c0be7bfff2c4ec3`, which completed the
Stage 3 symmetric-ratchet adapter but still kept PQXDH decisions and mutation
ordering in `src/pqxdh.rs`.

This stage covers deterministic message inputs, key-type tags, PQXDH root input
ordering, associated data, role-dependent ratchet initialization, explicit
registration states, and transactional publication of an established session.
It also adds PQXDH to the pinned hax/F* extraction and strict safety-checking
path.

Stage 4 does not add the PQXDH agreement or transcript lemmas planned for Stage
6, and it does not establish the authentication or replay claims reserved for
Stage 5.

## Implementation map

| File | Responsibility |
| --- | --- |
| `crates/protocol-core/src/pqxdh.rs` | Define deterministic PQXDH inputs, transcript builders, role-specific typestates, and commit/abort transitions. |
| `crates/protocol-core/src/lib.rs` | Export the PQXDH module from the dependency-free `no_std` core. |
| `crates/protocol-core/Makefile` | Include all public Stage 4 PQXDH transitions in pinned hax extraction. |
| `crates/protocol-core/proofs/fstar/extraction/Beaconcrypt_protocol_core.Pqxdh.fst` | Track the generated F* translation; it is generated output, not a hand-maintained specification. |
| `src/pqxdh.rs` | Adapt Cap'n Proto, libsodium, concrete key material, and the public provider traits to the core typestates. |
| `src/server.rs` | Expose an opaque registration token containing the derived root and pending core state. |
| `src/shared.rs` | Initialize concrete ratchets from a core direction plan and support encryption/decryption against staged ratchets. |
| `src/deser.rs` | Update persistence fixtures to use an explicit core ratchet-direction plan. |
| `tests/protocol.rs` | Exercise single-use beacon registration, terminal beacon failure, and server-side transactional failure through the production API. |

No generated F* file was hand-edited in this stage, and no handwritten PQXDH
lemma module was added.

## Extractable PQXDH core

The new core module contains no RNG, cryptographic implementation, wire parser,
allocator-backed collection, persistence code, or FFI. Instead, the adapter
supplies explicit values produced by those operations:

- `BeaconStartInputs` contains the beacon identity, prekey, and ML-KEM public
  material;
- `BeaconCoins` contains the per-registration one-time public key;
- `ServerCoins` contains the ephemeral public key and KEM ciphertext;
- `ServerBinding` contains the accepting server's identity public key and
  identity key ID;
- `PqxdhSharedSecrets` contains DH1 through DH4 and the KEM shared secret after
  the adapter has invoked the opaque primitives.

Given those inputs, every core transition is deterministic. Secret-key
generation, signing and signature verification, DH, encapsulation,
decapsulation, HKDF, AEAD, and entropy acquisition remain in the production
adapter and outside the extraction claim.

The core transition graph is:

```text
BeaconFresh
  -> BeaconInitSent
  -> BeaconRegistrationCandidate
  -> BeaconEstablished | BeaconAborted

ServerState + VerifiedInitKex + ServerBinding
  -> PendingServerRegistration
  -> ServerRegistrationCandidate
  -> (ServerState, EstablishedPeer) | unchanged ServerState
```

The pending and candidate states separate validation and expensive adapter work
from publication. The core types make the expected transition order explicit;
the production `ProviderRole` and `BeaconState` enums keep the matching concrete
keys available only in the states that can use them.

The high-level `BeaconCryptPqxdh::new(is_beacon, ...)` constructor and
beacon/server provider methods remain compatibility surfaces. The boolean
selects `ProviderRole` at construction; subsequent registration transitions
operate on the beacon or server variant and its typed control state rather than
repeatedly interpreting the flag. A production-only `FreshWithCoins` subphase
supports the existing one-time-key pre-generation helper while still mapping to
core `BeaconFresh` until a bundle is emitted.

`ProviderRole` keeps the large, secret-bearing beacon variant inline. A scoped
`clippy::large_enum_variant` allowance records the choice to avoid a separate
heap allocation with a different secret-memory lifecycle. This means a server
provider retains the enum's larger inline footprint; it is a concrete layout
decision, not part of the formal state-machine claim.

The server adapter maintains the counter refinement

```text
ProviderRole::Server(control).last_key_id() == server_kid
```

at construction, restoration, compatibility counter updates, and successful
registration commit. The persisted `server_kid` is sufficient to reconstruct
the core state, so the wire format does not duplicate this representation.

## Message and transcript construction

`beacon_start` constructs the exact unsigned `InitKex` key payloads. It prefixes
Ed25519 identity material with tag 1, X25519 prekey and one-time material with
tag 4, and ML-KEM-768 material with tag 3. The adapter signs the three KEM
payloads and serializes all four fields. On receipt, the adapter parses the
message and verifies the signatures before `validate_init_kex` strips and
checks the core-owned, disjoint tags.

`build_root_key_input` constructs the fixed 192-byte input

```text
0xff * 32 || DH1 || DH2 || DH3 || DH4 || KEM shared secret
```

and rejects an all-zero value in any classical DH position. The adapter passes
the resulting buffer to the opaque SHA-512 HKDF with `PQXDH_INFO`; the core does
not implement or assume the internals of that primitive.

The core expresses that rejection with ordinary fixed-array equality. The
production libsodium scalar-multiplication calls already reject invalid
all-zero results before this redundant check, but Rust array equality carries
no constant-time guarantee. Timing behavior of this guard therefore remains an
adapter/security-hardening obligation rather than part of the formal claim.

The secret-bearing `PqxdhSharedSecrets`, `RootKeyInput`, and registration
candidate types do not implement `Copy`, avoiding implicit transcript copies.
The production adapter explicitly zeroizes its `PqxdhSharedSecrets` arrays
after the core preparation call and the concrete 192-byte `RootKeyInput` after
HKDF, on success and error returns from those operations.

The secret-bearing core aggregates also omit `Clone` and `Debug`. This hygiene
is deliberately described narrowly: formal extraction does not establish what
the compiler does with temporary bytes, and comprehensive secret-memory
lifecycle and physical erasure remain outside the Stage 4 proof claim.

Associated data is constructed in one place as:

```text
tagged server identity || tagged beacon identity || PQXDH_INFO || SYM_RATCHET_INFO
```

Both roles therefore use the same identity ordering. The core also returns a
`RatchetInitialization` plan instead of asking the adapter to branch on an
`is_beacon` flag: the server sends from the first 32-byte half and the beacon
receives from it, while the beacon sends from the second half and the server
receives from it. Compile-time assertions connect the fixed core sizes to the
corresponding libsodium sizes.

The crate-private `RatchetManager::init_ratchets` now accepts that direction
plan and returns failure instead of unwrapping HKDF results. It validates the
core-provided offsets, copies both halves directly into zeroizing chain storage,
wipes the combined HKDF buffer, and then clears the caches and resets logical
ratchet control state. The former low-level `CryptoProvider::init_ratchets`
hook is no longer part of the public transition surface.

## Beacon transition and terminal failure

A fresh production beacon stores its prekey and ML-KEM keypair alongside
`BeaconFresh`. `get_registration_bundle` generates the one-time key once, calls
`beacon_start`, and replaces the fresh state with `BeaconInitSent`. A second
call is rejected because no fresh state remains.

`finish_registration` is admitted only from `BeaconInitSent`, and every failed
staged attempt replaces that state with `BeaconAborted`. After parsing, identity
checking, decapsulation, and the four DH operations, `beacon_prepare_finish`
supplies the core-owned root input, associated data, assigned identity, and
ratchet direction to a candidate. The adapter derives and initializes a new
ratchet off to the side, then authenticates the initial ciphertext against that
staged ratchet.

Only successful authentication calls `beacon_commit` and publishes the
assigned identity, associated data, and staged server ratchet. Every failure
enters `BeaconAborted`; prekey, one-time, and ML-KEM private material is no
longer reachable, no associated data or derived ratchet state is published, and
neither the response nor a new registration bundle can be retried on that
provider. The preconfigured server principal remains present for identity
pinning, but its ratchet is reset to the default empty state. This is the
explicit terminal failure behavior chosen for Stage 4.

## Server transaction

The server adapter first parses and signature-checks `InitKex`, generates its
ephemeral and ML-KEM results, and computes the four DH outputs. `server_accept`
validates the root input and returns a `PendingServerRegistration` while leaving
`ServerState` unchanged. The pending token records the accepting provider's
`ServerBinding`: its identity public key and identity key ID.

The public `RegistrationOutput` is now an opaque token containing only the
concrete derived root and its private pending core state. The response builder
consumes that token by value and derives the peer identity, ephemeral key, KEM
ciphertext, and associated data from the core candidate, so callers cannot
mutate public legacy fields out of correspondence with the validated
transcript. The token is neither clonable nor inspectable. Stage 5 replay is
still possible by presenting the same serialized `InitKex` to
`get_shared_secret` again and obtaining a new pending token.

`server_prepare_commit` then creates a candidate containing the proposed next
key ID, peer identity, associated data, response public material, and both the
previous and proposed server states. It first requires the provider's current
binding to equal the recorded binding. Moving a token to a differently
identified server is rejected without mutating either server; the candidate's
bound identity key ID is also used as the sender ID for staged initial-message
encryption. This local binding does not authenticate the separately assigned
beacon key ID in `KexResponse`, which remains Stage 5 work.

The adapter performs the remaining work on local values:

1. reject an existing peer ID and reserve peer-map capacity;
2. initialize a fresh peer ratchet from the token's concrete derived root;
3. encrypt the registration witness or application message against that staged
   ratchet;
4. serialize the complete `KexResponse`;
5. call `server_commit` and only then update the key counter and peer map.

Failure before the last step drops the staged peer and candidate. The candidate
owns only proposed state, so the live state does not need a rollback mutation.
The core's explicit abort transition returns the recorded previous state and is
covered directly by core tests. The live counter, peer-map entries, and
serialized server state remain unchanged, so the next successful registration
receives the still-unconsumed ID. The staged encryption helper uses the same
Stage 3 logical/concrete send-key completion path as normal application
encryption, including consumption on a post-allocation failure.

Capacity reservation occurs before any live mutation. Once the response has
serialized, the remaining core transition and assignments have no recoverable
failure path, so the counter and peer become visible together to callers.
Reservation can increase the map's physical capacity on a later failure; that
allocator detail is not protocol state and is excluded from the atomicity
claim.

The server persistence format is unchanged. Its persisted `server_kid` rebuilds
the corresponding `ServerState` during restoration; no duplicate core state is
serialized.

## API and persistence compatibility

The high-level beacon/server registration sequence, Cap'n Proto messages,
server JSON state, and C ABI function signatures are unchanged. The Rust
low-level surface is intentionally narrower where unrestricted mutation could
bypass the new states:

- `RegistrationOutput` is now opaque and consumed by
  `build_registration_response`; downstream code can no longer construct,
  destructure, or mutate its former public fields;
- the generic `CryptoProvider::init_ratchets` hook was removed, and the
  direction-planned `RatchetManager` initializer is crate-private;
- the existing one-time and post-quantum keypair helpers remain available, but
  now perform phase-safe transitions. Removing a pre-generated one-time key
  before emission returns to `Fresh`; removing it after `InitKex`, or deleting
  the required post-quantum key during registration, enters the terminal
  aborted state instead of leaving unrelated optional fields.

Downstream Rust code that used those low-level construction or initialization
paths must migrate to the high-level provider transitions. This narrowing does
not alter the persisted server format or wire protocol.

## Extraction and proof boundary

The pinned hax item list now includes the public PQXDH constructors,
validation, transcript builders, direction plans, and commit/abort transitions.
`make verify` regenerates and strictly verifies
`Beaconcrypt_protocol_core.Pqxdh.fst` alongside the existing ratchet extraction.
This confirms that the production core remains inside the supported extraction
subset and that the generated module is accepted by F* without `--lax`. F*
discharges the generated safety conditions, including the bounds obligations
for the fixed-array construction loops used by the PQXDH module.

Typechecking extracted code is not a proof of the Stage 6 PQXDH inventory. In
particular, this stage does not yet prove root agreement between roles, exact
transcript equivalence as a theorem, associated-data equality, matching ratchet
initialization, or the other semantic correspondence properties. Those
properties need hand-maintained lemmas over the generated module in Stage 6.

The Stage 4 correspondence claim is limited to high-level registration calls
on a freshly constructed or successfully restored provider. It continues to
assume correct Cap'n Proto translation, correct libsodium and ML-KEM operations,
fresh adapter-generated randomness, and no rollback or cloning of live secret
state. Zeroization mechanics, allocation failure, persistence confidentiality,
and FFI caller behavior remain outside the core proof boundary.

Direct compatibility mutators are also outside this trace. In particular,
callers can invoke `set_identity_kid`, `set_associated_data`, peer-map helpers,
or low-level ratchet operations after registration and deliberately change
adapter state independently of the PQXDH typestate. The production registration
path no longer uses these setters; claims in this stage begin with construction
or validated restoration and follow only the high-level provider transitions.

The small core control values are logical transition descriptors rather than
affine Rust capabilities. The single-bundle claim therefore comes from the
production provider replacing its private `Fresh` enum variant with
`InitSent`; it is not a claim that an arbitrary caller holding a copied
`BeaconFresh` value cannot invoke `beacon_start` twice outside that adapter.

## Regression coverage

Stage 4 adds or strengthens production-path tests for:

- one successful `InitKex` generation followed by rejection of a second call;
- terminal beacon failure after a corrupted initial ciphertext, including
  deletion of registration keys, absence of associated data, and restoration
  of the preconfigured server ratchet to its empty state;
- rejection of retries after the beacon has entered the aborted state;
- server response failure without counter advancement, peer insertion, or any
  change to exported state;
- rejection of a pending registration moved to a server with a different
  identity binding, with both providers' live state unchanged;
- reuse of the unconsumed server key ID by the next successful registration;
- phase-safe pre-generation and pre-emission deletion of a one-time key, plus
  terminal deletion after `InitKex` or deletion of the required post-quantum
  key;
- exact root-input order, disjoint key tags, role-ordered associated data,
  ratchet directions, explicit commit, and explicit abort in core unit tests;
- zeroization of the concrete root transcript immediately after the adapter's
  HKDF call;
- continued execution of the existing protocol, persistence, binding, and
  known-answer coverage through the transactional adapter.

## Validation performed

The implementation is validated with the same production feature matrix and
strict proof-toolchain checks used by Stage 3:

```sh
cargo fmt --all -- --check
cargo test --workspace --all-targets --locked
cargo check --locked --no-default-features --features pqxdh,server --lib
cargo check --locked --no-default-features --features pqxdh,beacon --lib
cargo clippy --workspace --all-targets --all-features --locked -- \
  -D warnings -A clippy::type-complexity
make -C crates/protocol-core verify
cargo build --locked --release --features gobinds
go test -a -count=1 .
```

The full workspace run completed with 155 passing tests and the two remaining
Stage 5 counterexamples ignored: 66 root unit tests, 1 beacon integration test,
46 protocol tests, 6 Rooterberg tests, 9 server tests, 6 Wycheproof tests, and 21
protocol-core tests. Both the server-only and beacon-only feature checks passed.
The release C/Go facade build and Go binding tests also passed, covering the
unchanged high-level registration sequence through the FFI boundary.

The pinned extraction generated the 855-line PQXDH module and strictly verified
it together with the ratchet module and existing ratchet lemmas; all
verification conditions were discharged. The new PQXDH artifact has SHA-256
`7eb8f63c428b81414dca677f78b1ad68e4d2923ce81a414ffd0623b04c140f97`.
Because it is a newly added file, Git's tracked-diff guard will begin checking
it after this change is staged or committed. At that point, rerun
`make -C crates/protocol-core check-generated` to establish a conclusive
byte-stability check. No PQXDH semantic lemma is included in the current strict
verification result.

Clippy completed with lints denied. The scoped large-enum allowance is described
above, and the command retains Stage 3's allowance for a pre-existing complex
deserialization signature. Cargo also prints a non-fatal configuration warning
because the workspace `clippy.toml` selects MSRV 1.96 while the isolated core
crate declares Rust 1.85.

## Remaining rollout work

Stage 4 deliberately preserves protocol behavior that the next stage must
change:

- `KexResponse.keyId` is still outside the authenticated handshake material;
- the server does not remember and reject a replayed `InitKex`;
- server key allocation still uses wrapping increment. The Stage 4 adapter
  rejects a proposed ID already present in the peer map, but it does not treat
  counter exhaustion and wrap as an explicit allocation failure.

Consequently, injective agreement on the assigned key ID and registration
replay-resistance must not be claimed yet. Stage 5 must bind the assigned ID,
add replay tracking, use checked collision-safe allocation, and enable the two
remaining ignored regressions before those claims can proceed.

Stage 6 must then add the functional PQXDH lemmas. ProVerif processes, events,
compromise scenarios, and trace queries remain Stage 7 work.
