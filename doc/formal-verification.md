<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification plan

## Goal and scope

The goal is to prove protocol-level properties of beaconcrypt from the Rust code that is used in production. The proof target is the composition and state-machine logic for PQXDH and the symmetric ratchet, not the implementation security of ChaCha20-Poly1305, BLAKE2b, HKDF, X25519, Ed25519, or ML-KEM.

This document complements the [protocol description](protocol.md) and [threat model](threat_model.md). It describes an extraction boundary, the responsibilities of each prover backend, the intended theorem inventory, and a staged path to a continuously checked proof.

The central rule is that there must not be a hand-written proof model that can silently diverge from the implementation. A small, extractable Rust crate will own the protocol transitions, and the existing public API will call that crate. hax will extract that same code to the prover backends.

## Verification architecture

Use two complementary backends from one Rust protocol core:

- F* for functional correctness of state transitions, transcript construction, bounds, key lifecycle, error behaviour, and panic freedom.
- ProVerif for trace properties in an active-attacker model: secrecy, authentication, identity binding, replay resistance, session separation, compromise scenarios, and forward secrecy.

F* is the primary extraction target. The hax ProVerif backend is experimental, so its models and generated output need closer review, but it addresses a different class of questions than functional verification. Neither backend is expected to prove the cryptographic primitives themselves.

The intended boundary is:

```text
Cap'n Proto / libsodium / serde / OS RNG / persistence
                         |
                      adapters
                         |
                         v
              beaconcrypt-protocol-core
              +-------------------------+
              | typed PQXDH states      |
              | symmetric ratchet state |
              | transcript construction |
              | sequence/replay logic   |
              | abstract crypto calls   |
              +-------------------------+
                    |             |
                  hax           hax
                    |             |
                    v             v
                   F*          ProVerif
             functional proof  attacker model
```

A target repository layout is:

```text
crates/protocol-core/
  Cargo.toml
  src/
    lib.rs
    types.rs
    crypto.rs
    pqxdh.rs
    ratchet.rs
    record.rs
  proofs/
    fstar/
      extraction/       # generated; do not edit
      Spec.fst
      Lemmas.fst
    pro-verif/
      extraction/       # generated; do not edit
      crypto.pvl
      environment.pv
      queries.pv
```

The first extraction slice may be smaller than this layout. In particular, a single total ratchet transition is enough for the initial hax-to-F* smoke test.

## The extractable production core

The initial production seams were the ratchet state and operations in
[`src/shared.rs`](../src/shared.rs), the frame encryption/decryption logic in
that file, and the PQXDH role transitions in
[`src/pqxdh.rs`](../src/pqxdh.rs). Stages 1 through 5 moved their deterministic
control decisions into the protocol core while leaving concrete cryptography
and wire translation in those adapters. Further moves should remain incremental
rather than attempting to extract the whole crate.

The core boundary is limited to deterministic protocol decisions:

- role and session states;
- key and nonce derivation requests;
- exact transcript, associated-data, and commitment inputs;
- sequence-number and receive-window rules;
- skipped-key bookkeeping;
- key consumption and deletion decisions;
- accepted and rejected state transitions.

The following remain in adapters outside the proof core:

- Cap'n Proto parsing and serialization;
- libsodium and ML-KEM calls;
- entropy acquisition;
- serde and persistence formats;
- zeroization mechanics and FFI/language bindings.

This division does not make those adapters trusted without review. Instead, it gives them a narrow obligation: translate validated wire data to core types, implement abstract primitive operations, and apply the transition result without changing its protocol meaning.

### Represent state explicitly

PQXDH now uses role-specific core typestates instead of making protocol
transitions depend on an `is_beacon` flag plus unrelated optional fields. The
public boolean constructor remains for API compatibility, but it selects an
internal role enum once; the transition code then matches the corresponding
state. The core states include:

```rust
pub struct BeaconFresh { /* server key assignment */ }
pub struct BeaconInitSent { /* identity tied to one InitKex */ }
pub struct BeaconRegistrationCandidate { /* validated proposed session */ }
pub struct AuthenticatedBeaconRegistration { /* authenticated assigned key ID */ }
pub struct BeaconEstablished { /* committed server and assigned IDs */ }
pub struct BeaconAborted;

pub struct ServerState { /* last allocated key ID */ }
pub struct ServerBinding { /* server identity key and key ID */ }
pub struct RegistrationId { /* beacon identity and one-time public key */ }
pub struct PendingServerRegistration { /* validated response inputs */ }
pub struct ServerRegistrationCandidate { /* previous and proposed state */ }
pub struct EstablishedPeer { /* committed peer metadata */ }
```

Transitions consume the old state and return the new state:

```rust
pub fn beacon_start(
    state: BeaconFresh,
    inputs: BeaconStartInputs,
    coins: BeaconCoins,
) -> BeaconStart;

pub fn beacon_prepare_finish(
    state: BeaconInitSent,
    inputs: &BeaconFinishInputs,
) -> Result<BeaconRegistrationCandidate, RegistrationError>;

pub fn authenticate_registration_key_id_binding(
    candidate: BeaconRegistrationCandidate,
    authenticated_binding: [u8; 8],
) -> Result<AuthenticatedBeaconRegistration, RegistrationError>;

pub fn beacon_commit(
    authenticated: AuthenticatedBeaconRegistration,
) -> BeaconEstablished;

pub fn server_accept(
    state: ServerState,
    init: VerifiedInitKex,
    registration_status: RegistrationStatus,
    server_binding: ServerBinding,
    coins: ServerCoins,
    secrets: &PqxdhSharedSecrets,
) -> Result<(ServerState, PendingServerRegistration), RegistrationError>;

pub fn server_prepare_commit(
    state: ServerState,
    pending: PendingServerRegistration,
    current_server_binding: ServerBinding,
    key_id_availability: KeyIdAvailability,
) -> Result<ServerRegistrationCandidate, RegistrationError>;

pub fn server_commit(
    candidate: ServerRegistrationCandidate,
) -> (ServerState, EstablishedPeer);
```

Randomness is explicit input. This makes a transition deterministic and lets proofs quantify over the generated material without modelling the operating system RNG.

Some small core control values are copyable logical descriptors. Single-use
registration is enforced by the private production enum replacing `Fresh` with
`InitSent`, rather than by claiming that the standalone descriptor is affine.

Ratchet transitions should also be owned and total:

```rust
pub fn send(
    state: RatchetState,
    message: Plaintext,
    peer: PeerId,
) -> Result<(RatchetState, CryptoFrame), RatchetError>;

pub fn receive(
    state: RatchetState,
    frame: CryptoFrame,
) -> (RatchetState, Result<Plaintext, RatchetError>);
```

Returning the receive state on both success and failure is intentional. The current implementation can advance the receive chain and cache intermediate keys before commitment or AEAD verification. An admissible, correctly sized forged future frame can therefore change state even when it is rejected. The implementation tests this behaviour in [`tests/protocol.rs`](../tests/protocol.rs#L173) (see `assert_invalid_future_frames_cannot_grow_receive_cache` and `invalid_future_frames_cannot_grow_receive_cache_beyond_gap`). The specification must describe the actual transition rather than assuming that every rejection is state-neutral.

For extraction, replace `HashMap` in the core with a bounded, packed sequence whose uniqueness and size are visible to the prover. Restoration can require sorted input even though successful receive uses swap-removal and does not preserve entry order. The adapter can use a different physical representation only if its refinement to the verified representation is established.

### Keep the core on production paths

After each extraction-sized move, the existing `BeaconCryptPqxdh` API must delegate to the new core. Existing known-answer and protocol tests must continue to exercise that path. A proof-only reimplementation is out of scope because its correspondence to production code would become a new, unproved assumption.

The low-level ratchet methods currently exposed from [`src/shared.rs`](../src/shared.rs) can bypass invariants expected at the higher-level protocol API. Either narrow their visibility or state theorem preconditions so that verified traces are explicitly limited to calls through the high-level API.

## Primitive abstraction boundary

Primitive implementations are opaque. Protocol composition remains visible.

Opaque operations include:

- ChaCha20-Poly1305 encryption and authentication internals;
- BLAKE2b compression and collision resistance;
- HKDF internals;
- X25519 and Ed25519 arithmetic;
- ML-KEM encapsulation and decapsulation internals;
- entropy generation and secret-memory erasure.

The extractable code must still expose:

- algorithm and key-type tags;
- the exact buffers signed or verified;
- the order of all four DH contributions;
- KDF domain-separation labels and input order;
- associated-data and commitment fields in their exact order;
- key, nonce, peer ID, direction, and sequence-number use;
- the points at which protocol state makes a key unavailable.

### F* assumptions

Assume only laws needed by the protocol proof:

- honest DH agreement;
- KEM encapsulation/decapsulation correctness;
- honest signature verification;
- AEAD open/seal correctness for the same key, nonce, plaintext, and associated data;
- KDF determinism and separation between distinct protocol labels.

Do not assume general hash injectivity. The functional proof should establish that beaconcrypt supplies the intended fixed-size fields, in the intended order, to the BLAKE2b commitment. Security of that commitment remains an explicit primitive assumption.

### ProVerif model

Represent the primitives with symbolic constructors and destructors, and annotate the protocol entry points and messages for extraction. hax provides protocol-oriented hooks such as `protocol_messages`, `process_init`, `process_read`, `process_write`, `pv_constructor`, and `pv_handwritten`; any handwritten fragments become part of the trusted model and must be inventoried and reviewed.

The model should include events for session initiation, acceptance, sending, receiving, key deletion, and compromise. These events make agreement and correspondence queries precise.

## Proof inventory

### F*: implementation and state-machine properties

PQXDH:

- An honest beacon and server compute the same PQXDH root.
- Both sides concatenate padding, DH1, DH2, DH3, DH4, and the KEM secret in the implemented order and use `PQXDH_INFO`.
- The signed prekey, one-time key, and post-quantum key carry authenticated, disjoint type tags.
- Both roles construct identical, ordered associated data.
- The response's assigned key ID is encoded as an exact little-endian `u64`
  inside the AEAD-authenticated initial payload, and only a candidate with a
  matching authenticated prefix can commit.
- A server rejects a registration identifier that its adapter classifies as
  consumed, where the identifier is the exact beacon identity and signed
  one-time public key rather than raw wire bytes or a hash.
- Server key-ID allocation cannot wrap and explicitly rejects an occupied next
  identifier.
- Beacon-send/server-receive and server-send/beacon-receive ratchets are initialized to matching states.
- Peer, counter, and ratchet publication commit atomically. Successful server
  acceptance consumes replay history earlier and monotonically, even if later
  response construction fails.

Symmetric ratchet and records:

- Send and receive counters are monotonic, start at one, and cannot wrap.
- Skipped receive-key indices are unique.
- The skipped-key cache contains at most `RATCHET_MAX_GAP` entries (currently 50).
- A receive request beyond the permitted window is state-neutral.
- Successful receive removes exactly the consumed message key, so replay is rejected.
- Failed authentication retains the candidate key when retry is part of the intended semantics.
- A transition for peer A leaves peer B's ratchet unchanged.
- Successful send makes the consumed message key logically unavailable.
- The commitment input is exactly `(key, nonce, associated data, AEAD tag, sequence, sender ID)` with unambiguous fixed-size encodings.
- Every accepted, bounded input follows a panic-free path.

Persistence is a separate boundary. Either prove that imported state validation re-establishes every core invariant, or explicitly exclude unvalidated imported states from the theorem's initial-state set.

### ProVerif: protocol trace properties

- Secrecy of the initial application message and subsequent application messages.
- Injective agreement on server identity, beacon identity, assigned key ID, transcript, and derived root.
- Accepted plaintext implies a preceding honest send for the same session, direction, sequence, sender, and plaintext.
- Replay resistance.
- Unknown-key-share and cross-peer resistance.
- Independence of concurrent sessions.
- Forward secrecy following a later compromise of live chain state.

Forward secrecy needs a precise statement. Send keys are deleted immediately, but skipped receive keys remain cached for out-of-order delivery. Compromise of a receiver can reveal cached skipped keys. The defensible theorem is secrecy of a message after its message key has become logically unavailable, not secrecy of every message whose sequence number is below the current counter.

The symmetric ratchet never mixes fresh entropy into an established chain, so it deliberately provides no post-compromise security. This should be recorded as a negative result, not formulated as an expected theorem.

ProVerif establishes these results only in the stated symbolic model. It does not establish computational security of the cryptographic primitives.

## Closed counterexamples

Three regression tests in [`tests/protocol.rs`](../tests/protocol.rs) track
executable counterexamples to properties that a proof might otherwise claim:

1. `beacon_rejects_tampered_registration_key_id`: Stage 5 authenticates the
   assigned ID as the fixed-width prefix of the initial encrypted payload.
2. `beacon_generates_only_one_registration_bundle`: Stage 4 closes this
   counterexample through the consuming `BeaconFresh` to `BeaconInitSent`
   production transition, and the regression is now mandatory.
3. `server_rejects_replayed_registration_bundle`: Stage 5 persistently consumes
   a semantic registration identifier on the first successful server
   acceptance.

All three regressions are now mandatory and passing. Stage 5 also completes the
supporting allocation changes:

- the replay key is the fixed 64-byte semantic tuple `(beacon identity,
  one-time X25519 public key)`, so alternate encodings of the same `InitKex`
  cannot bypass lookup and no hash-collision assumption is introduced;
- consumed identifiers survive export and restore and are not removed with a
  peer entry;
- checked increment rejects exhaustion at `u64::MAX`, while an explicit
  availability input rejects collision with the next peer-map ID.

This closes the executable counterexamples; it does not itself prove the later
F* agreement lemmas or ProVerif correspondence queries.

## Staged rollout

1. **Complete:** create the isolated core crate. Extract one total ratchet transition with hax and typecheck the generated F* without `--lax`. Keep this first slice intentionally small.
2. **Complete:** move the symmetric-ratchet control state into the core. Prove counter, bounds, replay, retry, peer-isolation, and key-consumption properties.
3. **Complete:** make the production API delegate to the core and run the existing unit, protocol, and known-answer tests through it.
4. **Complete:** move PQXDH into role-specific typestates with explicit randomness and atomic state commits. This stage also makes `InitKex` generation single-use.
5. **Complete:** close the three-counterexample milestone with authenticated key-ID binding, persistent server registration replay rejection, collision-safe checked allocation, and mandatory regressions.
6. Add the F* PQXDH agreement, transcript, associated-data, and initialization proofs.
7. Add ProVerif processes, events, primitive equations, compromise scenarios, and queries.
8. Pin rustc, hax, F*, Z3, and ProVerif and run extraction plus proofs in CI.
9. Maintain a reviewed inventory of every opaque Rust function, assumed primitive law, generated-code exception, and handwritten backend fragment.

Each stage should leave the existing crate buildable and tested. Extraction output should be reproducible and generated directories should never contain hand-maintained lemmas.

## Initial extraction acceptance criteria

Step 1 is complete when the repository contains:

- a standalone Rust core crate that does not depend on Cap'n Proto, libsodium, serde, bindings, or generated code;
- a small, deterministic, total ratchet transition using hax-supported Rust;
- a command or script that regenerates its F* output;
- an F* check that succeeds without lax checking;
- a pinned or clearly documented compatible toolchain;
- a CI-friendly failure mode when extraction or F* checking fails.

The transition need not yet implement the complete production ratchet. Its purpose is to validate the crate boundary and end-to-end hax/F* toolchain before moving stateful production logic.

### Step 1 implementation

The initial slice now lives in [`crates/protocol-core`](../crates/protocol-core). It is a dependency-free `no_std` workspace member containing a pure sending-counter transition with explicit exhaustion behaviour. hax extracts only that entry point and its transitive dependencies to [`proofs/fstar/extraction`](../crates/protocol-core/proofs/fstar/extraction).

Run the complete check from the core crate:

```sh
make verify
```

The target enters hax's revision-pinned `ci-examples` Nix shell, regenerates the F* module, computes and checks its proof-library dependencies, and verifies the extracted module without `--lax`. `make check-generated` adds a tracked-output diff check for CI. At Step 1 this slice was toolchain scaffolding and was not yet used by the production ratchet; production delegation followed in Step 3.

### Step 2 implementation

The core now contains the full symmetric-ratchet control state rather than only a send counter. It deliberately models concrete KDF results as logical, sequence-indexed key capabilities, leaving HKDF, ChaCha20-Poly1305, and secret byte storage opaque.

The state machine includes:

- monotonic send and receive counters with state-neutral exhaustion;
- receive admission using both the 50-message forward-gap limit and the total outstanding-key capacity;
- a fixed 50-slot receive cache with unique logical sequence ownership;
- separate planning and one-step receive derivation, so an adapter performs exactly one opaque KDF call for each admitted step;
- authentication completion that retains the exact key on failure and removes only the target on success;
- one-use send-key capabilities;
- checked restoration from sorted, unique, bounded cached sequences;
- pointwise peer transitions that return non-selected peers unchanged.

The fixed array is intentional. Several convenient dynamic-collection operations are assumptions in the current hax proof libraries; direct array append and validated swap removal keep the key-lifecycle semantics visible in generated F*. The strict lemma module proves the Step 2 property inventory against that generated code.

At the end of this stage, the production `RatchetManager` remained unchanged. Step 3 therefore had to make the core state authoritative, maintain equality between the concrete `recv_past` map and the core's logical sequence set, and reconstruct the core through its checked restoration typestate.

### Step 3 implementation

The detailed implementation record is in
[`formal-verification-stage-3.md`](formal-verification-stage-3.md).

The production crate now depends on `beaconcrypt-protocol-core`, and `RatchetManager` delegates its counter, receive-admission, key-lifecycle, and restoration decisions to the extracted state machine. The core `RatchetState` is authoritative: the adapter derives one concrete KDF output for each admitted core step and maintains the refinement invariant

```text
keys(recv_past) == logical_receive_sequences(core_state)
```

Authentication failure retains the same logical and concrete receive key, while successful authentication removes exactly that key from both representations. Each allocated logical send capability accompanies its concrete message key until the adapter consumes it with `finish_send`, including encryption-failure paths.

Persistence keeps the existing six-field `RatchetManager` format: `send_key`, `recv_key`, `send_past`, `send_ctr`, `recv_past`, and `recv_ctr`. The counters are serialized from the authoritative core state; no duplicate core representation is written. During import, the adapter sorts the concrete receive-key sequences and rebuilds the core exclusively through `start_restore`, `restore_receive_key`, and `finish_restore`. States with more than 50 outstanding receive keys are rejected rather than admitted outside the verified state space.

The verified production trace for this stage is restricted to `BeaconCryptPqxdh` operations through the high-level `encrypt_message` and `decrypt_message` methods, starting from a fresh or successfully validated state without rollback. Direct calls to the low-level ratchet/key helpers are outside that trace. `SendKey` is a logical availability marker rather than an affine Rust type, so the one-use claim relies on the production adapter retaining one marker per concrete key and removing both together; cloning or restoring a state with a pending send key and then using both forks is excluded. Selection from the production peer map is also an adapter refinement obligation: the core proves the pointwise peer frame rule, while unique peer lookup and the unchanged-state behavior of non-selected map entries remain covered by implementation validation and protocol regression tests rather than extraction.

### Step 4 implementation

The detailed implementation record is in
[`formal-verification-stage-4.md`](formal-verification-stage-4.md).

The protocol core now owns deterministic PQXDH composition: disjoint encoded
key tags, the exact padding and DH/KEM root input, ordered associated data,
role-dependent ratchet directions, and explicit beacon and server registration
states. Random key generation and primitive calls remain in the adapter, which
passes their public outputs and shared-secret results to deterministic core
transitions.

The production provider stores an internal role enum. Beacon material advances
through fresh, `InitKex` sent, established, or aborted states, so a registration
bundle is emitted once and every finish failure is terminal. On success the
beacon publishes its assigned identity, associated data, and staged ratchet only
after authenticating the initial ciphertext.

The server validates into a pending registration and builds its proposed peer
on a fresh ratchet outside the live peer map. It encrypts the initial message
and serializes the complete response before committing the core counter, public
counter, and peer map. A failure discards the candidate and leaves exported
server state unchanged. The pending production token is opaque and consumed by
the response builder, which obtains response public material and associated
data from the core candidate. It also records the accepting server's identity
public key and identity key ID, and candidate preparation rejects use by a
differently bound provider without changing live state.

The Stage 4 correspondence claim covers high-level registration transitions;
direct compatibility setters, peer-map mutation, low-level ratchet calls,
rollback, and cloned live provider state remain explicit preconditions outside
that trace.

The pinned hax item list extracts these PQXDH transitions to
`Beaconcrypt_protocol_core.Pqxdh.fst`, and the existing strict F* target
checks that generated module and its generated safety obligations without
`--lax`. No PQXDH semantic lemma module is part of Stage 4: agreement,
transcript, associated-data, and initialization proofs remain Step 6 work.

### Step 5 implementation

The detailed implementation record is in
[`formal-verification-stage-5.md`](formal-verification-stage-5.md).

The server now derives a canonical 64-byte registration identifier from the
verified beacon identity and signed one-time public key. The production adapter
looks it up in a persistent consumed set, passes an explicit fresh/consumed
classification to the core, and inserts it before returning a successful
pending token. This consumption is deliberately irreversible: dropping the
token, failing response construction, deleting the peer, or exporting and
restoring the server does not make the registration reusable. Persistence
serializes the set in sorted order and rejects missing, malformed, duplicate,
or structurally incomplete replay histories with fewer entries than committed
peers.

The server prefixes the initial application plaintext (or registration witness)
with the core-provided little-endian assigned key ID before AEAD encryption. The
beacon authenticates the ciphertext, separates the fixed eight-byte prefix,
and must obtain `AuthenticatedBeaconRegistration` from the core before
`beacon_commit` is callable. The prefix is stripped before the original
application plaintext is returned. This keeps the established 153-byte
associated-data and CTX commitment formats unchanged.

Allocation now uses the core's checked `server_next_key_id`; exhaustion at
`u64::MAX` is state-neutral, and `server_prepare_commit` requires an explicit
availability classification for the exact proposed ID. The production adapter
derives that classification from the peer map. The low-level compatibility
allocator is fallible and delegates to the same checked rule, so no wrapping
allocation path remains.

Replay history is the one intentional exception to Stage 4's statement that
server acceptance leaves exported state unchanged. Counter, peer, and ratchet
publication remain transactional during response construction, but a valid
accepted `InitKex` consumes its replay marker immediately. The history is
currently unbounded and persistence snapshots created before Stage 5 are
rejected because silently defaulting a missing history would reopen replay.

The new public core transitions are included in the pinned extraction. The
generated PQXDH module and its safety obligations typecheck strictly without
`--lax`; semantic PQXDH agreement, transcript, associated-data, and
initialization lemmas remain Step 6 work.

## Toolchain findings and CI policy

A direct extraction smoke test against the current root crate is not viable with the locally installed tools. The installed hax 0.3.7 toolchain uses a Rust 1.93 nightly, while [`Cargo.toml`](../Cargo.toml) declares Rust 1.96. Bypassing that version check exposes use of newer `slice_as_array` functionality and then reaches a hax frontend panic while processing generated Cap'n Proto code.

This supports the isolated-core approach: it avoids generated schemas and FFI-heavy dependencies, and it can remain within the Rust subset supported by the pinned hax release. It is not evidence that the application should lower its Rust requirement.

CI should pin all proof tools together and fail on:

- extraction errors or unexpected generated diffs;
- F* checking performed with `--lax`;
- admitted or newly unproved obligations;
- ProVerif queries reported as false, unproved, or inconclusive;
- an unreviewed change to the opaque/assumption inventory.

The proof artifact must state the exact versions of rustc, hax, F*, Z3, and ProVerif used to produce it.

## What a successful result means

The completed work should justify statements about the implemented PQXDH and symmetric-ratchet protocols under explicit primitive assumptions. It should not be presented as a proof of libsodium, ML-KEM, serialization safety, zeroization, persistence, binding code, the operating-system RNG, or computational reductions for the primitives. Those components remain separate implementation and audit obligations.
