<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification plan

## Goal and scope

The goal is to prove protocol-level properties of beaconcrypt from the Rust code that is used in production. The proof target is the composition and state-machine logic for PQXDH and the symmetric ratchet, not the implementation security of ChaCha20-Poly1305, BLAKE2b, HKDF, X25519, Ed25519, or ML-KEM.

This document complements the [protocol description](protocol.md) and [threat model](threat_model.md). It describes an extraction boundary, the responsibilities of each prover backend, the intended theorem inventory, and a staged path to a continuously checked proof.

For a plain-language audit of the properties actually checked by the current
proof corpus, their assumptions, and the limits of the resulting security
claims, see [What beaconcrypt's formal verification proves](formal-verification-analysis.md).

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
[`src/pqxdh.rs`](../src/pqxdh.rs). Stages 1 through 7 moved their deterministic
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

- algorithm/type markers and field-role markers;
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
- The signed X25519 prekey and one-time key encode authenticated, disjoint
  `[type: u8, role: u8, key]` layouts, with type and role markers drawn from
  disjoint byte domains; the post-quantum key carries its authenticated type.
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

Those original three regressions are mandatory and passing. Stage 5 also completes the
supporting allocation changes:

- the replay key is the fixed 64-byte semantic tuple `(beacon identity,
  one-time X25519 public key)`, so alternate encodings of the same `InitKex`
  cannot bypass lookup and no hash-collision assumption is introduced;
- consumed identifiers survive export and restore and are not removed with a
  peer entry;
- checked increment rejects exhaustion at `u64::MAX`, while an explicit
  availability input rejects collision with the next peer-map ID.

Stage 7's active-attacker model exposed a fourth counterexample: because the
prekey and one-time key formerly signed the same `[X25519 type, key]` layout,
an attacker could exchange or duplicate those two valid signed fields. The
server would accept a ghost registration under a different semantic ID, while
the beacon could not authenticate the response. The core now encodes prekeys
as `[0x04, 0x80, key]` and one-time keys as `[0x04, 0x81, key]`; core and
adapter regressions reject both substitution forms, and the regenerated F*
lemmas prove the exact layouts and cross-role rejection.

This closes the executable counterexamples. Stage 6 proves the core-side exact
identifier, binding, status, allocation, and conditional role correspondence
under explicit adapter preconditions. Truthful persistent-set refinement and
the production single-use transition remain adapter and regression-test
obligations. Stage 7 adds the active-attacker correspondences under the
explicit one-owner, non-rollback replay refinement described below.

## Staged rollout

1. **Complete:** create the isolated core crate. Extract one total ratchet transition with hax and typecheck the generated F* without `--lax`. Keep this first slice intentionally small.
2. **Complete:** move the symmetric-ratchet control state into the core. Prove counter, bounds, replay, retry, peer-isolation, and key-consumption properties.
3. **Complete:** make the production API delegate to the core and run the existing unit, protocol, and known-answer tests through it.
4. **Complete:** move PQXDH into role-specific typestates with explicit randomness and atomic state commits. This stage also makes `InitKex` generation single-use.
5. **Complete:** close the three-counterexample milestone with authenticated key-ID binding, persistent server registration replay rejection, collision-safe checked allocation, and mandatory regressions.
6. **Complete:** add the F* PQXDH agreement, transcript, associated-data, initialization, and assigned-ID correspondence proofs.
7. **Complete:** add ProVerif processes, events, primitive equations, compromise scenarios, strict result gates, and active-attacker queries.
8. **Complete:** pin rustc, hax, F*, Z3, and ProVerif and run extraction plus proofs in CI.
9. **Complete:** maintain a reviewed inventory of every opaque Rust function, assumed primitive law, adapter refinement, proof-library assumption, generated-code exception, and handwritten backend fragment, with a CI drift gate.

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
key type/role markers, the exact padding and DH/KEM root input, ordered associated data,
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
`--lax`. No PQXDH semantic lemma module was part of Stage 4; Stage 6 now adds
the agreement, transcript, associated-data, and initialization proofs.

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
`--lax`. Stage 6 now supplies the semantic PQXDH agreement, transcript,
associated-data, initialization, and assigned-ID lemmas that were intentionally
deferred here.

### Step 6 implementation

The detailed implementation record is in
[`formal-verification-stage-6.md`](formal-verification-stage-6.md).

The Stage 5 extraction was reviewed before adding semantic claims. Its fixed
copy loops reached F* through a library operation without a useful
postcondition, `u64::to_le_bytes` was opaque in the pinned model, and derived
whole-`ServerBinding` equality introduced a local generated assumption. The
core now uses specified fixed-range slice updates, constructs LE64 bytes from
explicit shifts and narrowing casts, and compares the two server-binding fields
directly. Compile-time assertions tie the literal proof ranges and production
KDF slices to the public protocol-core sizes. Production-used candidate
ratchet and binding accessors are also included in extraction.

The strict handwritten PQXDH module proves exact tagged-key construction and
validation, exact semantic registration IDs, the six-segment root transcript
and zero-DH rejection, exact associated data, complementary role ratchets,
authenticated assigned-ID correspondence, checked nonwrapping allocation,
binding and collision rejection, and commit/abort state shape. A composed
post-validation honest-run theorem relates both role transitions through their
authenticated and committed core peer IDs. Concrete HKDF output, ratchet byte
slicing, and atomic peer-map publication remain adapter obligations.

Agreement is deliberately conditional. The adapter must establish pairwise
X25519 and ML-KEM secret agreement, authenticate the same role identities,
pass the assigned-ID bytes from a successful AEAD open, refine `Fresh` and
`Available` from the persistent set and peer map, apply deterministic HKDF to
the verified input and labels, and maintain non-rollback single-owner server
state. Concrete primitives, wire translation, persistence, replicas,
zeroization, and low-level compatibility mutation remain outside the theorem.
The generated and handwritten modules contain no local `assume` or `admit`,
and the target checks them without `--lax`.

### Step 7 implementation

The detailed implementation record is in
[`formal-verification-stage-7.md`](formal-verification-stage-7.md).
That record is historical; the attacker-owned-registration extension described
below is tracked by the current analysis and canonical trust-boundary inventory.

Stage 7 reviewed the complete Stage 6 commit `493a23f` before adding a trace
model. The ProVerif backend now extracts the production `InitKex`, verified
registration, registration-ID, root-input, assigned-ID-binding, and associated
data boundary into
[`proofs/pro-verif/extraction/lib.pvl`](../crates/protocol-core/proofs/pro-verif/extraction/lib.pvl).
The three proof-visible production functions use narrowly scoped backend
replacements whose constructor arguments are the exact layouts already checked
by F*. Processes, events, the active network, primitive equations, and queries
remain handwritten because hax 0.3.7 does not generate top-level ProVerif
processes; every such fragment is inventoried in the Stage 7 record.

Active-attacker analysis found that the two X25519 fields had identical signed
encodings. Stage 7 therefore extends the production core, rather than assuming
field position in the model: X25519 payloads are now 34 bytes with exact
`[type, role, key]` layouts. Type markers occupy the low half of the `u8`
domain, while the prekey and one-time roles are `0x80` and `0x81`. The server
validates the expected role after signature verification. The Stage 6 F*
extraction and handwritten lemmas were regenerated and extended to prove the
new byte positions, round trips, marker-domain disjointness, and cross-role
rejection. Production tests exchange and duplicate the real signed Cap'n Proto
fields and require both inputs to fail.

The symbolic environment contains replicated fresh honest beacons, replicated
attacker-owned beacons that disclose all four private keys, an active public
network, ideal signature/DH/KEM/KDF/AEAD/commitment primitives, a bounded
honest-session record prefix, and a one-owner non-rollback replay process. The
replay owner returns `Fresh` exactly once and `Consumed` thereafter, including
after the explicit abort path. It is keyed by the fresh honest beacon identity
but records the publicly parsed transcript and semantic ID. Under the existing
single-bundle-per-fresh-identity typestate this refines the production semantic
ID set while ensuring that a future field-substitution regression falsifies the
origin correspondence instead of being hidden by private proof data. If
production ever permits multiple bundles under one honest beacon identity, the
signed fields must additionally share an authenticated bundle nonce or
ordered-bundle signature before extending this theorem.

The baseline model reports all eleven security queries true: five honest-task
secrecy queries; injective acceptance/origin, acceptance/consumption,
consumption/origin, abort/consumption, and beacon/server commit
correspondences; and bounded record send/receive correspondence with exact
session, direction, sequence, sender, receiver, and plaintext. Seven separate
non-vacuity queries deliberately report false negations. Five demonstrate the
original honest acceptance, replay rejection, abort, beacon-commit, and
record-receive traces. A sixth reaches a valid attacker-owned registration
response, and the seventh finds the deliberate attack on its private task
canary, proving that the malicious session is cryptographically usable rather
than blocked by proof instrumentation. The honest and malicious server paths
use private origin tables solely to model the threat model's recipient-specific
task routing; those tables are not production authorization mechanisms. The
malicious path treats every request as fresh, so no malicious-identity replay or
availability result is claimed.

The synchronized late-compromise model records the intended qualification.
The initial message and an already-consumed advanced receive message remain
secret. A skipped receive key still present in the cache is exposed, and the
live receive and send chains expose future traffic in both directions. Those
last three false secrecy results are required negative results documenting
cached-key exposure and the deliberate absence of post-compromise security.
The bounded ProVerif record process proves authentication and sequence binding;
general duplicate receive-key consumption remains the Stage 2 F* ratchet
theorem because this trace prefix has one receive program point per sequence.

`make verify` now regenerates and checks both backends in the revision-pinned
hax shell. Its result parser rejects timeouts, missing or substituted queries,
unexpected true/false classifications, and every unproved or inconclusive
security query. `make check-generated` covers both generated directories.

### Step 8 implementation

The detailed implementation record is in
[`formal-verification-stage-8.md`](formal-verification-stage-8.md).

The repository now owns [`flake.nix`](../flake.nix) and
[`flake.lock`](../flake.lock). The flake extends hax's revision-pinned proof
shell with the Rust nightly declared by that same hax revision and with the Z3
package supplied by the locked F* input. This closes Stage 7's ambient-tool
gap: its shell pinned hax, F*, and ProVerif but omitted rustc, so extraction
used whichever compiler was already on `PATH`.

Before either backend runs, `make check-toolchain` checks the exact rustc,
Cargo, hax, F*, Z3, and ProVerif identities. Nix is invoked with
`--no-update-lock-file`, and both cargo-hax calls use Cargo's `--locked` mode.
After F* extraction, a separate policy gate rejects `assume` or `admit` in
repository-owned F* modules and rejects lax or admitted-query checker flags.
The reviewed bundle is rustc 1.93.0-nightly (`843f8ce2e`), Cargo
1.93.0-nightly (`636800288`), hax 0.3.7 at revision `5b0ba8b`, F*
`2025.10.06~dev` at revision `7b34738`, Z3 4.15.3, and ProVerif 2.05.
The pinned nightly is scoped to the isolated proof shell; it does not lower or
override the production crate's Rust 1.96 requirement.

These are latest-compatible rather than merely copied upstream pins. The Stage
8 audit exercised every later F* release available on 2026-08-02 and found
each incompatible with hax's proof libraries, while the newest Z3 bundled by
the selected F* release, 4.15.3, discharged the complete proof corpus. The
detailed record contains the failure boundary and the rationale for each
retained dependency.

The dedicated `formal-verification.yml` GitHub Actions workflow installs Nix,
uses the public hax/F*/Z3 caches read-only, and runs
`make -C crates/protocol-core check-generated` on main-branch pushes, pull
requests targeting `main`, merge-queue checks, and manual dispatch. The job has
read-only repository permission and a 60-minute bound. It therefore
regenerates both backends, runs every strict Stage 2/6 F* and Stage 7 ProVerif
gate, and rejects tracked or untracked generated-artifact drift.

Re-extraction with the pinned Rust nightly is byte-identical to the Stage 7
artifacts. No theorem, primitive equation, process, or expected ProVerif result
changed in Stage 8.

### Step 9 implementation

The detailed implementation record is in
[`formal-verification-stage-9.md`](formal-verification-stage-9.md), and the
canonical maintained inventory is
[`crates/protocol-core/proofs/trusted-boundary.md`](../crates/protocol-core/proofs/trusted-boundary.md).

Stage 9 inventories the repository-owned production wrappers around entropy,
Ed25519, Ed25519/X25519 conversion, X25519, ML-KEM, HKDF,
ChaCha20-Poly1305, BLAKE2b, wire translation, persistence, allocation, and
zeroization. It separately records the primitive laws used by the conditional
F* results and ideal ProVerif theory, every concrete-to-logical adapter
refinement, the pinned hax/F*/ProVerif trust surface, all generated-code
exceptions, and every handwritten F* or ProVerif review unit.

`make check-inventory` validates a category/path/SHA-256 manifest and derives
the complete production Rust/schema, protocol-core Rust, generated-backend,
and handwritten-backend file sets. It also enforces the three and only three
ProVerif replacements; the generated type/default/converter/error baseline;
the single permitted generated converter used by handwritten code; the
handwritten primitive, event, process, and query counts; the absence of hax
opaque annotations; and the absence of the previously rejected generated F*
constructs.

The inventory check runs after regeneration in both the complete and
ProVerif-only locked-shell paths. The existing CI command therefore fails when
a monitored production wrapper, extraction selector, handwritten proof/model,
result classifier, generated artifact, tool control, or inventory policy
changes without an explicit reviewed-baseline update. The hashes are
deliberately conservative review tripwires; passing the mechanical gate does
not itself prove that a human review was adequate.

Stage 9 does not add a theorem, change a symbolic equation or query, or alter
production behavior. All limitations and conditional refinements recorded in
Stages 3 through 8 remain in force.

## Toolchain findings and CI policy

A direct extraction smoke test against the current root crate is not viable with the locally installed tools. The installed hax 0.3.7 toolchain uses a Rust 1.93 nightly, while [`Cargo.toml`](../Cargo.toml) declares Rust 1.96. Bypassing that version check exposes use of newer `slice_as_array` functionality and then reaches a hax frontend panic while processing generated Cap'n Proto code.

This supports the isolated-core approach: it avoids generated schemas and FFI-heavy dependencies, and it can remain within the Rust subset supported by the pinned hax release. It is not evidence that the application should lower its Rust requirement.

CI pins all proof tools together and fails on:

- extraction errors or unexpected generated diffs;
- F* checking performed with `--lax`;
- admitted or newly unproved obligations;
- baseline ProVerif queries reported as false, unproved, or inconclusive, or
  reachability/compromise queries that differ from their reviewed expected
  classifications;
- tracked or untracked generated output that differs from the reviewed
  artifacts;
- any monitored opaque-function, primitive-law, adapter-refinement,
  proof-library, generated-exception, or handwritten-fragment inventory drift
  that lacks an explicit reviewed-baseline update.

The proof artifact must state the exact versions of rustc, hax, F*, Z3, and ProVerif used to produce it.
The Stage 9 manifest also fingerprints the selectors and locked tool/CI
controls that define that artifact.

## What a successful result means

The completed work should justify statements about the implemented PQXDH and symmetric-ratchet protocols under explicit primitive assumptions. It should not be presented as a proof of libsodium, ML-KEM, serialization safety, zeroization, persistence, binding code, the operating-system RNG, or computational reductions for the primitives. Those components remain separate implementation and audit obligations.
