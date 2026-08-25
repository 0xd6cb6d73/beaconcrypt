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

Use complementary verification layers around one Rust protocol core:

- F* for functional correctness of state transitions, transcript construction, bounds, key lifecycle, error behaviour, and panic freedom.
- ProVerif for symbolic trace properties under active and passive classical or quantum-capability threat models: secrecy, authentication, identity binding, replay resistance, session separation, compromise scenarios, and forward secrecy.
- SSProve for probabilistic games, event reductions, and advantage reasoning under explicit deterministic and primitive-security contracts.

F* is the primary extraction target. The hax ProVerif backend is experimental, so its models and generated output need closer review, but it addresses a different class of questions than functional verification. Direct hax-to-SSProve extraction is currently rejected by the reviewed safety gate, so the checked CTX event theorem consumes an explicit deterministic contract intended for cross-prover discharge. None of these layers is expected to prove the cryptographic primitives themselves.

The intended boundary is:

```text
Cap'n Proto / libsodium / serde / OS RNG / persistence
                         |
                      adapters
                         |
                         v
              beaconcrypt-core
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
beaconcrypt-core/
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

The initial production seams were the ratchet state and frame encryption/decryption operations now in [`beaconcrypt/src/ratchet.rs`](../beaconcrypt/src/ratchet.rs), and the PQXDH role transitions in [`beaconcrypt/src/pqxdh.rs`](../beaconcrypt/src/pqxdh.rs).
Stages 1 through 7 moved their deterministic control decisions into the protocol core while leaving concrete cryptography and wire translation in those adapters.
Further moves should remain incremental rather than attempting to extract the whole crate.

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

PQXDH now uses role-specific core typestates instead of making protocol transitions depend on an `is_beacon` flag plus unrelated optional fields. Production likewise exposes separate `Beacon` and `Server` Rust types, each of which owns only its role-specific adapter state; no public boolean constructor or internal provider-role enum remains. The core states include:

```rust
pub struct BeaconFresh { /* pinned expected ServerBinding */ }
pub struct BeaconInitSent { /* pinned binding and identity tied to one InitKex */ }
pub struct BeaconRegistrationCandidate { /* validated session retaining that binding */ }
pub struct AuthenticatedBeaconRegistration { /* authenticated sender and assigned IDs */ }
pub struct BeaconEstablished { /* committed binding and assigned ID */ }
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
    authenticated_server_key_id: u64,
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

Returning the receive state on both success and failure makes the normal-return contract explicit. Production rejects empty, unparsable, wrong-sender, too-short, inadmissible, and missing-key frames without changing the selected ratchet. For an admitted future frame, `begin_receive` returns an affine continuation that stages the final receive chain, skipped entries, separate target material, and post-consumption logical control while retaining the exact entry kernel. Commitment comparison and AEAD opening run against the final phase's exact target before publication. `ReceiveOpen::finish(None)` drops the candidate and returns the entry kernel; `finish(Some(plaintext))` publishes the prevalidated final chain, counter, and skipped entries while consuming rather than caching the target. Repeating an invalid future target therefore repeats bounded derivation work but cannot fill the live cache. The implementation tests complete neutrality, authentic retry, replay rejection, cached out-of-order delivery, and the exact gap/capacity boundary in [`beaconcrypt/tests/protocol.rs`](../beaconcrypt/tests/protocol.rs).

For extraction, replace `HashMap` with a bounded, packed sequence whose uniqueness and size are visible to the prover. Restoration can require sorted input even though successful receive uses swap-removal and does not preserve entry order. The generic `RefinedRatchet` owns that logical sequence and its fixed array of sealed `CachedReceiveKey<Material>` values; production stores `ConcreteRatchetKernel`, which specializes both directional chains and cached material to core fixed-width values and stores no executor. Each cached value repeats its logical sequence in a private tag, so tag equality, mismatch-aware lookup, whole-entry removal, and restoration are structural invariant preservation rather than a relation to a parallel adapter array. `KernelRefines` now gives this direct state canonical ideal meaning for the proved send/failure behavior and cached-open construction under `ResponseRefines`; the consumed control-cache transition also refines ideal skipped-key filtering. Future staging, the material-array half of concrete cached swap-removal, and restoration still require the remaining phase lemmas.

### Keep the core on production paths

After each extraction-sized move, the public `Beacon` and `Server` APIs must delegate to the new core. Existing known-answer and protocol tests must continue to exercise those paths. A proof-only reimplementation is out of scope because its correspondence to production code would become a new, unproved assumption.

The low-level ratchet methods currently exposed from [`beaconcrypt/src/ratchet.rs`](../beaconcrypt/src/ratchet.rs) can bypass invariants expected at the higher-level protocol API. Either narrow their visibility or state theorem preconditions so that verified traces are explicitly limited to calls through the high-level API.

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
- core-owned KDF requests containing the exact selected input and fixed `SYM_RATCHET_INFO`, with production restricted to executing those requests;
- the exact per-step 76-byte key, next-chain, and nonce partition;
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

Do not assume general hash injectivity.
The implemented proof extracts the production transcript helper, proves its exact 229-byte layout and both LE64 fields, proves both integer encodings and the complete six-field transcript injective, and machine-checks `ctx_distinct_openings_imply_hash_collision`.
That theorem quantifies over arbitrary pure hash and AEAD-open functions and proves pointwise that two distinct accepted explanations of the same fixed ciphertext, transmitted tag, and commitment yield an explicit hash-collision witness.
It deliberately allows unequal-key or unequal-context openings by the base AEAD.
SSProve machine-checks the displayed [same-execution event-probability inequality](ctx-commitment.md) under the pointwise contract. Constructing the adversary-facing CTX and collision games, completing their representation bridge, and accounting for queries and runtime remain conventional.
BLAKE2b-512 collision resistance and correct production use of the proved helper remain explicit primitive and adapter assumptions.

### ProVerif model

Represent the primitives with symbolic constructors and destructors, and annotate the protocol entry points and messages for extraction. hax provides protocol-oriented hooks such as `protocol_messages`, `process_init`, `process_read`, `process_write`, `pv_constructor`, and `pv_handwritten`; any handwritten fragments become part of the trusted model and must be inventoried and reviewed.

The model should include events for session initiation, acceptance, sending, receiving, key deletion, and compromise. These events make agreement and correspondence queries precise.

## Proof inventory

### F*: implementation and state-machine properties

The tracked F* extraction and ratchet lemmas in this inventory describe the predecessor executor/callback source snapshot. Their abstract layouts and control arguments remain historical proof evidence, but present-tense bullets about an executor-bearing `ConcreteRatchetKernel`, `concrete_seal_next`, `concrete_open_and_finish`, or executor-bound restoration do not verify the current affine effect API; the current Lean coverage and remaining phase/interpreter obligations are recorded separately below and in the trusted-boundary inventory.

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
- The extracted per-step KDF-output helper partitions the fixed 76 bytes exactly as key bytes `0..32`, next-chain bytes `32..64`, and nonce bytes `64..76`.
- Every initial and later symmetric-ratchet KDF invocation is represented by a core-owned `SymmetricRatchetKdfRequest` containing the exact 32-byte root or old chain and `SYM_RATCHET_INFO`; production cannot select either field.
- `ConcreteRatchetKernel` binds one per-step executor into both directional chains, carries that identical executor into every next chain, and selects the concrete step internally in its public operations.
- Every active concrete receive entry is sealed with a private sequence tag equal to the unique logical sequence in the same slot, and every inactive slot is empty.
- The generic `reachable` relation fixes initial chains and pure steps; `concrete_reachable` specializes it to the core chain/material types and sole executor-bearing step for a `ConcreteRatchetKernel` lifetime. It equates each live chain with exactly the number of iterations named by its counter and each cached material with the concrete receive-step result at its sealed sequence.
- Fresh concrete construction establishes `concrete_reachable`; the role-bound PQXDH constructors produce complementary reachable beacon/server kernels from one agreed root, and their opposing directional `material_at` values are equal at every sequence.
- A receive request beyond the permitted window is state-neutral.
- The extracted whole-plan receive definition preflights every planned fixed-array destination before its first abstract KDF evaluation. Its admission and preflight rejection branches preserve the complete refined state and cannot publish an executed prefix; the F* theorem establishes extensional independence from arbitrary pure executor/callback functions, while concrete non-invocation and side-effect claims additionally rely on generated/source control-flow review, faithful compilation, and Rust call-count tests. An admitted authentication rejection may perform bounded KDF work and one callback but still preserves the complete refined state.
- Every valid admitted future plan privately derives exactly its bounded consecutive sequences in order, stages each skipped sequence beside the corresponding abstract material at its eventual absolute slot, keeps the target material separate, preserves every old tagged association, and records the final chain and post-target-consumption control without changing the live refined state.
- An old or current receive target performs zero derivations and leaves the state unchanged before verified lookup decides whether its material is still cached; lookup rejects a populated slot whose sealed tag disagrees with the requested logical sequence.
- Successful receive removes exactly the consumed message key, so replay is rejected.
- Failed authentication drops the complete private candidate and returns the exact entry state without caching the target or any skipped material.
- Successful future publication installs the prepared final chain and counter, caches only skipped keys, consumes the separate target, and preserves every old tagged association.
- Retrying a rejected future target repeats its bounded private derivation from the unchanged live state, while a successful retry publishes the same transition the authentic frame would have published without the preceding rejection.
- A successful receive that skips exactly 50 messages ends with all 50 skipped keys cached while consuming the incoming target separately. The target never occupies a cache slot. Capacity admission and snapshot version 2 remain unchanged, restoration accepts structurally valid 50-entry caches, and the next no-skip target can progress even when the cache is full.
- Verified lookup returns the unique active slot for every cached receive sequence and returns `None` exactly when that sequence is absent.
- In the low-level compatibility completion API, `Missing` and `Retained` dispositions return no removal and preserve logical state. Refined completion validates the target tag and the previous-last tag before mutation, rejects a mismatch as `Missing`, and on success moves the complete previous-last tagged entry into the target slot when those slots differ. Production opening does not publish that compatibility retention path.
- The compatibility finish and restoration functions are projections of the detailed functions, with identical logical state, disposition, and accept/reject behavior.
- Successful concrete restoration binds the fixed executor into both imported chains, returns the old logical cache length as each append slot, and seals the supplied logical sequence beside its core material in that slot. The conditional generic `reachable_restore` relation is established only when trusted persistence provenance supplies canonical live chains and each appended material equals the fixed derivation for its sequence. The maintained adapter requires a `SnapshotStore` to preserve payload integrity and provenance and fences activation by lineage/generation/head CAS, but that store contract and the adapter are not extracted and therefore remain the reachability refinement obligation.
- A transition for peer A leaves peer B's ratchet unchanged.
- `concrete_seal_next` and `concrete_open_and_finish` select the fixed step internally and preserve concrete reachability on every pure callback result. `beacon_seal_server_open_preserves_concrete_session` and `server_seal_beacon_open_preserves_concrete_session` preserve the paired role-session invariant for the corresponding public-operation pairs.
- Successful send makes the consumed message key logically unavailable.
- The commitment input is exactly `(key, nonce, associated data, AEAD tag, sequence, sender ID)` with unambiguous fixed-size encodings.
- For arbitrary pure hash and AEAD-open functions, two distinct accepted explanations of one fixed commitment payload imply an explicit collision between distinct production transcript inputs.
- Every accepted, bounded input follows a panic-free extracted control path; abstract callback panics and production crash behavior remain external.

Persistence is a separate boundary. `start_concrete_restore`, `concrete_restore_receive_key`, and `finish_concrete_restore` bind the fixed executor and re-establish structural tag/cache invariants for supplied core values, while the generic F* builder lemmas preserve derivational reachability only under canonical-chain and canonical-material premises. Production requires a trusted `SnapshotStore` to supply canonical payload integrity and provenance and to win a fresh generation/head CAS before activation, but serde fidelity, store atomicity/durability/rollback resistance, and the claim that imported material was originally derived for its supplied sequence remain outside F*. Snapshots have no cryptographic authentication or encryption, and importing arbitrary structurally valid state alone still does not establish `concrete_reachable`.

### ProVerif: protocol trace properties

- Secrecy of the initial application message and subsequent application messages.
- Injective agreement on server identity, beacon identity, assigned key ID, transcript, and derived root.
- Accepted plaintext implies a preceding honest send for the same session, direction, sequence, sender, and plaintext.
- Replay resistance.
- Unknown-key-share and cross-peer resistance.
- Independence of concurrent sessions.
- Forward secrecy following a later compromise of live chain state.
- Secrecy of the state-neutral receive canaries while the receiver state remains private.
- Explicit negative results after disclosure of the unchanged post-rejection live chain: derivation of future skipped and target material and attacker forgery, without any claim that rejection enlarged the compromised state.
- Reachability of two neutral rejected attempts from one exact entry-state term, later honest future delivery, skipped-key publication from success, replay rejection, delayed cached delivery, maximum-gap success with 50 skipped keys, capacity rejection, cached consumption, and forward progress after one slot is freed.
- A differential negative control in which one deliberately non-key-committing base-AEAD ciphertext/tag has two distinct valid openings: the identical double-open query is unreachable with CTX and reachable when CTX is removed.

Forward secrecy needs a precise statement. Send keys are deleted immediately, but skipped receive keys remain cached for out-of-order delivery. Compromise of a receiver can reveal cached skipped keys. The defensible theorem is secrecy of a message after its message key has become logically unavailable, not secrecy of every message whose sequence number is below the current counter.

The symmetric ratchet never mixes fresh entropy into an established chain, so it deliberately provides no post-compromise security. This should be recorded as a negative result, not formulated as an expected theorem.

ProVerif establishes these results only in the stated symbolic model. It does not establish computational security of the cryptographic primitives.

The state-neutral receive ProVerif process is one exact finite witness, not an unbounded receive API. It starts after successful symbolic frame construction and models attacker-selected frames that have passed the production parser, sender lookup/check, and minimum payload-length gate. Cap'n Proto parsing, serialized byte lengths, and the handling of malformed, truncated, or wrong-sender inputs remain production-review and regression-test obligations. The short leg rejects a forged sequence-3 frame twice with the exact same receiver-state term, then accepts the honest target, publishes only skipped sequence 2, rejects replay, and accepts delayed sequence 2. The capacity leg advances from sequence 1 to sequence 52, caches sequences 2 through 51, consumes sequence 52 separately, rejects sequence 54 while those 50 slots remain occupied, consumes cached sequence 51, and then accepts sequence 54 while publishing skipped sequence 53. The predecessor F* lemmas provide general exact KDF-output partition, cached-tag invariant, fixed-origin derivational reachability, callback-`None` full-state equality, non-vacuous exact preparation for each then-admitted future plan and valid cached target, conditional callback-`Some` publication shape, replay neutrality, equality of an arbitrary retry before and after any finite repetition of one fixed rejected operation, and rejection capacity preservation for their old callback API. They do not prove the corrected current phase API's maximum-gap future success. The ProVerif traces and Rust tests additionally provide concrete cryptographic effect and exact-schedule witnesses. F* does not supply concrete HKDF semantics or output noncollision, cryptographic secrecy, or frame provenance.

## Closed counterexamples

Three regression tests in [`beaconcrypt/tests/protocol.rs`](../beaconcrypt/tests/protocol.rs) track
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

An earlier trust-anchor counterexample relied on replacing a beacon's mutable peer-map entry after `InitKex`, thereby changing the identity that finish treated as expected. The split `Beacon` no longer has such a map: it owns one constructor-provided server principal while proof-visible state retains the original public-key/ID pair. `finish_registration` checks the response identity and authenticated sender against that binding, then rechecks the sole concrete principal before publication; `beacon_rejects_registration_response_from_wrong_server` covers the remaining wrong-server response case.

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
8. **Complete:** pin rustc, hax, F*, Z3, ProVerif, Rocq, SSProve, and MathComp and run the applicable extraction plus proofs in CI.
9. **Complete:** maintain a reviewed inventory of every opaque Rust function, assumed primitive law, adapter refinement, proof-library assumption, generated-code exception, and handwritten backend fragment, with a standalone drift gate.
10. **Complete:** extract and prove the production CTX transcript order and injectivity, machine-check the pointwise collision-witness theorem and SSProve same-execution event-probability inequality, add a deliberately multi-opening ProVerif negative control with an exact no-CTX failure witness, and document the remaining conventional adversary-facing lifting.

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

The initial slice now lives in [`beaconcrypt-core`](../beaconcrypt-core). It is a dependency-free `no_std` workspace member containing a pure sending-counter transition with explicit exhaustion behaviour. hax extracts only that entry point and its transitive dependencies to [`proofs/fstar/extraction`](../beaconcrypt-core/proofs/fstar/extraction).

Run the complete check from the core crate:

```sh
make verify
```

The target enters hax's revision-pinned `ci-examples` Nix shell, regenerates the F* module, computes and checks its proof-library dependencies, and verifies the extracted module without `--lax`. `make check-generated` adds a tracked-output diff check for CI. At Step 1 this slice was toolchain scaffolding and was not yet used by the production ratchet; production delegation followed in Step 3.

### Step 2 implementation

The Step 2 through Step 9 descriptions below are historical records of the checked executor/callback architecture at those milestones. Step 10 supersedes their concrete runtime interface; theorem names tied to `ConcreteRatchetChain`, `concrete_seal_next`, or `concrete_open_and_finish` do not prove the new phase API.

At the Step 2 milestone, the core contained the full symmetric-ratchet control state and its then-production specialization. The generic layer treated chain and material types parametrically, while `ConcreteRatchetKernel` owned fixed-width `RatchetChain` and `RatchetMaterial` values and carried one executor in both private directional chains. `SymmetricRatchetKdfRequest` owned the exact selected 32-byte input and `SYM_RATCHET_INFO`; the initial and later helpers partitioned fixed executor outputs, and the concrete public operations selected the executor-bearing step internally. `concrete_reachable` gave these values lifetime derivational meaning. Those tracked F* results remain checked for that predecessor snapshot, while concrete PQXDH root and ratchet HKDF semantics, totality, output noncollision, ephemeral libsodium conversion and callback fidelity, ChaCha20-Poly1305, and the cryptographic meaning of secret bytes remained opaque.

The state machine includes:

- monotonic send and receive counters with state-neutral exhaustion;
- receive admission using both the 50-message forward-gap limit and the total outstanding-key capacity;
- a fixed 50-slot receive cache whose private concrete entries carry sequence tags checked against unique logical ownership;
- separate logical planning plus extracted whole-plan destination preflight, private bounded preparation, and success-only publication, so production does not interpret the plan or select callback count and append slots;
- verified sequence-to-current-slot lookup over the active packed prefix, with mismatched concrete tags rejected rather than exposed;
- source-level preparation that borrows the live refined state immutably, keeps future target material outside staged skipped slots, prevalidates cached target/old-last tags, and publishes the exact removal or future delta only after callback success;
- one-use send-key capabilities;
- checked restoration from sorted, unique, bounded cached sequence/material pairs, sealing each supplied pair and returning its append slot;
- pointwise peer transitions that return non-selected peers unchanged.

The fixed array is intentional. Several convenient dynamic-collection operations are assumptions in the current hax proof libraries; direct array preflight, private staged entries, bounded tag-checking lookup, and validated whole-entry swap-removal keep the key-lifecycle semantics visible in generated F*. The strict lemma module proves the Step 2 property inventory against that generated code, including the exact KDF request input/label, exact 76-byte output partition, executor preservation, active cached-tag equality, mismatched-tag rejection, callback-`None` complete-state equality, old-association preservation, zero-step cached lookup, exact successful removal shape, and restoration-slot correspondence. `admitted_future_plan_prepares_valid_pending` and `admitted_cached_target_prepares_valid_cached` supply non-vacuous returned constructors for every valid admitted nonzero future plan and valid cached target respectively; the exact callback-success publication theorems remain conditional on the callback returning plaintext. The public replay, repeated-fixed-rejection retry, capacity-neutrality, and conditional maximum-gap capstones compose those facts. The concrete reachability lift proves canonical iteration under the sole core-selected step and preservation through concrete construction, send, public open/seal outcomes, lookup, consumption, and conditionally admitted restoration.

At the end of Step 2, the production `RatchetManager` remained unchanged. The initial Step 3 adapter made the logical core authoritative and maintained equality with a parallel concrete receive array; the current refined-kernel follow-up internalizes that relation by owning both representations and reconstructing them through one paired restoration typestate.

### Step 3 implementation

The detailed implementation record is in [`formal-verification-stage-3.md`](impl/formal-verification-stage-3.md).

At the Step 3 milestone, the production crate depended on `beaconcrypt-core`, and `RatchetManager` wrapped one private `ConcreteRatchetKernel`. That extracted concrete kernel owned the logical counters and packed sequence cache, both fixed-width executor-bearing chain values, and `[Option<CachedReceiveKey<RatchetMaterial>>; 50]`; production no longer stored parallel chains, receive slots, role-specific chain wrappers, or persistent libsodium material. The cached record fields were private, and every live record repeated the sequence that caused the kernel to store its material. Step 10 later replaced the executor-bearing chains and callbacks with the current typed phases.

In that predecessor snapshot, the core constructed `SymmetricRatchetKdfRequest` with the exact root or old chain and fixed `SYM_RATCHET_INFO`; production's `initial_ratchet_hkdf` and `ratchet_hkdf` functions executed the request and returned the statically sized output. `derive_initial_ratchet_kernel` constructed `ConcreteRatchetKernel` directly, and each concrete chain carried `ratchet_hkdf` unchanged into the next step, so production no longer rebuilt a `RatchetStep`. Public `concrete_open_and_finish` privately prepared the exact target under the fixed step, lent its material and sequence plus frame context to one callback, dropped the candidate unchanged on `None`, and published consumption plus skipped material only on `Some`; `concrete_seal_next` retained its one-use send behavior. The callbacks converted borrowed key and nonce arrays to libsodium types only for the operation; those external values were not persistent ratchet storage.

The internal ratchet payload keeps the five fields `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`. Concrete send-message material is never serialized, legacy objects containing `send_past` are rejected, active pairs come only from the tag-checking accessor, output is sorted, and duplicate or noncanonical numeric map keys are rejected before `HashMap` insertion. Import rebuilds only through `start_concrete_restore`, `concrete_restore_receive_key`, and `finish_concrete_restore`, which check structural ordering, bounds, and sequence/material alignment but cannot prove HKDF provenance. Public update APIs return an inert `RatchetSnapshot`, not a live manager. Persistent restoration passes through `PersistentServer`; its canonical `ServerSnapshot` binds a lineage, generation, parent digest, version, and kind, while a conforming trusted `SnapshotStore` must supply payload integrity and provenance. Restoration, accepted receives, and every other state-changing result require a successful head CAS, and a loser is poisoned. A rejected receive performs no successor encoding, generation increment, store load, or CAS and returns the exact existing head. The C, Go, and Python convenience bindings use an in-memory store and export plaintext checkpoints for caller-managed storage; they cannot fence independent imports, make caller writes crash-atomic, or detect stale rollback and are outside the durable one-owner claim. The snapshot has no cryptographic authentication or encryption. F* proves only conditional reachability from trusted canonical provenance and does not prove the codec, store, durability, crash, or rollback-resistance contracts.

The strict F* lemmas retain the generic foundation but add the exact concrete specialization. `symmetric_ratchet_kdf_request_is_exact`, `ratchet_step_uses_exact_chain_and_partition`, and `concrete_ratchet_step_preserves_executor` prove the core-owned input/label, exact `key[0..32] || next_chain[32..64] || nonce[64..76]` interpretation, and fixed lifetime executor. `concrete_kernel_new_is_reachable`, `concrete_seal_next_preserves_reachability`, and `concrete_open_and_finish_preserves_reachability` establish and preserve the concrete invariant through the predecessor public lifecycle. The generic public-open theorem proves exact rejection equality; admitted future and cached preparation have explicit existence theorems; callback success conditionally publishes the exact prevalidated result; replay after success is neutral; any finite repetition of one fixed rejected operation leaves an arbitrary later retry equal to its direct transition; and rejection preserves cache capacity for that old callback API. These artifacts do not prove the corrected current phase API's maximum-gap success. Low-level retention/retry/capacity lemmas describe only the predecessor compatibility logical API and restored cached state, while restoration reachability remains conditional.

The Step 3 production claim was restricted to high-level encryption and decryption from successfully established role state and, for persisted server execution, fresh activation from the trusted store with no rollback. The reviewed adapter enforced this runtime gate by storing a beacon ratchet only in `BeaconState::Established` and server ratchets only in `EstablishedRemote` entries; it made operational ratchet state affine and kept manual insertion, reset, associated-data mutation, and mutable ratchet access test-only or crate-private. This was reviewed runtime enforcement rather than a generic compile-time typestate theorem. For that predecessor snapshot, F* composed authenticated equal root-input transcripts, a fixed pure root derivation, core-owned ratchet requests, direct role-bound kernel construction, fixed lifetime executors, all-sequence cross-role material equality, and public seal/open reachability preservation. Its remaining assumptions included correct and total HKDF semantics, output noncollision, faithful callbacks, complete establishment-gate refinement, canonical serde, trusted snapshot payload integrity/provenance, store atomicity/durability/rollback resistance, hax/Rust/compiler correspondence, crash behavior, and role-specific selection. Core secret arrays zeroized on `Drop`, but physical erasure, compiler treatment, allocator copies, and retained external values remained outside F*.

### Step 4 implementation

The detailed implementation record is in
[`formal-verification-stage-4.md`](impl/formal-verification-stage-4.md).

The protocol core now owns deterministic PQXDH composition: disjoint encoded
key type/role markers, the exact padding and DH/KEM root input, ordered associated data,
role-dependent ratchet directions, and explicit beacon and server registration
states. Random key generation and primitive calls remain in the adapter, which
passes their public outputs and shared-secret results to deterministic core
transitions.

Production exposes separate `Beacon` and `Server` types. `Beacon` stores `BeaconState` directly plus the constructor-bound server public key; its state advances through fresh, `InitKex` sent, established, or aborted, and only the established variant owns an operational ratchet. The fresh state receives the configured server public key and numeric identity-key ID as one proof-visible `ServerBinding`; successful transitions preserve the pair, response preparation compares the received public key with the stored key, and post-open authentication compares the initial frame's sender ID with the stored numeric ID. On success the beacon publishes its assigned identity, associated data, and staged ratchet together in `BeaconState::Established`; failure leaves no operational ratchet. The server peer map analogously stores only `EstablishedRemote` entries committed after PQXDH or reconstructed by fresh restoration from the trusted store.

The server validates into a pending registration and builds its proposed peer
on a fresh ratchet outside the live peer map. It encrypts the initial message
and serializes the complete response before committing the core counter, public
counter, and peer map. A failure discards the candidate and leaves exported
server state unchanged. The pending production token is opaque and consumed by
the response builder, which obtains response public material and associated
data from the core candidate. It also records the accepting server's identity
public key and identity key ID, and candidate preparation rejects use by a
differently bound `Server` without changing live state.

The Stage 4 correspondence claim covers high-level registration transitions on `Beacon` and `Server`; direct beaconcrypt-core construction and test-only or crate-private compatibility setters, peer-map mutation, and low-level ratchet calls remain outside that trace. The maintained high-level operational state is not `Clone`, while persistent no-fork/no-rollback behavior depends on `PersistentServer` and its external store contract and is not proved by Stage 4.

The pinned hax item list extracts these PQXDH transitions to
`Beaconcrypt_core.Pqxdh.fst`, and the existing strict F* target
checks that generated module and its generated safety obligations without
`--lax`. No PQXDH semantic lemma module was part of Stage 4; Stage 6 now adds
the agreement, transcript, associated-data, and initialization proofs.

### Step 5 implementation

The detailed implementation record is in
[`formal-verification-stage-5.md`](impl/formal-verification-stage-5.md).

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
[`formal-verification-stage-6.md`](impl/formal-verification-stage-6.md).

The Stage 5 extraction was reviewed before adding semantic claims. Its fixed
copy loops reached F* through a library operation without a useful
postcondition, `u64::to_le_bytes` was opaque in the pinned model, and derived
whole-`ServerBinding` equality introduced a local generated assumption. The
core now uses specified fixed-range slice updates, constructs LE64 bytes from
explicit shifts and narrowing casts, and compares the two server-binding fields
directly. Compile-time assertions tie the literal proof ranges and production
KDF slices to the public beaconcrypt-core sizes. Production-used candidate
ratchet and binding accessors are also included in extraction.

For the predecessor extraction, the strict handwritten PQXDH module proves exact tagged-key construction and validation, exact semantic registration IDs, the six-segment root transcript and zero-DH rejection, exact associated data, server-binding and response-ID checks, checked allocation, and commit/abort shape. `authenticated_registration_derives_common_fixed_root` bridges authenticated equal root transcripts under one fixed pure root function. `concrete_initial_kernels_are_complementary`, `concrete_initial_kernels_are_reachable`, and `concrete_directional_materials_agree` cover its direct role-bound kernel construction and both opposing material equalities at every sequence; `authenticated_registrations_establish_concrete_session` is that snapshot's capstone composition. `beacon_seal_server_open_preserves_concrete_session` and `server_seal_beacon_open_preserves_concrete_session` preserve its paired concrete reachability invariant through callback-based public operations. Those concrete theorem names are historical rather than proofs of the current phase API. Root-HKDF and ratchet-HKDF semantics/totality, output noncollision, ephemeral libsodium conversion and callback fidelity, compiler correspondence, and atomic peer-map publication remain obligations.

Agreement is deliberately conditional. The adapter must establish pairwise X25519 and ML-KEM secret agreement, authenticate the same role identities, pass the authenticated sender ID and assigned-ID bytes from a successful AEAD open, refine `Fresh` and `Available` from the persistent set and peer map, apply deterministic HKDF to the verified input and labels, and maintain non-rollback single-owner server state. The maintained adapter uses affine established-only runtime state plus `PersistentServer` generation/head CAS to enforce those ownership conditions when the external store contract holds, but concrete primitives, wire translation, codec/store correctness, trusted payload provenance, replicas outside that store, zeroization, and low-level test paths remain outside the theorem.
The generated and handwritten modules contain no local `assume` or `admit`,
and the target checks them without `--lax`.

### Step 7 implementation

The detailed implementation record is in
[`formal-verification-stage-7.md`](impl/formal-verification-stage-7.md).
That record is historical; the attacker-owned-registration extension described
below is tracked by the current analysis and canonical trust-boundary inventory.

Stage 7 reviewed the complete Stage 6 commit `493a23f` before adding a trace
model. The ProVerif backend now extracts the production `InitKex`, verified
registration, registration-ID, root-input, assigned-ID-binding, and associated
data boundary into
[`proofs/pro-verif/extraction/lib.pvl`](../beaconcrypt-core/proofs/pro-verif/extraction/lib.pvl).
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

The dedicated state-neutral receive extension models the production transaction boundary with explicit symbolic receiver states. Its first exact server-to-beacon leg consumes sequence 1, rejects a correctly shaped forged sequence-3 frame twice while carrying the exact same ready-state term, accepts the authentic sequence-3 ciphertext, publishes only skipped sequence 2, consumes sequence 3, rejects replay relative to the exact post-success state, and accepts delayed sequence 2. A separate capacity leg advances from sequence 1 to sequence 52, retains exactly sequences 2 through 51, and consumes sequence 52 separately. It rejects sequence 54 while all 50 slots remain occupied, consumes cached sequence 51, and then accepts sequence 54 while publishing only skipped sequence 53. The extracted F* control lemmas are role/direction independent; the ProVerif secrecy and compromise composition is not a separate mirrored beacon-to-server trace.

The private-state scenario proves secrecy of the consumed-past, short-leg skipped/target, maximum-gap target, cached, and after-release application values and preserves the normal receive-to-honest-send correspondence. Its top level concurrently permits replicated attacker-owned beacon registrations and requires reachability of both their response commit and malicious canary without activating the legitimate-state compromise channel. The receive record sessions still start from independently fresh symbolic roots rather than composing PQXDH into those record traces, so relating the state namespaces to production relies on the peer-selection and independent-root adapter refinements. The synchronized compromise scenario deliberately crosses the base threat model's no-legitimate-state-compromise boundary immediately after both rejected attempts. Its snapshot repeats the same ready-state term on both sides of rejection and contains the unchanged live chain plus an empty cache. Revealing that chain can still derive the future skipped and target material, expose their ciphertext plaintexts, and permit an authentic replacement frame. The capacity leg remains independently rooted and private. A separate reachability witness shows that later delivery of the honest target ciphertext remains possible when the attacker forwards it; availability or eventual delivery is not claimed.

This ProVerif construction is an exact capacity-50 execution, whereas the predecessor F* lemmas quantify over every valid refined state satisfying their preconditions and prove whole-plan destination preflight, pure extensional independence of admission rejection from executor/callback choice, complete callback-failure equality, preservation of old associations, zero-step old lookup, and reachability preservation for that snapshot. Every then-admitted nonzero future plan and valid cached target has a non-vacuous exact preparation; callback success remains conditional on the callback returning plaintext and publishes the exact prevalidated state. The predecessor F* artifact also proves neutral replay after public success, equality of an arbitrary retry before and after any finite repetition of one fixed rejected operation, and cache-capacity preservation on rejection, but it does not prove the corrected current phase API's maximum-gap success. Current Lean proves the generated control driver refines `Ratchet.recvStep` directly at the common 50-skipped-key bound. It also independently proves rollback for supplied finite failed-phase trace witnesses, constructs the generated cached-open phase from `KernelRefines` plus an ideal lookup, proves the control-plane half of consumed cached publication, and proves the conditional cached-success slice described in Step 10; trace reachability, effect-level future success, and the cached material-array publication theorem remain open. The finite ProVerif trace supplies the concrete cryptographic secrecy, compromise, and exact schedule. Concrete effect-path rejection additionally relies on generated/source control-flow review, faithful compilation, and Rust call-count tests. The ProVerif frame is already a symbolic `crypto_frame`: the model does not parse Cap'n Proto bytes or represent every serialized length. Production's pre-admission rejection of empty, unparsable, unknown/wrong-sender, and too-short frames remains an adapter/refinement claim supported by Rust tests, not a conclusion of the symbolic trace.

The later commitment extension separates facts that the original ideal frame rule conflated.
The ordinary record correspondence still assumes exact symbolic opening.
The extracted F* helper is proved to emit `key || nonce || associated data || tag || LE64(sequence) || LE64(sender ID)` exactly, both integer encodings and the complete transcript are proved injective, and `ctx_distinct_openings_imply_hash_collision` machine-checks the pointwise collision witness for arbitrary pure hash and AEAD-open functions.
The same payload fixes ciphertext, tag, and commitment, while distinct accepted explanations may differ in key, nonce, associated data, sequence, sender ID, or plaintext and the base AEAD remains free to multi-open under unequal contexts.
SSProve now mechanizes the same-execution event-probability inequality from misattribution to collision under the F*-backed pointwise contract. The complete adversary-facing CTX and hash-oracle games, representation bridge, query and runtime accounting, and BLAKE2b collision resistance remain unmechanized or assumed.
A dedicated weak-AEAD ProVerif library supplements this theorem with one explicit ideal-hash counterfactual: CTX makes its double-opening event unreachable, while the same query produces a trace when the CTX checks are removed.

`make verify` now regenerates or checks every configured backend in the revision-pinned proof shell. Its ProVerif result parser rejects timeouts, missing or substituted queries, unexpected true/false classifications, and every unproved or inconclusive security query. The aggregate ProVerif check runs its thirteen `check-proverif-<scenario>` targets concurrently, and the corresponding `verify-proverif-<scenario>` and `check-generated-proverif-<scenario>` targets support isolated locked-shell and generated-drift checks. `make check-generated` covers the generated F*, ProVerif, and Lean artifacts, while SSProve objects are checked separately under `target/formal-verification/ssprove`.

### Step 8 implementation

The detailed implementation record is in
[`formal-verification-stage-8.md`](impl/formal-verification-stage-8.md).

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

The dedicated `formal-verification.yml` GitHub Actions workflow installs Nix, uses the public hax/F*/Z3 caches read-only, and runs F* plus each ProVerif scenario as separate matrix jobs on main-branch pushes, pull requests targeting `main`, merge-queue checks, and manual dispatch. Every matrix job has read-only repository permission and a 60-minute bound, regenerates the extraction it consumes, verifies its proof component, and rejects tracked or untracked generated-artifact drift. A final aggregate job retains the established `Extract and verify F* and ProVerif` status and fails unless every matrix job succeeds.

Re-extraction with the pinned Rust nightly is byte-identical to the Stage 7
artifacts. No theorem, primitive equation, process, or expected ProVerif result
changed in Stage 8.

### Step 9 implementation

The detailed implementation record is in
[`formal-verification-stage-9.md`](impl/formal-verification-stage-9.md), and the
canonical maintained inventory is
[`beaconcrypt-core/proofs/trusted-boundary.md`](../beaconcrypt-core/proofs/trusted-boundary.md).

Stage 9 inventories the repository-owned production wrappers around entropy, Ed25519, Ed25519/X25519 conversion, X25519, ML-KEM, HKDF, ChaCha20-Poly1305, BLAKE2b, wire translation, persistence, allocation, and zeroization. It separately records the primitive laws used by the conditional F* results and ideal ProVerif theory, every concrete-to-logical adapter refinement, the pinned hax/F*/ProVerif/Rocq/SSProve trust surface, all generated-code exceptions, and every handwritten F*, ProVerif, or SSProve review unit.

`make check-inventory` validates a category/path/SHA-256 manifest and derives
the complete production Rust/schema, beaconcrypt-core Rust, generated-backend,
and handwritten-backend file sets. It also enforces the three and only three
ProVerif replacements; the generated type/default/converter/error baseline;
the single permitted generated converter used by handwritten code; the
handwritten primitive, event, process, and query counts; the absence of hax
opaque annotations; and the absence of the previously rejected generated F*
constructs.

The inventory check is deliberately separate from the complete and ProVerif-only locked-shell proof paths and must be run after final proof regeneration. The formal-verification workflow includes it as an independent matrix job alongside the proof backends, and `make -C beaconcrypt-core check-inventory` fails when a monitored production wrapper, extraction selector, handwritten proof/model, result classifier, generated artifact, tool control, or inventory policy changes without an explicit reviewed-baseline update. The hashes are deliberately conservative review tripwires; passing the mechanical gate does not itself prove that a human review was adequate.

Stage 9 does not add a theorem, change a symbolic equation or query, or alter
production behavior. All limitations and conditional refinements recorded in
Stages 3 through 8 remain in force.

### Step 10 implementation: first-order effect boundary

The production concrete ratchet and PQXDH initialization no longer store KDF executors or accept seal/open callbacks. Instead, the core defunctionalizes external cryptography into affine request/response phases. This change addresses the pinned Charon/Aeneas inability to translate Rust function pointers without implying that Lean itself cannot model functions. All default `beaconcrypt-core` modules, including `ratchet::refined`, `ratchet::concrete`, and `pqxdh::concrete`, now lie inside the no-exclusion Lean translation boundary.

Initial construction returns `InitialRatchetKdfPending`, whose request contains the exact root and `SYM_RATCHET_INFO`; the adapter computes a 64-byte HKDF result, constructs `InitialRatchetKdfResponse`, and calls `resume_initial_ratchet_kdf`, which splits and role-orders the two chains. Production send follows `begin_send` → `SendKdf::resume` with a typed 76-byte response → `SendSeal::finish`; production receive follows `begin_receive` → zero or more `ReceiveKdf::resume` calls → `ReceiveOpen::finish`. `SealFrameContext` and `OpenFrameContext` move through the generic phases as opaque values, so the core chooses material and sequence but does not parse, serialize, commit, encrypt, or decrypt frames.

The adapter drives these phases synchronously in [`beaconcrypt/src/ratchet.rs`](../beaconcrypt/src/ratchet.rs). `ratchet_hkdf` executes only the core-owned request. `seal_frame` and `open_frame` create libsodium key/nonce values ephemerally and apply CTX plus ChaCha20-Poly1305 to the exact final phase arguments. `RatchetManager` temporarily moves its non-clonable kernel through a private `Option` slot and reinstalls the returned kernel before a normal high-level return. Phases never enter persistence, restoration no longer binds an executor, and the high-level `beaconcrypt`/FFI API, Cap'n Proto layout, and five-field ratchet payload remain unchanged; the public `beaconcrypt-core` Rust API intentionally changes from callbacks to effect phases.

Commit policy is encoded in the phase types. Send exhaustion and `SendKdf::cancel` return the exact entry kernel; after a KDF response, both `SendSeal::finish(Some(_))` and `finish(None)` return the advanced kernel, preserving failed-send key consumption. Receive admission rejection, `ReceiveKdf::cancel`, `ReceiveOpen::reject`, and `ReceiveOpen::finish(None)` return the exact entry kernel. Future KDF responses change only private continuation state; `finish(Some(plaintext))` alone publishes the prevalidated cached removal or future chain/skipped-cache/control delta. The theorem scope is normal return: a panic while the kernel is owned by a phase leaves the manager slot empty and drops the continuation, so the owner fails closed, but unwind/crash/concurrency atomicity is not proved.

Typed 64-byte and 76-byte response wrappers prevent cross-phase response confusion, and secret-bearing requests, responses, chains, keys, nonces, and material use `ZeroizeOnDrop`. Those types do not establish response provenance or cryptographic correctness. The trusted effect laws remain faithful and total HKDF-SHA-512 for the exact request, faithful CTX/AEAD interpretation for the exact final material/sequence/context, correct ephemeral conversion, and no untracked retained state; compiler-preserved physical erasure remains outside the model.

This step removes extraction exclusions and now includes checked control-to-ideal and phase-to-ideal refinements, but it does not complete verification. `RatchetRefinement.lean` proves that the generated control-plane receive driver refines `Ratchet.recvStep` directly at the common 50-skipped-key bound: the incoming target is advanced and consumed separately rather than cached. `KernelRefines` precisely relates generated control, direct send/receive chains and counters, and both directions of the cached-material correspondence to the handwritten ideal states; `ResponseRefines` is the explicit semantic law assumed for one typed KDF response. Lean proves non-exhausted send begin/resume/success and cancellation, receive KDF cancellation/open rejection/open failure, exact state neutrality and refinement preservation for supplied finite failed-trace witnesses, and conditional open-reply consistency through the phase-selected material and `cr.dec`. Given `KernelRefines`, target/index equality, and an ideal skipped-key lookup, `begin_receive_cached_refines` proves generated `begin_receive` returns an open satisfying `CachedOpenRefines`; cached success matches the cached branch of `recvStep`, and concrete finish returns the same plaintext. `finish_receive_with_removal_consumed_refines` proves the consumed control state refines the ideal filtered cache, while full post-state refinement still requires the separate `CachedPublicationRefines` material-array swap/empty-suffix premise. Required follow-up is to complete that cached material-array proof, prove future KDF staging/publication, compose initial roles and restoration, verify or assume the synchronous adapter driver, and model send exhaustion. The tracked concrete F* executor/callback theorems remain predecessor-only. See the [current proof analysis](formal-verification-analysis.md#defunctionalized-production-effect-interpreter) for the exact trust split.

## Toolchain findings and CI policy

A direct extraction smoke test against the current root crate is not viable with the locally installed tools. The installed hax 0.3.7 toolchain uses a Rust 1.93 nightly, while [`Cargo.toml`](../Cargo.toml) declares Rust 1.96. Bypassing that version check exposes use of newer `slice_as_array` functionality and then reaches a hax frontend panic while processing generated Cap'n Proto code.

This supports the isolated-core approach: it avoids generated schemas and FFI-heavy dependencies, and it can remain within the Rust subset supported by the pinned hax release. It is not evidence that the application should lower its Rust requirement.

CI pins all proof tools together and fails on:

- extraction errors or unexpected generated diffs;
- F* checking performed with `--lax`;
- no-exclusion Lean translation, policy checking, or the imported Lean build failing;
- admitted or newly unproved obligations;
- the CTX/no-CTX differential query, baseline ProVerif queries, or reachability/compromise queries differing from their exact reviewed classifications, or any query being unproved or inconclusive;
- tracked or untracked generated output that differs from the reviewed
  artifacts;
- any monitored opaque-function, primitive-law, adapter-refinement,
  proof-library, generated-exception, or handwritten-fragment inventory drift
  that lacks an explicit reviewed-baseline update.

The proof artifact must state the exact versions of rustc, hax, F*, Z3, ProVerif, Rocq, SSProve, and MathComp used to produce it.
The Stage 9 manifest also fingerprints the selectors and locked tool/CI
controls that define that artifact.

## What a successful result means

The completed production refactor and imported Lean refinements justify saying that the generated control-plane receive driver directly refines the ideal 50-skipped-key `Ratchet.recvStep`, that the core owns exact typed ratchet requests and commit/rollback phases, that a concrete kernel satisfying `KernelRefines` has a precise ideal meaning, that a response satisfying `ResponseRefines` drives a correct non-exhausted send, and that every supplied `ReceiveFailureTrace` witness returns the exact refining entry state. They also justify generated cached-open construction from an ideal skipped-key lookup, the control-plane filtered-cache result for cached consumption, and the conditional cached-success result described above. They do not yet justify saying that the complete effect-level receive lifecycle, send exhaustion, initial role construction, restoration, or synchronous adapter refines the ideal ratchet: the cached material-array publication, future-staging, ideal-send-exhaustion, composition, and driver obligations remain. The old concrete F* executor/callback theorems apply only to their predecessor snapshot. Production additionally enforces affine establishment-gated state, inert updates, canonical decoding, and generation/head CAS; `SnapshotStore` remains trusted, and snapshots have no cryptographic authentication or encryption. No current proof establishes concrete HKDF/AEAD/ML-KEM semantics, the adapter interpreter, output noncollision, serialization/store correctness, panic/crash behavior, bindings, compiler behavior, physical erasure, RNG behavior, or a complete computational protocol reduction; the SSProve result is only the conditional CTX event-inclusion milestone described above.
