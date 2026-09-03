<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt-core

The `beaconcrypt-core` package is the independently publishable, `no_std` extraction boundary for beaconcrypt's protocol state machines. Its Rust crate name is `beaconcrypt_core`. It intentionally has no cryptographic, serialization, FFI, or runtime dependencies. See the repository's [formal verification plan](../doc/formal-verification.md) for the intended boundary and proof inventory.

The crate contains the control-plane state machines for the symmetric ratchet and PQXDH registration, the production-specialized ratchet effect machine, and the fixed-width CTX commitment transcript builder. It owns ratchet counters, key availability, receive admission, exact KDF requests, response partitioning, staged receive publication, deterministic PQXDH/commitment transcript construction, role-specific registration states, and commit/abort decisions.

Production stores `ConcreteRatchetKernel`, which directly specializes `RefinedRatchet<RatchetChain, RatchetChain, RatchetMaterial>`. The kernel contains no executor or function pointer. Cryptographic work crosses the boundary through affine, first-order phases: the core owns an exact request and continuation, the adapter borrows the request, computes one fixed-width response, and consumes the continuation to resume. Separate `InitialRatchetKdfResponse` and `RatchetKdfResponse` types prevent a 64-byte initial response from being used as a 76-byte chain-step response. Generic context values are carried by value through the phase but remain opaque to the core.

Initial PQXDH ratchet construction uses `start_initial_ratchet_kdf` or a role/candidate-specific start function, followed by `resume_initial_ratchet_kdf`. Sending uses `begin_send` → `SendKdf::resume` → `SendSeal::finish`; receiving uses `begin_receive` → zero or more `ReceiveKdf::resume` calls → `ReceiveOpen::finish`. Send advancement is committed before sealing, so `SendSeal::finish(None)` returns the advanced kernel and preserves the established rule that a failed send still consumes its key. Receive derivations remain private in the owned continuation; rejection, cancellation, or `ReceiveOpen::finish(None)` returns the exact entry kernel, while `finish(Some(plaintext))` atomically publishes the prevalidated cached removal or future chain/cache/control delta. A successful future receive may retain all 50 skipped keys because the incoming target is consumed separately and never occupies a cache slot. Repeating an invalid future target may therefore repeat up to 51 KDF operations without increasing live cache state.

The application adapter interprets those phases synchronously in [`../beaconcrypt/src/ratchet.rs`](../beaconcrypt/src/ratchet.rs). It passes `SymmetricRatchetKdfRequest` only to HKDF-SHA-512, converts borrowed core key/nonce arrays to libsodium values only for `seal_frame` or `open_frame`, and returns the completed kernel to an internal `Option` slot before the high-level call returns. A panic while the slot is empty fails closed rather than restoring a guessed state; unwinding drops the owned continuation, but panic/crash atomicity remains outside the normal-return refinement claim. The high-level `beaconcrypt`/FFI API, Cap'n Proto layout, and five-field ratchet persistence payload do not change; the public `beaconcrypt-core` Rust API intentionally changes from callbacks to phases, and restoration no longer attaches an executor.

The concrete restoration builder accepts each `(sequence, RatchetMaterial)` pair in one checked operation and reconstructs control and cached slots together through `start_concrete_restore`, `concrete_restore_receive_key`, and `finish_concrete_restore`. The internal payload retains the five fields `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`; serialization reads active sequence/material pairs through the tag-checking accessor and emits them in numeric order, while import rejects duplicate and noncanonical numeric keys before `HashMap` insertion and supplies sorted pairs to the builder. Imports with more than 50 outstanding receive keys and legacy objects containing `send_past` are rejected. Persistence provenance, trusted-store behavior, crash durability, and rollback resistance remain external obligations; snapshots have no cryptographic authentication or encryption.

Lean proves unconditional panic freedom for all 269 non-helper `RustM` operations in the default extraction, including malformed represented states and arbitrary fixed-width response bytes. The checked aggregate and exact signature gate require a normal return for every operation; explicit protocol rejection is a normal result. This guarantee does not depend on state validity or cryptographic correctness.

The behavioral proofs cover the complete extracted send and receive phase lifecycles. `KernelRefines` relates control, counters, chains, and every live material slot bidirectionally to ideal ratchet state. A fixed response interpreter gives exact KDF step semantics; optional authentication results preserve the relation, and the ideal-opening specialization matches `Ratchet.recvStep`. Send exhaustion is neutral, failed sends consume their advanced key, every receive run terminates, failed receives return the exact entry state, and successful cached or future receives atomically publish the exact control and material result. Structural proofs also cover arbitrary valid states whose old keys and chains have no canonical origin: future derivation is exact relative to the supplied receive chain, successful receives consume their target and reject replay, and finite mixed send/receive histories preserve validity. A fresh gap of 50 publishes exactly 49 skipped keys; the current target-outside-cache implementation also admits 51 derivations with 50 retained keys.

The concrete PQXDH phase drivers establish complementary initial role kernels and preserve their paired session through both directional send/receive lifecycles, under the stated transcript agreement and fixed interpreter assumptions. Restoration proves generic ordering, capacity, tag alignment, exact append, and rejection neutrality. Additional conditional theorems preserve supplied chain/material provenance and construct the full concrete `KernelRefines` relation; they do not authenticate snapshots or establish that imported values have that provenance.

The ideal PQXDH and ratchet models are unchanged. The tracked F* concrete artifacts are retained historical evidence for the preceding callback implementation, while [the ratchet declaration ledger](../doc/impl/ratchet-fstar-coverage.md) records checked Lean replacements, superseded internal helpers, and the changed capacity bound. The source-fidelity checks tie adapter call order and transcripts to the extracted interface, but do not prove semantic execution of the Rust adapter. Primitive correctness/security, response and authentication provenance, parser/serializer and FFI behavior, compiler correspondence, durable single-owner persistence, panic/crash recovery outside the core, and physical erasure remain external boundaries. See [the proof analysis](../doc/formal-verification-analysis.md) for the maintained claims and validation.

## Ratchet module and interface layout

The Rust implementation keeps the flat `beaconcrypt_core::ratchet` API through scoped re-exports while placing definitions in dependency-ordered modules:

- [`src/ratchet/control.rs`](src/ratchet/control.rs) contains logical counters, cache admission, send/receive transitions, restoration, and peer helpers; hax generates `Beaconcrypt_core.Ratchet.Control`.
- [`src/ratchet/refined.rs`](src/ratchet/refined.rs) binds Control state to generic chain and material values and owns refined send, receive, open, and restoration machinery; hax generates `Beaconcrypt_core.Ratchet.Refined`.
- [`src/ratchet.rs`](src/ratchet.rs) defines fixed-width KDF request/response and material types and re-exports the production facade.
- [`src/ratchet/concrete.rs`](src/ratchet/concrete.rs) defines the direct-chain kernel, affine send/receive effects, and concrete restoration.
- [`src/pqxdh/concrete.rs`](src/pqxdh/concrete.rs) defines the affine initial-KDF effect and role/candidate starts.

The source dependency direction is `ratchet::control` → `ratchet::refined` → `ratchet::concrete`, with PQXDH's concrete initial phase depending on the ratchet facade. The tracked F* Control/Refined/root module split and narrow `.fsti` interfaces describe the predecessor generated snapshot; the no-exclusion Lean extraction follows the current Rust module definitions directly.

## PQXDH typestates and transactional adapter

Stage 4 adds deterministic beacon and server registration transitions. The
beacon advances through `BeaconFresh`, `BeaconInitSent`,
`BeaconRegistrationCandidate`, and either `BeaconEstablished` or
`BeaconAborted`. The server advances from `ServerState` through
`PendingServerRegistration` and `ServerRegistrationCandidate` before producing
an updated `ServerState` and `EstablishedPeer`.

Random generation and primitive calls remain explicit adapter inputs. The core
constructs and validates disjoint key type/role encodings, fixes the
`Padding || DH1 || DH2 || DH3 || DH4 || SS` root input, orders associated data
as server identity then beacon identity, and selects complementary beacon and
server ratchet halves. The production adapter signs and parses Cap'n Proto,
performs libsodium and ML-KEM operations, and applies the resulting plan.
Secret-bearing transcript and candidate values are not `Copy`, `Clone`, or
`Debug`; the adapter zeroizes its shared-secret copy and the concrete root
transcript after use, while physical erasure remains outside the formal claim.

The beacon emits one registration bundle and treats every finish failure as a terminal abort. `BeaconFresh` stores the configured server public key and numeric identity-key ID as one `ServerBinding`; `beacon_start` preserves both fields in `BeaconInitSent`, and finish compares the response public key and authenticated sender ID with that retained binding. Only `BeaconState::Established` owns the committed associated data and operational ratchet, while fresh, pending, and aborted states cannot process application records. The server initializes a fresh peer ratchet off-map, encrypts and serializes the initial response, and only then commits an `EstablishedRemote` entry and counter. Manual peer insertion, reset, mutable ratchet access, and associated-data mutation are test-only or crate-private. These visibility and runtime-state facts support the verified transitions but are not themselves proved by F*.

The production pending-registration token is opaque and non-clonable, and the
response public material is read from the core candidate. The token records the
accepting server's identity public key and identity key ID; candidate
preparation validates that binding, and staged encryption uses its bound sender
ID.

See Step 4 of the
[formal verification plan](../doc/formal-verification.md) and the
[Stage 4 implementation record](../doc/impl/formal-verification-stage-4.md).

Stage 5 derives a canonical registration ID from the verified beacon identity and signed one-time public key. The adapter refines the core's fresh/consumed classification with a persistent set, consumes an ID before returning a pending token, and rejects replay after a failed response or fresh restoration from the trusted store. The set is serialized deterministically inside the snapshot payload; malformed, duplicate, missing, and structurally incomplete histories with fewer entries than committed peers fail closed. Payload integrity and provenance, plus freshness across restarts or workers, depend on the shared conforming `SnapshotStore`. Response failure leaves the counter, peer map, and ratchet unchanged while replay history remains consumed.

The core encodes the assigned beacon ID as a fixed little-endian `u64` prefix
for the AEAD-authenticated initial plaintext. The beacon must validate that
prefix and obtain `AuthenticatedBeaconRegistration` before it can call
`beacon_commit`; the adapter strips the prefix before returning application
data. This leaves the established associated-data and CTX commitment layouts
unchanged.

Key allocation now rejects `u64::MAX` exhaustion and takes an explicit
available/occupied classification for the exact next ID, so neither the
registration path nor the compatibility allocator can wrap or overwrite a
peer. See the
[Stage 5 implementation record](../doc/impl/formal-verification-stage-5.md).

Stage 6 makes every proof-relevant byte layout visible to F* and adds the
handwritten PQXDH semantic lemmas. They prove exact tagged-key round trips,
registration-ID and root-input construction, associated-data ordering,
complementary role ratchet offsets, authenticated assigned-ID correspondence,
and checked server commit/abort behavior. The post-validation composed result is
conditional on pairwise X25519/ML-KEM agreement, authenticated role identities,
truthful replay and availability classifications, AEAD provenance for the
assigned-ID prefix, deterministic adapter KDFs, and non-rollback single-owner
server state. See the
[Stage 6 implementation record](../doc/impl/formal-verification-stage-6.md).

Stage 7 adds an active-attacker ProVerif model. Its review found that the
prekey and one-time key previously shared the same signed X25519 tag, permitting
valid signed fields to be exchanged or duplicated. They are now encoded as
`[type, role, key]`, using low-domain type byte `0x04` and disjoint high-domain
role bytes `0x80` (prekey) and `0x81` (one-time). The adapter signs the complete
34-byte encoding, and core validation requires the field-specific role. This
wire hardening is intentionally not interoperable with the former 33-byte
signed X25519 payloads. The regenerated F* lemmas prove both exact layouts,
round trips, domain disjointness, and cross-role rejection.

The ProVerif baseline proves five honest-session secrecy queries and seven injective registration, authenticated-bundle, replay, complete-establishment, and bounded-record correspondences while replicated attacker-owned beacons disclose all of their keys and submit valid self-signed registrations.
The commitment correspondence compares one 18-field symbolic transcript containing both identities, the authenticated `InitKex`, registration ID, prekey, one-time X25519 key, selected ML-KEM public key, server ephemeral key, exact KEM ciphertext, initial frame, complete response, ordered root input, derived root, exact associated data, assigned beacon key ID, pinned server key ID, session identifier, and registration origin.
Eight separate reachability controls exercise the five original honest traces, the new authenticated-bundle acceptance event, server commitment of a valid malicious registration response, and attacker recovery of the task canary routed to that response.
The latter path assumes the surrounding application routes honest taskings only to their intended recipients; its private origin tables are proof instrumentation, not a production ACL.
The late-compromise model proves secrecy for deleted initial and advanced keys while deliberately finding attacks on a cached skipped key and on future traffic in both directions, recording the absence of post-compromise security.
The bounded active-quantum control binds its recovery witness to the selected replacement ML-KEM public key, server ephemeral key, exact KEM ciphertext, initial frame, complete response, ordered root input, root, and recovered plaintext, and it deliberately violates both honest initiation and authenticated-bundle agreement.
The production ProVerif KEM constructor additionally assumes ML-KEM public-key binding, or strong shared-secret collision resistance across distinct public keys; this assumption is stronger than generic IND-CCA and is not derived from it.
An isolated non-production same-identity multi-epoch fixture compromises only an old ML-KEM key and reaches an exact cross-key ciphertext-substitution attempt: the strong production-style theory preserves agreement and the new-session canary, while a deliberately weakened public re-encapsulation theory breaks both.
The supported `Beacon` API creates one identity, prekey, and ML-KEM keypair together, and `get_registration_bundle` can return `Some` at most once during one live object's lifecycle because successful serialization advances the object to `InitSent` and every later lifecycle transition remains ineligible. This claim does not cover bytes constructed by callers through public secret-key getters. The Server replay identifier is the exact 64-byte identity-key-plus-one-time-key concatenation, so changing only the ML-KEM key leaves that identifier consumed after a first successful `get_shared_secret`; a hypothetical rotation extension would need a new lifecycle and replay policy in addition to retaining the binding assumption or cryptographically binding the selected KEM key into the authenticated handshake transcript.
These are symbolic constructor-equality and reachability results, not byte-level serialization/extraction linkage or a computational handshake theorem, and they do not change the production root KDF input, associated data, or wire protocol.
An isolated Phase-2 response-binding scenario now follows the production beacon finish gates over the canonical five-field response: a genuine response commits, while independently reachable wrong outer-identity, relabeled outer assigned-ID, and wrong authenticated inner-sender responses do not. The wrong-identity and wrong-sender variants reach their internal comparison gates, while the relabeled-ID control proves that the unchanged genuine frame opens and exposes its original authenticated prefix before the outer/prefix comparison rejects it. Three non-vacuous injective correspondences link the accepted markers immediately preceding the sole commit to the pinned server identity, authenticated assigned-ID prefix, and pinned inner sender. This is a finite symbolic gate check under the existing ideal primitive theory, not a parser, adapter-refinement, primitive-security, or computational implementation theorem.
A paired negative control runs that identical fixture and finish process with only the assigned-ID equality gate deliberately weakened. The relabeled response then passes every unchanged identity, root, associated-data, sender, AEAD, and CTX step, commits under the distinct outer ID, exposes a commit canary, and breaks only the assigned-prefix correspondence; the outer-identity and inner-sender mutations remain rejected and their correspondences remain true. The production scenario is a prerequisite and proves the same relabeled commit unreachable and canary secret under the equality gate, so the differential demonstrates that the source binding check is necessary rather than reporting a production attack or primitive weakness.
See the [Stage 7 implementation record](../doc/impl/formal-verification-stage-7.md) and [current proof analysis](../doc/formal-verification-analysis.md).

### ProVerif cryptographic transcript fidelity

[`proofs/pro-verif/production-transcript-interface.pvl`](proofs/pro-verif/production-transcript-interface.pvl) is one canonical interface consumed by every ProVerif scenario and carries 465 ordered machine-readable facts about the exact Phase-1 `InitKex` boundary, the exact two HKDF domains, shared symmetric prefix, padded root input, key encodings, associated data, unlabeled AEAD and CTX structures, the five-field Phase-2 response wire layout, the production `CryptoFrame` boundary, endpoint caller wiring, the synchronous ratchet effect driver, the finite receive-state fixtures, registration lifecycle and replay-key scope, the exact source-shaped initial-ratchet handoff, the finite later-sequence registration witness, and the complete 18-field agreement transcript.
[`tests/proverif_transcript_fidelity.rs`](tests/proverif_transcript_fidelity.rs) checks those facts against compiled dependency-free core builders, mutable snapshots of the relevant adapter, commitment, schema, concrete ratchet, and checked Lean sources, the exact Phase-1, Phase-2, and `CryptoFrame` schema ordinals, the covered Server and Beacon caller sites, the symbolic declarations and scoped process fixtures, and the active-quantum witnesses, including the exact sizes, offsets, field order, shared-domain uses, normal-return effect-driver order, and absence of invented AEAD, CTX, direction, sequence, session, or phase labels from the frame cryptographic arguments.
The 18 Phase-1 facts bind `identityKey @0`, `preKey @1`, `oneTimeKey @2`, and `pqKey @3` to their exact Ed25519 identity, attached-signature, tagged-key, Server verification, `InitKex::from_encoded`, and symbolic meanings. Production evaluates the three signature getters in PQ, prekey, one-time order, while ProVerif evaluates its pure gates in prekey, one-time, PQ order; the checker records both orders separately and claims exact semantic field mapping, not security significance for evaluation order.
The 42 `CryptoFrame` facts bind schema ordinals `seq @0`, sender `keyId @1`, and `cipherText @2`; distinguish local target-key metadata from the serialized sender ID; record the source setter order payload, sequence, sender separately from the schema order; and lock detached `C,T`, retained-tag commitment `U`, exact `C || T || U` boundaries, parser gates, one-use ratchet material/sequence flow, and the ideal symbolic constructor rule. The concrete check records a call to libsodium `memcmp` but does not prove its timing behavior, and the symbolic opening equation applies only to exact well-formed constructor terms rather than proving Cap'n Proto or Rust parser semantics.
The 56 endpoint facts bind ordinary Server and Beacon send/receive target, sender, server-first associated-data, selected ratchet, and expected-sender arguments; registration's distinct assigned target and candidate server sender; the post-initial-frame peer-map and Beacon established-state provenance; and the security-relevant commit order. The symbolic facts are explicitly scoped to the finite main-honest and malicious-registration fixtures: their exact frame calls and event arrays synchronize those checked roles only and are not a theorem that production has a fixed traffic schedule.
The 38 ratchet-driver facts bind only the two production message helpers on normal-return paths: affine slot take/put, exact typed KDF request/response handoff, send exhaustion and failed-seal advanced-key consumption, receive prechecks before take, the core-issued KDF request sequence without a hard-coded adapter iteration count, no slot publication in a receive KDF arm, exact seal/open/finish handoff, terminal kernel restoration before success or error propagation, and the atomic ProVerif abstraction. The core separately bounds admissible future derivation. The listed Lean structural declarations and conditional refinement relations are checked interpretation anchors; the text checker does not compose them into a Rust-to-Lean or Rust-to-ProVerif refinement.
The 46 receive-fixture facts synchronize the current core's capacity-50 planning, separate uncached target, staged skipped keys, failure neutrality, successful publication, cached swap-removal, and replay branch with the two existing finite ProVerif receive legs and their exact query tuples. The short fixture's two malformed inputs are each equated to one canonical forged target frame and continue only through the `open_frame` destructor-failure branch. The capacity fixture instead rejects its canonical over-capacity frame before opening. Core cache slots are oldest first while the symbolic cache term is nested newest first, so this boundary compares only sequence/material membership, count, and the named committed states, not representation order.
The 60 registration-lifecycle facts bind the exact identity-plus-one-time replay ID and its exclusions; `get_registration_bundle` eligibility, completed serialization, one-successful-`Some` state transition, retry caveat, and complete post-`InitSent` transition graph; Server status, reserve, derivation, insertion, output, and later-response-failure order; the finite honest replay owner; the intentionally fresh malicious-server overapproximation; and HB-49's unsupported same-identity/same-one-time/PQ-only fixture. This is deterministic source and finite-model synchronization, not a uniqueness, persistence, semantic refinement, or primitive-security theorem, and it excludes caller-constructed bundles made through exposed secret-key accessors.
The 71 initial-ratchet facts lock the exact caller-supplied `RegistrationOutput` field handoff, the 32-byte `KexDerivedSecret` alias and `SecretArr::as_array` accessor, the role-specific typed start signatures, affine pending request, distinct 64-byte response and exact adapter-local construction/resume flow, `0..32`/`32..64` partition, complementary Server/Beacon kernel order, zero initial counters, existing Lean interpretation anchors, both ProVerif chain definitions, the exact PQXDH-root binding in each of the three scoped roles, and exactly five scoped initial chain uses with their material bindings. Complementarity is conditional on equal local roots and equal outputs from the same faithful deterministic response function; the roles do not share a response object. The response type prevents 64/76-byte phase-class confusion but does not carry request provenance, and `RegistrationOutput` is not indexed by its producing `Server` instance. This is source and finite-model text synchronization, not equality between Rust arrays and ProVerif terms, a proof that endpoint roots agree, a Rust-to-Lean/ProVerif refinement, or an HKDF-SHA-512 correctness or security proof.
The 68 later-registration facts separately lock the source's generic receive path and absence of a first-sequence gate, the core's bounded future-derivation staging and exact publication helpers, existing general-receive Lean interpretation anchors, and one finite ideal fixture. In that fixture one genuine Server emits an original sequence-1 response before genuine sequence-2 and sequence-3 frames; an attacker substitutes only the response's application frame; and a fresh Beacon accepts the sequence-3 frame with its send side unchanged, receive counter at 3, live receive chain 4, sequence-2 then sequence-1 cached materials, and target material 3 used for opening but absent from the constructed cache. The same candidate reaches an explicit counterfactual first-sequence gate only after the successful finite open, then cannot commit or reveal its canary. These source-text and ideal free-constructor results do not prove arbitrary schedules, parser/compiler/serialization correspondence, semantic Rust-to-ProVerif or Rust-to-Lean refinement, liveness, primitive correctness/totality/security, a production sequence gate, the complete established Beacon state, persistence, multi-user behavior, crash behavior, or erasure.
The same check runs 2,861 in-memory drift mutations: the retained 40 transcript/Phase-2 cases, the separately counted 163-case Phase-1 matrix, the separately counted 223-case `CryptoFrame` matrix, the separately counted 242-case endpoint matrix, the separately counted 154-case ratchet-driver matrix, the separately counted 1,230-case finite receive-state matrix, the separately counted 177-case registration-lifecycle matrix, the separately counted 223-case initial-ratchet matrix, and the separately counted 409-case later-registration matrix. The receive-state matrix changes all 46 receive-fixture facts and independently exercises core admission/publication/removal, every manifested short and capacity frame/state/event field, the full 50-entry boundary cache, target absence, rejection control flow, and every field of the eleven correspondence and ten state-event reachability queries. The lifecycle matrix changes all 60 lifecycle facts and independently exercises replay-ID fields, Beacon eligibility/serialization/transitions, complete Server derive/consume ordering, honest replay-owner cardinality and topology, malicious bypass, and the HB-49 field reuse. The initial-ratchet matrix changes all 71 facts and independently exercises the shared-root alias/accessor, cross-method by-value handoff, both role callers, pending/response phase separation, adapter-local provenance, split bounds/orientation, kernel construction, Lean anchors, and every scoped ProVerif root derivation, chain, and material occurrence. The later-registration matrix changes all 68 facts and independently exercises the general-receive/no-first-gate source path, receive-plan counters and staged-slot validation/publication, two-sided finite DH/KEM/root construction, response-field substitution and one-candidate fanout, exact poststate/cache certificates, all 18 query formulas and result polarities, and the Makefile scenario wiring. Some cases deliberately guard exact source or finite-model spelling and need not change reachable semantics; they are deterministic drift controls, not 2,861 executable security attacks or a semantic refinement proof.
These are fidelity checks that must reject drift even if a secrecy theorem would remain true; the separate weakened-theory ProVerif scenarios are security controls that must produce their required disclosure, confusion, correspondence failure, or multi-opening witness.
Every ProVerif scenario depends on `check-proverif-transcript-fidelity`, and the formal-verification workflow also runs it as a dedicated job.
The mechanism is CI-enforced synchronization, not generated model extraction, a Rust-to-ProVerif refinement theorem, primitive verification, or an end-to-end computational security theorem.

The supported milestone claim is: “ProVerif proves the modeled BeaconCrypt protocol using the exact two production HKDF domains, the intentional shared symmetric-HKDF prefix semantics, the exact authenticated-context structure, disjoint concrete key encodings, and an explicitly named ML-KEM public-key-binding assumption.”

The dedicated receive model uses two exact finite legs. The first consumes sequence 1, rejects a forged sequence-3 frame twice while reusing the exact same receiver-state term, accepts the honest sequence-3 frame, publishes only skipped sequence 2, rejects replay, and accepts delayed sequence 2. The second advances from sequence 1 to sequence 52, caches sequences 2 through 51, and consumes sequence 52 without placing it in the cache. It rejects sequence 54 while all 50 skipped-key slots remain occupied, consumes cached sequence 51, and then accepts sequence 54 while caching sequence 53. Every rejection and success event has a required reachability witness. HB-60 now locks these finite state, membership, event, and query records against the current core control/publication source, but it does not prove arbitrary schedules or semantic Rust-to-ProVerif refinement. Its compromise variant discloses the same symbolic state immediately before and after rejection; disclosure of the unchanged live chain can still expose future material, so the result is rejection non-expansion rather than post-compromise secrecy.

The production CTX transcript delegates to the core's fixed-size commitment builder.
Hax extracts that helper, and the strict F* commitment lemmas prove the exact 229-byte order `key || nonce || associated data || tag || LE64(sequence) || LE64(sender ID)`, injectivity of both integer encodings and the complete input, and `ctx_distinct_openings_imply_hash_collision`.
That theorem fixes one ciphertext, transmitted tag, and commitment and machine-checks an explicit collision witness for any two accepted explanations that differ in key, nonce, associated data, sequence, sender ID, or plaintext, while allowing the base AEAD to multi-open under unequal contexts.
Lean's [computational lifting](../doc/ctx-commitment.md) machine-checks a factor-one bound from ideal-model misattribution advantage to BLAKE2b-512 collision advantage and proves that the current generated 229-byte builder equals the ideal preimage, while PPT/runtime preservation and the adapter hash-invocation and field-provenance bridge are not mechanized.
A supplementary ProVerif differential control uses one deliberately multi-opening base-AEAD ciphertext/tag: the double-opening query is unreachable with CTX and deliberately reachable when only the CTX checks are removed.
The real-world binding claim remains conditional on BLAKE2b collision resistance, correct libsodium and adapter behavior, and hax/compiler correspondence.

Stage 9 adds the maintained trust-boundary inventory. It names every
proof-relevant opaque production wrapper and primitive law, the ratchet and
PQXDH adapter refinements, the pinned proof-library assumptions, all accepted
generated-backend exceptions, and every handwritten proof/model/control
fragment. A category/path/SHA-256 manifest and structural checks make an
unreviewed boundary change fail CI. See the
[canonical inventory](proofs/trusted-boundary.md) and
[Stage 9 implementation record](../doc/impl/formal-verification-stage-9.md).

## Strict hax/F*/ProVerif/SSProve/Lean verification

From this directory, run:

```sh
make verify
```

The target enters the repository's locked Nix proof shell; checks the exact rustc, Cargo, hax, F*, Z3, ProVerif, Rocq, and SSProve identities; checks the production transcript interface; regenerates the F*, ProVerif, and Lean extractions; checks all three F* lemma modules without `--lax`; runs every ProVerif scenario; checks the SSProve suite; and builds the complete maintained Lean root.
A policy gate rejects `assume` or `admit` in repository-owned F* modules and lax/admitted-query checker flags. The result gate rejects timeouts, missing queries, unexpected classifications, and every unproved or inconclusive security query. `make verify-proverif` runs only the ProVerif extraction and checks in the same locked shell, with the twenty-eight scenario targets running concurrently, including shared-HKDF prefix/domain controls, strong/weak public-key-confusion controls, strong/weak ML-KEM re-encapsulation controls, the strong/weak Phase-2 assigned-ID binding pair, and the finite later-sequence registration control. Each scenario is also available independently as `make check-proverif-<scenario>`, `make verify-proverif-<scenario>`, or `make check-generated-proverif-<scenario>`; for example, `make verify-proverif-baseline` enters the locked shell, regenerates the extraction, and checks only the baseline model. `make verify-ssprove` and `make verify-lean` run their respective suites in the same locked environment.

Run `make check-proverif-transcript-fidelity` for only the canonical interface, production/core synchronization, and mutation suite.

The inventory-only check does not require entering the proof shell:

```sh
make check-inventory
```

It checks exact monitored file membership and fingerprints, the three embedded
ProVerif replacements, generated default/converter exceptions and their
permitted use, handwritten theory/process/query counts, prohibited hax opaque
annotations, and prohibited generated F* constructs. The full proof target
separately enforces the handwritten F* assumption policy. Intentional boundary
changes must update the prose inventory and only the affected manifest hashes
after their production and proof diffs have been reviewed.

The maintained Lean suite checks the complete extracted core's panic freedom, structural state preservation, exact staged/cached publication, conditional ideal ratchet and paired-session lifecycles, and generic plus conditional canonical restoration. The finite ProVerif traces and Rust tests supply complementary symbolic, compromise, schedule, and runtime evidence; they do not replace the semantic Lean proofs or discharge the external primitive, adapter, compiler, and persistence assumptions. The tracked F* artifacts remain historical evidence for the predecessor callback API, and the aggregate F* regeneration/check status is recorded separately in the proof analysis.

`make check-generated` reruns the configured proof suite and additionally fails when extraction changes a tracked artifact or creates an untracked artifact. The formal-verification workflow retains F* alongside the Lean and ProVerif gates until F* retirement is explicitly completed. Each claimed current component must regenerate and check its relevant extraction before acceptance. Run the separate `make check-inventory` tripwire after reviewing intentional production/proof boundary changes.

The checked-in `flake.lock` pins hax revision `4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800` (hax CLI 0.4.0-rc.1), its `nightly-2025-11-08` Rust toolchain (rustc 1.93.0-nightly, commit `843f8ce2e`), F* revision `7b347386330d0e5a331a220535b6f15288903234` (`2025.10.06~dev`), Z3 4.15.3, ProVerif 2.05, Rocq 9.0.0, SSProve 0.2.4, and MathComp 2.4.0.
Nix is invoked with `--no-update-lock-file`, and the version gate fails before extraction if a checked version banner differs.
Z3 4.15.3 is the newest solver bundled by this F* release and was qualified against the complete corpus; later F* releases were tested and rejected by hax's proof libraries.
See the [Stage 8 implementation record](../doc/impl/formal-verification-stage-8.md) for the historical Stage 8 pinning decision and the current `flake.lock` and version gate for the maintained toolchain.
