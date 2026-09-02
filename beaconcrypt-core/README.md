<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt-core

The `beaconcrypt-core` package is the independently publishable, `no_std` extraction boundary for beaconcrypt's protocol state machines. Its Rust crate name is `beaconcrypt_core`. It intentionally has no cryptographic, serialization, FFI, or runtime dependencies. See the repository's [formal verification plan](../doc/formal-verification.md) for the intended boundary and proof inventory.

The crate contains the control-plane state machines for the symmetric ratchet and PQXDH registration, the production-specialized ratchet effect machine, and the fixed-width CTX commitment transcript builder. It owns ratchet counters, key availability, receive admission, exact KDF requests, response partitioning, staged receive publication, deterministic PQXDH/commitment transcript construction, role-specific registration states, and commit/abort decisions.

Production stores `ConcreteRatchetKernel`, which directly specializes `RefinedRatchet<RatchetChain, RatchetChain, RatchetMaterial>`. The kernel contains no executor or function pointer. Cryptographic work crosses the boundary through affine, first-order phases: the core owns an exact request and continuation, the adapter borrows the request, computes one fixed-width response, and consumes the continuation to resume. Separate `InitialRatchetKdfResponse` and `RatchetKdfResponse` types prevent a 64-byte initial response from being used as a 76-byte chain-step response. Generic context values are carried by value through the phase but remain opaque to the core.

Initial PQXDH ratchet construction uses `start_initial_ratchet_kdf` or a role/candidate-specific start function, followed by `resume_initial_ratchet_kdf`. Sending uses `begin_send` → `SendKdf::resume` → `SendSeal::finish`; receiving uses `begin_receive` → zero or more `ReceiveKdf::resume` calls → `ReceiveOpen::finish`. Send advancement is committed before sealing, so `SendSeal::finish(None)` returns the advanced kernel and preserves the established rule that a failed send still consumes its key. Receive derivations remain private in the owned continuation; rejection, cancellation, or `ReceiveOpen::finish(None)` returns the exact entry kernel, while `finish(Some(plaintext))` atomically publishes the prevalidated cached removal or future chain/cache/control delta. A successful future receive may retain all 50 skipped keys because the incoming target is consumed separately and never occupies a cache slot. Repeating an invalid future target may therefore repeat up to 51 KDF operations without increasing live cache state.

The application adapter interprets those phases synchronously in [`../beaconcrypt/src/ratchet.rs`](../beaconcrypt/src/ratchet.rs). It passes `SymmetricRatchetKdfRequest` only to HKDF-SHA-512, converts borrowed core key/nonce arrays to libsodium values only for `seal_frame` or `open_frame`, and returns the completed kernel to an internal `Option` slot before the high-level call returns. A panic while the slot is empty fails closed rather than restoring a guessed state; unwinding drops the owned continuation, but panic/crash atomicity remains outside the normal-return refinement claim. The high-level `beaconcrypt`/FFI API, Cap'n Proto layout, and five-field ratchet persistence payload do not change; the public `beaconcrypt-core` Rust API intentionally changes from callbacks to phases, and restoration no longer attaches an executor.

The concrete restoration builder accepts each `(sequence, RatchetMaterial)` pair in one checked operation and reconstructs control and cached slots together through `start_concrete_restore`, `concrete_restore_receive_key`, and `finish_concrete_restore`. The internal payload retains the five fields `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`; serialization reads active sequence/material pairs through the tag-checking accessor and emits them in numeric order, while import rejects duplicate and noncanonical numeric keys before `HashMap` insertion and supplies sorted pairs to the builder. Imports with more than 50 outstanding receive keys and legacy objects containing `send_past` are rejected. Persistence provenance, trusted-store behavior, crash durability, and rollback resistance remain external obligations; snapshots have no cryptographic authentication or encryption.

The tracked F* concrete refinement theorems describe the preceding executor/callback implementation and must not be cited as proofs of this phase API until regenerated or ported. The Lean work retains the handwritten ideal symmetric ratchet, translates the defunctionalized Rust modules without Charon exclusions, and checks both exact structural phase equations and a substantive phase-to-ideal refinement. `KernelRefines` relates control, direct chains/counters, and the concrete cache bidirectionally to ideal send/receive state; `ResponseRefines` is the assumed ideal-KDF response law. The generated control-plane driver now refines the ideal `Ratchet.recvStep` directly at its 50-skipped-key bound. The checked effect theorems cover non-exhausted send begin/resume/success and cancellation, receive cancellation/rejection/open failure and supplied finite failed-trace witnesses, conditional open-result consistency through the selected material and `cr.dec`, and conditional cached success against `recvStep`. For a refining kernel and ideal skipped-key lookup, `begin_receive_cached_refines` derives the actual generated cached-open phase and `CachedOpenRefines`; `finish_receive_with_removal_consumed_refines` separately proves that consuming its logical control-cache entry refines ideal skipped-key filtering. Remaining gaps are the material-array swap-remove relation needed to complete `CachedPublicationRefines`, future KDF staging/publication, ideal send exhaustion, initial role composition, restoration, and the synchronous adapter driver. HKDF, commitment, ChaCha20-Poly1305, adapter interpretation, zeroization at machine-code level, and compiler correspondence remain external effect laws or assumptions.

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
These are symbolic constructor-equality and reachability results, not byte-level serialization/extraction linkage or a computational handshake theorem, and they do not change the production root KDF input, associated data, or wire protocol.
See the [Stage 7 implementation record](../doc/impl/formal-verification-stage-7.md) and [current proof analysis](../doc/formal-verification-analysis.md).

The dedicated receive model uses two exact finite legs. The first consumes sequence 1, rejects a forged sequence-3 frame twice while reusing the exact same receiver-state term, accepts the honest sequence-3 frame, publishes only skipped sequence 2, rejects replay, and accepts delayed sequence 2. The second advances from sequence 1 to sequence 52, caches sequences 2 through 51, and consumes sequence 52 without placing it in the cache. It rejects sequence 54 while all 50 skipped-key slots remain occupied, consumes cached sequence 51, and then accepts sequence 54 while caching sequence 53. Every rejection and success event has a required reachability witness. Its compromise variant discloses the same symbolic state immediately before and after rejection; disclosure of the unchanged live chain can still expose future material, so the result is rejection non-expansion rather than post-compromise secrecy.

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

The target enters the repository's locked Nix proof shell; checks the exact rustc, Cargo, hax, F*, Z3, ProVerif, Rocq, and SSProve identities; regenerates the F*, ProVerif, and Lean extractions; checks all three F* lemma modules without `--lax`; runs every ProVerif scenario; checks the SSProve suite; and builds the complete maintained Lean root.
A policy gate rejects `assume` or `admit` in repository-owned F* modules and
lax/admitted-query checker flags. The result gate rejects timeouts, missing
queries, unexpected classifications, and every unproved or inconclusive
security query. `make verify-proverif` runs only the ProVerif extraction and checks in the same locked shell, with the twenty-three scenario targets running concurrently, including shared-HKDF prefix/domain controls and strong/weak public-key-confusion controls. Each scenario is also available independently as `make check-proverif-<scenario>`, `make verify-proverif-<scenario>`, or `make check-generated-proverif-<scenario>`; for example, `make verify-proverif-baseline` enters the locked shell, regenerates the extraction, and checks only the baseline model. `make verify-ssprove` and `make verify-lean` run their respective suites in the same locked environment.

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

The checked Lean control refinement covers counters, admission, cache behavior, and rollback by authentication verdict against the handwritten ideal receive model; separate control lemmas establish structural restoration well-formedness and bounds. The imported effect files additionally check current generated phase equations and the send, failed-receive, open-reply, and conditional cached-success refinements summarized above, including generated cached-open construction and the control-plane half of cached consumption. They do not yet prove the material-array half of `CachedPublicationRefines`, future-receive success, initial role composition, restoration of the concrete relation, or adapter interpretation. The finite ProVerif traces and Rust tests supply complementary cryptographic, compromise, schedule, and runtime witnesses. The tracked F* concrete reachability and paired-session results remain valid only for their predecessor executor/callback snapshot; generic proof structure may be ported, but those theorem names are not current production evidence.
`make check-generated` reruns the complete claimed proof suite and additionally fails when extraction changes a tracked artifact or creates an untracked artifact. The formal-verification workflow checks F*, Lean, and every ProVerif scenario through their configured jobs; each claimed component must regenerate and check its relevant extraction before acceptance. Run the separate `make check-inventory` tripwire after reviewing intentional production/proof boundary changes.

The checked-in `flake.lock` pins hax revision `4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800` (hax CLI 0.4.0-rc.1), its `nightly-2025-11-08` Rust toolchain (rustc 1.93.0-nightly, commit `843f8ce2e`), F* revision `7b347386330d0e5a331a220535b6f15288903234` (`2025.10.06~dev`), Z3 4.15.3, ProVerif 2.05, Rocq 9.0.0, SSProve 0.2.4, and MathComp 2.4.0.
Nix is invoked with `--no-update-lock-file`, and the version gate fails before extraction if a checked version banner differs.
Z3 4.15.3 is the newest solver bundled by this F* release and was qualified against the complete corpus; later F* releases were tested and rejected by hax's proof libraries.
See the [Stage 8 implementation record](../doc/impl/formal-verification-stage-8.md) for the historical Stage 8 pinning decision and the current `flake.lock` and version gate for the maintained toolchain.
