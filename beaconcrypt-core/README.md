<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt-core

The `beaconcrypt-core` package is the independently publishable, `no_std` extraction boundary for beaconcrypt's protocol state machines. Its Rust crate name is `beaconcrypt_core`. It intentionally has no cryptographic, serialization, FFI, or runtime dependencies. See the repository's [formal verification plan](../doc/formal-verification.md) for the intended boundary and proof inventory.

The crate contains the control-plane state machines for the symmetric ratchet and PQXDH registration plus the fixed-width CTX commitment transcript builder. It owns ratchet counters, key availability and receive admission as well as deterministic PQXDH/commitment transcript construction, role-specific registration states, and commit/abort decisions.

The extracted generic `RefinedRatchet<SendChain, ReceiveChain, Material>` remains the proof foundation, while production stores the concrete specialization `ConcreteRatchetKernel`. That kernel owns logical control, both fixed-width directional chains, one executor sealed into both chain values for the kernel's lifetime, and a packed fixed array of at most 50 sealed `CachedReceiveKey<RatchetMaterial>` values. Each cached value stores the logical sequence that caused the kernel to store its material. Production calls this same kernel rather than maintaining independent chains or receive slots, and lookup, completion, serialization, and restoration reject a cached tag that does not match the logical sequence in its slot. The operational chain, material, kernel, restoration-builder, and application-manager types are affine rather than `Clone`, and high-level update APIs expose only inert serialized views.

The concrete cryptographic boundary is represented by `SymmetricRatchetKdfRequest`, whose private fields contain the exact core-selected 32-byte input and the exact `SYM_RATCHET_INFO` bytes, plus fixed-output executors for the initial 64-byte expansion and each later 76-byte expansion. `derive_initial_ratchet_chains` constructs that request from the agreed root, partitions the executor output, and selects complementary role directions; `derive_beacon_ratchet_kernel` and `derive_server_ratchet_kernel` construct the role-bound `ConcreteRatchetKernel` values directly. `derive_ratchet_step` constructs the same request from the exact old chain, and the concrete chain carries its executor unchanged into the next chain. Public `concrete_seal_next` and `concrete_open_and_finish` select that fixed step internally, so production supplies only the request executor and the ephemeral seal/open callback; it no longer converts persistent core values into role-specific chain/material wrappers or reconstructs a `RatchetStep` outside extraction. Receive admission, whole-plan destination preflight, bounded ordered derivation, tagged lookup, and success-only publication remain inside the kernel. A future receive privately stages its final chain and skipped entries while keeping target material separate; a cached receive prevalidates whole-entry removal metadata. The open callback runs against that exact private selection before publication, callback `None` returns the complete entry state, and callback `Some` publishes the prevalidated chain/cache/control delta while consuming rather than caching the target. Pending transactions remain private, affine, fixed-capacity values. Repeating an invalid boundary target can re-execute up to 50 private KDF steps, so denial-of-service controls remain external and must not encode rejection by mutating the kernel. Seal/open callbacks borrow core `RatchetMaterial`; production converts its key and nonce arrays only ephemerally for the corresponding libsodium call.

The concrete restoration builder accepts each `(sequence, RatchetMaterial)` pair in one checked operation, seals that sequence into the cached value, reconstructs control and cached slots together, and binds the same executor into both restored directional chains through `start_concrete_restore`, `concrete_restore_receive_key`, and `finish_concrete_restore`. The internal payload retains the five fields `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`; serialization reads active sequence/material pairs through the tag-checking accessor and emits them in numeric order, while import rejects duplicate and noncanonical numeric keys before `HashMap` insertion and supplies sorted pairs to the builder. Imports with more than 50 outstanding receive keys and legacy objects containing `send_past` are rejected. The unchanged version-2 format still accepts a structurally valid 50-entry cache, including trusted state produced by the former failed-receive behavior; a fresh distance-50 success now retains only 49 skipped entries, but that stronger lifecycle fact is not an import invariant. The unconditional builder lemmas prove only structural sequence/material association. The separate proof-only `reachable_restore` relation starts only when trusted persistence provenance supplies canonical live chains and cached material. Production attempts to discharge that premise through `PersistentServer`, whose `SnapshotStore` contract requires payload integrity and provenance plus a linearizable, durable, rollback-resistant lineage/generation/head CAS before activation and accepted or otherwise state-changing result release. A normal rejected receive produces no successor snapshot or CAS. Snapshots have no cryptographic authentication or encryption, and F* does not verify serde, the store contract, crash behavior, or deployment fencing. See Step 3 of the [formal verification plan](../doc/formal-verification.md) and the [Stage 3 implementation record](../doc/impl/formal-verification-stage-3.md).

The generic F* refinement lemmas remain parametric, but the concrete layer closes the production specialization. `symmetric_ratchet_kdf_request_is_exact` proves that every core-created request contains the exact input and `SYM_RATCHET_INFO`; `ratchet_step_uses_exact_chain_and_partition` proves exact old-chain handoff and the 32/32/12-byte output partition; `concrete_ratchet_step_preserves_executor` proves that every next chain retains the same executor; `concrete_kernel_new_is_reachable`, `concrete_seal_next_preserves_reachability`, and `concrete_open_and_finish_preserves_reachability` specialize the lifetime derivation invariant and its public transitions to `ConcreteRatchetKernel`. In the PQXDH layer, `authenticated_registration_derives_common_fixed_root` bridges authenticated equal root-input transcripts under one fixed pure root derivation, `concrete_initial_kernels_are_complementary` and `concrete_initial_kernels_are_reachable` connect the agreed root to both role constructors, and `concrete_directional_materials_agree` proves at every natural-number sequence that beacon-send material equals server-receive material and server-send material equals beacon-receive material. The capstone `authenticated_registrations_establish_concrete_session` composes authenticated root agreement, direct role-kernel construction, fresh concrete reachability, and both material equalities at an arbitrary sequence. `beacon_seal_server_open_preserves_concrete_session` and `server_seal_beacon_open_preserves_concrete_session` prove that the paired reachable-session invariant survives the corresponding public seal/open attempts for every pure callback outcome. These results compose exact initial directions, one fixed lifetime executor, all-sequence cross-role material agreement, and public lifecycle preservation without an adapter-reconstructed `RatchetStep`.

The correspondence claim covers high-level encryption and decryption traces that begin in a concrete reachable established initialization and continue without state rollback. The production runtime stores server ratchets only in `EstablishedRemote` entries and a beacon ratchet only in `BeaconState::Established`; this is an adapter establishment gate, not a new generic F* typestate theorem. Equal concrete roots still depend on correct PQXDH root derivation, and request executors and callbacks must faithfully implement HKDF-SHA-512, commitment, and ChaCha20-Poly1305. Core arrays zeroize on `Drop`, but physical erasure and compiler behavior remain outside F*. A no-reuse conclusion remains conditional on noncollision of relevant KDF projections and one authoritative owner. Affine Rust state and `PersistentServer` generation/head CAS support that ownership premise only with a conforming durable store. The C, Go, and Python trusted-checkpoint helpers use an in-memory store and can be forked or rolled back by restoring exported bytes, so they are outside that persistence premise. F* does not prove the Rust ownership boundary, codec/store behavior, trusted payload provenance, crash durability, role-specific selection, external copies, or rollback prevention.

## Ratchet module and interface layout

The Rust implementation keeps the existing flat `beaconcrypt_core::ratchet` API through scoped re-exports while placing definitions in three dependency-ordered modules:

- [`src/ratchet/control.rs`](src/ratchet/control.rs) contains logical counters, cache admission, send/receive transitions, restoration, and peer helpers; hax generates `Beaconcrypt_core.Ratchet.Control`.
- [`src/ratchet/refined.rs`](src/ratchet/refined.rs) binds Control state to generic chain and material values and owns refined send, receive, open, and restoration machinery; hax generates `Beaconcrypt_core.Ratchet.Refined`.
- [`src/ratchet.rs`](src/ratchet.rs) retains fixed-width KDF types, concrete chain and kernel specialization, concrete restoration, and tests; hax generates `Beaconcrypt_core.Ratchet`.

The dependency direction is `Ratchet.Control` → `Ratchet.Refined` → `Ratchet` → `Pqxdh`. The corresponding Control and Refined `.fsti` files expose only declarations used by the next layer, and [`proofs/fstar/Beaconcrypt_core.Ratchet.fsti`](proofs/fstar/Beaconcrypt_core.Ratchet.fsti) exposes the eight constants, types, and constructors used directly by generated PQXDH. The Ratchet and PQXDH lemma interfaces export no declarations; their named implementations use explicit F* friend access where representation-dependent proofs need hidden definitions.

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

The ProVerif baseline proves five honest-session secrecy queries and six
injective registration, replay, commit, and bounded-record correspondences
while replicated attacker-owned beacons disclose all of their keys and submit
valid self-signed registrations. Seven separate reachability controls exercise
the five original honest traces, server commitment of a valid malicious
registration response, and attacker recovery of the task canary routed to that
response. The
latter path assumes the surrounding application routes honest taskings only to
their intended recipients; its private origin tables are proof instrumentation,
not a production ACL. The late-compromise model proves secrecy for deleted
initial and advanced keys while deliberately finding attacks on a cached
skipped key and on future traffic in both directions, recording the absence of
post-compromise security. See the
[Stage 7 implementation record](../doc/impl/formal-verification-stage-7.md) and
[current proof analysis](../doc/formal-verification-analysis.md).

The dedicated receive model uses two exact finite legs. The first consumes sequence 1, rejects a forged sequence-3 frame twice while reusing the exact same receiver-state term, accepts the honest sequence-3 frame, publishes only skipped sequence 2, rejects replay, and accepts delayed sequence 2. The second accepts sequence 51 from counter 1 with exactly 49 skipped entries, rejects sequence 53 because `49 + 2 > 50`, consumes cached sequence 50, and then accepts sequence 53 while retaining only skipped sequence 52. Every rejection and success event has a required reachability witness. Its compromise variant discloses the same symbolic state immediately before and after rejection; disclosure of the unchanged live chain can still expose future material, so the result is rejection non-expansion rather than post-compromise secrecy.

The production CTX transcript delegates to the core's fixed-size commitment builder.
Hax extracts that helper, and the strict F* commitment lemmas prove the exact 229-byte order `key || nonce || associated data || tag || LE64(sequence) || LE64(sender ID)`, injectivity of both integer encodings and the complete input, and `ctx_distinct_openings_imply_hash_collision`.
That theorem fixes one ciphertext, transmitted tag, and commitment and machine-checks an explicit collision witness for any two accepted explanations that differ in key, nonce, associated data, sequence, sender ID, or plaintext, while allowing the base AEAD to multi-open under unequal contexts.
The conventional [computational lifting](../doc/ctx-commitment.md) bounds misattribution advantage by BLAKE2b-512 collision advantage, but the probability and runtime theorem is not mechanized.
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

## Strict hax/F*/ProVerif verification

From this directory, run:

```sh
make verify
```

The target enters the repository's locked Nix proof shell, checks the exact rustc, Cargo, hax, F*, Z3, and ProVerif identities, regenerates the F* commitment, ratchet, and PQXDH modules plus the ProVerif extraction, checks all three F* lemma modules without `--lax`, and runs the CTX differential, baseline, reachability, state-neutral receive, and compromise models.
A policy gate rejects `assume` or `admit` in repository-owned F* modules and
lax/admitted-query checker flags. The result gate rejects timeouts, missing
queries, unexpected classifications, and every unproved or inconclusive
security query. `make verify-proverif` runs only the ProVerif extraction and
checks in the same locked shell, with the nine scenario targets running concurrently. Each scenario is also available independently as `make check-proverif-<scenario>`, `make verify-proverif-<scenario>`, or `make check-generated-proverif-<scenario>`; for example, `make verify-proverif-baseline` enters the locked shell, regenerates the extraction, and checks only the baseline model.

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

The checked ratchet properties cover the core-owned request's exact input and label, fixed output partition, lifetime executor preservation, counter and cache bounds, sequence/material association, complete receive-rejection equality, non-vacuous exact preparation for admitted future plans and valid cached targets, conditional callback-success publication, exact cached consumption, replay neutrality, arbitrary-retry equivalence after any finite repetition of one fixed rejected operation, rejection capacity preservation, the conditional fresh maximum-gap 49-entry result, restoration structure, and non-selected peer isolation. `concrete_reachable` fixes one kernel's initial chains and step; fresh construction establishes it, and public seal/open preserve it. The finite ProVerif traces and Rust tests additionally supply concrete cryptographic callback, compromise, and exact-schedule witnesses. PQXDH lemmas cover conditional authenticated common-root derivation, complementary reachable role kernels, all-sequence opposing material equality, and paired-session preservation. Structural restoration remains unconditional, while `reachable_restore` requires canonical chain/material premises supplied by trusted persistence provenance. `PersistentServer` and its trusted-store generation/CAS contract are intended to discharge those premises, but neither the store contract nor the adapter is part of the checked F* result.
`make check-generated` reruns the complete proof suite and additionally fails when extraction changes a tracked artifact or creates an untracked artifact. The dedicated formal-verification workflow runs F* and every ProVerif scenario as separate matrix jobs on every main-branch push, pull request targeting `main`, and merge-queue check; each job regenerates and checks its relevant extraction before accepting the proof result. Run the separate `make check-inventory` tripwire after reviewing intentional production/proof boundary changes.

The checked-in `flake.lock` pins hax revision
`5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3` (hax 0.3.7), its
`nightly-2025-11-08` Rust toolchain (rustc 1.93.0-nightly, commit `843f8ce2e`),
F* revision `7b347386330d0e5a331a220535b6f15288903234`
(`2025.10.06~dev`), Z3 4.15.3, and ProVerif 2.05. Nix is invoked with
`--no-update-lock-file`, and the version gate fails before extraction if a
checked version banner differs. Z3 4.15.3 is the newest solver bundled by this
F* release and was qualified against the complete corpus; later F* releases
were tested and rejected by hax's proof libraries. See the
[Stage 8 implementation record](../doc/impl/formal-verification-stage-8.md).
