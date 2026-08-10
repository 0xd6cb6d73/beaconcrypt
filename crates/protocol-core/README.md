<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt protocol core

This `no_std` crate is the extraction boundary for beaconcrypt's protocol
state machines. It intentionally has no cryptographic, serialization, FFI, or
runtime dependencies. See the repository's
[formal verification plan](../../doc/formal-verification.md) for the intended
boundary and proof inventory.

The crate contains the control-plane state machines for the symmetric ratchet and PQXDH registration plus the fixed-width CTX commitment transcript builder.
It owns ratchet counters, key availability and receive admission as well as deterministic PQXDH/commitment transcript construction, role-specific registration states, and commit/abort decisions.
Cryptographic chain bytes, concrete message keys, hashing, private-key operations, and entropy stay behind the adapter boundary.

The receive cache is a packed fixed array of at most 50 logical key sequences. Its operations are implemented directly rather than through an assumed `Vec` model, so F* can see allocation and exact-key removal. The production adapter stores concrete receive keys in a parallel fixed array indexed by the core's verified slots and maintains this refinement invariant:

```text
concrete_receive_keys[slot].is_some() == (slot < core_state.receive_cache_len())
```

The existing beaconcrypt API now delegates its ratchet control decisions to
this crate. For each admitted logical step, the adapter performs exactly one
opaque KDF operation and associates the resulting concrete key with the same
sequence. It removes concrete receive keys only when the core consumes their
logical capability, retains both representations on authentication failure,
and completes allocated send capabilities on both successful and failed
encryption paths.

The persistence adapter preserves the existing six-field wire format. It serializes each concrete receive-array slot under the corresponding logical sequence from the core state and reconstructs both packed arrays from sorted persisted map keys through the checked restoration API. Imports with more than 50 outstanding receive keys are rejected. See Step 3 of the [formal verification plan](../../doc/formal-verification.md) and the [Stage 3 implementation record](../../doc/formal-verification-stage-3.md).

The Stage 3 correspondence claim covers high-level encryption and decryption
traces without state rollback. Direct low-level ratchet calls, forks containing
pending send keys, and the production peer-map lookup remain explicit adapter
preconditions; the core's `SendKey` represents logical availability but is not
an affine Rust type.

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

The beacon emits one registration bundle and treats every finish failure as a terminal abort. `BeaconFresh` stores the configured server public key and numeric identity-key ID as one `ServerBinding`; `beacon_start` preserves both fields in `BeaconInitSent`, and finish compares the response public key with that stored value instead of looking it up again in the mutable peer map. The candidate and established states retain the complete binding, the initial record is opened using its numeric ID, and the post-open transition checks the authenticated sender ID before commit. The beacon publishes the assigned identity, associated data, and derived ratchet only after those checks and confirms that its concrete peer-map entry still represents the pinned binding. The server initializes a fresh peer ratchet, encrypts the initial message, and serializes the response off to the side; only then does it commit the key counter and peer map. A failed response leaves those values and the staged ratchet unchanged.

The production pending-registration token is opaque and non-clonable, and the
response public material is read from the core candidate. The token records the
accepting server's identity public key and identity key ID; candidate
preparation validates that binding, and staged encryption uses its bound sender
ID.

See Step 4 of the
[formal verification plan](../../doc/formal-verification.md) and the
[Stage 4 implementation record](../../doc/formal-verification-stage-4.md).

Stage 5 derives a canonical registration ID from the verified beacon identity
and signed one-time public key. The adapter refines the core's fresh/consumed
classification with a persistent set, consumes an ID before returning a
pending token, and rejects replay even after a failed response, peer deletion,
or export and restore. The set is serialized deterministically; malformed,
duplicate, missing, and structurally incomplete histories with fewer entries
than committed peers fail closed. This adds one earlier state transition to the
transactional response flow: response failure leaves the counter, peer map, and
ratchet state unchanged, while replay history remains consumed.

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
[Stage 5 implementation record](../../doc/formal-verification-stage-5.md).

Stage 6 makes every proof-relevant byte layout visible to F* and adds the
handwritten PQXDH semantic lemmas. They prove exact tagged-key round trips,
registration-ID and root-input construction, associated-data ordering,
complementary role ratchet offsets, authenticated assigned-ID correspondence,
and checked server commit/abort behavior. The post-validation composed result is
conditional on pairwise X25519/ML-KEM agreement, authenticated role identities,
truthful replay and availability classifications, AEAD provenance for the
assigned-ID prefix, deterministic adapter KDFs, and non-rollback single-owner
server state. See the
[Stage 6 implementation record](../../doc/formal-verification-stage-6.md).

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
[Stage 7 implementation record](../../doc/formal-verification-stage-7.md) and
[current proof analysis](../../doc/formal-verification-analysis.md).

The production CTX transcript delegates to the core's fixed-size commitment builder.
Hax extracts that helper, and the strict F* commitment lemmas prove the exact 229-byte order `key || nonce || associated data || tag || LE64(sequence) || LE64(sender ID)`, injectivity of both integer encodings and the complete input, and `ctx_distinct_openings_imply_hash_collision`.
That theorem fixes one ciphertext, transmitted tag, and commitment and machine-checks an explicit collision witness for any two accepted explanations that differ in key, nonce, associated data, sequence, sender ID, or plaintext, while allowing the base AEAD to multi-open under unequal contexts.
The conventional [computational lifting](../../doc/ctx-commitment.md) bounds misattribution advantage by BLAKE2b-512 collision advantage, but the probability and runtime theorem is not mechanized.
A supplementary ProVerif differential control uses one deliberately multi-opening base-AEAD ciphertext/tag: the double-opening query is unreachable with CTX and deliberately reachable when only the CTX checks are removed.
The real-world binding claim remains conditional on BLAKE2b collision resistance, correct libsodium and adapter behavior, and hax/compiler correspondence.

Stage 9 adds the maintained trust-boundary inventory. It names every
proof-relevant opaque production wrapper and primitive law, the ratchet and
PQXDH adapter refinements, the pinned proof-library assumptions, all accepted
generated-backend exceptions, and every handwritten proof/model/control
fragment. A category/path/SHA-256 manifest and structural checks make an
unreviewed boundary change fail CI. See the
[canonical inventory](proofs/trusted-boundary.md) and
[Stage 9 implementation record](../../doc/formal-verification-stage-9.md).

## Strict hax/F*/ProVerif verification

From this directory, run:

```sh
make verify
```

The target enters the repository's locked Nix proof shell, checks the exact rustc, Cargo, hax, F*, Z3, and ProVerif identities, regenerates the F* commitment, ratchet, and PQXDH modules plus the ProVerif extraction, checks all three F* lemma modules without `--lax`, checks the complete reviewed trust-boundary inventory, and runs the CTX differential, baseline, reachability, failed-receive, and compromise models.
A policy gate rejects `assume` or `admit` in repository-owned F* modules and
lax/admitted-query checker flags. The result gate rejects timeouts, missing
queries, unexpected classifications, and every unproved or inconclusive
security query. `make verify-proverif` runs only the ProVerif extraction and
checks in the same locked shell.

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

The checked properties cover send and receive counter monotonicity and
exhaustion, receive-gap and cache bounds, retry retention, exact key
consumption and replay rejection, one-use send keys, and non-selected peer
isolation. The PQXDH properties cover exact type/role encodings and validation, the semantic
registration ID, root and associated-data transcripts, conditional honest-role
agreement, complementary ratchet initialization, authenticated key-ID
correspondence, replay-status handling, and checked server transactions.
`make check-generated` additionally fails when extraction changes a tracked
artifact or creates an untracked artifact, and it now inherits the inventory
gate from `make verify`. The dedicated formal-verification workflow runs that
complete target on every main-branch push, pull request targeting `main`, and
merge-queue check.

The checked-in `flake.lock` pins hax revision
`5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3` (hax 0.3.7), its
`nightly-2025-11-08` Rust toolchain (rustc 1.93.0-nightly, commit `843f8ce2e`),
F* revision `7b347386330d0e5a331a220535b6f15288903234`
(`2025.10.06~dev`), Z3 4.15.3, and ProVerif 2.05. Nix is invoked with
`--no-update-lock-file`, and the version gate fails before extraction if a
checked version banner differs. Z3 4.15.3 is the newest solver bundled by this
F* release and was qualified against the complete corpus; later F* releases
were tested and rejected by hax's proof libraries. See the
[Stage 8 implementation record](../../doc/formal-verification-stage-8.md).
