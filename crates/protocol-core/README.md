<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt protocol core

This `no_std` crate is the extraction boundary for beaconcrypt's protocol state machines. It intentionally has no cryptographic, serialization, FFI, or runtime dependencies. See the repository's [formal verification plan](../../doc/formal-verification.md) for the intended boundary and proof inventory.

The crate contains the control-plane state machines for the symmetric ratchet and PQXDH registration plus the fixed-width CTX commitment transcript builder. It owns ratchet counters, key availability and receive admission as well as deterministic PQXDH/commitment transcript construction, role-specific registration states, and commit/abort decisions.

The extracted `RefinedRatchet<SendChain, ReceiveChain, Material>` owns the complete symmetric-ratchet refinement state: logical control, opaque typed send and receive chains, and a packed fixed array of at most 50 sealed `CachedReceiveKey<Material>` values. Each cached value stores the logical sequence that caused the kernel to store its material. Production specializes and calls this same kernel rather than maintaining an independent parallel slot array, and lookup, completion, and serialization reject a cached tag that does not match the logical sequence in its slot.

HKDF is represented by the sole opaque step callback `fn(&Chain, &[u8]) -> RatchetStep<Chain, Material>`. Production applies HKDF-SHA-512 and passes its fixed 76-byte expansion to the extracted `split_ratchet_kdf_output`, which exposes borrowed views of the exact 32-byte key, 32-byte next-chain, and 12-byte nonce ranges before production wraps those named fields in its typed secret values; the only complete output buffer therefore remains under the adapter's zeroizing owner. Production delegates receive-until directly to `refined_advance_receive_until`, which decides admission and preflights every planned fixed-array destination before its first callback. A valid admitted future plan then executes the exact bounded sequence of counters, append slots, tagged cache entries, and callback-produced materials in order and reaches the requested receive counter without an intermediate reported failure that could publish only a prefix; an old or current target performs zero steps and leaves availability to the subsequent lookup. Every reported rejection is state-neutral and invokes no callback. The kernel also resolves material by sequence and performs retention or swap-removal of the complete tagged entry internally after authentication. On send, it returns a non-clonable `RefinedSendKey<Material>` that keeps the allocated sequence paired with its material until consuming finish. The older logical APIs remain available for proof compatibility.

The refined restoration builder accepts each `(sequence, material)` pair in one checked operation, seals that sequence into the cached value, and reconstructs control and cached slots together. The persistence adapter retains the five-field format containing `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`; serialization reads active sequence/material pairs through the tag-checking kernel accessor, and import supplies sorted pairs to the refined builder. Imports with more than 50 outstanding receive keys are rejected, as are legacy six-field objects containing `send_past`; this is an intentional compatibility break. The adapter remains responsible for the cryptographic provenance of each persisted pair because the kernel can preserve a supplied association but cannot prove that imported bytes were originally derived for the supplied sequence. See Step 3 of the [formal verification plan](../../doc/formal-verification.md) and the [Stage 3 implementation record](../../doc/formal-verification-stage-3.md).

The F* refinement lemmas are parametric in the chain and material types and in the step callback. They prove the exact 76-byte KDF-output partition, require every active cached tag to equal its logical slot sequence, prove direct mismatched-tag lookup rejection and full-state neutrality for `Missing` and `Retained` outcomes, and cover whole-plan preflight and rejection neutrality, exact bounded receive sequence/slot/material execution, future-target counter equality, preservation of old cached associations, zero-step old lookup, callback and mutation ordering, retry retention, exact internal swap-removal of complete tagged entries, restoration, and the consuming send-token lifecycle for normal returned transitions. The extracted completion code additionally validates the target and old-last tags before mutation and returns `Missing` without mutation on a disagreement. The lemmas deliberately do not assign cryptographic meaning to the HKDF bytes or callback output and do not prove callback panic behavior or crash atomicity.

The correspondence claim covers high-level encryption and decryption traces without state rollback. The concrete HKDF implementation, old-chain input and `SYM_RATCHET_INFO` label, faithful passage of the requested 76 bytes into the extracted splitter, faithful typed wrapping of its named result fields, callback panic behavior, authentication-result provenance, serde translation and persisted-pair cryptographic provenance, crash atomicity, physical erasure and zeroization, hax/Rust/compiler correspondence, direct low-level compatibility calls, pre-send state forks, and production peer-map selection remain explicit assumptions or exclusions. The key/next-chain/nonce offsets themselves are no longer an adapter assumption. `Clone` is available only when all three refined types are cloneable, so preventing state forks and rollback still relies on one authoritative production owner.

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

The target enters the repository's locked Nix proof shell, checks the exact rustc, Cargo, hax, F*, Z3, and ProVerif identities, regenerates the F* commitment, ratchet, and PQXDH modules plus the ProVerif extraction, checks all three F* lemma modules without `--lax`, and runs the CTX differential, baseline, reachability, failed-receive, and compromise models.
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

The checked ratchet properties cover the exact 76-byte key/next-chain/nonce partition, send and receive counter monotonicity and exhaustion, receive-gap and cache bounds, equality of every active cached sequence tag with its logical slot, mismatched-tag lookup rejection and neutral missing outcomes, whole-plan destination preflight, neutral callback-free rejection, exact bounded receive sequence/slot/material execution to the target counter for admitted future plans, preservation of existing cache associations, zero-step old lookup, callback ordering, lookup soundness and completeness, retry retention, internal swap-removal of complete tagged entries, paired restoration, exact key consumption and replay rejection, consuming refined send tokens, compatibility with the older logical transitions, and non-selected peer isolation. The extracted runtime also validates target and old-last tags before completion mutation. The PQXDH properties cover exact type/role encodings and validation, the semantic registration ID, root and associated-data transcripts, conditional honest-role agreement, complementary ratchet initialization, authenticated key-ID correspondence, replay-status handling, and checked server transactions.
`make check-generated` reruns the complete proof suite and additionally fails when extraction changes a tracked artifact or creates an untracked artifact. The dedicated formal-verification workflow runs that target on every main-branch push, pull request targeting `main`, and merge-queue check. Run the separate `make check-inventory` tripwire after reviewing intentional production/proof boundary changes.

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
