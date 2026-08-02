<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt protocol core

This `no_std` crate is the extraction boundary for beaconcrypt's protocol
state machines. It intentionally has no cryptographic, serialization, FFI, or
runtime dependencies. See the repository's
[formal verification plan](../../doc/formal-verification.md) for the intended
boundary and proof inventory.

The crate contains the control-plane state machines for the symmetric ratchet
and PQXDH registration. It owns ratchet counters, key availability and receive
admission as well as deterministic PQXDH transcript construction,
role-specific registration states, and commit/abort decisions. Cryptographic
chain bytes, concrete message keys, private-key operations, and entropy stay
behind the adapter boundary.

The receive cache is a packed fixed array of at most 50 logical key sequences.
Its operations are implemented directly rather than through an assumed `Vec`
model, so F* can see allocation and exact-key removal. The production adapter
maintains this refinement invariant:

```text
keys(concrete_receive_key_map) == logical_receive_sequences(core_state)
```

The existing beaconcrypt API now delegates its ratchet control decisions to
this crate. For each admitted logical step, the adapter performs exactly one
opaque KDF operation and associates the resulting concrete key with the same
sequence. It removes concrete receive keys only when the core consumes their
logical capability, retains both representations on authentication failure,
and completes allocated send capabilities on both successful and failed
encryption paths.

The persistence adapter preserves the existing six-field wire format. It
serializes counters from the authoritative core state and reconstructs the
logical receive cache from sorted concrete-map keys through the checked
restoration API. Imports with more than 50 outstanding receive keys are
rejected. See Step 3 of the
[formal verification plan](../../doc/formal-verification.md) and the
[Stage 3 implementation record](../../doc/formal-verification-stage-3.md).

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
constructs and validates disjoint key tags, fixes the
`Padding || DH1 || DH2 || DH3 || DH4 || SS` root input, orders associated data
as server identity then beacon identity, and selects complementary beacon and
server ratchet halves. The production adapter signs and parses Cap'n Proto,
performs libsodium and ML-KEM operations, and applies the resulting plan.
Secret-bearing transcript and candidate values are not `Copy`, `Clone`, or
`Debug`; the adapter zeroizes its shared-secret copy and the concrete root
transcript after use, while physical erasure remains outside the formal claim.

The beacon emits one registration bundle and treats every finish failure as a
terminal abort. It publishes the assigned identity, associated data, and
derived ratchet only after the initial ciphertext authenticates. The server
initializes a fresh peer ratchet, encrypts the initial message, and serializes
the response off to the side; only then does it commit the key counter and peer
map. A failed response leaves those values and the staged ratchet unchanged.

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
PQXDH functional lemmas remain Stage 6 work.

## Strict hax/F* verification

From this directory, run:

```sh
make verify
```

The target enters the pinned hax Nix shell, regenerates the ratchet and PQXDH
modules under `proofs/fstar/extraction`, and fully checks both generated
modules, their dependencies, and the hand-maintained ratchet lemmas in
`proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst`. It never passes
`--lax`.

The checked properties cover send and receive counter monotonicity and
exhaustion, receive-gap and cache bounds, retry retention, exact key
consumption and replay rejection, one-use send keys, and non-selected peer
isolation. The PQXDH module, including the Stage 5 key-ID binding, replay
classification, and checked allocation transitions, is extracted and its
generated safety obligations are strictly verified, but it has no handwritten
semantic property lemmas yet; those are deliberately scheduled for Stage 6.
`make check-generated` additionally fails when a tracked extraction changes,
which is suitable for a generated-diff CI check.

The hax revision is
`5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3` (hax 0.3.7). Its lock file pins
the coupled tools used here, including Rust nightly 2025-11-08 (rustc 1.93.0),
F* v2025.10.06, and Z3 4.13.3.
