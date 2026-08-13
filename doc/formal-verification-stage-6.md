<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 6 implementation

## Status and scope

This document records the original Stage 6 snapshot. The maintained core stores the configured public key and numeric identity-key ID together in beacon state and proves their preservation and agreement through successful response-key and authenticated sender-ID acceptance; see [the current analysis](formal-verification-analysis.md#pqxdh-registration-and-key-establishment). The maintained adapter additionally uses affine establishment-gated runtime state and trusted-store generation/head CAS persistence, but those mechanisms do not strengthen the Stage 6 F* theorem and remain external refinements. Adapter-only equality and persistence descriptions below are historical.

Stage 6 adds the handwritten F* semantics for the extracted PQXDH protocol
core. It proves exact key tagging and validation, registration-ID and root
transcript construction, associated-data construction, conditional honest-role
agreement, complementary ratchet initialization, and the Stage 5 assigned-ID
and transactional state correspondences.

The implementation is based on commit
`36cac8793456518871441795588cd3af9eb170d9`, which completed Stage 5. That
commit was reviewed before this work. Its runtime transitions and regression
coverage were preserved, but its generated PQXDH module exposed several
operations only through trusted hax-library interfaces. Strictly checking the
generated module established safety relative to those interfaces; it did not
yet make the byte layouts available for semantic proof.

This stage remains a functional protocol-core proof. Concrete X25519, ML-KEM,
HKDF, signature, and AEAD operations are outside extraction. The honest
agreement result therefore states their required laws as adapter preconditions
instead of assuming or reimplementing the primitives in F*. Active-attacker
trace properties remain Stage 7 work.

## Implementation map

| File | Responsibility |
| --- | --- |
| `crates/protocol-core/src/pqxdh.rs` | Replace proof-opaque byte construction with specified fixed-range operations, make LE64 construction explicit, and avoid derived whole-struct equality in an extracted branch. |
| `src/shared.rs` | Tie the production KDF output sizes to the core ratchet-chain size at compile time. |
| `crates/protocol-core/Makefile` | Include production-used candidate ratchet and assigned-ID accessors in extraction. |
| `crates/protocol-core/proofs/fstar/extraction/Beaconcrypt_protocol_core.Pqxdh.fst` | Track the regenerated PQXDH module; it remains generated and is not hand-edited. |
| `crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst` | State and prove the Stage 6 PQXDH semantic and correspondence properties. |
| `crates/protocol-core/proofs/fstar/Makefile` | Check multiple handwritten modules with per-module hints through one strict invocation. |
| `crates/protocol-core/README.md` and `doc/formal-verification.md` | Record the completed theorem scope and its explicit assumptions. |

## Review of the Stage 5 proof surface

The Stage 5 implementation correctly introduced the authenticated assigned-ID
typestate, persistent replay classification, checked allocation, and explicit
collision classification. Its production tests showed the intended behavior.
The review found five proof-surface gaps to close before claiming Stage 6:

- fixed-size copy helpers extracted through
  `Rust_primitives.Hax.while_loop_return`, whose interface has no semantic
  postcondition, so exact registration-ID, root, tag, and associated-data
  layouts were not derivable;
- the pinned model of `u64::to_le_bytes` did not expose the eight byte values;
- derived equality for the whole `ServerBinding` struct introduced a local
  unconstrained `impl_116'` assumption in the generated PQXDH module;
- the candidate methods actually used by the production adapter to obtain
  ratchet plans and key-ID bindings were not selected for extraction; and
- the production KDF buffer constants were numerically equal to the core
  ratchet size but were not compile-time-linked to it.

Fixed-array `=.` and `<>.` in the generated code were also audited. In the
pinned proof library those operators are direct F* logical equality and
inequality, not an opaque `PartialEq` call. They remain suitable for the
all-zero DH check, authenticated binding comparison, and fixed-array identity
comparison. Only the former derived whole-struct equality required removal.

## Proof-transparent byte construction

The core now uses fixed `copy_from_slice` ranges for every proof-relevant
layout. Hax translates them to the monomorphized `update_at_range`,
`update_at_range_to`, and `update_at_range_from` operations. Their F*
interfaces specify the exact replaced slice and preservation of the prefix and
suffix. The handwritten lemmas can consequently recover every byte segment
without trusting a loop summary.

The ranges are literal so the generated arithmetic is stable and immediately
visible to F*. Compile-time assertions tie those literals to the public core
constants:

```text
registration ID:  [0, 32) || [32, 64)
root input:        [0, 32) padding, then five 32-byte secret ranges
associated data:  [0, 33), [33, 66), [66, 112), [112, 153)
tagged keys:       one tag byte followed by 32 or 1184 key bytes
```

The assertions also pin the ratchet half to 32 bytes and the assigned-ID
binding to eight bytes. Production `KEX_KDF_OUT_LEN` and `KDF_STATE_SIZE` are
now each asserted equal to the core `RATCHET_CHAIN_SIZE`, preventing the
adapter's concrete slices from drifting away from the verified offsets.

Assigned IDs are constructed from eight explicit shifted byte expressions.
The generated model exposes Rust's narrowing cast as modulo 256 and exposes
right shift as division by the corresponding power of two. This supports an
arithmetic LE64 theorem rather than relying on the opaque standard-library
`to_le_bytes` model. A Rust regression compares the explicit implementation to
`u64::to_le_bytes` for zero, ordinary, patterned, 32-bit-maximum, and
64-bit-maximum values.

`server_prepare_commit` now compares the server identity key ID and public key
as separate fields. This is behaviorally equivalent to the previous derived
`ServerBinding` equality and removes the generated local equality assumption.
Tests exercise a mismatch in each field independently.

## PQXDH theorem inventory

The handwritten module proves the following properties directly against the
regenerated Rust extraction, without a second handwritten protocol model.

### Tagged initialization material

- Ed25519, ML-KEM-768, and X25519 tags have values 1, 3, and 4 and are pairwise
  distinct.
- Each encoded key is exactly its one-byte tag followed by the unchanged
  public-key bytes.
- Each tag/untag pair round-trips exactly.
- A message produced by `beacon_start` is accepted by `validate_init_kex` and
  recovers all four original public keys while preserving the pending beacon
  identity and server ID.

Signature verification remains an adapter precondition. The core theorem
covers the exact tagged payloads that the adapter signs, verifies, and passes
to validation; it does not prove Ed25519 itself.

### Registration and root transcripts

- `VerifiedInitKex::registration_id` is exactly the 32-byte authenticated
  beacon identity followed by the 32-byte authenticated one-time X25519 key.
- Successful root-input construction is exactly 32 bytes of `0xff`, followed
  by DH1, DH2, DH3, DH4, and the ML-KEM shared secret, each 32 bytes.
- Root construction rejects exactly when at least one classical DH output is
  all zero, and reports `InvalidDhOutput`.
- If the beacon and server adapters supply pairwise-equal DH1 through DH4 and
  KEM secret values, both roles produce the same success or failure and the
  same root-input bytes on success.

The equality result is an IKM/transcript agreement result. Equal concrete HKDF
roots follow under the explicit adapter law that HKDF is deterministic for the
same input and `PQXDH_INFO`; no claim is made about HKDF's implementation or
computational security.

### Associated data and ratchets

- Associated data is exactly tagged server identity, tagged beacon identity,
  the 46-byte `PQXDH_INFO`, and the 41-byte `SYM_RATCHET_INFO`, in that order.
- Equal authenticated role identities imply byte-for-byte associated-data
  agreement.
- Beacon send/server receive use offset 32, while beacon receive/server send
  use offset 0. Both the public helpers and the candidate accessors choose the
  same complementary plan for the two 32-byte halves of the 64-byte adapter
  KDF result.

### Assigned IDs and server transaction

- Every assigned-ID binding byte is the corresponding LE64 quotient modulo
  256.
- The exact candidate binding authenticates, every unequal binding returns
  `KeyIdMismatch`, and commit preserves the IDs in an authenticated record.
- `Fresh` is admitted and `Consumed` returns `RegistrationReplay` before root
  construction.
- Fresh server acceptance preserves the live counter state and constructs the
  exact semantic registration ID, root input, public response material, and
  server binding in the pending token.
- Next-ID allocation is either mathematical increment by one or explicit
  `KeyIdExhausted` at `u64::MAX`; it never wraps.
- A changed server public key or identity key ID returns `IdentityMismatch`,
  and an adapter-classified occupied proposal returns `KeyIdCollision`.
- A truthful available classification constructs the exact next candidate,
  response AD, and peer metadata. Core commit returns exactly that next state
  and peer; abort returns the exact previous state.

The composed honest-run correspondence begins with pairwise primitive-secret
agreement, the same authenticated server and beacon identities, a fresh
semantic registration classification, an available next ID, and a
non-exhausted counter. It follows the extracted beacon and server transitions
through candidate preparation, authenticates the server candidate's binding
on the beacon, and relates both commits. On success it establishes equal root
inputs, equal associated data, complementary ratchet directions, equal binding
bytes, and the same assigned/established peer ID. This success theorem requires
valid DH inputs. Separately, pairwise secret agreement and the all-zero
rejection lemma establish that both roles return `InvalidDhOutput` for an
invalid DH input.

Rust keeps `AuthenticatedBeaconRegistration` fields private and exposes the
authentication transition as the production constructor, so an ordinary
`BeaconRegistrationCandidate` is not accepted by the production commit API.
F* record constructors are visible inside the proof language; the isolated
commit-field lemma therefore proves preservation, not unforgeability of that
record. The composed theorem establishes provenance by invoking
`authenticate_registration_key_id_binding` on the compared server binding
before relating the commits.

This is a post-validation protocol-core correspondence, not a complete wire
handshake theorem. It starts from `VerifiedInitKex` and `BeaconInitSent` values
whose beacon identities agree; the separate start/validation theorem proves an
honest constructor round trip, while signature checks, wire provenance, and
the relationship of all received keys to that earlier start remain adapter
obligations.

## Explicit adapter and primitive preconditions

The proof deliberately does not turn adapter attestations into facts. The
production high-level trace must establish all of the following:

- X25519 agreement pairs the server and beacon DH1 through DH4 results in the
  order represented by `PqxdhSharedSecrets`, and ML-KEM encapsulation and
  decapsulation produce the same secret;
- the same fixed root input and `PQXDH_INFO` are passed to deterministic HKDF;
- signature verification authenticates the public material passed to
  `validate_init_kex`;
- the beacon's configured expected server identity, the parsed response
  identity, and the current server binding name the same public key; the
  theorem constructs the honest core input with that equality, while applying
  it to parsed production inputs requires the adapter to establish the
  equality rather than treating response-wire authentication as proved;
- the binding supplied to the beacon authentication transition is the exact
  eight-byte prefix returned by a successful initial AEAD open;
- `RegistrationStatus::Fresh` means the exact 64-byte registration ID is not
  in the persistent consumed set, and successful acceptance inserts it
  monotonically;
- `KeyIdAvailability::Available` means the exact proposed ID is absent from
  the production peer map at candidate preparation; and
- the server state is single-owner and non-rollback for the trace. Independent
  replicas, restored forks, or rollback require external coordination and are
  not covered by the local replay result.

Cap'n Proto translation, allocation failure, persistence integrity,
zeroization, concrete ratchet byte slicing, and low-level compatibility
mutators remain adapter obligations. Stage 6 narrows and documents that
boundary; it does not silently verify those components.

Likewise, `server_commit` in F* returns the proposed core state and
`EstablishedPeer`. Atomic mutation of the production counter, peer map, and
concrete ratchet is adapter behavior covered by the high-level transaction and
regression tests, not by the pure return-shape lemma alone.

## Strictness and assumption audit

The proof target checks generated modules first and handwritten modules second
with the same pinned F*, Z3, proof libraries, checked-module cache, and strict
flags. Multiple handwritten roots now use `--hint_dir`, allowing F* to select
the corresponding hint file for each module. The target never passes `--lax`.

The Stage 6 generated PQXDH module contains no local `assume`, `admit`,
`while_loop_return`, opaque `u64::to_le_bytes`, or derived `ServerBinding`
equality helper. The handwritten module also contains no `assume` or `admit`.
This does not eliminate the reviewed primitive and adapter assumptions listed
above, nor the trusted interfaces in the pinned hax/F* libraries. It ensures
the Stage 6 conclusions are derived from specified array and integer semantics
rather than from newly introduced local axioms.

The final generated PQXDH artifact is 909 lines with SHA-256
`5ba8e8c6f835b635d0e93fa0b30aa8a11cbf0e7e283a782c7efd31dc0005c8e4`.
The handwritten PQXDH lemma module is 726 lines with SHA-256
`bbdcc9417cdfd3339d10ffc6e5a189e49579e4b09ab0907c797cad58e28b124a`.

## Compatibility effects

The Stage 6 Rust changes are proof-transparency refactors. They preserve the
Stage 5 wire format, 153-byte associated data, 192-byte root input, semantic
registration ID, authenticated eight-byte assigned-ID prefix, and transaction
ordering. No public high-level API or persistence format changes in this
stage. Compile-time size assertions intentionally turn future layout drift
into a build failure that must be reconciled with the proofs.

## Validation performed

The final implementation was validated with:

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
uv run maturin develop --uv
uv run pytest tests
```

The complete Rust workspace reports 166 passing tests with no failures or
ignored tests, including 25 protocol-core unit tests. Both minimal role builds
and the warnings-denied Clippy command exit successfully. The release Go
binding build and Go tests pass. The Python extension builds and all 33 Python
tests pass.

The standard outer verification command regenerates the two extracted modules
with the pinned hax revision, reports both generated files unchanged from the
preceding pinned regeneration, and strictly verifies the generated PQXDH and
ratchet modules plus both handwritten lemma modules. F* reports all
verification conditions discharged successfully and the command exits zero;
neither the Makefile nor the invocation contains `--lax`.

A final static gate over the generated and handwritten PQXDH files finds no
local `assume`, `admit`, `while_loop_return`, modeled `u64::to_le_bytes`, former
derived `ServerBinding` helper, or bare unspecified array-range update. `git
diff --check` and the final formatting check also pass. `make check-generated`
is intended for a committed generated baseline; during this uncommitted Stage
6 implementation it would correctly flag the intentional change from Stage 5.

## Remaining rollout work

Stage 7 must add ProVerif processes, events, equations, compromise scenarios,
and queries for active-attacker secrecy, authentication, injective agreement,
replay, session separation, and compromise behavior. It must distinguish the
server's monotonic replay-consumption event from the later transactional peer
commit.

Stage 8 still needs to run the complete pinned proof suite in CI. Stage 9 must
maintain the reviewed inventory of primitive laws, adapter refinements, proof
library assumptions, generated exceptions, and handwritten backend fragments.
