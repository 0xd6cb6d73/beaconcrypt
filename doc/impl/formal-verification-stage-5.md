<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 5 implementation

This document records the historical Stage 5 persistence boundary. The maintained high-level runtime makes operational ratchet state affine, exposes only inert update snapshots, and uses `PersistentServer` with a trusted `SnapshotStore` for restart and multi-owner safety. The store must supply payload integrity and provenance plus linearizable, durable, rollback-resistant generation/head CAS; snapshots have no cryptographic authentication or encryption. Neither the Stage 5 proof nor current F* verifies the codec, store, crash durability, or deployment discipline.

## Status and scope

Stage 5 closes the three executable counterexamples identified by the formal
verification plan. It authenticates the beacon's assigned key ID, permanently
rejects reuse of an accepted registration, and replaces wrapping server key-ID
allocation with checked, collision-safe transitions. The implementation was
based on commit `bff24136315c1a29e245b2cfdd15b158904eb41d`, whose Stage 4 work
introduced the PQXDH typestates and transactional response commit used here.

The Stage 4 changes were reviewed before extending them. In particular, this
stage preserves their role-specific provider state, opaque pending server
token, server-binding check, off-map ratchet initialization, and final atomic
publication of the counter, peer, and ratchet. It deliberately changes one
part of Stage 4's failure semantics: a successfully accepted `InitKex` now
updates replay history before a response token is returned, so that update is
not rolled back if response construction later fails.

This stage adds no PQXDH agreement theorem and no ProVerif model. The newly
extracted transitions are strictly typechecked by F* and their generated
safety obligations are discharged, but the semantic PQXDH lemmas remain Stage
6 and the active-attacker trace properties remain Stage 7.

## Implementation map

| File | Responsibility |
| --- | --- |
| `crates/protocol-core/src/pqxdh.rs` | Define the semantic registration ID, replay classification, authenticated key-ID typestate, checked allocation, and collision classification. |
| `crates/protocol-core/Makefile` | Add the Stage 5 public transitions to pinned hax extraction. |
| `crates/protocol-core/proofs/fstar/extraction/Beaconcrypt_protocol_core.Pqxdh.fst` | Track regenerated F* output; it remains generated rather than hand-maintained. |
| `src/pqxdh.rs` | Refine core classifications with production sets/maps, bind the assigned ID inside the initial ciphertext, and apply the new transitions. |
| `src/ser.rs` | Serialize replay history deterministically. |
| `src/deser.rs` | Restore only present, fixed-size, duplicate-free replay histories consistent with the peer count. |
| `src/server.rs` | Document the permanent consumption point of a successful acceptance. |
| `src/shared.rs` | Make the compatibility key-ID allocator fallible. |
| `tests/protocol.rs` | Enable the two remaining counterexample regressions and cover persistence, semantic canonicalization, deletion, exhaustion, collision, and failure ordering. |
| `tests/server.rs` and `tests/test_server_state.py` | Cover replay-history persistence and malformed-state rejection through Rust and Python-facing server state. |
| `doc/protocol.md` and `doc/persistence.md` | Record the changed handshake plaintext and server-state formats. |

No generated F* file was hand-edited, and no handwritten Stage 5 lemma module
was added.

## Authenticated assigned key ID

The Stage 4 response carried the assigned beacon key ID only in the outer
`KexResponse.keyId` field. That field selected the candidate identity on the
beacon, but it was not covered by AEAD or by the CTX commitment. An attacker
could therefore replace it while leaving the initial ciphertext valid.

Stage 5 binds the value without changing the established associated-data or
commitment layouts. The server constructs the initial plaintext as:

```text
LE64(assigned beacon key ID) || application plaintext
```

When no application plaintext is supplied, the existing one-byte `0xFF`
registration witness follows the prefix. An explicitly supplied empty slice
remains invalid. The eight-byte prefix and the application bytes are encrypted
together using the staged initial send ratchet, so AEAD authentication covers
the complete value. The temporary combined plaintext is explicitly zeroized
after the encryption call.

On the beacon, `beacon_prepare_finish` still treats `KexResponse.keyId` only as
a proposed assignment. After initial-message authentication, the adapter
requires more than eight plaintext bytes, splits the exact eight-byte prefix,
and passes it to:

```rust
authenticate_registration_key_id_binding(
    candidate: BeaconRegistrationCandidate,
    authenticated_binding: [u8; 8],
) -> Result<AuthenticatedBeaconRegistration, RegistrationError>
```

The core compares the prefix to `candidate.assigned_key_id().to_le_bytes()`.
Only the resulting `AuthenticatedBeaconRegistration` is accepted by
`beacon_commit`; a plain `BeaconRegistrationCandidate` is no longer a
committable type. The production adapter publishes the assigned ID, associated
data, and staged ratchet only after this transition succeeds, and strips the
prefix before returning the original application plaintext.

This design keeps two existing fixed-format inputs unchanged:

- the long-lived PQXDH associated data remains exactly 153 bytes; and
- the CTX commitment remains `(key, nonce, associated data, tag, sequence,
  sender ID)` with its existing fixed-width fields.

The outer `KexResponse.keyId` and the inner `CryptoFrame.keyId` have different
roles. The outer field assigns the receiving beacon's identity. The inner
field identifies the sending server and is already bound by the record
commitment. The new encrypted prefix authenticates the former; it does not
replace or duplicate the latter.

The core equality transition by itself does not prove authenticity. Its
adapter precondition is that the supplied eight bytes came only from a
successfully opened initial AEAD ciphertext under the staged session. That
precondition, and the assumed authenticity of AEAD, are part of the primitive
and adapter boundary.

## Semantic registration replay identifier

Replay tracking does not use serialized Cap'n Proto bytes. Different accepted
wire encodings can represent the same public keys, and keying the replay table
by raw bytes would let such encodings bypass it. It also does not hash the
registration, avoiding a new collision-resistance assumption in the
functional core.

After signature verification and key-type validation, `VerifiedInitKex`
constructs the exact 64-byte identifier:

```text
beacon Ed25519 identity public key (32 bytes)
|| signed one-time X25519 public key (32 bytes)
```

Both components are decoded public-key bytes authenticated by the accepted
`InitKex`. Including the identity scopes one-time keys to a beacon principal;
including the one-time key makes each honest registration attempt distinct.
Reusing that tuple is rejected even if the prekey, post-quantum key, signatures,
or wire representation differ.

The core exposes `RegistrationStatus::{Fresh, Consumed}` and rejects
`Consumed` in both `validate_registration_status` and `server_accept`.
Production maintains the refinement with a
`HashSet<[u8; REGISTRATION_ID_SIZE]>`:

1. parse the message and verify all three signed public-key payloads;
2. validate their disjoint core-owned key tags;
3. construct the semantic ID and reject it if already present;
4. reserve set capacity before expensive acceptance can succeed;
5. perform KEM, DH, root-input validation, and root derivation;
6. insert the ID; and
7. return the opaque pending response token.

Malformed messages, invalid signatures or tags, failed primitive operations,
invalid DH output, failed root construction, and allocation failure do not
consume an identifier because no pending token is returned. Once
`get_shared_secret` succeeds, consumption is permanent for that server state:

- dropping or moving the pending token does not undo it;
- failure to build or serialize a response does not undo it;
- key-ID exhaustion or collision during response building does not undo it;
- deleting the eventual peer does not undo it; and
- export followed by restoration does not undo it.

This consumption point prevents two successful pending tokens for the same
registration. It necessarily precedes final peer publication: waiting until
`server_commit` would leave a replay window whenever a token was dropped or a
response failed.

The replay set is local to one mutable provider instance. The Rust `&mut self`
entry point serializes calls to that instance, but independent restored forks,
multiple server replicas, or rollback to an older snapshot require external
coordination and anti-rollback storage. Stage 5 does not claim global replay
protection across such forks.

## Replay-history persistence

Server export adds a required `consumed_registrations` array. Each element is
exactly 64 bytes. Serialization sorts the entries lexicographically, making
otherwise unordered `HashSet` state deterministic and stable for persistence
comparisons.

Restoration rejects:

- a missing `consumed_registrations` field;
- an entry shorter or longer than 64 bytes;
- a duplicate entry; or
- fewer consumed identifiers than committed peer entries.

The last check is a conservative structural invariant for states produced only
by the high-level registration path. The persistence format cannot reconstruct
the exact peer-to-one-time-key relationship from `known_ids`, so it cannot
prove set membership for each peer. Direct peer-map compatibility mutators can
also create peers without registrations and remain outside the verified trace,
as they did in Stage 4.

Pre-Stage-5 snapshots have no replay history and are intentionally rejected.
Defaulting the new field to an empty set would silently reopen every prior
registration for replay. Operators must migrate by establishing trusted replay
history or begin with a new server state; there is no safe automatic inference
from the old four-field snapshot.

The history currently has no expiry or size bound. Any party able to submit
arbitrarily many cryptographically valid, self-signed registration bundles can
grow both memory use and persisted state. Bounding or externally storing that
history requires a retention rule compatible with the desired replay theorem
and is an explicit operational limitation of this stage.

## Revised server transaction

Stage 4 made response publication transactional. Stage 5 preserves that
transaction for the counter, peer map, and ratchet, while replay consumption
becomes an earlier monotonic transition:

```text
verified fresh InitKex
  -> derive root and consume registration ID
  -> PendingServerRegistration
  -> checked unoccupied key ID
  -> staged peer + encrypted and serialized response
  -> commit counter, peer, and ratchet together
```

If response preparation fails, the live counter, peer map, and ratchet remain
unchanged, and the next fresh registration can still receive the same proposed
key ID. The consumed registration ID remains present, so the failed attempt
cannot itself be retried. This is the intentional Stage 5 exception to Stage
4's statement that every failed response leaves the complete exported state
unchanged.

The opaque pending token records its semantic registration ID as well as the
Stage 4 server identity binding. The production set owns replay history; the
token carries the ID only to preserve correspondence and support assertions.
Moving a token to a differently identified server still fails the core binding
check without publishing counter, peer, or ratchet state.

## Checked, collision-safe key-ID allocation

`ServerState` continues to store the last allocated remote key ID. The new
`server_next_key_id` transition returns an explicit `KeyIdExhausted` error at
`u64::MAX`; it never wraps to zero. It computes a proposal without changing
the live state.

`server_prepare_commit` additionally requires
`KeyIdAvailability::{Available, Occupied}` for that exact proposal and returns
`KeyIdCollision` for an occupied value. The production adapter derives the
classification from `known_ids` immediately before candidate preparation.
Only `server_commit` advances the core and production counters.

The public low-level `CryptoProvider::new_remote_kid` compatibility method now
returns `Option<u64>`. On a server it applies the same checked increment and
peer-map collision test before advancing; on exhaustion or collision it
returns `None` without changing either counter. This removes the second
wrapping allocation path. Registration itself does not call this mutating
helper, retaining the staged transaction described above.

The core transition makes overflow and collision handling explicit, but the
correctness of `KeyIdAvailability` remains an adapter refinement obligation.
For the production high-level path it is derived directly from the unique-key
`HashMap`; callers invoking low-level peer-map mutators remain outside the
formal trace.

## Compatibility effects

The Cap'n Proto schemas and high-level C ABI registration signatures are
unchanged. Nevertheless, Stage 5 intentionally changes protocol behavior:

- registration plaintext gains an authenticated eight-byte prefix, so
  pre-Stage-5 and Stage-5 peers are not registration-wire-compatible even
  though `KexResponse` has the same fields;
- server JSON state gains a required fifth field and old snapshots fail closed;
- the Rust low-level `new_remote_kid` method changes from `u64` to
  `Option<u64>`; and
- the two formerly ignored security regressions are now mandatory.

Established-session record framing, the 153-byte associated data, the CTX
commitment input, and application plaintext returned after a successful new
registration remain unchanged. No new secret is added to persistence; the
replay IDs consist only of authenticated public keys.

## Extraction and proof boundary

The pinned hax item list now includes:

- `registration_key_id_binding` and
  `authenticate_registration_key_id_binding`;
- `validate_registration_status` and the extended `server_accept`;
- `server_next_key_id`; and
- the extended `server_prepare_commit`.

`make -C crates/protocol-core verify` regenerates the PQXDH F* module and
checks it without `--lax`. The generated Stage 5 artifact is 1,036 lines with
SHA-256
`e4c5ee1b84aa833644640a91b465a730bdc39c2ea6e8feaca0ed2b4469981670`.
All generated verification conditions were discharged. As with the Stage 4
fixed-array builders, the registration-ID copy loop repeats its input and
output bounds inside the loop body because hax does not infer the `while`
condition as an F* loop invariant.

That result is deliberately narrower than a protocol proof. In particular:

- the `HashSet` lookup, insertion, serialization, and anti-rollback behavior
  are outside extraction; the core receives an adapter-supplied replay status;
- the peer-map lookup is outside extraction; the core receives an
  adapter-supplied availability status;
- the authenticated-prefix claim assumes the adapter passes bytes obtained
  from a successful AEAD open;
- Cap'n Proto translation, cryptographic primitive calls, allocation,
  persistence integrity, concurrency across replicas, and zeroization remain
  outside the core proof; and
- there are still no handwritten PQXDH agreement, transcript, associated-data,
  ratchet-initialization, or registration-correspondence lemmas.

The core tests establish executable behavior for the pure transitions. They do
not turn the adapter refinements above into F* theorems. Those assumptions must
remain visible when Stage 6 lemmas and Stage 7 ProVerif queries are stated.

## Regression coverage

Stage 5 enables the two remaining ignored counterexample tests and adds or
strengthens coverage for:

- rejection of an outer assigned key ID that does not match the authenticated
  plaintext prefix;
- replay rejection immediately after the first successful server acceptance;
- acceptance of the original registration after invalid signatures or signed
  key-type encodings were rejected, showing that pre-acceptance failures do not
  consume its identifier;
- replay rejection after the pending token is dropped;
- replay rejection after export and restore;
- replay rejection after a committed peer is deleted;
- equality of semantic replay IDs across alternate accepted wire encodings;
- permanent replay consumption after response construction fails;
- acceptance of a fresh registration after that failure without counter loss;
- allocation of `u64::MAX` exactly once, followed by state-neutral exhaustion
  without wrap to zero;
- preservation of exhausted state through export and restore;
- rejection of an occupied next ID by both registration and compatibility
  allocation paths without counter advancement;
- deterministic 64-byte replay-history export; and
- rejection of missing, malformed, duplicate, and structurally incomplete
  replay histories in Rust and Python-facing persistence tests.

Core unit tests separately cover exact registration-ID layout, little-endian
key-ID encoding and authenticated equality, consumed-status rejection before
root construction, checked exhaustion, explicit collision rejection, and
state-neutral failure.

## Validation performed

The implementation was validated with:

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

The complete Rust workspace run has 164 passing tests, with no ignored or
failed tests. The strict F* run reports that every verification condition was
discharged without lax checking. Both minimal role feature builds, the lint
run with warnings denied, and the release Go facade and Go tests pass. The
Python extension build and all 33 Python tests also pass, including the
Python-facing malformed replay-history cases.

The generated extraction changed only through the pinned `make verify` path.
`make check-generated` is intended for a clean committed baseline; while this
stage is an uncommitted implementation diff, its tracked-output check would
correctly report the new generated artifact as different from Stage 4.

## Remaining rollout work

Stage 6 must add semantic F* lemmas for honest root agreement, exact transcript
construction, associated-data equality, matching role-dependent ratchet
initialization, and the new assigned-ID correspondence transition. It should
also make the adapter classification preconditions explicit rather than
mistaking extracted status enums for verified storage.

Stage 7 must model registration events and replay consumption in ProVerif
before enabling injective agreement and replay-resistance queries. The model
must distinguish acceptance from final response commit, because Stage 5
consumes replay history at the former point. It must also state the single,
non-rollback server-state assumption and must not infer global replay
resistance across uncoordinated replicas.

Stage 8 still needs to put the complete pinned extraction and proof suite into
CI, and Stage 9 still needs the reviewed inventory of opaque adapter behavior,
primitive assumptions, and handwritten backend fragments.
