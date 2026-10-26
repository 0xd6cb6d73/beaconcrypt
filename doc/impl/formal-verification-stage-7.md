<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 7 implementation

This document records the historical Stage 7 symbolic model. Its replay owner still assumes one serialized non-rollback owner and does not model the maintained `PersistentServer`, canonical codec, trusted payload integrity/provenance, external generation/head CAS store, or affine establishment gate. Snapshots have no cryptographic authentication or encryption. Those production controls help discharge the model premise only when their external contracts hold; ProVerif does not prove them or turn the model into a multi-replica theorem.

## Status and scope

Stage 7 adds an active-attacker ProVerif model for PQXDH registration and a
bounded symmetric-ratchet record trace. It covers secrecy, authenticated
agreement, persistent registration replay rejection, exact record
correspondence, reachability, deleted-key forward secrecy, cached skipped-key
exposure, and the protocol's deliberate lack of post-compromise security.

The implementation is based on commit
`493a23fad65e0971f38631c5cd1e5f5cb0da2e61`, which completed Stage 6. That
commit and its complete diff were reviewed before this work. In particular,
Stage 6 made the registration ID, six-part root input, associated data,
assigned-ID binding, and complementary ratchet initialization visible to F*
and proved their exact layouts without `--lax`, local `assume`, or `admit`.
Stage 7 preserves those functional results, extends one signed-key layout in
response to an active-attacker counterexample, regenerates the F* extraction,
and rechecks the affected lemmas before adding trace claims.

This is a symbolic proof under ideal primitive equations. It does not prove
the computational security of Ed25519, X25519, ML-KEM, HKDF, ChaCha20-
Poly1305, or BLAKE2b. It also does not verify Cap'n Proto, concrete memory
allocation, persistence code, zeroization, replicas, rollback recovery, or
bindings.

## Implementation map

| File | Responsibility |
| --- | --- |
| `crates/protocol-core/src/pqxdh.rs` | Add exact X25519 type/role encodings, expose production wrappers to hax, and attach the three reviewed ProVerif replacements. |
| `src/pqxdh.rs` | Use the shared registration-ID wrapper and sign/validate the role-bearing core encodings on the production wire. |
| `crates/protocol-core/proofs/fstar/extraction/Beaconcrypt_protocol_core.Pqxdh.fst` | Track regenerated F* after the 33-to-34-byte X25519 encoding change. This file remains generated. |
| `crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst` | Prove concrete marker values, exact type/role byte positions, both role-specific round trips, and cross-role rejection while retaining every Stage 6 theorem. |
| `crates/protocol-core/proofs/pro-verif/extraction/lib.pvl` | Generated hax types, constructors, accessors, converters, and the three production-core replacements used by the model. This file is never hand-edited. |
| `crates/protocol-core/proofs/pro-verif/crypto.pvl` | Reviewed symbolic primitive boundary and exact seal/open equation. |
| `crates/protocol-core/proofs/pro-verif/environment.pvl` | Public wire, events, replicated beacon/server processes, non-rollback replay owner, bounded records, and synchronized state compromise. |
| `crates/protocol-core/proofs/pro-verif/queries.pvl` | Eleven baseline secrecy and injective-correspondence queries. |
| `crates/protocol-core/proofs/pro-verif/reachability-queries.pvl` | Five non-vacuity queries for acceptance, replay rejection, abort, commit, and receive. |
| `crates/protocol-core/proofs/pro-verif/compromise-queries.pvl` | Two required positive and three required negative late-compromise secrecy results. |
| `crates/protocol-core/proofs/pro-verif/baseline.pv` and `compromise.pv` | Top-level baseline and compromise scenarios. |
| `crates/protocol-core/proofs/pro-verif/check-results.awk` | Strict result classifier that rejects missing, substituted, false, unproved, inconclusive, or unexpectedly successful queries. |
| `crates/protocol-core/Makefile` | Reproducible extraction plus F*, ProVerif, timeout, placeholder, and generated-diff gates. |
| `crates/protocol-core/Cargo.toml` and `Cargo.lock` | Optional, extraction-only `hax-lib` 0.3.7 feature. Normal core builds remain dependency-free. |
| `doc/protocol.md`, `crates/protocol-core/README.md`, and `doc/formal-verification.md` | Specify the new wire encoding, completed Stage 7 claims, commands, and limitations. |

## Review finding: signed X25519 field substitution

The initial faithful wire prototype falsified exact server-acceptance origin
agreement. Before this stage, both X25519 fields were signed independently as
the same 33-byte shape:

```text
[X25519 type 0x04, 32-byte public key]
```

Cap'n Proto field position was not part of either signature. An active
attacker could therefore exchange the valid signed prekey and one-time fields,
or place the valid signed prekey in both fields. Signature and algorithm-tag
checks succeeded. The latter trace made the server consume
`(beacon identity, prekey)` while the honest bundle still used
`(beacon identity, one-time key)`, so the persistent set admitted two semantic
IDs. The server could stage a ghost peer, but the beacon computed its root from
the original secret roles and could not authenticate the altered response.

The production fix makes the role part of the signed core payload:

```text
prekey:   [type 0x04, role 0x80, 32-byte public key]
one-time: [type 0x04, role 0x81, 32-byte public key]
```

Type markers occupy the low half of the `u8` domain and role markers the high
half. `validate_init_kex` requires the expected role for each field. Both the
core regression and a production Cap'n Proto regression exchange and duplicate
the real valid signed fields and require rejection.

The Stage 6 generated F* module now exposes 34-byte X25519 arrays. Its
handwritten lemmas prove that byte zero is type `4`, byte one is the requested
role, bytes 2 through 33 are the unchanged key, values `1`, `3`, and `4` are
disjoint from role values `128` and `129`, both role-specific encodings round
trip, and decoding either role as the other returns `None`. All pre-existing
Stage 6 lemmas still verify.

This changes the signed Phase 1 X25519 payload and is not interoperable with
the former 33-byte encoding. The Cap'n Proto schema and field ordinals do not
change because the fields are variable-length `Data` values. Identity and
ML-KEM encodings remain one type byte followed by the key.

Independent per-field role signatures rely on the current Stage 4 invariant
that one fresh beacon identity emits one registration bundle. If a future API
allows multiple bundles under one identity, it must bind the fields together
with an authenticated bundle nonce or an ordered whole-bundle signature before
extending the Stage 7 theorem; role bytes alone would not prevent cross-bundle
splicing.

## Generated ProVerif boundary

Hax 0.3.7's ProVerif backend generates declarations and `letfun`/reduction
bodies, but not top-level protocol processes, events, compromise scheduling,
or queries. Stage 7 follows the pinned hax `proverif-psk` architecture: extract
a small production-code library, then compose it with separately reviewed
handwritten model files.

The selected production surface is deliberately narrow:

- `InitKex`, `VerifiedInitKex`, `RegistrationId`, `PqxdhSharedSecrets`,
  `RootKeyInput`, and `RegistrationKeyIdBinding` types and constructors;
- `registration_id`, whose backend reduction projects the exact identity and
  one-time key proved by F*;
- `build_root_key_input`, whose reduction preserves DH1, DH2, DH3, DH4, and
  KEM-secret order in an exact fixed-layout constructor; and
- `build_associated_data`, whose symbolic constructor corresponds to the exact
  tagged server identity, tagged beacon identity, and fixed domain suffixes
  proved by F*.

The production adapter calls the same free `registration_id` wrapper used by
extraction; it is not a second replay-ID implementation. Ordinary builds do
not enable the `proverif` feature, so the backend attributes have no runtime
effect.

The generated preamble contains hax's default type converters, default values,
and `construct_fail` helpers. The handwritten processes construct private core
states directly and never accept a network-supplied type converter, default,
or error value. The extraction gate checks the three required functions and
rejects known backend failure or unresolved replacement markers.

## Handwritten primitive and process inventory

Every declaration outside `extraction/lib.pvl` is part of the trusted symbolic
model and is reviewed as follows.

### Primitive equations

`crypto.pvl` declares abstract symbolic sorts for key IDs, sequences,
directions, and roles. Fresh key IDs model the checked, non-exhausted,
collision-free prefix of the production `u64` allocator. `first_sequence` and
`next_sequence` model the bounded prefix used in this trace rather than the
complete finite counter space.

The key encodings are disjoint data constructors. In particular,
`tag_x25519_prekey(k)` and `tag_x25519_one_time(k)` represent the exact
`[4, 128, k]` and `[4, 129, k]` layouts. The model has no generic constructor or
equation that can reinterpret one X25519 role as the other.

Ed25519 is represented by opaque public-key and signature constructors with
one honest verification reduction. X25519 exposes only the two complementary
role computations needed for honest DH agreement. Ed25519-to-X25519 conversion
uses the same underlying identity secret in that equation. ML-KEM has one
decapsulation-correctness reduction for a ciphertext created from the matching
public key and coins.

PQXDH root derivation, the two directional initial chains, ratchet advance,
message material, key, and nonce derivation are separate opaque constructors.
They therefore encode determinism, domain separation, and symbolic
collision-freedom. This is stronger than merely assuming a general hash and is
an explicit ideal-KDF assumption.

`seal_frame` constructs ideal AEAD ciphertext and tag plus the CTX commitment.
The sole `open_frame` reduction requires the same material, associated data,
sequence, and sender ID. The commitment constructor receives key, nonce,
associated data, AEAD tag, sequence, and sender ID in production order. Its
symbolic collision-freedom is an explicit BLAKE2b/CTX primitive assumption, not
a computational proof.

### Wire, events, and honest origins

The public `signed_init_kex` wire contains the raw tagged identity and three
signed fields, exactly as Phase 1 does; it does not carry a duplicate unsigned
core message. The server verifies each signed payload and only then constructs
the generated `InitKex` and `VerifiedInitKex` values used by the extracted
functions.

The model records:

- beacon initiation and the exact ordered, role-bearing `InitKex`;
- irreversible registration consumption, replay rejection, server acceptance,
  and abort after consumption;
- server and beacon commit with both identities, exact registration ID,
  assigned ID, root input, root, associated data, and session;
- record send/receive with session, direction, sequence, sender, receiver, and
  plaintext;
- unavailable or cached message material; and
- the exact live-chain state compromise point.

Agreement events are conditional on an uncompromised honest beacon identity.
`honest_origin` stores only that identity and a fresh event witness. It does not
store or match private copies of the received prekey, one-time key, PQ key,
transcript, or registration ID. The server events always carry values parsed
from the public attacker-controlled wire.

### Non-rollback replay owner

ProVerif 2.05 over-approximates a replicated table `get`/`insert` enough that an
otherwise serialized absence-check remained inconclusive for injective replay.
The final model uses an explicit one-owner replay process instead. For the
current one-bundle-per-fresh-identity trace, one owner is created per honest
identity. Its first private request carries the publicly parsed `InitKex` and
semantic ID, emits `RegistrationConsumed`, and receives `Fresh`. Every later
request under that identity receives `Consumed`, including after the response
abort path.

This is the symbolic refinement of the production single-owner,
non-rollback persistent set, not an additional private validity oracle. The
owner is keyed only by the fresh identity and echoes the first public values.
Consequently, restoring the former ambiguous X25519 constructor would allow an
altered first request and falsify the exact-origin correspondence instead of
silently blocking it. Independent replicas, rollback, and two server owners
for the same persistence domain remain outside the theorem.

### Bounded records and compromise

After registration, the server sends four records and the beacon sends one.
The beacon receives server sequence three before sequence two, making the
sequence-two material an explicit cached skipped key. It consumes sequence
three and records that material as unavailable. A synchronized private snapshot
then contains the live receive chain for sequence four, cached sequence-two
material, and the live beacon-to-server send chain.

The baseline snapshot sink acknowledges without revealing state. The
compromise process emits `StateCompromised`, reveals those three values to the
attacker, and only then acknowledges, so subsequent sequence-two, sequence-four,
and beacon-send events occur after the modeled compromise. This avoids relying
on an asynchronous stale snapshot.

The record correspondence covers the exact bounded send/receive program points
and proves authentication, peer/direction separation, and sequence binding.
It does not make a second receive call for the same sequence; general
post-consumption duplicate rejection remains the Stage 2 F* state-machine
theorem.

## Query results

### Baseline security

All eleven baseline queries are required to be true:

| Query group | ProVerif 2.05 result |
| --- | --- |
| Initial application secret | true |
| Cached-position application secret without compromise | true |
| Already-consumed advanced application secret | true |
| Future server-to-beacon application secret without compromise | true |
| Beacon-to-server application secret without compromise | true |
| Injective `ServerAccepted` to exact `BeaconInitiated` | true |
| Injective `ServerAccepted` to `RegistrationConsumed` | true |
| Injective `RegistrationConsumed` to exact `BeaconInitiated` | true |
| Injective `ServerResponseAborted` to earlier `RegistrationConsumed` | true |
| Injective `BeaconCommitted` to exact `ServerCommitted` | true |
| Injective bounded `MessageReceived` to exact `MessageSent` | true |

The exact-init correspondences include the role-bearing transcript and semantic
registration ID. Commit agreement additionally includes server identity,
beacon identity, assigned key ID, ordered root input, root, associated data,
and session. Record agreement includes direction, sequence, sender, receiver,
and plaintext, which supplies peer, cross-session, cross-direction, and
unknown-key-share separation within this model.

### Reachability

ProVerif phrases a positive reachability query as the negation it tries to
prove. The following five results are intentionally false, which means a trace
to each event was found:

| Negated reachability statement | Required result |
| --- | --- |
| No `ServerAccepted` event | false |
| No `RegistrationReplayRejected` event | false |
| No `ServerResponseAborted` event | false |
| No `BeaconCommitted` event | false |
| No `MessageReceived` event | false |

These results prevent a broken constructor, signature pattern, or process
ordering from making the security correspondences pass vacuously.

### Late compromise

The compromise classifications are exact and are checked as part of success:

| Secrecy statement | Required result | Meaning |
| --- | --- | --- |
| Initial message after its receive material is unavailable | true | Deleted-key forward secrecy. |
| Advanced sequence-three message after its material is unavailable | true | Deleted-key forward secrecy after out-of-order advancement. |
| Sequence-two message while its skipped key is cached | false | Receiver compromise exposes cached skipped keys. |
| Sequence-four message derived from the live receive chain | false | No post-compromise security for future inbound traffic. |
| Next beacon message derived from the live send chain | false | No post-compromise security for future outbound traffic. |

The three false statements are deliberate negative results, not ignored proof
failures.

## Strict verification and reproducibility

`make verify` enters the revision-pinned hax shell and runs, in order:

1. F* regeneration;
2. strict F* checking of generated and handwritten modules;
3. ProVerif regeneration with the extraction-only feature;
4. generated ProVerif placeholder and required-item checks;
5. all baseline queries with exact names and eleven true results;
6. all five reachability queries with the expected false negations; and
7. all five compromise queries with the exact two-true/three-false split.

Each ProVerif invocation has a 240-second timeout. Shell `pipefail` propagates a
timeout or verifier error. `check-results.awk` rejects a missing summary,
missing or substituted query, an unknown scenario, an unexpected
classification, and every `cannot be proved`, unknown, or inconclusive result.
This is necessary because ProVerif can exit zero even when a query is false or
unproved.

`make verify-proverif` runs only the ProVerif half in the same shell.
`make check-generated` runs the complete proof suite and checks both generated
directories for tracked differences.

The hax revision is
`5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3` (hax 0.3.7). The checked backend
versions are F* `2025.10.06~dev`, its default Z3 `4.13.3`, and ProVerif
`2.05`. The hax source declares Rust nightly `2025-11-08`; the frontend
actually used for this extraction reports rustc `1.97.1` (`8bab26f4f`,
2026-07-14) and Cargo `1.97.1` (`c980f4866`, 2026-06-30). Fully hermetic CI
toolchain selection remains Stage 8.

## Artifact inventory

The final tracked artifacts are recorded after a deterministic second
extraction:

| Artifact | Lines | SHA-256 |
| --- | ---: | --- |
| Generated F* PQXDH module | 932 | `d73891ba4ac6818a5a1d8fdb3f3fe8daaccb077489ee0fd428519c8eabd90941` |
| Handwritten F* PQXDH lemmas | 763 | `452f242c60fdb85bc34a49db9cd133bb7f29e03304aee21f108f71950114a64e` |
| Generated ProVerif library | 358 | `81ef938f5726bb5f6fcf482b29199c06e66c7805caac0b5a73414f653038f386` |
| Handwritten ProVerif primitive model | 195 | `952ab02660480b7e120b93f7cd5941ea88b3b94b203880daad929ae9ba69b11d` |
| Handwritten ProVerif environment | 787 | `a3a0b178fc8b37b129630374d4823a886e80cb63c3c739f3a7433deecce13e58` |
| Baseline queries | 170 | `aee77b38f47b9bd2e4f6b81c0ff938b940be19983d614396639896cc53b641b4` |
| Reachability queries | 89 | `934a85fe05b5b215e589111731683a5fd759f57766f2002d58535670b027cca7` |
| Compromise queries | 16 | `61f4e33c26ff34a0103ad47f2f06c2047eb3a38ae9348320a6817eb509a1147b` |

Generated directories contain no hand-maintained lemma or query files. The F*
lemmas and all ProVerif model/query files are outside their respective
`extraction` directories.

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
git diff --check
```

The production regression `server_rejects_swapped_or_duplicated_signed_x25519_roles`
passes together with the core role-layout regression. The complete Rust
workspace, minimal beacon/server builds, warnings-denied Clippy run, strict F*
proof, ProVerif baseline, reachability, and compromise gates all exit zero.
The workspace run executed 168 tests with no failures or ignored tests. F*
discharged every verification condition in both generated modules and both
handwritten lemma modules. ProVerif produced the required eleven true baseline
results, five false reachability negations, and the reviewed compromise split
of two true and three false secrecy results. A second extraction left the
generated ProVerif library unchanged; the final artifact identities are
recorded above. `git diff --check` also exits zero.

## Remaining rollout work

Stage 8 must run the complete extraction and proof suite in CI with hermetic
rustc, hax, F*, Z3, and ProVerif selection. Stage 9 must maintain the reviewed
inventory of primitive laws, adapter refinements, generated backend defaults,
and handwritten model fragments as production and proof code evolve.
