<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 3 implementation

This document records the historical Stage 3 boundary. The maintained adapter now removes `Clone` from operational ratchet state, returns inert serialization-only update views, permits operational ratchets only in establishment-gated runtime state, and activates full server snapshots only through a trusted-store generation/head CAS in `PersistentServer`. The store, rather than snapshot cryptography, must supply payload integrity and provenance; snapshots have no cryptographic authentication or encryption. Those production controls do not strengthen the Stage 3 F* theorems: `reachable_restore` remains conditional, and F* proves neither the codec nor the external store. References below to clonable state, raw restoration, or public reset describe the historical stage rather than the current supported API.

## Status and scope

Stage 3 connected the symmetric-ratchet state machine introduced in Stages 1 and 2 to the production messaging path. A subsequent refinement replaces the remaining production-owned parallel chains and receive slots with the extracted generic `RefinedRatchet<SendChain, RecvChain, KeyMaterial>`. Production now compiles and calls that same kernel through the role-specific `Beacon` and `Server` APIs, and its private state owns control, both typed chain values, and fixed slots containing sealed sequence-tagged material. The later whole-plan refinement makes the kernel-private `refined_advance_receive_until` preflight every planned destination before an abstract KDF call and execute an admitted plan without a reported intermediate failure branch. The material-lifecycle refinement adds public `refined_seal_next` and `refined_open_and_finish` operations that lend the exact kernel-selected sequence/material pair and frame context to one opaque AEAD callback and retain or consume material from the callback's `Option` result. The extracted `derive_ratchet_step` passes the exact old 32-byte chain to a domain-specific `32 -> 76` opaque primitive, owns the exact key/next-chain/nonce partition, and constructs fixed-width result types before production performs infallible conversions.

This record covers the production adapter for symmetric-ratchet control state, key lifecycle, authentication completion, tagged material-slot correspondence, per-step KDF-output layout, and persistence restoration. HKDF computation remains the one opaque ratchet step supplied by production, while the interpretation of its fixed-size output is extracted. PQXDH remains covered by Stage 4 and later stages.

## Implementation map

| File | Responsibility |
| --- | --- |
| `Cargo.toml` and `Cargo.lock` | Make `beaconcrypt-protocol-core` a production dependency. |
| `src/shared.rs` | Specialize `RefinedRatchet` to the production chain and material types, provide private fixed-signature `32 -> 76` and `32 -> 64` domain-specific primitives, invoke the extracted concrete adapters, convert their fixed-width outputs infallibly into production types, and route high-level send and receive operations through the shared kernel. |
| `src/ser.rs` | Emit the five-field ratchet persistence format from the kernel's counters, chains, and paired active-entry accessor. |
| `src/deser.rs` | Require the five-field ratchet schema and supply each sorted `(sequence, material)` pair atomically to the checked refined restoration builder. |
| `crates/protocol-core` | Own logical control, typed opaque chains, sealed sequence-tagged material slots, the exact 76-byte KDF-output partition, whole-plan receive preflight and execution, tag-checking lookup and removal, restoration, the private consuming send token, and the public callback-owned seal/open lifecycle in one extractable kernel. |

The older logical ratchet APIs and their lemmas remain crate-private for proof compatibility. Production message processing uses only the public callback-owned refined operations; checked persistence uses the paired refined restoration API.

## Production state representation

`RatchetManager` contains one private `RefinedRatchet<SendChain, RecvChain, KeyMaterial>`. The refined kernel is authoritative for:

- the next send sequence;
- the highest derived receive sequence;
- receive-window admission;
- both typed chain values;
- a sealed sequence tag on each cached material value, checked against the logical slot; and
- receive-key retention, swap-removal, and consumption.

The kernel's chain and material type parameters are opaque to the extracted control logic. Its KDF-step callback has the signature `fn(&Chain) -> RatchetStep<Chain, Material>` and cannot receive a caller-selected label. The production specialization calls extracted `derive_ratchet_step`, which passes the exact old chain to a private `fn(&[u8; 32]) -> [u8; 76]` primitive, partitions the returned array, and constructs owned fixed-width chain, key, and nonce values. The primitive implementation privately fixes `SYM_RATCHET_INFO`; production then uses only infallible fixed-array conversions into its role and libsodium types. The separate seal/open callbacks receive `(&Material, sequence, &FrameContext)` only from the kernel, so raw message material is not returned to production beside an independently reportable lifecycle decision.

The refined fields are private. There is no production-owned `recv_slots` array and no adapter-maintained positional invariant. Internally, every active logical sequence has one populated slot in `[Option<CachedReceiveKey<Material>>; 50]`, every cached value repeats that exact sequence in its private tag, and every inactive slot is empty. The kernel rejects lookup or completion when a tag does not equal the logical sequence, validates the old-last tag before swap-removal, and moves the complete tagged value. The only serialization view is a tag-checking `(sequence, &material)` accessor for active entries.

The public C constant for the receive gap retains a literal initializer because cbindgen cannot evaluate a cross-crate constant path. A compile-time assertion requires that literal to equal `beaconcrypt_protocol_core::RATCHET_MAX_GAP`, so the C binding cannot silently diverge from the verified value.

## Send transition

A production send calls `refined_seal_next(&mut kernel, step, &frame_context, seal_callback)`. The kernel checks exhaustion before invoking the KDF-step callback, updates the send chain and counter together, keeps the allocated `RefinedSendKey<Material>` private, invokes `seal_callback` with the exact step material, allocated sequence, and supplied frame context, and consumes the private token before returning the callback result. Production performs AEAD, constructs the commitment, and serializes the frame only inside that callback. Neither raw material nor the token crosses the public kernel boundary, and a failed seal attempt still consumes the allocated send material under the existing send policy. Callback panics and cloning or restoring the complete ratchet remain outside the normal-return ownership claim, so single-owner and non-rollback use remain explicit assumptions.

## Receive transition

A production receive calls `refined_open_and_finish(&mut kernel, target, step, &frame_context, open_callback)`. The extracted operation decides gap and capacity admission and preflights every fixed-array destination selected by the complete plan before invoking the abstract KDF callback. Every reported rejection occurs at that preflight boundary, invokes no AEAD callback, preserves the complete control, chains, and material array, and cannot publish only a prefix of the requested refinement. For a valid admitted future plan, the kernel invokes the KDF callback exactly once for each planned sequence in chain order, appends the consecutive sequences to the consecutive slots beginning at the old cache length, seals each sequence together with the corresponding returned material, preserves every old tagged association, and reaches the target receive counter. An old or current target performs zero receive steps and leaves the complete refined state unchanged before the kernel selects the exact tagged material. The kernel invokes `open_callback` with only that material, the selected sequence, and the supplied frame context. `None` returns the complete post-admission state unchanged for retry; `Some(plaintext)` validates and performs logical/tagged swap-removal for that same sequence before publishing the plaintext. Production never receives raw material, never passes an authentication Boolean, and cannot request unconditional deletion.

Receive slots remain an internal packed representation rather than stable identifiers. Successful removal may move the former last sealed sequence/material value into the consumed pair's old slot; every later operation resolves by sequence and validates the stored tag through the kernel. Replay of an already consumed sequence therefore finds neither the logical entry nor its material and is rejected without changing state.

An admissible forged future frame can still advance the receive chain and cache keys before authentication fails. This matches the existing protocol semantics described in the verification plan. Admission or destination-preflight rejection is callback-free and state-neutral, while an admitted authentication failure occurs after the successful whole-plan transaction and retains the derived candidate keys for retry. The proof covers reported return paths; callback panics and process crashes remain outside its atomicity claim.

## Persistence and compatibility break

The serialized `RatchetManager` is a five-field object:

```text
send_key, recv_key, send_ctr, recv_past, recv_ctr
```

No send-message key or logical send capability is persisted. No duplicate serialization of the core representation was added: `send_ctr` and `recv_ctr` are emitted from the authoritative core getters, and physical receive slots are never persisted.

Serialization reads each active `(sequence, material)` pair through `receive_entry_at`, which rejects tag/logical divergence. The private cached fields prevent safe production code from manufacturing or retagging a live entry independently of checked derivation or restoration. The existing sequence-keyed `recv_past` map remains a wire representation rather than a second live cache.

Deserialization performs the following checked reconstruction:

1. require the exact five-field ratchet schema, so every legacy object containing `send_past` is rejected rather than migrated or silently accepted;
2. collect and numerically sort all sequence/material entries from the persisted `recv_past` map;
3. call `start_refined_restore(send_ctr, recv_ctr, send_chain, receive_chain)`;
4. call `refined_restore_receive_key(&mut builder, sequence, material)` once for every sorted pair, so logical append and sealing that supplied sequence with its material are one operation; and
5. call `finish_refined_restore(builder)` to obtain the complete kernel.

This rejects zero receive sequences, receive sequences above `recv_ctr`, and receive caches larger than 50 entries. The original Stage 3 adapter collected entries through a map before sorting, but `HashMap` did not establish uniqueness of raw JSON keys because ordinary deserialization could collapse a duplicate first. The maintained adapter instead observes raw entries with a duplicate-rejecting visitor before insertion, requires canonical decimal `u64` keys, and then sorts for strictly increasing builder input. The builder proves that a supplied sequence remains paired with supplied material, but neither its tag nor F* establishes canonical HKDF provenance; the trusted store's payload-integrity/provenance contract and external CAS are adapter obligations rather than theorem conclusions. Removing `send_past` remains an intentional schema break.

Because the kernel uses packed swap-removal while restoration uses sorted input, physical cache-slot order is not a persistence invariant. Round-trip tests compare remaining key and nonce bytes by sequence rather than requiring identical internal slot layout.

## Proof correspondence boundary

The Stage 3 correspondence claim applies to high-level `Beacon::{encrypt_message,decrypt_message}` and `Server::{encrypt_message,decrypt_message}` traces that start from fresh or successfully validated role state and do not roll state back.

The strict F* theorem surface is parametric in the typed chains, material, KDF-step callback, frame context, and seal/open callbacks. It proves the exact `key[0..32] || next_chain[32..64] || nonce[64..76]` KDF-output partition, requires each active cached tag to equal its logical slot sequence, proves direct mismatched-tag lookup rejection, and proves full-state neutrality for `Missing` and `Retained` internal completion outcomes. It also proves that whole-plan receive preflight precedes KDF callback application, every reported rejection is callback-free and preserves the complete state, every valid admitted future plan executes exactly its bounded consecutive sequence and slot trace with the corresponding KDF-produced materials and reaches the target counter while preserving old tagged associations, and an old or current target performs zero steps before lookup. The new lifecycle lemmas prove that `refined_seal_next` passes the exact allocated step material, sequence, and context to its callback, that an open callback returning `None` retains the complete admitted state, and that callback `Some(plaintext)` publishes that plaintext only with the state produced by consuming the same selected sequence. Successful internal swap-removal preserves complete tagged values, checked restoration seals each supplied pair together, and the extracted completion code validates target and old-last tags before mutation. The older logical theorems remain available as compatibility results.

These theorems mechanize exact passage of the old 32-byte chain to the opaque `32 -> 76` primitive, the fixed 76-byte output split and fixed-width construction, tagged cache correspondence, mismatch rejection, whole-plan destination preflight, reported-rejection neutrality, slot mutation, callback ordering, restoration, and normal-return publication inside the extracted kernel. They do not establish the private primitive's HKDF-SHA-512 cryptographic semantics or give those bytes the intended cryptographic relation. The reviewed primitive implementation unconditionally selects private `SYM_RATCHET_INFO`, so callers and refined callbacks cannot select a label. The theorems also do not cover primitive panics, the final infallible conversion into external libsodium types, compiler correspondence, or crash atomicity.

The following remain explicit adapter preconditions or exclusions:

- concrete HKDF semantics and totality of the private fixed-signature primitive, plus compiler correspondence for the final infallible conversion into external libsodium types;
- correctness and totality of the concrete seal/open callbacks, including their ChaCha20-Poly1305 and commitment semantics;
- serde translation and rejection behavior outside the refined builder, including cryptographic provenance of imported sequence/material pairs;
- hax extraction, Rust compilation, and correspondence of the checked kernel to the deployed executable;
- rollback, cloned state forks, callback panics, and crash atomicity across surrounding high-level persistence;
- zeroization and physical erasure of chain and material bytes;
- the production Server peer-map lookup and uniqueness refinement plus the Beacon's sole-server selection refinement;
- correctness of the concrete AEAD, hash, allocation, and entropy primitives; and
- any test-only or crate-internal use of older low-level compatibility APIs outside the public callback-owned production trace.

The private `RefinedSendKey<Material>` and private receive completion close the former adapter assumptions that a logical capability remains paired with the right concrete material and that a caller-reported authentication result came from using that material. This does not prevent cloning or restoring the complete ratchet before allocation when its concrete types permit cloning, and F* treats the opaque AEAD callbacks as arbitrary pure functions rather than proving concrete cryptographic correctness. The high-level claim therefore still assumes correct callbacks and one authoritative non-rollback owner. Similarly, the core proves a pointwise peer frame rule, while production map selection remains an adapter obligation tested by multi-peer protocol regressions.

## Regression coverage added

Stage 3 adds or strengthens tests for:

- paired sequence/material lookup after multi-key derivation;
- rejection without mutation when a cached target tag or old-last tag disagrees with the logical cache;
- exact extracted splitting of distinct 32-byte key, 32-byte next-chain, and 12-byte nonce regions;
- whole-plan rejection when a later planned destination is already occupied, including zero callback calls and preservation of every earlier destination;
- exact non-last and last-slot internal removal behavior, including preservation of both key and nonce bytes for a moved sequence;
- unchanged logical state, receive-chain bytes, sequence/material association, and concrete material after failed authentication and zero-cost retry;
- replay neutrality, full-capacity rejection, non-last release and refill, clone independence, and reset;
- callback-owned seal/open lifecycle, exact sequence/material/context callback arguments, failed-open retention with zero-step retry, successful same-sequence consumption, sequential advancement, direction matching, and exhaustion neutrality;
- the exact five-field persistence schema and rejection of legacy objects containing `send_past`;
- persistence round trips that compare remaining receive key and nonce bytes by sequence even when core slot order differs;
- refined restoration rejection for invalid, duplicate, unordered, and over-capacity sequence/material input;
- acceptance of an exactly 50-key receive cache and rejection of 51 keys;
- continued use of the existing protocol, server-state, Rooterberg, and
  Wycheproof tests through the production adapter.

## Validation gates

The completed receive-slot refinement is checked with:

```sh
cargo fmt --all -- --check
cargo test --locked -p beaconcrypt-protocol-core
cargo test --locked
cargo check --locked --no-default-features --features pqxdh,server --lib
cargo check --locked --no-default-features --features pqxdh,beacon --lib
cargo clippy --workspace --all-targets --all-features --locked -- \
  -D warnings -A clippy::type-complexity
make -C crates/protocol-core verify
make -C crates/protocol-core check-inventory
make -C crates/protocol-core check-generated
```

The hax-generated ratchet module intentionally changes because the generic refined state and transitions are now selected. Strict F* checking discharges the corresponding handwritten lemmas without `--lax`, `assume`, or `admit`; `check-generated` and `check-inventory` then ensure the reviewed generated artifacts and trust-boundary fingerprints match those checked sources. The `clippy::type-complexity` allowance applies to a pre-existing deserialization function outside the Stage 3 changes.

## Remaining rollout work

Stage 3 does not change the known PQXDH counterexamples or enable their formal
claims. The next planned work is to move PQXDH into role-specific typestates,
then fix and enable the registration authentication and replay tests before
adding the corresponding PQXDH and ProVerif proofs.

The protocol core remains `publish = false`, as established in the previous
stage. A future crates.io release of the root package therefore needs an explicit
publication or vendoring strategy for the core crate.
