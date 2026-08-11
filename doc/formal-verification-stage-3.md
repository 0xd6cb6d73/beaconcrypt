<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 3 implementation

## Status and scope

Stage 3 connected the symmetric-ratchet state machine introduced in Stages 1 and 2 to the production messaging path. A subsequent refinement replaces the remaining production-owned parallel chains and receive slots with the extracted generic `RefinedRatchet<SendChain, RecvChain, KeyMaterial>`. Production now compiles and calls that same kernel through the role-specific `Beacon` and `Server` APIs, and its private state owns control, both typed chain values, and fixed slots containing sealed sequence-tagged material. The later whole-plan refinement makes `refined_advance_receive_until` preflight every planned destination before an abstract KDF call and execute an admitted plan without a reported intermediate failure branch. The extracted `split_ratchet_kdf_output` now also owns the exact 76-byte key, next-chain, and nonce partition used by the production callback.

This record covers the production adapter for symmetric-ratchet control state, key lifecycle, authentication completion, tagged material-slot correspondence, per-step KDF-output layout, and persistence restoration. HKDF computation remains the one opaque ratchet step supplied by production, while the interpretation of its fixed-size output is extracted. PQXDH remains covered by Stage 4 and later stages.

## Implementation map

| File | Responsibility |
| --- | --- |
| `Cargo.toml` and `Cargo.lock` | Make `beaconcrypt-protocol-core` a production dependency. |
| `src/shared.rs` | Specialize `RefinedRatchet` to the production chain and material types, provide the sole opaque HKDF step callback, pass its 76-byte expansion to the extracted splitter, wrap the named result fields in production secret types, and route high-level send and receive operations through the shared kernel. |
| `src/ser.rs` | Emit the five-field ratchet persistence format from the kernel's counters, chains, and paired active-entry accessor. |
| `src/deser.rs` | Require the five-field ratchet schema and supply each sorted `(sequence, material)` pair atomically to the checked refined restoration builder. |
| `crates/protocol-core` | Own logical control, typed opaque chains, sealed sequence-tagged material slots, the exact 76-byte KDF-output partition, whole-plan receive preflight and execution, tag-checking lookup and removal, restoration, and the consuming refined send token in one extractable kernel. |

The older logical ratchet APIs and their lemmas remain for proof compatibility, but production uses the refined API.

## Production state representation

`RatchetManager` contains one private `RefinedRatchet<SendChain, RecvChain, KeyMaterial>`. The refined kernel is authoritative for:

- the next send sequence;
- the highest derived receive sequence;
- receive-window admission;
- both typed chain values;
- a sealed sequence tag on each cached material value, checked against the logical slot; and
- receive-key retention, swap-removal, and consumption.

The kernel's chain and material type parameters are opaque to the extracted control logic. Production supplies one pure-shaped callback with the signature `fn(&Chain, &[u8]) -> RatchetStep<Chain, Material>`; the concrete callback performs one HKDF ratchet step, passes the returned `[u8; 76]` to `split_ratchet_kdf_output`, and wraps the helper's borrowed 32-byte next-chain, 32-byte key, and 12-byte nonce views in the production types while the complete buffer remains under its zeroizing owner.

The refined fields are private. There is no production-owned `recv_slots` array and no adapter-maintained positional invariant. Internally, every active logical sequence has one populated slot in `[Option<CachedReceiveKey<Material>>; 50]`, every cached value repeats that exact sequence in its private tag, and every inactive slot is empty. The kernel rejects lookup or completion when a tag does not equal the logical sequence, validates the old-last tag before swap-removal, and moves the complete tagged value. The only serialization view is a tag-checking `(sequence, &material)` accessor for active entries.

The public C constant for the receive gap retains a literal initializer because cbindgen cannot evaluate a cross-crate constant path. A compile-time assertion requires that literal to equal `beaconcrypt_protocol_core::RATCHET_MAX_GAP`, so the C binding cannot silently diverge from the verified value.

## Send transition

A production send follows this sequence:

1. `refined_advance_send(&mut kernel, info, step)` checks exhaustion before calling the opaque step callback.
2. On admission, the kernel calls the callback once, updates the send chain and counter together, and returns `RefinedSendKey<Material>` with the allocated sequence paired with its concrete material.
3. The high-level encryption path borrows that token's material to perform AEAD, construct the commitment, and serialize the frame.
4. Every recoverable post-allocation outcome consumes the token with `refined_finish_send`, so neither a pending capability nor message material is stored in `RatchetManager`.

The refined send token is not `Clone` or `Copy`, so the production Rust API prevents callers from forging or copying its sequence/material pairing. The high-level helper's control flow passes every allocated token to consuming finish on each recoverable path; panic behavior is not a type-level guarantee. Cloning the whole ratchet remains conditionally possible when its type parameters are cloneable, so single-owner and non-rollback use remain explicit assumptions.

## Receive transition

A production receive follows the shared refined transition sequence:

1. `RatchetManager::ratchet_recv_until` delegates directly to `refined_advance_receive_until(&mut kernel, info, target, step)` rather than interpreting the receive plan in production.
2. The extracted operation decides gap and capacity admission and preflights every fixed-array destination selected by the complete plan before invoking the abstract KDF callback.
3. Every reported rejection occurs at that preflight boundary, invokes no callback, preserves the complete control, chains, and material array, and therefore cannot publish only a prefix of the requested refinement.
4. For a valid admitted future plan, the kernel invokes the callback exactly once for each planned sequence in chain order, appends the consecutive sequences to the consecutive slots beginning at the old cache length, seals each sequence together with the corresponding returned material, preserves every old tagged association, and reaches the target receive counter.
5. An old or current target performs zero receive steps and leaves the complete refined state unchanged; `refined_receive_key(&kernel, sequence)` then decides whether that sequence remains available and returns material only when the cached tag equals the requested logical sequence, without a production secondary index or physical slot view.
6. Commitment or AEAD failure is passed to `refined_finish_receive(&mut kernel, sequence, false)`, which retains the exact post-admission sequence/material state without moving a slot.
7. Successful authentication is passed to `refined_finish_receive(&mut kernel, sequence, true)`, which validates the target and old-last tags, performs the logical removal and complete tagged-value swap/take internally, and returns `Consumed`; a mismatch returns `Missing` without mutation.

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

This rejects zero receive sequences, receive sequences above `recv_ctr`, and receive caches larger than 50 entries. Collecting through a map establishes uniqueness, and numeric sorting supplies the restoration builder with strictly increasing input. The builder proves that the supplied sequence remains paired with the supplied material, but neither the tag nor the proof establishes that persisted bytes were cryptographically derived for that sequence; persisted-pair cryptographic provenance remains an adapter and storage obligation. The decision to reject more than 50 imported receive keys is intentional: such states are outside the verified core state space, and normal high-level traces cannot create them. Removing `send_past` is also an intentional persistence and API break; snapshots using the former six-field schema must not be restored by this version.

Because the kernel uses packed swap-removal while restoration uses sorted input, physical cache-slot order is not a persistence invariant. Round-trip tests compare remaining key and nonce bytes by sequence rather than requiring identical internal slot layout.

## Proof correspondence boundary

The Stage 3 correspondence claim applies to high-level `Beacon::{encrypt_message,decrypt_message}` and `Server::{encrypt_message,decrypt_message}` traces that start from fresh or successfully validated role state and do not roll state back.

The strict F* theorem surface is parametric in the typed chains, material, and step callback. It proves the exact `key[0..32] || next_chain[32..64] || nonce[64..76]` KDF-output partition, requires each active cached tag to equal its logical slot sequence, proves direct mismatched-tag lookup rejection, and proves full-state neutrality for `Missing` and `Retained` completion outcomes. It also proves that whole-plan receive preflight precedes callback application, every reported rejection is callback-free and preserves the complete state, every valid admitted future plan executes exactly its bounded consecutive sequence and slot trace with the corresponding callback-produced materials and reaches the target counter while preserving old tagged associations, and an old or current target performs zero steps before lookup. Failure retention and successful internal swap-removal preserve complete tagged values, checked restoration seals each supplied pair together, and the refined send lifecycle keeps the allocated sequence and callback-produced material in one consuming token. The extracted completion code additionally validates target and old-last tags before mutation and returns `Missing` without mutation on a disagreement. The older logical theorems remain available as compatibility results.

These theorems mechanize the fixed 76-byte output split, tagged cache correspondence, mismatch rejection, whole-plan destination preflight, reported-rejection neutrality, slot mutation, callback ordering, restoration, and normal-return publication inside the extracted kernel. Because the callback is arbitrary and pure in the proof, they do not establish that production invokes HKDF with the intended old chain and `SYM_RATCHET_INFO`, faithfully passes the requested 76 bytes to the extracted splitter, faithfully wraps the splitter's named fields in the production secret types, or gives those bytes the intended cryptographic relation; they also do not cover callback panics or crash atomicity.

The following remain explicit adapter preconditions or exclusions:

- concrete HKDF semantics, the old-chain input and `SYM_RATCHET_INFO` label, faithful passage of the requested 76 bytes to the extracted splitter, and faithful typed wrapping of its named result fields;
- provenance of the authentication boolean from the intended commitment and AEAD checks;
- serde translation and rejection behavior outside the refined builder, including cryptographic provenance of imported sequence/material pairs;
- hax extraction, Rust compilation, and correspondence of the checked kernel to the deployed executable;
- rollback, cloned state forks, callback panics, and crash atomicity across surrounding high-level persistence;
- zeroization and physical erasure of chain and material bytes;
- the production Server peer-map lookup and uniqueness refinement plus the Beacon's sole-server selection refinement;
- correctness of the concrete AEAD, hash, allocation, and entropy primitives; and
- direct calls to older low-level compatibility APIs outside the high-level production trace.

`RefinedSendKey<Material>` closes the former adapter assumption that a copyable logical `SendKey` remains paired with the right concrete material: its fields are private, it is not clonable, and finish consumes it. This does not prevent cloning or restoring the complete ratchet before allocation when its concrete types permit cloning. The high-level claim therefore still assumes one authoritative non-rollback owner. Similarly, the core proves a pointwise peer frame rule, while production map selection remains an adapter obligation tested by multi-peer protocol regressions.

## Regression coverage added

Stage 3 adds or strengthens tests for:

- paired sequence/material lookup after multi-key derivation;
- rejection without mutation when a cached target tag or old-last tag disagrees with the logical cache;
- exact extracted splitting of distinct 32-byte key, 32-byte next-chain, and 12-byte nonce regions;
- whole-plan rejection when a later planned destination is already occupied, including zero callback calls and preservation of every earlier destination;
- exact non-last and last-slot internal removal behavior, including preservation of both key and nonce bytes for a moved sequence;
- unchanged logical state, receive-chain bytes, sequence/material association, and concrete material after failed authentication and zero-cost retry;
- replay neutrality, full-capacity rejection, non-last release and refill, clone independence, and reset;
- consuming refined send tokens, sequential advancement, direction matching, and exhaustion neutrality;
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
