<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 3 implementation

## Status and scope

Stage 3 connects the symmetric-ratchet state machine introduced in Stages 1 and 2 to the production `BeaconCryptPqxdh` path. The implementation was based on commit `78482e8498ea77b11fd5a565559746319a35f3f3`, which contained the standalone protocol core, its hax extraction, and the F* lemmas, but left the production `RatchetManager` unchanged. The completed receive-slot refinement additionally moves sequence lookup, successful swap-removal planning, and restoration slot assignment into the extracted core so production consumes those verified decisions directly. The current adapter also removes unnecessary send-key staging and confines each concrete send key and verified logical capability to its single high-level encryption call.

This stage covers the production adapter for symmetric-ratchet control state, key lifecycle, authentication completion, physical receive-slot correspondence, and persistence restoration. It does not move PQXDH into the core; that remains Stage 4.

## Implementation map

| File | Responsibility |
| --- | --- |
| `Cargo.toml` and `Cargo.lock` | Make `beaconcrypt-protocol-core` a production dependency. |
| `src/shared.rs` | Store authoritative core state, keep each send capability and concrete key stack-local to one encryption attempt, store concrete receive material in the returned core slots, resolve receive sequences through verified lookup, and apply the exact returned removal plan. |
| `src/ser.rs` | Emit the five-field ratchet persistence format while mapping active physical slots back to logical sequences and rejecting either direction of logical/concrete divergence. |
| `src/deser.rs` | Require the five-field ratchet schema, validate persisted receive state, and place each sorted receive-map entry in the slot returned by the checked restoration typestate. |
| `crates/protocol-core` | Provide the extracted transition API and strict F* lemmas for lookup, detailed removal, compatibility projections, and restoration slots in addition to the existing ratchet properties. |

No generated F* file was hand-edited in this stage.

## Production state representation

`RatchetManager` no longer stores independent `send_ctr` and `recv_ctr` fields. It contains one `beaconcrypt_protocol_core::RatchetState`, named `control`, which is authoritative for:

- the next send sequence;
- the highest derived receive sequence;
- receive-window admission;
- logical ownership of cached receive keys;
- receive-key retention and consumption.

Concrete cryptographic material stays in the production adapter:

- `send_key` and `recv_key` hold the opaque HKDF chain bytes;
- `recv_slots` is a fixed array holding concrete AEAD receive keys and nonces in the physical slots assigned by the core; and
- each concrete AEAD send key and its logical `SendKey` capability exist only in the stack-local transaction that performs one encryption attempt.

The principal receive refinement invariant is:

```text
recv_slots[slot].is_some() == (slot < control.receive_cache_len())
```

The adapter checks this invariant in debug builds after construction and every receive-cache mutation. There is no persistent send-key refinement invariant because `RatchetManager` contains neither pending concrete send material nor logical send capabilities.

The public C constant for the receive gap retains a literal initializer because cbindgen cannot evaluate a cross-crate constant path. A compile-time assertion requires that literal to equal `beaconcrypt_protocol_core::RATCHET_MAX_GAP`, so the C binding cannot silently diverge from the verified value.

## Send transition

A production send now follows this sequence:

1. `advance_send(control)` decides whether a sequence can be allocated. Counter exhaustion returns `None` without changing either core or concrete state.
2. The adapter requires the returned sequence, logical `SendKey`, and advanced control counter to agree before it mutates the concrete chain.
3. For an admitted sequence, the adapter performs exactly one opaque HKDF step and keeps the resulting concrete key, nonce, and logical capability together in a private stack-local transaction.
4. The high-level encryption path borrows that local concrete material to perform AEAD, construct the commitment, and serialize the frame.
5. After the attempt, the adapter passes the local logical capability to `finish_send`, requires the result to report consumption and unavailability, and drops the concrete key. This happens for successful encryption and every recoverable failure after allocation, including frame-serialization failure.

The resulting production state never stores or exposes a pending concrete send key or logical send capability. The former low-level staging, lookup, deletion, and restoration behavior has been removed.

No protocol-core or F* change is needed for this storage simplification. The existing `advance_send_key_matches_sequence`, `finish_send_consumes_available`, and `finish_send_is_one_use` lemmas already cover the logical transitions used by the local operation; the non-affinity and adapter-lifetime limitations remain explicit below.

## Receive transition

A production receive now follows the verified planning, lookup, and completion split:

1. `plan_receive_until(control, target)` decides admission before any KDF state is advanced. A target outside the gap or total-cache bound is state-neutral.
2. For each planned derivation, `advance_receive` adds one logical sequence and returns its append slot. Only after that logical step succeeds does the adapter perform one concrete HKDF step and store its key and nonce in exactly the returned slot.
3. Before using an existing key, the adapter passes its stable sequence number to `lookup_receive_key` and requires concrete material in the returned current slot. Production contains no independent sequence-to-slot scan or secondary receive index.
4. Commitment or AEAD failure is passed to `finish_receive_with_removal(..., false)`. The core returns `Retained`, no removal plan, and the unchanged post-admission logical state, so production performs no concrete slot mutation and preserves the exact key for retry.
5. Successful AEAD verification is passed to `finish_receive_with_removal(..., true)`. The core returns `Consumed`, the new logical state, and the exact old target and old last slots. Production validates those concrete slots, swaps them, takes the old last entry, and only then publishes the returned logical state.

Core receive slots are not stable identifiers. Successful removal may move the former last sequence into the consumed sequence's old slot, so every later operation resolves the sequence again through `lookup_receive_key`. Replay of an already consumed sequence therefore finds neither a logical capability nor concrete material and is rejected without changing state.

An admissible forged future frame can still advance the receive chain and cache keys before authentication fails. This matches the existing protocol semantics described in the verification plan. Capacity and forward-gap rejection remain state-neutral, while an admitted authentication failure retains the derived candidate keys for retry.

## Persistence and compatibility break

The serialized `RatchetManager` is a five-field object:

```text
send_key, recv_key, send_ctr, recv_past, recv_ctr
```

No send-message key or logical send capability is persisted. No duplicate serialization of the core representation was added: `send_ctr` and `recv_ctr` are emitted from the authoritative core getters, and physical receive slots are never persisted.

Serialization checks the packed positional invariant in both directions before emitting `recv_past`: every active logical slot must contain concrete material, and every inactive physical slot must be empty. Each active slot is serialized under the logical sequence stored in that same core slot, preserving the existing sequence-keyed map schema.

Deserialization performs the following checked reconstruction:

1. require the exact five-field ratchet schema, so every legacy object containing `send_past` is rejected rather than migrated or silently accepted;
2. collect and numerically sort all sequence/material entries from the persisted `recv_past` map;
3. call `start_restore(send_ctr, recv_ctr)`;
4. call `restore_receive_key_with_slot` once for every sorted entry and place its concrete material directly in the returned slot;
5. reject the import if any append fails, any returned slot is outside the concrete array, or a returned slot is already populated; and
6. call `finish_restore` and pair the resulting core state with the packed receive array.

This rejects zero receive sequences, receive sequences above `recv_ctr`, and receive caches larger than 50 entries. Collecting through a map establishes uniqueness, and numeric sorting supplies the restoration builder with strictly increasing input. The decision to reject more than 50 imported receive keys is intentional: such states are outside the verified core state space, and normal high-level traces cannot create them. Removing `send_past` is also an intentional persistence and API break; snapshots using the former six-field schema must not be restored by this version.

Because the core uses packed swap-removal while restoration uses sorted input, physical cache-slot order is not a persistence invariant. Round-trip tests compare remaining key and nonce bytes by sequence rather than requiring identical slot layout.

## Proof correspondence boundary

The Stage 3 correspondence claim applies to high-level `BeaconCryptPqxdh::encrypt_message` and `decrypt_message` traces that start from a fresh or successfully validated state and do not roll state back.

The strict F* theorem surface now explains the physical decisions production mirrors. Lookup soundness and completeness connect `Some(slot)` and `None` to membership in the active unique logical cache. Detailed completion is proved equivalent to the compatibility wrapper, missing and retained results produce no removal and preserve state, and successful completion identifies the exact target/old-last slots plus the logical entry moved by swap-removal. Successful detailed restoration returns the previous logical length as its append slot and places the restored sequence there, while the compatibility restore wrapper has identical accept/reject behavior and projected state.

These theorems mechanize the control decisions that were formerly reconstructed by adapter code. They do not prove the concrete `KeyMaterial` bytes, the HKDF step, or the Rust array mutation itself. Production must still derive the local concrete send material for the sequence named by `advance_send`, pair its disposal with `finish_send`, perform one correct HKDF step after each successful logical receive advance, store the receive output in the returned slot, use the lookup result for the intended receive sequence, apply the returned swap/take exactly, and retain or drop concrete receive material in step with the proved disposition.

The following remain explicit adapter preconditions or exclusions:

- direct calls to low-level receive-ratchet, key-lookup, or deletion helpers;
- cloning ratchet state before a send and using multiple forks;
- rollback of persisted chain state;
- the production peer-map lookup and uniqueness refinement;
- correctness and provenance of concrete HKDF, AEAD, hash, allocation, authentication-result, serialization, array-mutation, and zeroization behavior;
- crash atomicity between concrete array mutation and publication of the returned core state;
- physical erasure of removed key material and compiler correspondence from the checked extraction to the deployed executable.

`SendKey` is a copyable logical availability value, not an affine Rust type. The core theorem threads the unavailable value returned by `finish_send` into a second call; it does not prevent copying the original available value or forking pre-send ratchet state. The high-level one-use statement therefore relies on the private production transaction keeping one capability beside one concrete key, not persisting the capability or reusing a copy, leaving no reusable copy after the call, calling `finish_send` once on every recoverable post-allocation outcome, and using one authoritative non-rollback ratchet state. Similarly, the core proves a pointwise peer frame rule, while the production map-selection refinement remains an adapter obligation tested by multi-peer protocol regressions.

## Regression coverage added

Stage 3 adds or strengthens tests for:

- verified lookup and concrete occupancy after multi-key derivation;
- exact non-last and last-slot removal behavior, including preservation of both key and nonce bytes for a moved sequence;
- unchanged logical state, receive-chain bytes, slot mapping, and concrete material after failed authentication and zero-cost retry;
- replay neutrality, full-capacity rejection, non-last release and refill, clone independence, and reset;
- successful stack-local send transactions, sequential advancement, direction matching, and exhaustion neutrality;
- the exact five-field persistence schema and rejection of legacy objects containing `send_past`;
- persistence round trips that compare remaining receive key and nonce bytes by sequence even when core slot order differs;
- serialization rejection for both a missing active concrete key and concrete material in an inactive slot;
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

The hax-generated ratchet module intentionally changes because lookup, detailed completion, and slot-returning restoration are now selected. Strict F* checking discharges the corresponding handwritten lemmas without `--lax`, `assume`, or `admit`; `check-generated` and `check-inventory` then ensure the reviewed generated artifacts and trust-boundary fingerprints match those checked sources. The `clippy::type-complexity` allowance applies to a pre-existing deserialization function outside the Stage 3 changes.

## Remaining rollout work

Stage 3 does not change the known PQXDH counterexamples or enable their formal
claims. The next planned work is to move PQXDH into role-specific typestates,
then fix and enable the registration authentication and replay tests before
adding the corresponding PQXDH and ProVerif proofs.

The protocol core remains `publish = false`, as established in the previous
stage. A future crates.io release of the root package therefore needs an explicit
publication or vendoring strategy for the core crate.
