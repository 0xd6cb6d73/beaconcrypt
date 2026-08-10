<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 3 implementation

## Status and scope

Stage 3 connects the symmetric-ratchet state machine introduced in Stages 1
and 2 to the production `BeaconCryptPqxdh` path. The implementation was based
on commit `78482e8498ea77b11fd5a565559746319a35f3f3`, which contained the
standalone protocol core, its hax extraction, and the F* lemmas, but left the
production `RatchetManager` unchanged.

This stage covers the production adapter for symmetric-ratchet control state,
key lifecycle, authentication completion, and persistence restoration. It does
not move PQXDH into the core; that remains Stage 4.

## Implementation map

| File | Responsibility |
| --- | --- |
| `Cargo.toml` and `Cargo.lock` | Make `beaconcrypt-protocol-core` a production dependency. |
| `src/shared.rs` | Store authoritative core state and adapt concrete KDF, AEAD, send, receive, and reset operations to core transitions. |
| `src/ser.rs` | Preserve the persistence format while serializing counters from core state. |
| `src/deser.rs` | Validate persisted state and rebuild the core through its checked restoration typestate. |
| `crates/protocol-core` | Provide the extracted transition API and the already checked F* model and lemmas. |

No generated F* file was hand-edited in this stage.

## Production state representation

`RatchetManager` no longer stores independent `send_ctr` and `recv_ctr`
fields. It contains one `beaconcrypt_protocol_core::RatchetState`, named
`control`, which is authoritative for:

- the next send sequence;
- the highest derived receive sequence;
- receive-window admission;
- logical ownership of cached receive keys;
- receive-key retention and consumption.

Concrete cryptographic material stays in the production adapter:

- `send_key` and `recv_key` hold the opaque HKDF chain bytes;
- `send_past` holds concrete AEAD send keys and nonces;
- `recv_past` is a fixed array holding concrete AEAD receive keys and nonces in the physical slots assigned by the core;
- `send_capabilities` pairs each pending concrete send key with the logical
  `SendKey` returned by the core.

The principal receive refinement invariant is:

```text
recv_past[slot].is_some() == (slot < control.receive_cache_len())
```

The adapter checks this invariant in debug builds after construction and every receive-cache mutation. It also checks that pending concrete send keys and logical send capabilities have equal sequence sets.

The public C constant for the receive gap retains a literal initializer because
cbindgen cannot evaluate a cross-crate constant path. A compile-time assertion
requires that literal to equal `beaconcrypt_protocol_core::RATCHET_MAX_GAP`, so
the C binding cannot silently diverge from the verified value.

## Send transition

A production send now follows this sequence:

1. `advance_send(control)` decides whether a sequence can be allocated. Counter
   exhaustion returns `None` without changing either core or concrete state.
2. For an admitted sequence, the adapter performs exactly one opaque HKDF step
   and stores the resulting concrete key and nonce under that sequence.
3. The logical `SendKey` returned by the core is stored under the same sequence.
4. The high-level encryption path uses the concrete key to perform AEAD,
   construct the commitment, and serialize the frame.
5. After the attempt, `finish_send` consumes the logical capability and the
   adapter removes the concrete key. This happens for successful encryption and
   every recoverable failure after allocation, including frame-serialization
   failure.

The resulting production state exposes neither the concrete key nor its logical
capability after a completed high-level send.

Persisted legacy states can contain pending `send_past` entries even though the
normal high-level API removes them before returning. During restoration the
adapter validates each sequence against `send_ctr` and reconstructs the matching
logical capability through the core send transition. This preserves the existing
wire format and low-level continuation behavior.

## Receive transition

A production receive now follows the verified planning and completion split:

1. `plan_receive_until(control, target)` decides admission before any KDF state
   is advanced. A target outside the gap or total-cache bound is state-neutral.
2. For each planned derivation, `advance_receive` adds one logical sequence and
   the adapter performs exactly one concrete HKDF step for that same sequence.
3. The adapter resolves the sequence through the core's verified array and requires a concrete key in that same physical `recv_past` slot before attempting commitment or AEAD verification.
4. Commitment or AEAD failure calls `finish_receive(..., false)`. The core
   returns `Retained`, and both logical and concrete representations remain
   available for an exact retry.
5. Successful AEAD verification calls `finish_receive(..., true)`. The core swap-removes the requested logical sequence, and the adapter applies the identical physical-slot swap to the concrete array.

Core receive slots are not treated as stable identifiers. Successful removal uses the core's swap-removal representation, and the adapter mirrors that swap in its parallel concrete array after resolving the current slot by sequence. Replay of an already consumed sequence therefore finds neither a logical nor a concrete key and is rejected without changing state.

An admissible forged future frame can still advance the receive chain and cache
keys before authentication fails. This matches the existing protocol semantics
described in the verification plan. Capacity and forward-gap rejection remain
state-neutral, while an admitted authentication failure retains the derived
candidate keys for retry.

## Persistence and compatibility

The serialized `RatchetManager` remains a six-field object:

```text
send_key, recv_key, send_past, send_ctr, recv_past, recv_ctr
```

No duplicate serialization of the core representation was added. `send_ctr`
and `recv_ctr` are emitted from the authoritative core getters.

Deserialization performs the following checked reconstruction:

1. validate every pending send sequence against `1..=send_ctr`;
2. collect and numerically sort all `recv_past` sequences;
3. call `start_restore(send_ctr, recv_ctr)`;
4. call `restore_receive_key` once for every sorted receive sequence;
5. reject the import if any append fails;
6. call `finish_restore` and pair the resulting core state with the concrete
   maps.

This rejects zero sequences, receive sequences above `recv_ctr`, and receive
caches larger than 50 entries. Collecting through a map establishes uniqueness,
and numeric sorting supplies the restoration builder with strictly increasing
input. The decision to reject more than 50 imported receive keys is intentional:
such states are outside the verified core state space, and normal high-level
traces cannot create them. The JSON syntax is unchanged, but previously
accepted oversized snapshots are no longer compatible.

Because the core uses packed swap-removal while restoration uses sorted input,
physical cache-slot order is not a persistence invariant. Round-trip tests
compare counters and logical sequence sets rather than slot layout.

## Proof correspondence boundary

The Stage 3 correspondence claim applies to high-level
`BeaconCryptPqxdh::encrypt_message` and `decrypt_message` traces that start from
a fresh or successfully validated state and do not roll state back.

The following remain explicit adapter preconditions or exclusions:

- direct calls to low-level ratchet, key lookup, or deletion helpers;
- cloning or restoring a state with a pending send key and then using multiple
  forks;
- rollback of persisted chain state;
- the production peer-map lookup and uniqueness refinement;
- correctness, secrecy, and erasure behavior of HKDF, AEAD, hash, allocation,
  serialization, and zeroization implementations.

`SendKey` is a logical availability value, not an affine Rust type. The
high-level one-use statement follows from the adapter keeping one capability per
concrete key and removing both after the operation; it is not a claim that Rust
prevents arbitrary callers from copying state. Similarly, the core proves a
pointwise peer frame rule, while the production map-selection refinement remains
an adapter obligation tested by multi-peer protocol regressions.

## Regression coverage added

Stage 3 adds or strengthens tests for:

- equality of the concrete receive-key set and the core logical set after
  derivation, retry retention, successful swap-removal, replay, clone, and
  reset;
- pairing and consumption of concrete send keys with logical send
  capabilities;
- reconstruction and later consumption of persisted pending send keys;
- persistence round trips where logical sets are equal but core slot order
  differs;
- acceptance of an exactly 50-key receive cache and rejection of 51 keys;
- continued use of the existing protocol, server-state, Rooterberg, and
  Wycheproof tests through the production adapter.

## Validation performed

The implementation was checked with:

```sh
cargo fmt --all -- --check
cargo test --workspace --all-targets --locked
cargo check --locked --no-default-features --features pqxdh,server --lib
cargo check --locked --no-default-features --features pqxdh,beacon --lib
cargo clippy --workspace --all-targets --all-features --locked -- \
  -D warnings -A clippy::type-complexity
make -C crates/protocol-core check-generated
```

The workspace test run completed with 141 passing tests. Three registration
tests remain ignored because they are the known Stage 5 protocol
counterexamples, not Stage 3 failures. Hax regenerated byte-identical F* output,
and strict F* checking discharged the extracted ratchet module and its manual
lemmas without `--lax`.

The `clippy::type-complexity` allowance applies to a pre-existing deserialization
function outside the Stage 3 changes.

## Remaining rollout work

Stage 3 does not change the known PQXDH counterexamples or enable their formal
claims. The next planned work is to move PQXDH into role-specific typestates,
then fix and enable the registration authentication and replay tests before
adding the corresponding PQXDH and ProVerif proofs.

The protocol core remains `publish = false`, as established in the previous
stage. A future crates.io release of the root package therefore needs an explicit
publication or vendoring strategy for the core crate.
