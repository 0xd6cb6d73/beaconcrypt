<!-- SPDX-License-Identifier: 0BSD -->

# beaconcrypt protocol core

This `no_std` crate is the extraction boundary for beaconcrypt's protocol
state machines. It intentionally has no cryptographic, serialization, FFI, or
runtime dependencies. See the repository's
[formal verification plan](../../doc/formal-verification.md) for the intended
boundary and proof inventory.

The crate contains the complete control-plane state machine for the symmetric
ratchet. It owns counters, receive-key availability, receive-window admission,
one-use send capabilities, authentication completion, restoration validation,
and pointwise peer selection. Cryptographic chain bytes and concrete message
keys stay behind the adapter boundary.

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

## Strict hax/F* verification

From this directory, run:

```sh
make verify
```

The target enters the pinned hax Nix shell, regenerates
`proofs/fstar/extraction/Beaconcrypt_protocol_core.Ratchet.fst`, and fully
checks that module, its dependencies, and the hand-maintained lemmas in
`proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst`. It never passes
`--lax`.

The checked properties cover send and receive counter monotonicity and
exhaustion, receive-gap and cache bounds, retry retention, exact key
consumption and replay rejection, one-use send keys, and non-selected peer
isolation. `make check-generated` additionally fails when a tracked extraction
changes, which is suitable for a generated-diff CI check.

The hax revision is
`5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3` (hax 0.3.7). Its lock file pins
the coupled tools used here, including Rust nightly 2025-11-08 (rustc 1.93.0),
F* v2025.10.06, and Z3 4.13.3.
