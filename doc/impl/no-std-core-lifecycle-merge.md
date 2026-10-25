# Merge portable crypto onto the extracted protocol core

Target: `codex/core-lifecycle` at `2b924febc49b9a5e6fb93990ff8d4b053b7ca4b2`. Incoming: `codex/no-std-rustcrypto` at `30cbdc6a30a36867cc0ec4eddde96cdc5e0842c9`. Common base: `278204b921ae31a3e900cf21f690184173e531f5`.

The extraction branch takes priority. Keep its core controllers, registration/agreement/record/peer/transport flow, session ownership, proof files and proof assertions unchanged. Resolve adapter conflicts by applying portable imports, RustCrypto/Dalek primitives and caller entropy around that flow. Reconstruct restored peer maps with identity-keyed hashers and fallible reservation.

Server agreement draws from the caller RNG for ephemeral key generation and KEM encapsulation. Beacon completion supplies a private rejecting entropy source because its extracted agreement needs no new randomness; an unexpected entropy request fails closed.

Validation passed: all-feature workspace Clippy; strict Clippy for the adapter, backend and native package; warning-free hosted no_std beacon/server checks; 471 all-feature Rust runtime tests including differential/vector/protocol/persistence/binding coverage; four independent Thumb consumer configurations; 27 WASI tests plus the allocation-failure probe; eight packaging tests; both Go Wasm modes; native Go race tests and the C persistence harness; 79 Python tests; and a wheel built from the unpacked Git source archive. The C header is unchanged. Details are recorded in the [runtime receipt](no-std-core-lifecycle-validation.json), [bindings receipt](no-std-core-lifecycle-bindings.json) and [portable receipt](no-std-core-lifecycle-portable.json).

The 22 explicitly deferred source-fidelity checks comprise the original five plus 17 extraction-era checks whose baselines pin the previous native backend identifiers or exact interpreter bodies. All other 20 source-fidelity checks remain enabled and passed. Their assertions are unchanged; [the deferral receipt](no-std-core-lifecycle-deferred.json) records each identity and diagnostic. Proof migration and regeneration remain outside this merge, as requested.

The complete `beaconcrypt-core` subtree, including its proof files, is byte-for-byte unchanged from the target parent (tree `16ef0be42e3fff3facf21da48b48da7a7756910c`). Existing parent mutation and library-size receipts describe their named parent checkpoints, not this merged tree.
