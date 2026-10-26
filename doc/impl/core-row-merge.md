# Row persistence integration into the extracted portable core

This merge candidate combines `codex/core-lifecycle` at `eda5a18424d816d9e1f5ba86eafbdae5da788411` with `codex/concurrent-persistence` at `2b38ad523f6e4b67f4a38f431636101f4a14be6a`. It uses a direct merge to preserve both development histories and historical benchmark provenance. The target branch itself remains unchanged while this candidate is reviewed.

## Preservation requirements

The complete `beaconcrypt-core` subtree, extracted protocol controllers, proof assertions, generated artifacts and existing proof deferrals must remain unchanged from the target. The adapter remains an `rlib` supporting `no_std + alloc`, using the portable `beaconcrypt-crypto` backend; hosted native artifacts continue to use `beaconcrypt-ffi`. Database drivers remain example/test dependencies only.

Row and cached-row operations retain the existing transaction contract, two-phase durable registration, core-owned protocol decisions, exact committed-row cache validation, and commit-before-output behavior. Peer restoration reconstructs the core session binding with identity and row context rather than restoring context-free operational peers. Explicit RNG methods support portable registration and creation; hosted convenience APIs remain available.

## Validation

The runtime validation covers the merged implementation, including row and cached-row property tests, concurrent database writers, replay/rollback paths, caller-entropy failure at each registration draw, contextual peer restoration, and vacant-only peer insertion. The new entropy property test also checks that an explicitly empty registration response fails after acceptance while retaining the durable replay marker. The regression seed for that boundary is retained.

The base already defers 22 exact proof-source checks; their assertions and exclusion list remain unchanged in this merge. See `no-std-core-lifecycle-deferred.json`. No proof verification or regeneration was performed. The complete `beaconcrypt-core` subtree retains tree `16ef0be42e3fff3facf21da48b48da7a7756910c`; the crypto backend and parser subtrees are also unchanged from the target.

The independent downstream build script now exercises the row APIs and caller entropy on both `thumbv7em-none-eabihf` and `thumbv6m-none-eabi`. Each target builds four feature combinations using ordinary downstream Cargo builds. The latter verifies the `Rc` identity-sharing path on a target without pointer atomics; hosted targets retain `Arc` and `Server: Send + Sync`.

The binding checks build the separate `beaconcrypt-ffi` package and exercise native Go with the race detector, the C persistence harness, all 97 Python tests, and eight packaging tests. The generated C header contains the added row API; regeneration changes no existing declarations. Both Go/Wasm build modes retain explicit unsupported row constructors.

The final all-feature runtime suite passed 533 tests, with exactly the 22 inherited proof-source exclusions. Workspace all-target Clippy passed with only existing core/WASI warnings. The focused mutation audit selected 74 mutations: 36 were caught and 38 failed to compile because of source type or constructor errors, with no survivors or timeouts. Parent-wide mutation receipts remain historical and are not claimed as measurements of this merged tree. Commands, source hashes and log hashes are recorded in the [runtime receipt](core-row-merge-validation.json) and [binding receipt](core-row-merge-bindings.json). Historical benchmark results describe their recorded revisions and backends; this integration does not rerun or reinterpret those measurements.

## Integration

The candidate branch is `codex/core-row-merge`, based directly on `codex/core-lifecycle`. Once reviewed, the target can fast-forward to this merge commit. There is no new design decision requiring user input. The inherited proof-source deferrals remain a follow-up item, as they were on the target before this merge.
